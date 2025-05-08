# WIP script to retrieve premises using the model
# Notebook version: see retrieve.ipynb on Colab
# RAM: 4.8 GB on Colab

from collections import OrderedDict
import logging
import os
import shutil
import tarfile
from typing import Optional, List, Dict, Union, Literal, Set

import numpy as np
from sentence_transformers import SentenceTransformer
import torch
from huggingface_hub import hf_hub_download
import faiss
from pydantic import BaseModel

from models import Corpus, PremiseSet, Premise

GPU_AVAILABLE = torch.cuda.is_available()
DATA_DIR = os.path.join(os.path.dirname(os.path.realpath(__file__)), "data")
# TODO tune this number
# (Thomas) Especially with the LRU cache, I think the primary bottleneck
# for increasing this number is on the user side:
# the time it takes to pretty-print all the new statements.
# For 2048, this is ~4 seconds
MAX_NEW_PREMISES = 2048 if GPU_AVAILABLE else 256
# TODO tune this number
# Batch size for encoding new premises
MINIBATCH_SIZE = 32 if GPU_AVAILABLE else 16
MAX_K = 1024

logger = logging.getLogger(__name__)

# TODO: hardcoded
model = SentenceTransformer("hanwenzhu/all-distilroberta-v1-lr2e-4-bs256-nneg3-ml-ne5-may07")
embedding_precision: Literal["float32", "int8", "uint8", "binary", "ubinary"] = "float32"

# Get corpus of premises, including their names and serialized expressions
# TODO: hardcoded
file_path = hf_hub_download(repo_id="hanwenzhu/wip-lean-embeddings", filename="mathlib_premises_418.tar.gz", revision="main")
logger.info(f"Mathlib declarations data saved to {file_path}")
if os.path.isdir(DATA_DIR):
    logger.info(f"Removing Mathlib declarations data at {DATA_DIR}")
    shutil.rmtree(DATA_DIR)
with tarfile.open(file_path, "r:gz") as tar:
    logger.info(f"Extracting Mathlib declarations data to {DATA_DIR}")
    tar.extractall(DATA_DIR)
ntp_toolkit_mathlib_path = os.path.join(DATA_DIR, "Mathlib")
corpus = Corpus.from_ntp_toolkit(ntp_toolkit_mathlib_path)

# Build index from corpus embeddings
def build_index(use_hub_embeddings=True) -> faiss.Index:
    if use_hub_embeddings:
        # TODO: hardcoded
        file_path = hf_hub_download(
            repo_id="hanwenzhu/wip-lean-embeddings",
            filename="embeddings_all-distilroberta-v1-lr2e-4-bs256-nneg3-ml-ne5_416.npy",
            revision="main"
        )
        corpus_embeddings = np.load(file_path)
    else:
        corpus_embeddings = model.encode(
            [premise.to_string() for premise in corpus.premises],
            show_progress_bar=True,
            batch_size=32,
            convert_to_tensor=True,
        )
    assert corpus_embeddings.shape == (
        len(corpus.premises),
        model.get_sentence_embedding_dimension()
    )

    # Build index to search from using FAISS
    index = faiss.IndexFlatIP(corpus_embeddings.shape[1])
    # NOTE: see README
    # if faiss.get_num_gpus() > 0:
    #     logger.info("Using FAISS on GPU")
    #     res = faiss.StandardGpuResources()  # type: ignore
    #     gpu_idx = 0  # TODO
    #     index = faiss.index_cpu_to_gpu(res, gpu_idx, index)  # type: ignore
    # else:
    logger.info("Using FAISS on CPU")
    index.add(corpus_embeddings)  # type: ignore

    return index

index = build_index()  # wrapping in a function for garbage collection


# Classes for retrieval API
class NewPremise(BaseModel):
    name: str
    decl: str

class RetrievalRequest(BaseModel):
    state: str  # str | List[str] is technically possible
    imported_modules: Optional[List[str]] = None  # Legacy support, TODO remove
    local_premises: List[str | int]
    new_premises: List[NewPremise]
    k: int


class LRUCache:
    def __init__(self, maxsize: int):
        self.cache: OrderedDict[str, np.ndarray] = OrderedDict()
        self.maxsize = maxsize

    def __getitem__(self, key: str) -> np.ndarray:
        self.cache.move_to_end(key)
        return self.cache[key]

    def __setitem__(self, key: str, value: np.ndarray):
        if key in self.cache:
            self.cache.move_to_end(key)
        self.cache[key] = value
        if len(self.cache) > self.maxsize:
            self.cache.popitem(last=False)

    def __contains__(self, key: str):
        return key in self.cache

    def __len__(self):
        return len(self.cache)

embedding_cache = LRUCache(maxsize=32768)  # 32768 items * 768 dimensions * float32 = 192 MB

def embed(states: List[str], premises: List[str]):
    if not states:
        raise ValueError("Empty list of states")
    premises_to_embed = []
    premise_embeddings = np.empty((len(premises), index.d), dtype=embedding_precision)
    for i, premise in enumerate(premises):
        if premise in embedding_cache:
            premise_embeddings[i] = embedding_cache[premise]
        else:
            premises_to_embed.append((i, premise))
    packed_embeddings = model.encode(
        states + [text for _, text in premises_to_embed],
        batch_size=MINIBATCH_SIZE,
        precision=embedding_precision
    )
    state_embeddings = packed_embeddings[:len(states)]
    computed_premise_embeddings = packed_embeddings[len(states):]
    for (i, premise), embedding in zip(premises_to_embed, computed_premise_embeddings):
        embedding_cache[premise] = embedding
        premise_embeddings[i] = embedding
    return state_embeddings, premise_embeddings


def retrieve_premises_core(states: Union[str, List[str]], k: int, new_premises: List[NewPremise], **kwargs):
    if isinstance(states, str):
        return_list = False
        states = [states]
    else:
        return_list = True

    # Embed states and new premises
    new_premise_decls = [premise_data.decl for premise_data in new_premises]
    state_embeddings, new_premise_embeddings = embed(states, new_premise_decls)

    # Retrieve premises from indexed premises
    scoress, indicess = index.search(state_embeddings, k, **kwargs)  # type: ignore
    scored_indexed_premises = [
        [
            # TODO: make this a class
            {"score": score.item(), "name": corpus.premises[i].name}
            for score, i in zip(scores, indices)
            if i >= 0  # FAISS returns -1 with `sel`
        ]
        for scores, indices in zip(scoress, indicess)
    ]

    # Rank new premises
    new_scoress = model.similarity(state_embeddings, new_premise_embeddings)
    scored_new_premises = [
        [
            {"score": score.item(), "name": premise_data.name}
            for score, premise_data in zip(scores, new_premises)
        ]
        for scores in new_scoress
    ]

    # Combine indexed and new premises
    scored_premises = [
        sorted(indexed + new, key=lambda p: p["score"], reverse=True)[:k]
        for indexed, new in zip(scored_indexed_premises, scored_new_premises)
    ]

    if return_list:
        return scored_premises
    else:
        return scored_premises[0]

def retrieve_premises(
    states: Union[str, List[str]],
    imported_modules: Optional[List[str]],
    local_premises: List[str | int],
    new_premises: List[NewPremise],
    k: int
):
    """Retrieve premises from all indexed premises in:
    indexed premises in local_premises + unindexed premises in new_premises.

    In case of duplicate names, the signature in `new_premises` overrides the signature indexed on the server.
    """
    if k > MAX_K:
        raise ValueError(f"value of k ({k}) exceeds maximum ({MAX_K})")

    # Accessible premises from the state, starting from imported modules
    accessible_premises: Set[str] = set()

    # Legacy support, TODO remove
    if imported_modules is not None:
        imported_modules_set = set(imported_modules)
        for premise in corpus.premises:
            if premise.module in imported_modules_set:
                accessible_premises.add(premise.name)

    if len(new_premises) > MAX_NEW_PREMISES:
        raise ValueError(f"{len(new_premises)} new premises uploaded, exceeding maximum ({MAX_NEW_PREMISES})")

    # Add local_premises to accessible premises
    for name in local_premises:
        # A new version of the client side optimizes by only sending the index
        # Here we allow both versions
        if isinstance(name, int) and 0 <= name < len(corpus.unfiltered_premises):
            name = corpus.unfiltered_premises[name].name
        if name in corpus.name2premise:
            accessible_premises.add(name)
        else:
            continue  # not raising an error, because the supplied local premises are unfiltered, so might not be in corpus

    # Remove user-uploaded new premises from accessible set, because they override the server-side signature
    for premise_data in new_premises:
        name = premise_data.name
        if name in corpus.name2premise:
            # User-uploaded premise overrides server-side premise
            accessible_premises.remove(name)

    accessible_premise_idxs = [corpus.name2idx[name] for name in accessible_premises]
    # NOTE: the types of faiss Selector, SearchParameters, and Index should align
    sel = faiss.IDSelectorArray(accessible_premise_idxs)  # type: ignore
    kwargs = {}
    kwargs["params"] = faiss.SearchParameters(sel=sel)  # type: ignore

    return retrieve_premises_core(states, k, new_premises, **kwargs)

# original_modules: List[str] = corpus.modules.copy()
added_premises: List[str] = []
def add_premise_to_corpus_index(premise: Premise):
    """**Permanently** adds a premise to the index (for the current session).
    Warning: this is (as of currently) only intended for testing / easier benchmarking.
    In most cases, the `new_premises` field of /retrieve should be used instead.
    """
    # WARNING: this will override existing premise if their names coincide.
    # For now, only use for tests.
    # WARNING: this is not thread safe -- it relies on the order of corpus = the order of the index.
    # if premise.module in original_modules:
    #     raise ValueError("Added premise is not from a new module")
    if premise.module in corpus.module_to_premises and premise.name in corpus.module_to_premises[premise.module]:
        # We don't add duplicate premises from the same module
        return
    corpus.add_premise(premise)
    premise_embedding = model.encode([premise.to_string()])
    index.add(premise_embedding)  # type: ignore
    added_premises.append(premise.name)

# def remove_added_modules():
#     """Remove all new modules added using `add_premise_to_corpus_index`.
#     Warning: same as `add_premise_to_corpus_index`, this is currently for test only.
#     It depends on the client only adding premises from new modules."""
#     for module in corpus.modules:
#         if module not in original_modules:
#             del corpus.module_to_premises[module]
#     corpus.modules = original_modules
