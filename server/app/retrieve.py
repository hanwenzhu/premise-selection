# WIP script to retrieve premises using the model

from collections import OrderedDict
import logging
import os
import shutil
import tarfile
from typing import Optional, List, Dict, Union, Literal, Set

import numpy as np
import faiss
import httpx
from pydantic import BaseModel

from models import Corpus, PremiseSet, Premise

DATA_DIR = os.environ["DATA_DIR"]
MATHLIB_DIR = os.path.join(DATA_DIR, "Mathlib")
PRECOMPUTED_EMBEDDINGS_PATH = os.environ["PRECOMPUTED_EMBEDDINGS_PATH"]

EMBED_SERVICE_URL = os.environ["EMBED_SERVICE_URL"]
EMBED_SERVICE_TIMEOUT = int(os.environ["EMBED_SERVICE_TIMEOUT"])

MAX_NEW_PREMISES = int(os.environ["MAX_NEW_PREMISES"])
MAX_CLIENT_BATCH_SIZE = int(os.environ["MAX_CLIENT_BATCH_SIZE"])
MAX_K = int(os.environ["MAX_K"])
DTYPE = os.environ["DTYPE"]
assert DTYPE in ["float32", "float16"]

logger = logging.getLogger(__name__)

# Get corpus of premises, including their names and serialized expressions
if os.path.isdir(MATHLIB_DIR):
    logger.info(f"Using saved declarations at {MATHLIB_DIR}")
else:
    raise FileNotFoundError(f"Run download_data.py to save data to {MATHLIB_DIR} first")
corpus = Corpus.from_ntp_toolkit(MATHLIB_DIR)

# Build index from corpus embeddings
def build_index(use_precomputed=True) -> faiss.Index:
    if use_precomputed:
        corpus_embeddings = np.load(PRECOMPUTED_EMBEDDINGS_PATH)
    else:
        from sentence_transformers import SentenceTransformer
        MODEL_ID = os.environ["MODEL_ID"]
        model = SentenceTransformer(MODEL_ID)
        corpus_embeddings = model.encode(
            [premise.to_string() for premise in corpus.premises],
            show_progress_bar=True,
            batch_size=32,
            convert_to_tensor=True,
        )
    assert corpus_embeddings.shape[0] == len(corpus.premises)

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

async def encode(texts: List[str]):
    async with httpx.AsyncClient() as client:
        response = await client.post(
            f"{EMBED_SERVICE_URL}/embed",
            json={"inputs": texts},
            timeout=EMBED_SERVICE_TIMEOUT
        )
        response.raise_for_status()
        embeddings = response.json()["embeddings"]
    return np.array(embeddings, dtype=DTYPE)

async def embed(states: List[str], premises: List[str]):
    if not states:
        raise ValueError("Empty list of states")
    premises_to_embed = []
    premise_embeddings = np.empty((len(premises), index.d), dtype=DTYPE)
    for i, premise in enumerate(premises):
        if premise in embedding_cache:
            premise_embeddings[i] = embedding_cache[premise]
        else:
            premises_to_embed.append((i, premise))
    packed_embeddings = await encode(
        states + [text for _, text in premises_to_embed],
    )
    state_embeddings = packed_embeddings[:len(states)]
    computed_premise_embeddings = packed_embeddings[len(states):]
    for (i, premise), embedding in zip(premises_to_embed, computed_premise_embeddings):
        embedding_cache[premise] = embedding
        premise_embeddings[i] = embedding
    return state_embeddings, premise_embeddings


async def retrieve_premises_core(states: List[str], k: int, new_premises: List[NewPremise], **kwargs):
    # Embed states and new premises
    new_premise_decls = [premise_data.decl for premise_data in new_premises]
    state_embeddings, new_premise_embeddings = await embed(states, new_premise_decls)

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
    new_scoress = np.matmul(state_embeddings, new_premise_embeddings.T)
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

    return scored_premises

async def retrieve_premises(
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

    if isinstance(states, str):
        premises = await retrieve_premises_core([states], k, new_premises, **kwargs)
        return premises[0]
    else:
        premises = await retrieve_premises_core(states, k, new_premises, **kwargs)
        return premises

# original_modules: List[str] = corpus.modules.copy()
added_premises: List[str] = []
async def add_premise_to_corpus_index(premise: Premise):
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
    premise_embedding = await encode([premise.to_string()])
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
