# WIP script to retrieve premises using the model
# Notebook version: see retrieve.ipynb on Colab
# RAM: 4.8 GB on Colab

import os
from typing import Optional, List, Dict, Union

import numpy as np
from sentence_transformers import SentenceTransformer
import torch
from huggingface_hub import hf_hub_download
import faiss

from models import Corpus, PremiseSet, Premise

model = SentenceTransformer("hanwenzhu/all-distilroberta-v1-lr2e-4-bs256-nneg3-ml-mar13")

# Get corpus of premises, including their names and serialized expressions
file_path = hf_hub_download(repo_id="hanwenzhu/wip-lean-embeddings", filename="mathlib_premises_416.tar.gz", revision="main")
print(f"Mathlib declarations data saved to {file_path}")
# !tar -xf {file_path}
ntp_toolkit_mathlib_path = "./Mathlib"
corpus = Corpus.from_ntp_toolkit(ntp_toolkit_mathlib_path)


# Get corpus embeddings
file_path = hf_hub_download(repo_id="hanwenzhu/wip-lean-embeddings", filename="embeddings_mathlib_416.npy", revision="main")
corpus_embeddings = np.load(file_path)
# Note that these embeddings were generated using the following (takes too long on a CPU):
# corpus_embeddings = model.encode(
#     [premise.to_string() for premise in corpus_premises],
#     show_progress_bar=True,
#     batch_size=32,
#     convert_to_tensor=True,
# )

assert corpus_embeddings.shape[0] == len(corpus.premises)

# Build index to search from using FAISS
index = faiss.IndexFlatIP(corpus_embeddings.shape[1])
index.add(corpus_embeddings)  # type: ignore


def retrieve_premises_core(states: Union[str, List[str]], k=8, new_premises: Optional[List[Dict[str, str]]] = None, **kwargs):
    if isinstance(states, str):
        return_list = False
        states = [states]
    else:
        return_list = True

    # Retrieve premises from indexed premises
    state_embeddings = model.encode(states)
    scoress, indicess = index.search(state_embeddings, k, **kwargs)  # type: ignore
    scored_indexed_premises = [
        [
            # TODO: remove `"premise"` here
            # TODO: make this a class
            {"score": score.item(), "name": corpus.premises[i].name, "decl": corpus.premises[i].to_string()}
            for score, i in zip(scores, indices)
        ]
        for scores, indices in zip(scoress, indicess)
    ]

    # Embed and rank new user-defined premises
    if not new_premises:
        new_premises = []
        # new_premise_embeddings = torch.zeros(0, state_embeddings.shape[1]).to(state_embeddings)
        new_premise_embeddings = np.zeros((0, state_embeddings.shape[1]), dtype=state_embeddings.dtype)
    else:
        new_premise_embeddings = model.encode([premise_data["decl"] for premise_data in new_premises])
    new_scoress = model.similarity(state_embeddings, new_premise_embeddings)
    scored_new_premises = [
        [
            # TODO: remove `"premise"` here
            {"score": score.item(), "name": premise_data["name"], "decl": premise_data["decl"]}
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
    new_premises: Optional[List[Dict[str, str]]],
    k: int
):
    kwargs = {}
    if imported_modules is None:
        imported_modules = []
    accessible_premises = PremiseSet(corpus, set(imported_modules))
    # NOTE: corpus.accessible_premises is currently not used by the server
    # which should be taken into account in a future refactor
    # accessible_premises = corpus.accessible_premises(module, line, column)
    if new_premises is not None:
        for premise_data in new_premises:
            # TODO: better JSON schema handling
            name = premise_data["name"]
            if name in corpus.name2premise:
                premise = corpus.name2premise[name]
                # User-uploaded premise overrides server-side premise
                accessible_premises.remove(premise)
    sel = faiss.PyCallbackIDSelector(lambda i: corpus.premises[i] in accessible_premises)
    kwargs["params"] = faiss.SearchParametersHNSW(sel=sel)  # type: ignore
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
