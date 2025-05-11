# TODO run this in docker-compose.yaml

import logging
import os
import shutil
import tarfile

from huggingface_hub import hf_hub_download

DATA_DIR = os.path.join(os.path.dirname(os.path.realpath(__file__)), "data")
PRECOMPUTED_EMBEDDINGS_PATH = os.path.join(DATA_DIR, "embeddings.npy")

logger = logging.getLogger(__name__)

if os.path.isdir(DATA_DIR):
    logger.info(f"Removing Mathlib declarations data at {DATA_DIR}")
    shutil.rmtree(DATA_DIR)

# TODO: hardcoded
file_path = hf_hub_download(
    repo_id="hanwenzhu/wip-lean-embeddings",
    filename="mathlib_premises_418.tar.gz",
    revision="main"
)
logger.info(f"Mathlib declarations data saved to {file_path}")
with tarfile.open(file_path, "r:gz") as tar:
    logger.info(f"Extracting Mathlib declarations data to {DATA_DIR}")
    tar.extractall(DATA_DIR)

# TODO: hardcoded
file_path = hf_hub_download(
    repo_id="hanwenzhu/wip-lean-embeddings",
    filename="embeddings_all-distilroberta-v1-lr2e-4-bs256-nneg3-ml-ne5_418.npy",
    revision="main",
    local_dir=DATA_DIR,
)
shutil.move(file_path, PRECOMPUTED_EMBEDDINGS_PATH)
logger.info(f"Pre-computed embeddings saved to {PRECOMPUTED_EMBEDDINGS_PATH}")
