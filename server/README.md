## Server setup

Install the following Python dependencies:
* `fastapi[standard]`
* `sentence-transformers`
* `torch` (CPU/GPU)
* `faiss` (CPU/GPU)
* `huggingface_hub`

(For GPU, I recommend `conda install pytorch::faiss-gpu conda-forge::pytorch-gpu` as of April 2025 because `pytorch::pytorch` is discontinued while `conda-forge::faiss-gpu` did not work for me.)

## Deployment

```sh
uvicorn main:app --workers <num_workers>
```

(Set `--host` and `--port` as needed)
