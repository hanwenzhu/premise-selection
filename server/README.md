## Server setup

Install the following Python dependencies:
* `fastapi[standard]`
* `sentence-transformers`
* `torch` (CPU/GPU)
* `faiss` (CPU)
* `huggingface_hub`

Information on faiss-gpu:
* To install both faiss and pytorch on GPU, I recommend `conda install pytorch::faiss-gpu conda-forge::pytorch-gpu` as of April 2025 because `pytorch::pytorch` is discontinued while `conda-forge::faiss-gpu` did not work for me.
* However, preliminary results show that faiss-cpu is just as fast, and faiss-gpu doesn't support selectors which is critical for us. So we use faiss-cpu instead.

## Deployment

```sh
uvicorn main:app --workers <num_workers>
```

(Set `--host` and `--port` as needed)
