## Server setup

Install the following Python dependencies:
* `fastapi[standard]`
* `sentence-transformers`
* `torch` (CPU)
* `faiss` (CPU)
* `huggingface_hub`
* `pydantic`

TODO: GPU is not supported yet.

## Deployment

```sh
uvicorn main:app --workers <num_workers>
```

(Set `--host` and `--port` as needed)
