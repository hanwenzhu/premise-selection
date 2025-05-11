

## Server setup

Run

```sh
python download_data.py
```

which downloads Mathlib data in JSONL and pre-computed embeddings for them to `server/data`.

This also means this should be re-ran for every data or model update.

## Deployment

Go to directory `server`.

Set the relevant variables in `.env`. The important ones are: `TEI_VERSION` (for switching to CPU or different GPU backends for Hugging Face text-embeddings-inference); `MAX_BATCH_TOKENS` (see text-embeddings-inference README).

To start, run
```sh
docker compose up
```
which runs the service on `http://0.0.0.0:80`.

#### Misc
Information on faiss-gpu:
* To install both faiss and pytorch on GPU, I recommend `conda install pytorch::faiss-gpu conda-forge::pytorch-gpu` as of April 2025 because `pytorch::pytorch` is discontinued while `conda-forge::faiss-gpu` did not work for me.
* However, preliminary results show that faiss-cpu is just as fast, and faiss-gpu doesn't support selectors which is critical for us. So we use faiss-cpu instead.
