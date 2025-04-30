from fastapi import FastAPI
from pydantic import BaseModel
import uvicorn

from models import SimplePremise
from retrieve import corpus, retrieve_premises, add_premise_to_corpus_index, added_premises, MAX_NEW_PREMISES, MAX_K, RetrievalRequest

app = FastAPI()

@app.post("/retrieve")
def retrieve(request: RetrievalRequest):
    if request.k <= 0:
        return []
    if request.k > MAX_K:
        request.k = MAX_K
    if len(request.new_premises) > MAX_NEW_PREMISES:
        request.new_premises = request.new_premises[:MAX_NEW_PREMISES]

    premises = retrieve_premises(
        states=request.state,
        imported_modules=request.imported_modules,
        local_premises=request.local_premises,
        new_premises=request.new_premises,
        k=request.k
    )
    return premises

@app.get("/max-new-premises")
def max_new_premises():
    return MAX_NEW_PREMISES

@app.get("/indexed-premises")
def indexed_premises():
    premises = [premise.name for premise in corpus.unfiltered_premises]
    return premises

@app.get("/indexed-modules")
def indexed_modules():
    modules = corpus.modules
    return modules

if False:
    class AddPremiseRequest(BaseModel):
        name: str
        decl: str
        module: str

    @app.post("/add-premise")
    def add_premise(request: AddPremiseRequest):
        premise = SimplePremise(
            name=request.name,
            decl=request.decl,
            module=request.module,
        )
        add_premise_to_corpus_index(premise)
        return {"success": True, "warning": "use /retrieve instead with new_premises"}

    @app.route("/added-premises", methods=["GET"])
    def added_premises_():
        return added_premises

if __name__ == "__main__":
    uvicorn.run(app, host="127.0.0.1", port=5000, workers=2)
