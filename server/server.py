from typing import Optional, List, Dict

from flask import Flask, request, jsonify

from models import SimplePremise
from retrieve import corpus, retrieve_premises, add_premise_to_corpus_index, added_premises, MAX_NEW_PREMISES, MAX_K

app = Flask(__name__)

@app.route("/retrieve", methods=["POST"])
def retrieve():
    data = request.json
    if not data:
        return jsonify({"error": "No JSON data provided"}), 400

    # TODO: better data validation method (eg pydantic/jsonschema)
    state: str | List[str] = data["state"]
    imported_modules: List[str] = data["imported_modules"]  # list of module names
    local_premises: List[str | int] = data["local_premises"]  # list of local premises indexed by the server
    new_premises: List[Dict[str, str]] = data["new_premises"]  # list of dicts with keys "name" and "decl", new (usually unindexed) premises
    k: int = data.get("k", 32)

    if k <= 0:
        return jsonify([])
    if k > MAX_K:
        k = MAX_K
        # return jsonify({"error": f"value of k ({k}) exceeds maximum ({MAX_K})"})
    if new_premises is not None and len(new_premises) > MAX_NEW_PREMISES:
        new_premises = new_premises[:MAX_NEW_PREMISES]
        # return jsonify({"error": f"{len(new_premises)} new premises uploaded, exceeding maximum ({MAX_NEW_PREMISES})"}), 400

    premises = retrieve_premises(state, imported_modules, local_premises, new_premises, k=k)
    return jsonify(premises)

@app.route("/max-new-premises", methods=["GET"])
def max_new_premises():
    return jsonify(MAX_NEW_PREMISES)

@app.route("/indexed-premises", methods=["GET"])
def indexed_premises():
    premises = [premise.name for premise in corpus.unfiltered_premises]
    return jsonify(premises)

@app.route("/indexed-modules", methods=["GET"])
def indexed_modules():
    modules = corpus.modules
    return jsonify(modules)

@app.route("/add-premise", methods=["POST"])
def add_premise():
    data = request.json
    if not data:
        return jsonify({"success": False, "error": "No JSON data provided"}), 400
    # TODO: better data validation method (eg pydantic/jsonschema)
    premise = SimplePremise(
        name=data["name"],
        decl=data["decl"],
        module=data["module"],
    )
    add_premise_to_corpus_index(premise)
    return jsonify({"success": True, "warning": "use /retrieve instead with new_premises"})

@app.route("/added-premises", methods=["GET"])
def added_premises_():
    return jsonify(added_premises)

if __name__ == "__main__":
    app.run(debug=False)
