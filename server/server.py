from flask import Flask, request, jsonify
from retrieve import corpus, retrieve_premises

app = Flask(__name__)

@app.route("/retrieve", methods=["POST"])
def retrieve():
    data = request.json
    if not data:
        return jsonify({"error": "No JSON data provided"}), 400
    state = data["state"]
    imported_modules = data.get("imported_modules")
    new_premises = data.get("new_premises")
    k = data.get("k", 256)
    if k <= 0:
        return jsonify([])

    # Legacy support
    if new_premises is None and data.get("local_premises"):
        new_premises = [{"name": name, "decl": corpus.name2premise[name].to_string()} for name in data["local_premises"] if name in corpus.name2premise]

    premises = retrieve_premises(state, imported_modules, new_premises, k=k)
    return jsonify(premises)

@app.route("/indexed-premises", methods=["GET"])
def indexed_premises():
    premises = [premise.name for premise in corpus.unfiltered_premises]
    return jsonify(premises)

@app.route("/indexed-modules", methods=["GET"])
def indexed_modules():
    modules = corpus.modules
    return jsonify(modules)

if __name__ == "__main__":
    app.run(debug=False)
