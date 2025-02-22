import PremiseSelection.Premise
import Lean.Server.Utils

namespace Lean.PremiseSelection.Cloud

section IndexedPremises

/-! Retrieving indexed premises and modules stored on the server -/

/-- Unfiltered list of all premises known by the server.
This is currently not used in Lean (but the API `/indexed-premises` will always be available). -/
def getIndexedPremises : IO NameSet := do
  let apiUrl := "http://52.206.70.13/indexed-premises"
  let curlArgs := #[
    "-X", "GET",
    "--user-agent", "LeanProver (https://leanprover-community.github.io/)",
    apiUrl
  ]
  let out ← IO.Process.output { cmd := "curl", args := curlArgs }

  if out.exitCode != 0 then
    IO.throwServerError <|
      "Could not send API request to retrieve premises. " ++
      s!"curl exited with code {out.exitCode}:\n{out.stderr}"

  match Json.parse out.stdout >>= fromJson? with
  | .ok (result : Array String) =>
      let mut names := ∅
      for name in result do
        names := names.insert name.toName
      return names
  | .error e => IO.throwServerError <|
      s!"Could not parse server output (error: {e})"

/-- All modules known by the server. -/
def getIndexedModules : IO NameSet := do
  let apiUrl := "http://52.206.70.13/indexed-modules"
  let curlArgs := #[
    "-X", "GET",
    "--user-agent", "LeanProver (https://leanprover-community.github.io/)",
    apiUrl
  ]
  let out ← IO.Process.output { cmd := "curl", args := curlArgs }

  if out.exitCode != 0 then
    IO.throwServerError <|
      "Could not send API request to retrieve modules. " ++
      s!"curl exited with code {out.exitCode}:\n{out.stderr}"

  match Json.parse out.stdout >>= fromJson? with
  | .ok (result : Array String) =>
      let mut moduleNames := ∅
      for moduleName in result do
        moduleNames := moduleNames.insert moduleName.toName
      return moduleNames
  | .error e => IO.throwServerError <|
      s!"Could not parse server output (error: {e})"

end IndexedPremises

register_option apiUrl : String := {
  defValue := "http://52.206.70.13/retrieve"
  descr := "The URL of the premise retrieval API"
}

def getApiUrl (opts : Options) : String :=
  apiUrl.get opts

def getApiUrlM : CoreM String := do
  let opts ← getOptions
  return getApiUrl opts

scoped instance : FromJson Suggestion where
  fromJson? json := do
    let name ← json.getObjValAs? Name "name"
    let score ← json.getObjValAs? Float "score"
    return { name, score }

scoped instance : ToString Suggestion where
  toString p := s!"{p.name} ({p.score})"

scoped instance : ToMessageData Suggestion where
  toMessageData p := s!"{p.name} ({p.score})"

initialize Lean.registerTraceClass `premiseSelection.debug

def selectPremisesCore (apiUrl : String) (state : String)
    (importedModules : Option (Array Name)) (newPremises : Option (Array Premise))
    (k : Nat) : IO (Array Suggestion) := do
  let data := Json.mkObj [
    ("state", .str state),
    ("imported_modules", toJson importedModules),
    ("new_premises", toJson newPremises),
    ("k", .num (.fromNat k)),
  ]
  let curlArgs := #[
    "-X", "POST",
    "--header", "Content-Type: application/json",
    "--user-agent", "LeanProver (https://leanprover-community.github.io/)",
    "--data-raw", data.compress,
    apiUrl
  ]
  let out ← IO.Process.output { cmd := "curl", args := curlArgs }

  if out.exitCode != 0 then
    IO.throwServerError <|
      "Could not send API request to select premises. " ++
      s!"curl exited with code {out.exitCode}:\n{out.stderr}"

  match Json.parse out.stdout >>= fromJson? with
  | .ok result => return result
  | .error e => IO.throwServerError <|
      s!"Could not parse premise retrieval output (error: {e})\nRaw output:\n{out.stdout}"

def selectPremises (goal : MVarId) (k : Nat) : MetaM (Array Suggestion) := do
  let env ← getEnv
  let state ← withOptions (fun o => (o.set `pp.notation false).set `pp.fullNames true) $ Meta.ppGoal goal
  let state := state.pretty
  trace[premiseSelection.debug] m!"State: {state}"

  let importedModules := env.allImportedModuleNames
  let indexedModules ← getIndexedModules
  let newPremises ← Premise.getPremises indexedModules
  let apiUrl ← getApiUrlM

  let suggestions ← profileitM Exception "Cloud.selectPremises" (← getOptions) do
    selectPremisesCore apiUrl state importedModules newPremises k

  trace[premiseSelection.debug] m!"Suggestions: {suggestions}"
  return suggestions

def premiseSelector : Selector := fun goal config => do
  let premises ← selectPremises goal (config.maxSuggestions.getD 16)
  premises.filterM fun suggestion => config.filter suggestion.name

end Lean.PremiseSelection.Cloud
