import Lean.PremiseSelection
import Lean.Server.Utils
import PremiseSelection.Basic

namespace Lean.PremiseSelection.Cloud

open Meta

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

def selectPremisesCore (apiUrl : String) (state : String) (importedModules localPremises : Option (Array Name))
    (k : Nat) : IO (Array Suggestion) := do
  let data := Json.mkObj [
    ("state", .str state),
    ("imported_modules", toJson importedModules),
    ("local_premises", toJson localPremises),
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

initialize Lean.registerTraceClass `premiseSelection.debug

def selectPremises (goal : MVarId) (k : Nat) : MetaM (Array Suggestion) := do
  let env ← getEnv
  let state ← withOptions (fun o => (o.set `pp.notation false).set `pp.fullNames true) $ Meta.ppGoal goal
  let state := state.pretty
  trace[premiseSelection.debug] m!"State: {state}"

  let importedModules := env.allImportedModuleNames
  let localPremises := env.constants.map₂.foldl (fun arr name _ => arr.push name) #[]
  let apiUrl ← getApiUrlM

  let suggestions ← profileitM Exception "Cloud.selectPremises" (← getOptions) do
    selectPremisesCore apiUrl state importedModules localPremises k
  trace[premiseSelection.debug] m!"Suggestions: {suggestions}"

  return suggestions

def premiseSelector : Selector := fun goal config => do
  let premises ← selectPremises goal (config.maxSuggestions.getD 16)
  premises.filterM fun suggestion => config.filter suggestion.name

end Lean.PremiseSelection.Cloud
