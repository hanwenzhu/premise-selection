import PremiseSelection.Premise
import Lean.Server.Utils

namespace Lean.PremiseSelection.Cloud

register_option apiBaseUrl : String := {
  defValue := "http://52.206.70.13"
  descr := "The base URL of the premise retrieval API"
}

def getApiBaseUrl (opts : Options) : String :=
  apiBaseUrl.get opts

section IndexedPremises

/-! Retrieving indexed premises and modules stored on the server -/

/-- Unfiltered list of all premises known by the server.
This is currently not used in Lean (but the API `/indexed-premises` will always be available). -/
def getIndexedPremises (apiBaseUrl : String) : IO NameSet := do
  let apiUrl := apiBaseUrl ++ "/indexed-premises"
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
def getIndexedModules (apiBaseUrl : String) : IO NameSet := do
  let apiUrl := apiBaseUrl ++ "/indexed-modules"
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

def selectPremisesCore (apiBaseUrl : String) (state : String)
    (importedModules : Option (Array Name)) (newPremises : Option (Array Premise))
    (k : Nat) : IO (Array Suggestion) := do
  let apiUrl := apiBaseUrl ++ "/retrieve"
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
    -- We put data in stdin rather than command argument, because the data may be too long
    "--data", "@-",
    apiUrl
  ]

  let child ← IO.Process.spawn { cmd := "curl", args := curlArgs, stdin := .piped, stdout := .piped, stderr := .piped }
  let (stdin, child) ← child.takeStdin
  stdin.putStr data.compress
  let exitCode ← child.wait
  let stdout ← child.stdout.readToEnd

  if exitCode != 0 then
    let stderr ← child.stderr.readToEnd
    IO.throwServerError <|
      "Could not send API request to select premises. " ++
      s!"curl exited with code {exitCode}:\n{stderr}"

  match Json.parse stdout >>= fromJson? with
  | .ok result => return result
  | .error e => IO.throwServerError <|
      s!"Could not parse premise retrieval output (error: {e})\nRaw output:\n{stdout}"

def selectPremises (goal : MVarId) (k : Nat) : MetaM (Array Suggestion) := do
  let env ← getEnv
  let state ← withOptions (fun o => (o.set `pp.notation false).set `pp.fullNames true) $ Meta.ppGoal goal
  let state := state.pretty
  trace[premiseSelection.debug] m!"State: {state}"

  let importedModules := env.allImportedModuleNames
  let indexedModules ← getIndexedModules (getApiBaseUrl (← getOptions))
  let newPremises ← Premise.getPremises indexedModules
  let apiBaseUrl := getApiBaseUrl (← getOptions)

  let suggestions ← profileitM Exception "Cloud.selectPremises" (← getOptions) do
    selectPremisesCore apiBaseUrl state importedModules newPremises k

  trace[premiseSelection.debug] m!"Suggestions: {suggestions}"
  return suggestions

def premiseSelector : Selector := fun goal config => do
  let premises ← selectPremises goal (config.maxSuggestions.getD 16)
  premises.filterM fun suggestion => config.filter suggestion.name

end Lean.PremiseSelection.Cloud
