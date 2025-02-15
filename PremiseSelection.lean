import Lean

namespace Lean.PremiseSelection.Cloud

open Meta

register_option premiseSelection.apiUrl : String := {
  defValue := "http://52.206.70.13/retrieve"
  descr := "The URL of the premise retrieval API"
}

def getPremiseSelectionApiUrl (opts : Options) : String :=
  premiseSelection.apiUrl.get opts

def getPremiseSelectionApiUrlM : CoreM String := do
  let opts ← getOptions
  return getPremiseSelectionApiUrl opts

structure PremiseSuggestion where
  name : Name
  score : Float
deriving Repr, FromJson

instance : ToString PremiseSuggestion where
  toString p := s!"{p.name} ({p.score})"

instance : ToMessageData PremiseSuggestion where
  toMessageData p := s!"{p.name} ({p.score})"

def selectPremisesCore (apiUrl : String) (state : String) (importedModules localPremises : Option (Array Name))
  (k : Nat) : IO (Array PremiseSuggestion) := do
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

def selectPremises (goal : MVarId) (k : Nat) : MetaM (Array PremiseSuggestion) := do
  let env ← getEnv
  let state ← withOptions (fun o => (o.set `pp.notation false).set `pp.fullNames true) $ Meta.ppGoal goal
  let state := state.pretty
  trace[premiseSelection.debug] m!"State: {state}"

  let importedModules := env.allImportedModuleNames
  let localPremises := env.constants.map₂.foldl (fun arr name _ => arr.push name) #[]
  let apiUrl ← getPremiseSelectionApiUrlM

  let suggestions ← profileitM Exception "Cloud.selectPremises" (← getOptions) do
    selectPremisesCore apiUrl state importedModules localPremises k

  return suggestions

elab "suggest_premises_cloud" k:num : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  logInfo $ .ofArray $ (← selectPremises goal k.getNat).map toMessageData

end Lean.PremiseSelection.Cloud
