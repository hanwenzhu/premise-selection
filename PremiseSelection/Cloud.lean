import PremiseSelection.Premise
import Lean.Server.Utils

namespace Lean.PremiseSelection.Cloud

register_option premiseSelection.apiBaseUrl : String := {
  defValue := "http://52.206.70.13"
  descr := "The base URL of the premise retrieval API"
}

def getApiBaseUrl (opts : Options) : String :=
  premiseSelection.apiBaseUrl.get opts

def makeRequest {α : Type _} [FromJson α] (method urlPath : String) (data? : Option Json) : CoreM α := do
  let apiBaseUrl := getApiBaseUrl (← getOptions)
  let apiUrl := apiBaseUrl ++ urlPath
  let mut curlArgs := #[
    "-X", method,
    "--user-agent", "LeanProver (https://leanprover-community.github.io/)"
  ]
  if data?.isSome then
    curlArgs := curlArgs ++ #[
      "--header", "Content-Type: application/json",
      -- We put data in stdin rather than command argument, because the data may be too long
      "--data", "@-"
    ]
  curlArgs := curlArgs.push apiUrl

  let output : IO.Process.Output ← id <| do
    if let some data := data? then
      let childInit ← IO.Process.spawn { cmd := "curl", args := curlArgs, stdin := .piped, stdout := .piped, stderr := .piped }
      let (stdin, child) ← childInit.takeStdin
      stdin.putStr data.compress
      let exitCode ← child.wait
      let stdout ← child.stdout.readToEnd
      let stderr ← child.stderr.readToEnd
      return { exitCode, stdout, stderr }
    else
      IO.Process.output { cmd := "curl", args := curlArgs }

  if output.exitCode != 0 then
    IO.throwServerError <|
      s!"Could not send API request to {apiUrl}. " ++
      s!"curl exited with code {output.exitCode}:\n{output.stderr}"

  match Json.parse output.stdout >>= fromJson? with
  | .ok (result : α) =>
      return result
  | .error e => IO.throwServerError <|
      s!"Could not parse server output (error: {e})\nRaw output:\n{output.stdout}"

section IndexedPremises

/-! Retrieving indexed premises and modules stored on the server, and collecting
new premises either imported or defined locally.

The reason we make the distinction between imported and local premises is only because
we can cache the results (set of premises and their signatures if unindexed) for imported
premises in `IO.Ref`, because they won't change unless imports are changed.
-/

/-- The maximum number of new premises to send to the server. -/
def getMaxUnindexedPremises : CoreM Nat := do
  makeRequest "GET" "/max-new-premises" none

/-- A cache holding indexed premises by the server. -/
initialize indexedPremisesFromServerRef : IO.Ref (Option NameSet) ← IO.mkRef none
/-- Unfiltered list of all premises known by the server. The result is cached in an `IO.Ref`,
because (assuming the server is static) the result will not change. -/
def getIndexedPremisesFromServer : CoreM NameSet := do
  match ← indexedPremisesFromServerRef.get with
  | some names => return names
  | none =>
    let names ← core
    indexedPremisesFromServerRef.set (some names)
    return names
where
  core : CoreM NameSet := do
    let names : Array String ← makeRequest "GET" "/indexed-premises" none
    return names.foldl (fun ns n => ns.insert n.toName) ∅

/-- All modules known by the server. **NOTE** This is not used. -/
def getIndexedModules : CoreM NameSet := do
  let moduleNames : Array String ← makeRequest "GET" "/indexed-modules" none
  return moduleNames.foldl (fun ns n => ns.insert n.toName) ∅

/-- A cache holding the premises imported from other modules that are indexed by the server. -/
initialize indexedImportedPremisesRef : IO.Ref (Option (Array Name)) ← IO.mkRef none
/-- A cache holding the premises imported from other modules that are not indexed by the server. -/
initialize unindexedImportedPremisesRef : IO.Ref (Option (Array Premise)) ← IO.mkRef none

/-- Get imported premises, separated by whether they are indexed by the server. -/
protected def getImportedPremisesCore (chunkSize := 256) : CoreM (Array Name × Array Premise) := do
  let env ← getEnv
  let maxUnindexedPremises ← getMaxUnindexedPremises
  let indexedPremises ← getIndexedPremisesFromServer
  let moduleNames := env.header.moduleNames
  let moduleData := env.header.moduleData

  let mut indexedNames := #[]
  let mut unindexedNames := #[]
  for i in [0:moduleData.size] do
    let moduleName := moduleNames[i]!
    if Premise.isBlackListedModule moduleName then
      continue
    let modData := moduleData[i]!
    for name in modData.constNames do
      if indexedPremises.contains name then
        indexedNames := indexedNames.push name
      else
        unless Premise.isBlackListedPremise env name do
          unindexedNames := unindexedNames.push name

  if unindexedNames.size > maxUnindexedPremises then
    logWarning m!"Found {unindexedNames.size} unindexed premises in imports, which exceeds the maximum number of new premises ({maxUnindexedPremises}). Discarding premises beyond this limit"
    unindexedNames := unindexedNames.take maxUnindexedPremises
  -- `useCache := false` because the `Premise`s are cached using our `unindexedImportedPremisesRef`
  let unindexedPremises ← Premise.fromNames unindexedNames chunkSize false

  return (indexedNames, unindexedPremises)

/-- Get the imported premises that are indexed by the server. The result is cached in an `IO.Ref`,
because (assuming the server is static) the result will not change unless the file is restarted. -/
def getIndexedImportedPremises (chunkSize := 256) : CoreM (Array Name) := do
  match ← indexedImportedPremisesRef.get with
  | some names => return names
  | none =>
    let (names, _) ← Cloud.getImportedPremisesCore chunkSize
    indexedImportedPremisesRef.set (some names)
    return names

/-- Get the imported premises not indexed by the server. The result is cached in an `IO.Ref`,
because (assuming the server is static) the result will not change unless the file is restarted. -/
def getUnindexedImportedPremises (chunkSize := 256) : CoreM (Array Premise) := do
  match ← unindexedImportedPremisesRef.get with
  | some premises => return premises
  | none =>
    let (_, premises) ← Cloud.getImportedPremisesCore chunkSize
    unindexedImportedPremisesRef.set (some premises)
    return premises

/-- Get the local premises defined in the current file that are indexed by the server.
Modifications to these premises will *not* be reflected in the retrieval results, with
the assumption being even if modifications are made, they should be small enough
to significantly change the semantic meaning (the name is kept after all).
-/
def getIndexedLocalPremises : CoreM (Array Name) := do
  let env ← getEnv
  let indexedPremises ← getIndexedPremisesFromServer
  let mut names := #[]
  for (name, _) in env.constants.map₂ do
    if indexedPremises.contains name then
      names := names.push name
  return names

/-- Returns the local premises defined in the current file that are not indexed by the server.
The set of premises is not cached, to allow for adding/deleting local premises (unless indexed by the server).
Currently, the printed signature itself is cached by the `Premise.fromName` function,
meaning that it does not support modifying local premises,
but (**TODO**) this behavior might (or should) change in the future either by disabling this cache
or by making an option for users to purge cache.
-/
def getUnindexedLocalPremises (chunkSize := 256) : CoreM (Array Premise) := do
  let env ← getEnv
  let indexedPremises ← getIndexedPremisesFromServer
  let mut names := #[]
  for (name, _) in env.constants.map₂ do
    unless indexedPremises.contains name do
      unless Premise.isBlackListedPremise env name do
        names := names.push name
  Premise.fromNames names chunkSize true -- **TODO** see docstring

/-- Returns new unindexed premises defined in the environment, from both imported and local premises. -/
def getUnindexedPremises (chunkSize := 256) : CoreM (Array Premise) := do
  let premises₁ ← getUnindexedImportedPremises chunkSize
  let premises₂ ← getUnindexedLocalPremises chunkSize
  return premises₁ ++ premises₂

/-- Returns indexed premises defined in the environment, from both imported and local premises. -/
def getIndexedPremises (chunkSize := 256) : CoreM (Array Name) := do
  let names₁ ← getIndexedImportedPremises chunkSize
  let names₂ ← getIndexedLocalPremises
  return names₁ ++ names₂

elab "clear_premise_selection_cache" : command => do
  Premise.fromNameCacheRef.set ∅
  indexedPremisesFromServerRef.set none
  indexedImportedPremisesRef.set none
  unindexedImportedPremisesRef.set none

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

def selectPremisesCore (state : String)
    (importedModules indexedLocalPremises : Array Name) (unindexedPremises : Array Premise)
    (k : Nat) : CoreM (Array Suggestion) := do
  let data := Json.mkObj [
    ("state", .str state),
    ("imported_modules", toJson importedModules),
    ("local_premises", toJson indexedLocalPremises),
    ("new_premises", toJson unindexedPremises),
    ("k", .num (.fromNat k)),
  ]
  makeRequest "POST" "/retrieve" (some data)

def selectPremises (goal : MVarId) (k : Nat) : MetaM (Array Suggestion) := do
  let env ← getEnv
  let state ← withOptions (fun o => (o.set `pp.notation false).set `pp.fullNames true) $ Meta.ppGoal goal
  let state := state.pretty
  trace[premiseSelection.debug] m!"State: {state}"

  let importedModules := env.allImportedModuleNames
  let indexedLocalPremises ← getIndexedLocalPremises
  let unindexedPremises ← getUnindexedPremises

  let suggestions ← profileitM Exception "Cloud.selectPremises" (← getOptions) do
    selectPremisesCore state importedModules indexedLocalPremises unindexedPremises k

  trace[premiseSelection.debug] m!"Suggestions: {suggestions}"
  return suggestions

def premiseSelector : Selector := fun goal config => do
  let premises ← selectPremises goal (config.maxSuggestions.getD 16)
  premises.filterM fun suggestion => config.filter suggestion.name

end Lean.PremiseSelection.Cloud
