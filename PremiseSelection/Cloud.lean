import Lean.PremiseSelection
import Lean.Server.Utils
import PremiseSelection.Premise

namespace Lean.PremiseSelection.Cloud

register_option premiseSelection.apiBaseUrl : String := {
  defValue := "http://leanpremise.net"
  descr := "The base URL of the premise retrieval API"
}

register_option premiseSelection.maxUnindexedPremises : Nat := {
  defValue := 8192
  descr := "The maximum number of unindexed premises to send to the premise selection server. The server may also impose its own restriction on this number, so we take the minimum of this number and the server's limit."
}

def getApiBaseUrl (opts : Options) : String :=
  premiseSelection.apiBaseUrl.get opts

initialize Lean.registerTraceClass `premiseSelection.cloud.debug

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

  trace[premiseSelection.cloud.debug] "Making a {method} request to {urlPath} with data {data?}"

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

Indexed premises are represented by a `Nat` (index in `getIndexedPremisesFromServer`).
Unindexed premises are represented as a `Premise` (name and signature).
-/

/-- The maximum number of new premises to send to the server. -/
def getMaxUnindexedPremises : CoreM Nat := do
  let serverMaxNewPremises ← makeRequest "GET" "/max-new-premises" none
  let userMaxNewPremises := premiseSelection.maxUnindexedPremises.get (← getOptions)
  return min serverMaxNewPremises userMaxNewPremises

/-- A cache holding indexed premises by the server. -/
initialize indexedPremisesFromServerRef : IO.Ref (Option (NameMap Nat)) ← IO.mkRef none
/-- Unfiltered list of all premises known by the server, as a mapping from name to index.
The result is cached in an `IO.Ref`, because (assuming the server is static) the result will not change. -/
def getIndexedPremisesFromServer : CoreM (NameMap Nat) := do
  match ← indexedPremisesFromServerRef.get with
  | some map => return map
  | none =>
    let map ← core
    indexedPremisesFromServerRef.set (some map)
    return map
where
  core : CoreM (NameMap Nat) := do
    let names : Array String ← makeRequest "GET" "/indexed-premises" none
    return names.zipIdx.foldl (fun ns (n, i) => ns.insert n.toName i) ∅

/-- All modules known by the server. **NOTE** This is not used. -/
def getIndexedModules : CoreM NameSet := do
  let moduleNames : Array String ← makeRequest "GET" "/indexed-modules" none
  return moduleNames.foldl (fun ns n => ns.insert n.toName) ∅

/-- A cache holding the premises imported from other modules that are indexed by the server. -/
initialize indexedImportedPremisesRef : IO.Ref (Option (Array Nat)) ← IO.mkRef none
/-- A cache holding the premises imported from other modules that are not indexed by the server. -/
initialize unindexedImportedPremisesRef : IO.Ref (Option (Array Premise × Nat)) ← IO.mkRef none

/-- Get imported premises, separated by whether they are indexed by the server,
and a number indicating the true number of unindexed imported premises. -/
protected def getImportedPremisesCore (chunkSize := 256) : CoreM (Array Nat × Array Premise × Nat) := do
  let env ← getEnv
  let maxUnindexedPremises ← getMaxUnindexedPremises
  let indexedPremisesFromServer ← getIndexedPremisesFromServer
  let moduleNames := env.header.moduleNames
  let moduleData := env.header.moduleData

  let mut indexedIdxs := #[]
  let mut unindexedNames := #[]
  for i in [0:moduleData.size] do
    let moduleName := moduleNames[i]!
    if isDeniedModule env moduleName then
      continue
    let modData := moduleData[i]!
    for name in modData.constNames do
      if let some idx := indexedPremisesFromServer.find? name then
        indexedIdxs := indexedIdxs.push idx
      else
        unless isDeniedPremise env name do
          unindexedNames := unindexedNames.push name

  let numUnindexedImportedPremises := unindexedNames.size
  if numUnindexedImportedPremises > maxUnindexedPremises then
    -- We may already truncate here, because only the last `maxUnindexedPremises` premises
    -- might possibly be included.
    unindexedNames := unindexedNames.drop (numUnindexedImportedPremises - maxUnindexedPremises)
  -- `useCache := false` because the `Premise`s are cached using our `unindexedImportedPremisesRef`
  let unindexedPremises ← Premise.fromNames unindexedNames chunkSize false

  return (indexedIdxs, unindexedPremises, numUnindexedImportedPremises)

/-- Get the imported premises that are indexed by the server. The result is cached in an `IO.Ref`,
because (assuming the server is static) the result will not change unless the file is restarted. -/
def getIndexedImportedPremises (chunkSize := 256) : CoreM (Array Nat) := do
  match ← indexedImportedPremisesRef.get with
  | some idxs => return idxs
  | none =>
    let (idxs, _) ← Cloud.getImportedPremisesCore chunkSize
    indexedImportedPremisesRef.set (some idxs)
    return idxs

/-- Get the imported premises not indexed by the server. The result is cached in an `IO.Ref`,
because (assuming the server is static) the result will not change unless the file is restarted. -/
def getUnindexedImportedPremises (chunkSize := 256) : CoreM (Array Premise) := do
  match ← unindexedImportedPremisesRef.get with
  | some (premises, _) => return premises
  | none =>
    let (_, premises, numUnindexedImportedPremises) ← Cloud.getImportedPremisesCore chunkSize
    unindexedImportedPremisesRef.set (some (premises, numUnindexedImportedPremises))
    return premises

/-- Get the number of imported premises not indexed by the server. The result is cached in an `IO.Ref`,
because (assuming the server is static) the result will not change unless the file is restarted.
This number is used only for printing a warning message. -/
def getNumUnindexedImportedPremises (chunkSize := 256) : CoreM Nat := do
  match ← unindexedImportedPremisesRef.get with
  | some (_, numUnindexedImportedPremises) => return numUnindexedImportedPremises
  | none =>
    let (_, premises, numUnindexedImportedPremises) ← Cloud.getImportedPremisesCore chunkSize
    unindexedImportedPremisesRef.set (some (premises, numUnindexedImportedPremises))
    return numUnindexedImportedPremises

/-- Get the local premises defined in the current file that are indexed by the server.
Modifications to these premises will *not* be reflected in the retrieval results, with
the assumption being even if modifications are made, they should be small enough
to significantly change the semantic meaning (the name is kept after all).
-/
def getIndexedLocalPremises : CoreM (Array Nat) := do
  let env ← getEnv
  let indexedPremisesFromServer ← getIndexedPremisesFromServer
  let mut idxs := #[]
  for (name, _) in env.constants.map₂ do
    if let some idx := indexedPremisesFromServer.find? name then
      idxs := idxs.push idx
  return idxs

/-- Returns the local premises defined in the current file that are not indexed by the server.
The set of premises is not cached, to allow for adding/deleting local premises (unless indexed by the server).
Currently, the printed signature itself is cached by the `Premise.fromName` function,
meaning that it does not support modifying local premises,
but (**TODO**) this behavior might (or should) change in the future by disabling this cache.
-/
def getUnindexedLocalPremises (chunkSize := 256) : CoreM (Array Premise) := do
  let env ← getEnv
  let indexedPremisesFromServer ← getIndexedPremisesFromServer
  let mut names := #[]
  for (name, _) in env.constants.map₂ do
    unless indexedPremisesFromServer.contains name do
      unless isDeniedPremise env name do
        names := names.push name
  Premise.fromNames names chunkSize true -- **TODO** see docstring

/-- Returns new unindexed premises defined in the environment, from both imported and local premises,
truncated to the maximum number of unindexed premises allowed by the server. -/
def getUnindexedPremises (chunkSize := 256) : CoreM (Array Premise) := do
  let maxUnindexedPremises ← getMaxUnindexedPremises
  let premises₁ ← getUnindexedImportedPremises chunkSize
  let premises₂ ← getUnindexedLocalPremises chunkSize

  -- This is the true number of unindexed premises in the environment (imported and local).
  -- This may be higher than `(premises₁ ++ premises₂).size`, because
  -- `getUnindexedImportedPremises` already optimizes away the unnecessary pretty-printing
  -- for unindexed imported premises beyond the limit.
  let numUnindexedPremises := (← getNumUnindexedImportedPremises chunkSize) + premises₂.size
  if numUnindexedPremises > maxUnindexedPremises then
    logWarning m!"Found {numUnindexedPremises} unindexed premises in the environment, which exceeds the maximum number of new premises ({maxUnindexedPremises}). Discarding premises beyond this limit"

  -- Truncate to the last `maxUnindexedPremises` premises
  let mut premises := premises₁ ++ premises₂
  premises := premises.drop (premises.size - maxUnindexedPremises)
  return premises

/-- Returns indexed premises defined in the environment, from both imported and local premises. -/
def getIndexedPremises (chunkSize := 256) : CoreM (Array Nat) := do
  let idxs₁ ← getIndexedImportedPremises chunkSize
  let idxs₂ ← getIndexedLocalPremises
  return idxs₁ ++ idxs₂

elab "set_premise_selection_cloud_cache" : command => do
  Elab.Command.liftCoreM do
    let _ ← getUnindexedPremises
    let _ ← getIndexedPremises

elab "clear_premise_selection_cloud_cache" : command => do
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
    (indexedPremises : Array Nat) (unindexedPremises : Array Premise)
    (k : Nat) : CoreM (Array Suggestion) := do
  let data := Json.mkObj [
    ("state", .str state),
    ("local_premises", toJson indexedPremises),  -- the name `local_premises` is an artifact from previous versions
    ("new_premises", toJson unindexedPremises),
    ("k", .num (.fromNat k)),
  ]
  makeRequest "POST" "/retrieve" (some data)

def selectPremises (goal : MVarId) (k : Nat) : MetaM (Array Suggestion) := do
  -- let env ← getEnv
  let state ← withOptions (fun o => (o.set `pp.notation false).set `pp.fullNames true) $ Meta.ppGoal goal
  let state := state.pretty
  trace[premiseSelection.debug] "State: {state}"

  let indexedPremises ← getIndexedPremises
  let unindexedPremises ← getUnindexedPremises

  let suggestions ← profileitM Exception "Cloud.selectPremises" (← getOptions) do
    selectPremisesCore state indexedPremises unindexedPremises k

  trace[premiseSelection.debug] "Suggestions: {suggestions}"
  return suggestions

def premiseSelector : Selector := fun goal config => do
  let premises ← selectPremises goal (config.maxSuggestions.getD 32)
  premises.filterM fun suggestion => config.filter suggestion.name

end Lean.PremiseSelection.Cloud
