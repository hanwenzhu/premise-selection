import Lean.LibrarySuggestions
import Lean.Server.Utils
import PremiseSelection.Premise

namespace Lean.LibrarySuggestions.Cloud

register_option premiseSelection.apiBaseUrl : String := {
  defValue := "http://leanpremise.net"
  descr := "The base URL of the premise retrieval API"
}

register_option premiseSelection.maxUnindexedPremises : Nat := {
  defValue := 2048
  descr := "The maximum number of unindexed premises to send to the premise selection server. The server may also impose its own restriction on this number, so we take the minimum of this number and the server's limit."
}

register_option premiseSelection.checkMaxUnindexedPremises : Bool := {
  defValue := false
  descr := "An option which determines whether the server's limit on max unindexed premises is checked, or whether premiseSelection.maxUnindexedPremises is just used."
}

register_option premiseSelection.indexByIndividualPremise : Bool := {
  defValue := false
  descr :=
    "An option which determines whether LeanPremise relays the exact set of premises that are cached/indexed by the server (true) " ++
    "or just relays the set of files that are cached/indexed by the server (false). Setting this option to true is expected to be slower, " ++
    "but may be better able to capture changes made to cached import files (e.g. additions made to imported Mathlib files)."
}

def getApiBaseUrl (opts : Options) : String :=
  premiseSelection.apiBaseUrl.get opts

initialize
  Lean.registerTraceClass `premiseSelection.cloud.debug
  Lean.registerTraceClass `premiseSelection.cloud.debug.full
  Lean.registerTraceClass `premiseSelection.cloud.profiling

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

  trace[premiseSelection.cloud.debug] "Making a {method} request to {urlPath}"
  trace[premiseSelection.cloud.debug.full] "Making a {method} request to {urlPath} with data {data?}"

  let output : IO.Process.Output ← id <| do
    if let some data := data? then
      let curlSpawnStart ← IO.monoMsNow
      let childInit ← IO.Process.spawn { cmd := "curl", args := curlArgs, stdin := .piped, stdout := .piped, stderr := .piped }
      let (stdin, child) ← childInit.takeStdin
      stdin.putStr data.compress
      let exitCode ← child.wait
      trace[premiseSelection.cloud.profiling] "{decl_name%} :: curl process run time: {(← IO.monoMsNow) - curlSpawnStart}ms"
      let stdout ← child.stdout.readToEnd
      let stderr ← child.stderr.readToEnd
      return { exitCode, stdout, stderr }
    else
      IO.Process.output { cmd := "curl", args := curlArgs }

  if output.exitCode != 0 then
    IO.throwServerError <|
      s!"Could not send API request to {apiUrl}. " ++
      s!"curl exited with code {output.exitCode}:\n{output.stderr}"

  let parseOutputStart ← IO.monoMsNow
  match Json.parse output.stdout >>= fromJson? with
  | .ok (result : α) =>
    trace[premiseSelection.cloud.profiling] "{decl_name%} :: time to parse curl output: {(← IO.monoMsNow) - parseOutputStart}ms"
    return result
  | .error e =>
    IO.throwServerError $ s!"Could not parse server output (error: {e})\nRaw output:\n{output.stdout}"

section IndexedPremises

/-! Retrieving indexed premises and modules stored on the server, and collecting
new premises either imported or defined locally.

The reason we make the distinction between imported and local premises is only because
we can cache the results (set of premises and their signatures if unindexed) for imported
premises in `IO.Ref`, because they won't change unless imports are changed.

Indexed premises are represented by a `Nat` (index in `getIndexedPremisesFromServer`).
Unindexed premises are represented as a `Premise` (name and signature).
-/

/-- A cache holding the maximum number of new premises to send to the server. -/
initialize maxUnindexedPremises : IO.Ref (Option Nat) ← IO.mkRef none

/-- The maximum number of new premises to send to the server. -/
def getMaxUnindexedPremises : CoreM Nat := do
  match ← maxUnindexedPremises.get with
  | some max => return max
  | none =>
    let userMaxNewPremises := premiseSelection.maxUnindexedPremises.get (← getOptions)
    if premiseSelection.checkMaxUnindexedPremises.get (← getOptions) then
      let serverMaxNewPremises ← makeRequest "GET" "/max-new-premises" none
      let res := min serverMaxNewPremises userMaxNewPremises
      maxUnindexedPremises.set res
      return res
    else
      maxUnindexedPremises.set userMaxNewPremises
      return userMaxNewPremises

/-- A cache holding indexed premises by the server. -/
initialize indexedPremisesFromServerRef : IO.Ref (Option (NameMap Nat)) ← IO.mkRef none
/-- Unfiltered list of all premises known by the server, as a mapping from name to index.
    The result is cached in an `IO.Ref`, because (assuming the server is static) the result will not change. -/
def getIndexedPremisesFromServer : CoreM (NameMap Nat) := do
  let getIndexedPremisesFromServerStart ← IO.monoMsNow
  match ← indexedPremisesFromServerRef.get with
  | some map =>
    trace[premiseSelection.debug] "{decl_name%} :: cache hit"
    trace[premiseSelection.cloud.profiling] "{decl_name%} cache hit run time {(← IO.monoMsNow) - getIndexedPremisesFromServerStart}ms"
    return map
  | none =>
    let map ← core getIndexedPremisesFromServerStart
    indexedPremisesFromServerRef.set (some map)
    trace[premiseSelection.debug] "{decl_name%} :: cache miss"
    trace[premiseSelection.cloud.profiling] "{decl_name%} cache miss run time {(← IO.monoMsNow) - getIndexedPremisesFromServerStart}ms"
    return map
where
  core (getIndexedPremisesFromServerStart : Nat) : CoreM (NameMap Nat) := do
    let names : Array String ← makeRequest "GET" "/indexed-premises" none
    trace[premiseSelection.cloud.profiling]
      "{decl_name%} :: Time to make GET /indexed-premises request result: {(← IO.monoMsNow) - getIndexedPremisesFromServerStart}ms"
    return names.zipIdx.foldl (fun ns (n, i) => ns.insert n.toName i) ∅

/-- A cache holding indexed modules by the server. -/
initialize indexedModulesFromServerRef : IO.Ref (Option (NameMap Nat)) ← IO.mkRef none

/-- A list of all files known by the server, as a mapping from name to index.
    The result is cached in an `IO.Ref`, because (assuming the server is static) the result will not change. -/
def getIndexedModules : CoreM (NameMap Nat) := do
  let getIndexedModulesFromServerStart ← IO.monoMsNow
  match ← indexedModulesFromServerRef.get with
  | some map =>
    trace[premiseSelection.debug] "{decl_name%} :: cache hit"
    trace[premiseSelection.cloud.profiling] "{decl_name%} cache hit run time {(← IO.monoMsNow) - getIndexedModulesFromServerStart}ms"
    return map
  | none =>
    let map ← core getIndexedModulesFromServerStart
    indexedModulesFromServerRef.set map
    trace[premiseSelection.debug] "{decl_name%} :: cache miss"
    trace[premiseSelection.cloud.profiling] "{decl_name%} cache miss run time {(← IO.monoMsNow) - getIndexedModulesFromServerStart}ms"
    return map
where
  core (getIndexedModulesFromServerStart : Nat) : CoreM (NameMap Nat) := do
    let names : Array String ← makeRequest "GET" "/indexed-modules" none
    trace[premiseSelection.cloud.profiling]
      "{decl_name%} :: Time to make GET /indexed-modules request result: {(← IO.monoMsNow) - getIndexedModulesFromServerStart}ms"
    return names.zipIdx.foldl (fun ns (n, i) => ns.insert n.toName i) ∅

/-- A cache holding the premises imported from other modules that are indexed by the server. -/
initialize indexedImportedPremisesRef : IO.Ref (Option (Array Nat)) ← IO.mkRef none
/-- A cache holding the imported modules that are indexed by the server
    (used when `premiseSelection.indexByIndividualPremise` is `false`). -/
initialize indexedImportedModulesRef : IO.Ref (Option (Array Nat)) ← IO.mkRef none
/-- A cache holding the premises imported from other modules that are not indexed by the server. -/
initialize unindexedImportedPremisesRef : IO.Ref (Option (Array Premise × Nat)) ← IO.mkRef none

/-- Get imported premises, separated by whether they are indexed by the server,
and a number indicating the true number of unindexed imported premises. -/
protected def getImportedPremisesCore (chunkSize := 256) : CoreM (Array Nat × Array Premise × Nat) := do
  let getImportedPremisesCoreStart ← IO.monoMsNow
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

  trace[premiseSelection.cloud.profiling] "{decl_name%} run time: {(← IO.monoMsNow) - getImportedPremisesCoreStart}ms"
  return (indexedIdxs, unindexedPremises, numUnindexedImportedPremises)

/-- Get the imported modules that are indexed by the server, the premises of imported modules that
are not indexed by the server, and a number indicating the true number of unindexed imported premises.

This is the analogue of `Cloud.getImportedPremisesCore` used when `premiseSelection.indexByIndividualPremise`
is `false`: rather than checking each imported premise against the server's set of indexed premises,
each imported module is checked against the server's set of indexed modules, and all premises of an
indexed module are assumed to be indexed by the server (so changes made to indexed modules,
e.g. additions made to imported Mathlib files, are not captured). -/
protected def getImportedModulesCore (chunkSize := 256) : CoreM (Array Nat × Array Premise × Nat) := do
  let getImportedModulesCoreStart ← IO.monoMsNow
  let env ← getEnv
  let maxUnindexedPremises ← getMaxUnindexedPremises
  let indexedModulesFromServer ← getIndexedModules
  let moduleNames := env.header.moduleNames
  let moduleData := env.header.moduleData

  let mut indexedModuleIdxs := #[]
  let mut unindexedNames := #[]
  for i in [0:moduleData.size] do
    let moduleName := moduleNames[i]!
    if isDeniedModule env moduleName then
      continue
    if let some idx := indexedModulesFromServer.find? moduleName then
      indexedModuleIdxs := indexedModuleIdxs.push idx
    else
      for name in moduleData[i]!.constNames do
        unless isDeniedPremise env name do
          unindexedNames := unindexedNames.push name

  let numUnindexedImportedPremises := unindexedNames.size
  if numUnindexedImportedPremises > maxUnindexedPremises then
    -- We may already truncate here, because only the last `maxUnindexedPremises` premises
    -- might possibly be included.
    unindexedNames := unindexedNames.drop (numUnindexedImportedPremises - maxUnindexedPremises)
  -- `useCache := false` because the `Premise`s are cached using our `unindexedImportedPremisesRef`
  let unindexedPremises ← Premise.fromNames unindexedNames chunkSize false

  trace[premiseSelection.cloud.profiling] "{decl_name%} run time: {(← IO.monoMsNow) - getImportedModulesCoreStart}ms"
  return (indexedModuleIdxs, unindexedPremises, numUnindexedImportedPremises)

/-- Get the imported premises that are indexed by the server. The result is cached in an `IO.Ref`,
because (assuming the server is static) the result will not change unless the file is restarted. -/
def getIndexedImportedPremises (chunkSize := 256) : CoreM (Array Nat) := do
  match ← indexedImportedPremisesRef.get with
  | some idxs => return idxs
  | none =>
    let (idxs, premises, numUnindexedImportedPremises) ← Cloud.getImportedPremisesCore chunkSize
    indexedImportedPremisesRef.set (some idxs)
    unindexedImportedPremisesRef.set (some (premises, numUnindexedImportedPremises))
    return idxs

/-- Get the imported modules that are indexed by the server (used when
`premiseSelection.indexByIndividualPremise` is `false`). The result is cached in an `IO.Ref`,
because (assuming the server is static) the result will not change unless the file is restarted. -/
def getIndexedImportedModules (chunkSize := 256) : CoreM (Array Nat) := do
  match ← indexedImportedModulesRef.get with
  | some idxs => return idxs
  | none =>
    let (idxs, premises, numUnindexedImportedPremises) ← Cloud.getImportedModulesCore chunkSize
    indexedImportedModulesRef.set (some idxs)
    unindexedImportedPremisesRef.set (some (premises, numUnindexedImportedPremises))
    return idxs

/-- Get the imported premises not indexed by the server. The result is cached in an `IO.Ref`,
because (assuming the server is static) the result will not change unless the file is restarted. -/
def getUnindexedImportedPremises (chunkSize := 256) : CoreM (Array Premise) := do
  match ← unindexedImportedPremisesRef.get with
  | some (premises, _) => return premises
  | none =>
    if premiseSelection.indexByIndividualPremise.get (← getOptions) then
      let (idxs, premises, numUnindexedImportedPremises) ← Cloud.getImportedPremisesCore chunkSize
      indexedImportedPremisesRef.set (some idxs)
      unindexedImportedPremisesRef.set (some (premises, numUnindexedImportedPremises))
      return premises
    else
      let (idxs, premises, numUnindexedImportedPremises) ← Cloud.getImportedModulesCore chunkSize
      indexedImportedModulesRef.set (some idxs)
      unindexedImportedPremisesRef.set (some (premises, numUnindexedImportedPremises))
      return premises

/-- Get the number of imported premises not indexed by the server. The result is cached in an `IO.Ref`,
because (assuming the server is static) the result will not change unless the file is restarted.
This number is used only for printing a warning message. -/
def getNumUnindexedImportedPremises (chunkSize := 256) : CoreM Nat := do
  match ← unindexedImportedPremisesRef.get with
  | some (_, numUnindexedImportedPremises) => return numUnindexedImportedPremises
  | none =>
    if premiseSelection.indexByIndividualPremise.get (← getOptions) then
      let (idxs, premises, numUnindexedImportedPremises) ← Cloud.getImportedPremisesCore chunkSize
      indexedImportedPremisesRef.set (some idxs)
      unindexedImportedPremisesRef.set (some (premises, numUnindexedImportedPremises))
      return numUnindexedImportedPremises
    else
      let (idxs, premises, numUnindexedImportedPremises) ← Cloud.getImportedModulesCore chunkSize
      indexedImportedModulesRef.set (some idxs)
      unindexedImportedPremisesRef.set (some (premises, numUnindexedImportedPremises))
      return numUnindexedImportedPremises

/-- Get the local premises defined in the current file that are indexed by the server.
Modifications to these premises will *not* be reflected in the retrieval results, with
the assumption being even if modifications are made, they should be small enough
to significantly change the semantic meaning (the name is kept after all).
-/
def getIndexedLocalPremises : CoreM (Array Nat) := do
  let getIndexedLocalPremisesStart ← IO.monoMsNow
  let env ← getEnv
  let indexedPremisesFromServer ← getIndexedPremisesFromServer
  let mut idxs := #[]
  for (name, _) in env.constants.map₂ do
    if let some idx := indexedPremisesFromServer.find? name then
      idxs := idxs.push idx
  trace[premiseSelection.cloud.profiling] "{decl_name%} run time: {(← IO.monoMsNow) - getIndexedLocalPremisesStart}ms"
  return idxs

/-- Returns the local premises defined in the current file that are not indexed by the server.
The set of premises is not cached, to allow for adding/deleting local premises (unless indexed by the server).
Currently, the printed signature itself is cached by the `Premise.fromName` function,
meaning that it does not support modifying local premises,
but (**TODO**) this behavior might (or should) change in the future by disabling this cache.
-/
def getUnindexedLocalPremises (chunkSize := 256) : CoreM (Array Premise) := do
  let getUnindexedLocalPremisesStart ← IO.monoMsNow
  let env ← getEnv
  -- When `premiseSelection.indexByIndividualPremise` is `false`, the set of premises indexed by
  -- the server is never retrieved, so all local premises are treated as unindexed
  let indexedPremisesFromServer ←
    if premiseSelection.indexByIndividualPremise.get (← getOptions) then
      getIndexedPremisesFromServer
    else
      pure (∅ : NameMap Nat)
  let mut names := #[]
  for (name, _) in env.constants.map₂ do
    unless indexedPremisesFromServer.contains name do
      unless isDeniedPremise env name do
        names := names.push name
  let res ← Premise.fromNames names chunkSize true -- **TODO** see docstring
  trace[premiseSelection.cloud.profiling] "{decl_name%} run time: {(← IO.monoMsNow) - getUnindexedLocalPremisesStart}ms"
  return res

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
    if premiseSelection.indexByIndividualPremise.get (← getOptions) then
      let _ ← getIndexedPremises
    else
      let _ ← getIndexedImportedModules

elab "clear_premise_selection_cloud_cache" : command => do
  Premise.fromNameCacheRef.set ∅
  indexedPremisesFromServerRef.set none
  indexedModulesFromServerRef.set none
  indexedImportedPremisesRef.set none
  indexedImportedModulesRef.set none
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
    (indexedPremises : Array Nat) (importedModules : Array Nat) (unindexedPremises : Array Premise)
    (k : Nat) : CoreM (Array Suggestion) := do
  let data := Json.mkObj [
    ("state", .str state),
    ("local_premises", toJson indexedPremises),  -- the name `local_premises` is an artifact from previous versions
    ("imported_modules", toJson importedModules),
    ("new_premises", toJson unindexedPremises),
    ("k", .num (.fromNat k)),
  ]
  makeRequest "POST" "/retrieve" (some data)

def selectPremises (goal : MVarId) (k : Nat) : MetaM (Array Suggestion) := do
  let start ← IO.monoMsNow
  let state ← withOptions (fun o => (o.set `pp.notation false).set `pp.fullNames true) $ Meta.ppGoal goal
  let state := state.pretty
  trace[premiseSelection.cloud.profiling] "Time to produce state: {(← IO.monoMsNow) - start}ms"
  trace[premiseSelection.debug] "State: {state}"

  let indexedAndUnindexedPremisesStart ← IO.monoMsNow
  -- When `premiseSelection.indexByIndividualPremise` is `true`, indexed premises are relayed to
  -- the server individually (via `local_premises`); when it is `false`, only the imported modules
  -- indexed by the server are relayed (via `imported_modules`).
  let (indexedPremises, importedModules) ←
    if premiseSelection.indexByIndividualPremise.get (← getOptions) then
      pure ((← getIndexedPremises), #[])
    else
      pure (#[], (← getIndexedImportedModules))
  trace[premiseSelection.cloud.profiling] "Time to get just indexed premises: {(← IO.monoMsNow) - indexedAndUnindexedPremisesStart}ms"
  let unindexedPremises ← getUnindexedPremises
  trace[premiseSelection.cloud.profiling] "Time to get indexed and unindexed premises: {(← IO.monoMsNow) - indexedAndUnindexedPremisesStart}ms"

  let selectPremiseCoreStart ← IO.monoMsNow
  let suggestions ← profileitM Exception "Cloud.selectPremises" (← getOptions) do
    selectPremisesCore state indexedPremises importedModules unindexedPremises k
  trace[premiseSelection.cloud.profiling] "Time to call selectPremisesCore: {(← IO.monoMsNow) - selectPremiseCoreStart}ms"

  trace[premiseSelection.cloud.profiling] "Total premise selection runtime: {(← IO.monoMsNow) - start}ms"
  trace[premiseSelection.debug] "Suggestions: {suggestions}"
  return suggestions

def premiseSelector : Selector := fun goal config => do
  let premises ← selectPremises goal config.maxSuggestions
  premises.filterM fun suggestion => config.filter suggestion.name

end Lean.LibrarySuggestions.Cloud
