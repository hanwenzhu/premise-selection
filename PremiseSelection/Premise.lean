/-
Getting new user-defined premises in an environment
-/
import PremiseSelection.Basic
import Batteries.Data.List.Basic

open Lean

namespace Lean.PremiseSelection

/-!
Here we define mechanisms that send new user-defined premises to the server.

The entire architecture is very WIP: it depends on several unreal assumptions
* If a user imports a module that is indexed by the server, the contents of the module is not changed
* After a user calculates the pretty-printed form of a premise, it will not be changed any more (because of caching)
-/

/-- The data of a new premise sent to the server, including name and a signature consisting of docstring and type. -/
structure Premise where
  name : Name
  decl : String
deriving Inhabited, Repr, ToJson

namespace Premise

section PrettyPrinting

open Meta PrettyPrinter Delaborator

/--
Returns kind (string) given constant (from declarations.lean)
-/
def getKind (cinfo : ConstantInfo) : MetaM String := do
  let env ← getEnv
  let kind : String :=
    match cinfo with
    | .axiomInfo _ => "axiom"
    | .thmInfo _ => "theorem"
    | .opaqueInfo _ => "opaque"
    | .defnInfo i =>
      if isInstanceCore env i.name then
        "instance"
      else
        "def"
    | .inductInfo i =>
      if isClass env i.name then
        "class"
      else if isStructure env i.name then
        "structure"
      else
        "inductive"
    | .ctorInfo _ => "def"
    | .recInfo _ => "def"
    | .quotInfo _ => "def"
  return kind

/-- A reference holding a mapping from a user-defined premise `name` to `Premise.fromName name` (see `Premise.fromName`). -/
initialize Premise.fromNameCacheRef : IO.Ref (NameMap Premise) ← IO.mkRef ∅

/--
Serialize a declaration into a `Premise` by pretty-printing the declaration docstring and signature.

This function is cached by `Premise.fromNameCacheRef`, so on the second time it is
called on the same declaration, it reads the previously stored result instead of calculates the signature again.
(**TODO**) This is just a temporary solution so that it is reasonable to call e.g. `aesop (add unsafe (by hammer))`
where `hammer` is called many times.
-/
def fromName (name : Name) : CoreM Premise := do
  if let some premise := (← Premise.fromNameCacheRef.get).find? name then
    return premise

  -- Calculate signature from declaration name
  let premise ← MetaM.run' do
    withOptions (fun o => (o.set `pp.notation false).set `pp.fullNames true) do
      let env ← getEnv
      -- IO.eprintln name
      let cinfo ← profileitM Exception "cinfo" (← getOptions) do getConstInfo name
      let doc? ← profileitM Exception "doc?" (← getOptions) do findSimpleDocString? env name  -- **TODO** any difference with findDocString?
      let kind ← profileitM Exception "kind?" (← getOptions) do getKind cinfo
      /-
      Regarding `ppSignature`:
      * This is (probably) the same output as the `"decl"` in `constantInfoToJson` from `declarations.lean`
      * `ppSignature` is the bottleneck in preparing a list of new premises to send to the server
      * It usually takes ≤10ms, but can be much longer on constants with a complicated (TODO: in what way?) signature;
        for an example, see `set_option profiler true in #eval Premise.fromName ``ProbabilityTheory.integrable_kernel_prod_mk_left`
        or the tests
      * Using `pp.raw true` makes it very fast (on order of 1ms); see the logic inside `ppSignature` which uses `s!"{cinfo.type}"` when `pp.raw`
      * Therefore I think there are probably things inside `ppSignature` (`delabConstWithSignature`) that are
        unoptimized (there was no reason to optimize signature pretty-printing to less than 1ms, until now)
        and perhaps a custom version `ppSignature'` that cuts corners might be significantly faster
      -/
      let ⟨fmt, _⟩ ← profileitM Exception "ppSignature" (← getOptions) do ppSignature name

      -- Format declaration into `decl`
      let mut decl := ""
      if let some doc := doc? then
        decl := decl ++ "/-- " ++ doc.stripSuffix " " ++ " -/\n"
      decl := decl ++ kind ++ " "
      decl := decl ++ fmt.pretty 1000000000

      return { name, decl }

  Premise.fromNameCacheRef.modify fun cache => cache.insert name premise
  return premise

end PrettyPrinting

open Lean Core

/-- Premises from a module whose name has one of the following as a component are not retrieved. -/
def moduleBlackList : Array String := #[
  "Aesop", "Auto", "Cli", "CodeAction", "DocGen4", "Duper", "ImportGraph", "Lake", "Lean", "LeanSearchClient", "Linter", "Mathport",
  "MD4Lean", "Plausible", "ProofWidgets", "Qq", "QuerySMT", "Tactic", "TacticExtra", "Test", "Testing", "UnicodeBasic", "Util"
]

/-- A premise whose name has one of the following as a component is not retrieved. -/
def nameBlackList : Array String := #["Lean", "Lake", "Qq"]

/-- A premise whose `type.getForallBody.getAppFn` is a constant that has this prefix is not retrieved. -/
def typePrefixBlackList : Array Name := #[`Lean]

def isBlackListedPremise (env : Environment) (name : Name) : Bool := Id.run do
  if name == ``sorryAx then return true
  if name.isInternalDetail then return true
  if nameBlackList.any (fun p => name.anyS (· == p)) then return true
  -- let some moduleName := env.getModuleFor? name | return true
  -- if moduleBlackList.any (fun p => moduleName.anyS (· == p)) then return true
  let some ci := env.find? name | return true
  if let .const fnName _ := ci.type.getForallBody.getAppFn then
    if typePrefixBlackList.any (fun p => p.isPrefixOf fnName) then return true
  return false

def getModules (exclude : NameSet) : CoreM (Array ModuleData) := do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let moduleData := env.header.moduleData
  let mut modules := #[]

  -- For each index `i` of a new module
  for i in [0:moduleData.size] do
    let moduleName := moduleNames[i]!
    if exclude.contains moduleName then
      continue
    if moduleBlackList.any (fun p => moduleName.anyS (· == p)) then
      continue

    -- Add corresponding module data
    modules := modules.push moduleData[i]!

  return modules

/-- Set of new premises in the environment -/
def getNames (excludeModules : NameSet) : CoreM (Array Name) := do
  let env ← getEnv
  let mut names := #[]
  let modules ← getModules excludeModules

  -- All filtered constants from unindexed modules
  for moduleData in modules do
    for name in moduleData.constNames do
      unless isBlackListedPremise env name do
        names := names.push name

  -- All filtered constants from this module
  -- unless indexedMods.contains env.header.mainModule do
  for (name, _) in env.constants.map₂ do
    unless isBlackListedPremise env name do
      names := names.push name
  return names

def getPremises (excludeModules : NameSet) (chunkSize := 256) : CoreM (Array Premise) := do
  let name ← getNames excludeModules

  if chunkSize == 1 then
    let premises ← name.mapM Premise.fromName
    return premises

  else
    let ctxCore ← readThe Core.Context
    let sCore ← getThe Core.State

    -- The only reason for toList is because `List.toChunks` exists
    -- In my tests, chunking is about 25% faster than not chunking, so the gain is not significant (can probably remove)
    -- (This is a monadic version of `List.mapAsyncChunked` in Mathlib)
    let premiseChunkTasks ← name.toList.toChunks chunkSize |>.mapM fun names =>
      IO.asTask do
        let (premises, _) ← CoreM.toIO (ctx := ctxCore) (s := sCore) do
          names.mapM Premise.fromName
        return premises
    let premises ← premiseChunkTasks.flatMapM fun task => do
      IO.ofExcept (← IO.wait task)
    return premises.toArray

end Lean.PremiseSelection.Premise
