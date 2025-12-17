/-
Getting new user-defined premises in an environment
-/
import Lean.LibrarySuggestions.Basic

open Lean Core

namespace Lean.LibrarySuggestions

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
initialize fromNameCacheRef : IO.Ref (NameMap Premise) ← IO.mkRef ∅

def fromNameCore (name : Name) : CoreM Premise := do
  -- Calculate signature from declaration name
  MetaM.run' do
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

/--
Serialize a declaration into a `Premise` by pretty-printing the declaration docstring and signature.

If `useCache := true`, this function is cached by `fromNameCacheRef`, so on the second time it is
called on the same declaration, it reads the previously stored result instead of calculates the signature again.
(**TODO**) This is just a temporary solution so that it is reasonable to call e.g. `aesop (add unsafe (by hammer))`
where `hammer` is called many times.
-/
def fromName (name : Name) (useCache : Bool) : CoreM Premise := do
  if !useCache then
    let premise ← fromNameCore name
    return premise
  else
    match (← fromNameCacheRef.get).find? name with
    | some premise => return premise
    | none =>
      let premise ← fromNameCore name
      fromNameCacheRef.modify fun cache => cache.insert name premise
      return premise

/--!
Copied from `List.toChunks` in `Batteries.Data.List.Basic`
(not importing `batteries` to minimize dependencies; this is a temporary decision for easier development).
-/
private def List.toChunks {α} : Nat → List α → List (List α)
  | _, [] => []
  | 0, xs => [xs]
  | n, x :: xs =>
    let rec
    /-- Auxliary definition used to define `toChunks`.
    `toChunks.go xs acc₁ acc₂` pushes elements into `acc₁` until it reaches size `n`,
    then it pushes the resulting list to `acc₂` and continues until `xs` is exhausted. -/
    go : List α → Array α → Array (List α) → List (List α)
    | [], acc₁, acc₂ => acc₂.push acc₁.toList |>.toList
    | x :: xs, acc₁, acc₂ =>
      if acc₁.size == n then
        go xs ((Array.mkEmpty n).push x) (acc₂.push acc₁.toList)
      else
        go xs (acc₁.push x) acc₂
    go xs #[x] #[]

/-- This is equivalent to `names.mapM Premise.fromName`, but it processes chunks in parallel. -/
def fromNames (names : Array Name) (chunkSize : Nat) (useCache : Bool) : CoreM (Array Premise) := do
  if chunkSize == 1 then
    let premises ← names.mapM (Premise.fromName (useCache := useCache))
    return premises

  else
    let ctxCore ← readThe Core.Context
    let sCore ← getThe Core.State

    -- The only reason for toList is because `List.toChunks` exists
    -- In my tests, chunking is about 25% faster than not chunking, so the gain is not significant (can probably remove)
    -- (This is a monadic version of `List.mapAsyncChunked` in Mathlib)
    let premiseChunkTasks ← List.toChunks chunkSize names.toList |>.mapM fun names =>
      IO.asTask do
        let (premises, _) ← CoreM.toIO (ctx := ctxCore) (s := sCore) do
          names.mapM (Premise.fromName (useCache := useCache))
        return premises
    let premises ← premiseChunkTasks.flatMapM fun task => do
      IO.ofExcept (← IO.wait task)
    return premises.toArray

end PrettyPrinting

/-! **TODO**: use the implementation of deny-list in https://github.com/leanprover/lean4/tree/mepo instead (once the branch is merged) -/

run_cmd
  for module in #[
    "Aesop", "Auto", "Cli", "CodeAction", "DocGen4", "Duper", "ImportGraph", "Lake", "Lean", "LeanSearchClient", "Linter", "Mathport",
    "MD4Lean", "Plausible", "ProofWidgets", "Qq", "QuerySMT", "Tactic", "TacticExtra", "Test", "Testing", "UnicodeBasic", "Util"
  ] do
    modifyEnv fun env => moduleDenyListExt.addEntry env module

run_cmd
  for name in #["Lean", "Lake", "Qq"] do
    modifyEnv fun env => nameDenyListExt.addEntry env name

run_cmd
  for typePrefix in #[`Lean] do
    modifyEnv fun env => typePrefixDenyListExt.addEntry env typePrefix

end Lean.LibrarySuggestions.Premise
