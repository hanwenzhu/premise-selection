import PremiseSelection
import Lean

open Lean PremiseSelection

set_option trace.premiseSelection.debug true

section Cloud

open Cloud

theorem Nat.add_eq_add_swap (a b : Nat) : a + b = b + a := Nat.add_comm ..
theorem Nat.add_comm' (a b : Nat) : a + b = b + a := Nat.add_comm ..
theorem add_comm_nat (a b : Nat) : a + b = b + a := Nat.add_comm ..
theorem add_comm (a b : Nat) : a + b = b + a := Nat.add_comm ..
theorem Nat.add.comm (a b : Nat) : a + b = b + a := Nat.add_comm ..

set_premise_selector premiseSelector
set_option premiseSelection.apiBaseUrl "http://leanpremise.net"

section Profiling

set_option profiler true

section ClientSideCache

#time  -- populate cache for premises to send to server
set_premise_selection_cloud_cache

#time  -- second call to cache; should be fast
set_premise_selection_cloud_cache

end ClientSideCache

section ServerSideCache

#time  -- first server call
example : True := by
  suggest_premises
  trivial

#time  -- second server call (to test server-side caching; need a freshly started server)
example : True := by
  suggest_premises
  trivial

end ServerSideCache

#time
example (a b : Nat) : a + b = b + a := by
  suggest_premises
  apply Nat.add_comm

-- The output is nonsense if no imported module and local premise information is provided
-- (i.e. no premise to select from)
#eval show CoreM _ from do
  selectPremisesCore "a b : Nat
    ⊢ Eq (HAdd.hAdd a b) (HAdd.hAdd b a)" #[] #[] 2

#eval show CoreM _ from do
  selectPremisesCore "a b : Nat
    ⊢ Eq (HAdd.hAdd a b) (HAdd.hAdd b a)" #[] #[← Premise.fromName ``Nat.add.comm false] 2

elab "simp_all_premises" k:num : tactic => do
  let suggestions ← select (← Elab.Tactic.getMainGoal) { maxSuggestions := k.getNat }
  let simpLemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
    suggestions.mapM fun suggestion => do
      let name := mkIdent suggestion.name
      `(Lean.Parser.Tactic.simpLemma| $name:term)
  Elab.Tactic.evalTactic (← `(tactic| simp_all [$simpLemmas,*]))

#time
example (a b : Nat) : a + b = b + a := by
  simp_all_premises 16

#time
example (a b : Nat) : a + (b + 1) = (a + b) + 1 := by
  simp_all_premises 16

#time
example (a b : Nat) : a + (b + 1) = (a + b) + 1 := by
  simp_all_premises 16

end Profiling

end Cloud

section Premise

#eval Cloud.getUnindexedImportedPremises
#eval Cloud.getUnindexedLocalPremises
#time
#eval Cloud.getUnindexedPremises
-- clear_premise_selection_cache
#time
#eval show CoreM _ from do
  let premises ← Cloud.getIndexedPremises
  let json := toJson premises
  return json.compress.length

/--
info: { name := `Nat.add,
  decl := "/-- Addition of natural numbers.\n\nThis definition is overridden in both the kernel and the compiler to efficiently\nevaluate using the \"bignum\" representation (see `Nat`). The definition provided\nhere is the logical model (and it is soundness-critical that they coincide).\n -/\ndef Nat.add : Nat → Nat → Nat" }
-/
#guard_msgs in #eval Premise.fromName ``Nat.add false

/--
info: { name := `Nat.add_comm, decl := "theorem Nat.add_comm (n m : Nat) : Eq (HAdd.hAdd n m) (HAdd.hAdd m n)" }
-/
#guard_msgs in #eval Premise.fromName ``Nat.add_comm false

-- set_option profiler true
-- set_option profiler.threshold 1

-- #time
-- #eval show MetaM _ from do
--   let env ← getEnv
--   for (name, ci) in env.constants do
--     discard $ Premise.fromName name

-- #eval show IO _ from do
--   let cache ← Premise.fromNameCacheRef.get
--   IO.println $ cache.find? `p
--   Premise.fromNameCacheRef.set (cache.insert `p default)

section Generated

/-! Generate 1000 theorems -/

#eval show Elab.Command.CommandElabM _ from do
  for i in [0:1000] do
    let name : Name := .str (.str .anonymous "Generated") s!"theorem{i}"
    Elab.Command.elabCommand (← `(command| theorem $(mkIdent name) : $(Syntax.mkNatLit i) = $(Syntax.mkNatLit i) := rfl))

end Generated

#time
#eval show MetaM _ from do
  let premises ← Cloud.getUnindexedLocalPremises
  assert! 1000 <= premises.size && premises.size < 2000
  return premises

-- This makes the server OOM if not for maxUnindexedPremises
example : 4882 = 4882 := by
  suggest_premises
  rfl

-- Stress test
-- #eval show MetaM _ from do
--   let premises : Array Premise := (Array.range 500).map fun n =>
--     { name := s!"thm{n}".toName, decl := "theorem MeasureTheory.pdf.indepFun_iff_pdf_prod_eq_pdf_mul_pdf {Ω : Type u_1} {E : Type u_2} [MeasurableSpace E] {m : MeasurableSpace Ω} {ℙ : Measure Ω} {μ : Measure E} {F : Type u_3} [MeasurableSpace F] {ν : Measure F} {X : Ω → E} {Y : Ω → F} [IsFiniteMeasure ℙ] [SigmaFinite μ] [SigmaFinite ν] [HasPDF (fun (ω : Ω) => (X ω, Y ω)) ℙ (μ.prod ν)] : ProbabilityTheory.IndepFun X Y ℙ ↔ pdf (fun (ω : Ω) => (X ω, Y ω)) ℙ (μ.prod ν) =ᶠ[ae (μ.prod ν)] fun (z : E × F) => pdf X ℙ μ z.1 * pdf Y ℙ ν z.2" }
--   Cloud.selectPremisesCore "a b : Nat ⊢ Eq (HAdd.hAdd a b) (HAdd.hAdd b a)" #[] #[] premises 32

end Premise

section MePo

open MePo

def mepoP := 0.6
def mepoC := 0.9

set_premise_selector mepoSelector (useRarity := true) (p := mepoP) (c := mepoC)

example (a b : Nat) : a + b = b + a := by
  suggest_premises
  simp_all_premises 16

end MePo

section Combinators

/-! `orElse` -/

set_premise_selector
  Cloud.premiseSelector
  <|> empty

/--
warning: Lean.PremiseSelection.orElse: Premise selector failed with error:
Could not send API request to --malformed-url/max-new-premises. curl exited with code 2:
curl: option --malformed-url/max-new-premises: is unknown
curl: try 'curl --help' or 'curl --manual' for more information
 Trying the alternative selector.
---
info: Premise suggestions: []
---
info: [premiseSelection.debug] State: a b : Nat
    ⊢ Eq (HAdd.hAdd a b) (HAdd.hAdd b a)
-/
#guard_msgs in
set_option premiseSelection.apiBaseUrl "--malformed-url" in
example (a b : Nat) : a + b = b + a := by
  suggest_premises
  apply Nat.add_comm

/-! `interleave` -/

set_premise_selector interleave #[
  Cloud.premiseSelector,
  mepoSelector (useRarity := true) (p := mepoP) (c := mepoC),
  empty
]

/-- Manually check this is the interleave of cloud & MePo results -/
example (a b : Nat) : a + b = b + a := by
  suggest_premises
  apply Nat.add_comm

end Combinators
