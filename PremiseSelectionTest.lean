import PremiseSelection

open Lean PremiseSelection

section Cloud

open Cloud

theorem Nat.add_eq_add_swap (a b : Nat) : a + b = b + a := Nat.add_comm ..
theorem Nat.add_comm' (a b : Nat) : a + b = b + a := Nat.add_comm ..
theorem add_comm_nat (a b : Nat) : a + b = b + a := Nat.add_comm ..
theorem add_comm (a b : Nat) : a + b = b + a := Nat.add_comm ..
theorem Nat.add.comm (a b : Nat) : a + b = b + a := Nat.add_comm ..

set_premise_selector premiseSelector

section Profiling

set_option profiler true

example (a b : Nat) : a + b = b + a := by
  suggest_premises
  apply Nat.add_comm

-- The output is nonsense if no imported module and local premise information is provided
-- (i.e. no premise to select from)
#eval show CoreM _ from do
  selectPremisesCore "a b : Nat
    ⊢ Eq (HAdd.hAdd a b) (HAdd.hAdd b a)" #[] #[] #[] 2

#eval show CoreM _ from do
  selectPremisesCore "a b : Nat
    ⊢ Eq (HAdd.hAdd a b) (HAdd.hAdd b a)" #[] #[] #[← Premise.fromName ``Nat.add.comm false] 2

end Profiling

set_option trace.premiseSelection.debug true

elab "simp_all_premises" k:num : tactic => do
  let suggestions ← select (← Elab.Tactic.getMainGoal) { maxSuggestions := k.getNat }
  let simpLemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
    suggestions.mapM fun suggestion => do
      let name := ⟨(mkIdent suggestion.name).raw⟩
      `(Lean.Parser.Tactic.simpLemma| $name:term)
  Elab.Tactic.evalTactic (← `(tactic| simp_all [$simpLemmas,*]))

example (a b : Nat) : a + b = b + a := by
  simp_all_premises 16

example (a b : Nat) : a + (b + 1) = (a + b) + 1 := by
  simp_all_premises 16

end Cloud

-- Check the legacy API works

deriving instance FromJson for Suggestion in
def callApiLegacy (apiBaseUrl : String) (state : String)
    (importedModules : Array Name) (newPremises : Array Name)
    (k : Nat) : IO (Array Suggestion) := do
  let apiUrl := apiBaseUrl ++ "/retrieve"
  let data := Json.mkObj [
    ("state", .str state),
    ("imported_modules", toJson importedModules),
    ("local_premises", toJson newPremises),
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

deriving instance Repr for Suggestion in
#eval show CoreM _ from do
  let baseUrl := Cloud.getApiBaseUrl (← getOptions)
  callApiLegacy baseUrl "a b : Nat\n⊢ Eq (HAdd.hAdd a b) (HAdd.hAdd b a)" #[] #[``Nat.add_comm] 10

section Premise

#eval Cloud.getUnindexedImportedPremises
#eval Cloud.getUnindexedLocalPremises
#time
#eval Cloud.getUnindexedPremises

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

-- This might make the server OOM
-- example : 4882 = 4882 := by
--   suggest_premises

-- Stress test
-- #eval show MetaM _ from do
--   let premises : Array Premise := (Array.range 500).map fun n =>
--     { name := s!"thm{n}".toName, decl := "theorem MeasureTheory.pdf.indepFun_iff_pdf_prod_eq_pdf_mul_pdf {Ω : Type u_1} {E : Type u_2} [MeasurableSpace E] {m : MeasurableSpace Ω} {ℙ : Measure Ω} {μ : Measure E} {F : Type u_3} [MeasurableSpace F] {ν : Measure F} {X : Ω → E} {Y : Ω → F} [IsFiniteMeasure ℙ] [SigmaFinite μ] [SigmaFinite ν] [HasPDF (fun (ω : Ω) => (X ω, Y ω)) ℙ (μ.prod ν)] : ProbabilityTheory.IndepFun X Y ℙ ↔ pdf (fun (ω : Ω) => (X ω, Y ω)) ℙ (μ.prod ν) =ᶠ[ae (μ.prod ν)] fun (z : E × F) => pdf X ℙ μ z.1 * pdf Y ℙ ν z.2" }
--   Cloud.selectPremisesCore "a b : Nat ⊢ Eq (HAdd.hAdd a b) (HAdd.hAdd b a)" #[] #[] premises 32

end Premise

-- section MePo

-- open MePo

-- set_premise_selector fun g _ => mepo (useRarity := true) g

-- example (a b : Nat) : a + b = b + a := by
--   suggest_premises
--   apply Nat.add_comm

-- end MePo
