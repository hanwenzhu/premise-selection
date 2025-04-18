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
  let url := getApiBaseUrl (← getOptions)
  selectPremisesCore url "a b : Nat
    ⊢ Eq (HAdd.hAdd a b) (HAdd.hAdd b a)" none none 2

#eval show CoreM _ from do
  let url := getApiBaseUrl (← getOptions)
  selectPremisesCore url "a b : Nat
    ⊢ Eq (HAdd.hAdd a b) (HAdd.hAdd b a)" none (some #[← Premise.fromName ``Nat.add.comm]) 2

end Profiling

set_option trace.premiseSelection.debug true

elab "simp_all_premises" k:num : tactic => do
  let suggestions ← selectPremises (← Elab.Tactic.getMainGoal) k.getNat
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
    (importedModules : Option (Array Name)) (newPremises : Option (Array Name))
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
  callApiLegacy baseUrl "a b : Nat\n⊢ Eq (HAdd.hAdd a b) (HAdd.hAdd b a)" none #[``Nat.add_comm] 10

section Premise

/--
info: { name := `Nat.add,
  decl := "/-- Addition of natural numbers.\n\nThis definition is overridden in both the kernel and the compiler to efficiently\nevaluate using the \"bignum\" representation (see `Nat`). The definition provided\nhere is the logical model (and it is soundness-critical that they coincide).\n -/\ndef Nat.add : Nat → Nat → Nat" }
-/
#guard_msgs in #eval Premise.fromName ``Nat.add

/--
info: { name := `Nat.add_comm, decl := "theorem Nat.add_comm (n m : Nat) : Eq (HAdd.hAdd n m) (HAdd.hAdd m n)" }
-/
#guard_msgs in #eval Premise.fromName ``Nat.add_comm

#eval show MetaM _ from do
  let names ← Premise.getNames (← Cloud.getIndexedModules (Cloud.getApiBaseUrl (← getOptions)))
  assert! names.contains ``add_comm_nat
  IO.eprintln (names.take 100)

-- set_option profiler true
-- set_option profiler.threshold 1

-- #eval show IO _ from do
--   let cache ← Premise.fromNameCacheRef.get
--   IO.println $ cache.find? `p
--   Premise.fromNameCacheRef.set (cache.insert `p default)

section Generated

/-! Generate 10000 theorems -/

#eval show Elab.Command.CommandElabM _ from do
  for i in [0:10000] do
    let name : Name := .str (.str .anonymous "Generated") s!"theorem{i}"
    Elab.Command.elabCommand (← `(command| theorem $(mkIdent name) : $(Syntax.mkNatLit i) = $(Syntax.mkNatLit i) := rfl))

end Generated

#time
#eval show MetaM _ from do
  let premises ← Premise.getPremises (← Cloud.getIndexedModules (Cloud.getApiBaseUrl (← getOptions)))
  assert! 10000 <= premises.size && premises.size < 20000
  return premises.size

-- This makes the server OOM
-- example : 4882 = 4882 := by
--   suggest_premises

end Premise
