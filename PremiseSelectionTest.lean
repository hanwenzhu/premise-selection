import PremiseSelection

open Lean PremiseSelection.Cloud

section Profiling

set_option trace.premiseSelection.debug true
set_option trace.profiler true

example (a b : Nat) : a + b = b + a := by
  suggest_premises_cloud 16
  apply Nat.add_comm

#eval show CoreM _ from do
  let url ← getPremiseSelectionApiUrlM
  selectPremisesCore url "a b : Nat
    ⊢ Eq (HAdd.hAdd a b) (HAdd.hAdd b a)" none none 10

end Profiling

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
