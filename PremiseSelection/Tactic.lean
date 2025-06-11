import PremiseSelection.Cloud
import PremiseSelection.Combinators
import PremiseSelection.MePo

namespace Lean.PremiseSelection.Tactic

open Lean PremiseSelection

syntax (name := premises) "premises" (ppSpace num)? : tactic

open Elab Tactic in
@[tactic premises] def evalPremises : Tactic
| `(tactic| premises $[$k?]?) => do
  let selector := premiseSelectorExt.getState (← getEnv)
  let defaultSelector := Cloud.premiseSelector <|> mepoSelector (useRarity := true) (p := 0.6) (c := 0.9)
  let selector := selector.getD defaultSelector
  let mut config : Config :=
    { maxSuggestions := k?.map (·.getNat)
      caller := `premises }
  liftMetaTactic1 fun mvarId => do
    let suggestions ← selector mvarId config
    for suggestion in suggestions do
      let signature := MessageData.signature suggestion.name
      logInfo m!"Premise suggestion:\n{signature}"
    return mvarId
| _ => throwUnsupportedSyntax

end Lean.PremiseSelection.Tactic
