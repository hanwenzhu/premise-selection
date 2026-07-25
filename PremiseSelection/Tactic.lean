module

public meta import Lean.Elab.Tactic
public meta import PremiseSelection.Cloud
public meta import PremiseSelection.Combinators
public meta import Lean.LibrarySuggestions.MePo

namespace Lean.LibrarySuggestions.Tactic

open Lean LibrarySuggestions Cloud

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

syntax (name := premises) "premises" (ppSpace num)? : tactic

open Elab Tactic in
@[tactic premises] public meta def evalPremises : Tactic
| `(tactic| premises $[$k?]?) => do
  let selector ← getSelector
  let defaultSelector := Cloud.premiseSelector <|> mepoSelector (useRarity := true) (p := 0.6) (c := 0.9)
  let selector := selector.getD defaultSelector
  let mut config : Config :=
    { maxSuggestions := (k?.map (·.getNat)).getD 100
      caller := "premises" }
  liftMetaTactic1 fun mvarId => do
    let suggestions ← selector mvarId config
    for suggestion in suggestions do
      let signature := MessageData.signature suggestion.name
      logInfo m!"Premise suggestion:\n{signature}"
    return mvarId
| _ => throwUnsupportedSyntax

end Lean.LibrarySuggestions.Tactic
