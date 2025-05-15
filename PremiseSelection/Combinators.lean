/-
Combinators that combine two premise selectors
-/

import Lean.PremiseSelection

namespace Lean.PremiseSelection

/-- Try the first premise selector. If it throws an error, try the second one. -/
def orElse (s₁ : Selector) (s₂ : Unit → Selector) : Selector := fun g config => do
  try
    s₁ g config
  catch e =>
    logWarning m!"Lean.PremiseSelection.orElse: Premise selector failed with error:
{e.toMessageData}
Trying the alternative selector."
    s₂ () g config

instance : OrElse Selector := ⟨orElse⟩

/--
A single combinator that lets each of the `n` selectors select `k` premises,
merge the `n * k` results by rank, and returns the deduplicated top `k` among them.

This combinator is inspired by MeSh, but it is a simplified version of MeSh.
(MeSh can control the weight and steepness of probability density for each selector.)
-/
def interleave (selectors : Array Selector) : Selector := fun g config => do
  let allSelectorSuggestions ← selectors.mapM fun s => s g config
  let mut suggestions := #[]
  let mut visited : NameSet := {}
  let maxNumSuggestions := allSelectorSuggestions.foldl (fun n ss => max n ss.size) 0
  for idx in List.range maxNumSuggestions do
    for selectorSuggestions in allSelectorSuggestions do
      if let some s := selectorSuggestions[idx]? then
        unless visited.contains s.name do
          suggestions := suggestions.push s
          visited := visited.insert s.name
          if some suggestions.size == config.maxSuggestions then
            return suggestions
  return suggestions

end Lean.PremiseSelection
