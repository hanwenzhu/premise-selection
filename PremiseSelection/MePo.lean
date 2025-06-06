
/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import PremiseSelection.Premise
import Lean.Util.FoldConsts
import Lean.Meta.Basic

/-!
# MePo premise selection
This is a naive implement of the MePo premise selection algorithm, from
"Lightweight relevance filtering for machine-generated resolution problems" by Meng and Paulson.
It needs to be tuned and evaluated for Lean.
-/

open Lean

namespace Lean.NameSet

instance : Union NameSet where
  union := fun s t => s.fold (fun t n => t.insert n) t

instance : Inter NameSet where
  inter := fun s t => s.fold (fun r n => if t.contains n then r.insert n else r) {}

instance : SDiff NameSet where
  sdiff := fun s t => t.fold (fun s n => s.erase n) s

end Lean.NameSet

namespace Lean.PremiseSelection.MePo

def symbolFrequency (env : Environment) : NameMap Nat := Id.run do
  let mut map := {}
  for (_, ci) in env.constants do
    for n' in ci.type.getUsedConstantsAsSet do
      map := map.insert n' (map.findD n' 0 + 1)
  return map

def weightedScore (weight : Name → Float) (relevant candidate : NameSet) : Float :=
  let S := candidate
  let R := relevant ∩ S
  let R' := S \ R
  let M := R.fold (fun acc n => acc + weight n) 0
  M / (M + R'.size.toFloat)

-- This function is taken from the MePo paper and needs to be tuned.
def weightFunction (n : Nat) := 1.0 + 2.0 / (n.log2.toFloat + 1.0)

def frequencyScore (frequency : Name → Nat) (relevant candidate : NameSet) : Float :=
  weightedScore (fun n => weightFunction (frequency n)) relevant candidate

def unweightedScore (relevant candidate : NameSet) : Float := weightedScore (fun _ => 1) relevant candidate

def mepo (initialRelevant : NameSet) (score : NameSet → NameSet → Float) (accept : ConstantInfo → CoreM Bool) (p : Float) (c : Float) : CoreM (Array (Name × Float)) := do
  let env ← getEnv
  let mut p := p
  let mut candidates := #[]
  let mut relevant := initialRelevant
  let mut accepted : Array (Name × Float) := {}
  for (n, ci) in env.constants do
    if ← accept ci then
      candidates := candidates.push (n, ci.type.getUsedConstantsAsSet)
  while candidates.size > 0 do
    let (newAccepted, candidates') := candidates.map (fun (n, c) => (n, c, score relevant c)) |>.partition fun (_, _, s) => p ≤ s
    if newAccepted.isEmpty then return accepted
    accepted := newAccepted.foldl (fun acc (n, _, s) => acc.push (n, s)) accepted
    candidates := candidates'.map fun (n, c, _) => (n, c)
    relevant := newAccepted.foldl (fun acc (_, ns, _) => acc ++ ns) relevant
    p := p + (1 - p) / c
  return accepted

open Lean Meta MVarId in
def _root_.Lean.MVarId.getConstants (g : MVarId) : MetaM NameSet := withContext g do
  let mut c := (← g.getType).getUsedConstantsAsSet
  for t in (← getLocalHyps) do
    c := c ∪ (← inferType t).getUsedConstantsAsSet
  return c

end MePo

open MePo

-- The values of p := 0.6 and c := 2.4 are taken from the MePo paper, and need to be tuned.
-- When retrieving ≤32 premises for use by downstream automation, Thomas Zhu suggests that c := 0.5 is optimal.
def mepoSelector (useRarity : Bool) (p : Float := 0.6) (c : Float := 2.4) : Selector := fun g config => do
  let constants ← g.getConstants
  let env ← getEnv
  let score := if useRarity then
    let frequency := symbolFrequency env
    frequencyScore (frequency.findD · 0)
  else
    unweightedScore
  let accept := fun ci => do
    return ! isDeniedPremise env ci.name
  let suggestions ← mepo constants score accept p c
  let suggestions := suggestions
    |>.map (fun (n, s) => { name := n, score := s })
    |>.reverse  -- we favor constants that appear at the end of `env.constants`
  match config.maxSuggestions with
  | none => return suggestions
  | some k => return suggestions.take k
