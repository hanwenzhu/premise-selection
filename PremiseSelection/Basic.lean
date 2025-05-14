/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Thomas Zhu

(This file is copied from the `mepo` branch in `leanprover/lean4`.)
-/
import Lean.PremiseSelection

namespace Lean.PremiseSelection

section DenyList

/-- Premises from a module whose name has one of the following components are not retrieved. -/
initialize moduleDenyListExt : SimplePersistentEnvExtension String (List String) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := (·.cons)
    addImportedFn := mkStateFromImportedEntries (·.cons) []
  }

/-- A premise whose name has one of the following components is not retrieved. -/
initialize nameDenyListExt : SimplePersistentEnvExtension String (List String) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := (·.cons)
    addImportedFn := mkStateFromImportedEntries (·.cons) []
  }

/-- A premise whose `type.getForallBody.getAppFn` is a constant that has one of these prefixes is not retrieved. -/
initialize typePrefixDenyListExt : SimplePersistentEnvExtension Name (List Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := (·.cons)
    addImportedFn := mkStateFromImportedEntries (·.cons) []
  }

def isDeniedModule (env : Environment) (moduleName : Name) : Bool :=
  (moduleDenyListExt.getState env).any fun p => moduleName.anyS (· == p)

def isDeniedPremise (env : Environment) (name : Name) : Bool := Id.run do
  if name == ``sorryAx then return true
  if name.isInternalDetail then return true
  if (nameDenyListExt.getState env).any (fun p => name.anyS (· == p)) then return true
  if let some moduleIdx := env.getModuleIdxFor? name then
    let moduleName := env.header.moduleNames[moduleIdx.toNat]!
    if isDeniedModule env moduleName then
      return true
  let some ci := env.find? name | return true
  if let .const fnName _ := ci.type.getForallBody.getAppFn then
    if (typePrefixDenyListExt.getState env).any (fun p => p.isPrefixOf fnName) then return true
  return false

end DenyList

end Lean.PremiseSelection
