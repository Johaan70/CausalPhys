/-
  Axiom check for CI: every declaration of CausalPhys, CausalPhysAnalysis and PearlDoCalculus may
  depend only on the three standard axioms of Lean and Mathlib. This also
  catches `sorry` (which is the axiom `sorryAx`) and `native_decide`
  (which adds an axiom per use).
-/
import CausalPhys
import CausalPhysAnalysis

open Lean Elab Command

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

elab "#check_project_axioms" : command => do
  let env ← getEnv
  let mut bad : Array MessageData := #[]
  let mut count : Nat := 0
  for (n, _) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let modName := env.header.moduleNames[idx.toNat]!
    unless (`CausalPhys).isPrefixOf modName || (`CausalPhysAnalysis).isPrefixOf modName ||
        (`PearlDoCalculus).isPrefixOf modName do continue
    if n.isInternal then continue
    count := count + 1
    let axs ← liftCoreM <| Lean.collectAxioms n
    let extra := axs.filter fun a => !allowedAxioms.contains a
    unless extra.isEmpty do
      bad := bad.push m!"{n}: {extra.toList}"
  if bad.isEmpty then
    logInfo m!"axiom check passed: {count} declarations use only propext, Classical.choice, Quot.sound"
  else
    throwError m!"axiom check failed:\n{MessageData.joinSep bad.toList "\n"}"

#check_project_axioms
