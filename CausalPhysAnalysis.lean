/-
  CausalPhysAnalysis — functional analysis beyond what the causal language
  needs: Minty–Browder in Hilbert and reflexive Banach spaces (also with
  hemicontinuity only, via KKM), reflexivity of ℓᵖ and Lᵖ(μ), Goldstine and
  Milman–Pettis, and causal models with infinitely many variables on ℓ².

  It is a separate library so that a Mathlib update can move the language
  forward even when these proofs need repair. CI builds and checks it in its
  own step.
-/
import CausalPhysAnalysis.MintyBrowderHilbert
import CausalPhysAnalysis.MintyBrowderBanach
import CausalPhysAnalysis.MintyBrowderHemi
import CausalPhysAnalysis.LpReflexive
import CausalPhysAnalysis.Reflexivity
import CausalPhysAnalysis.LpMeasure
import CausalPhysAnalysis.InfiniteSCM
