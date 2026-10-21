/-
  Physics: two resistors in parallel (a current divider), with a current
  source or a voltage source.

  With a voltage source the model is acyclic: each branch current follows from
  Ohm's law and the total current is their sum. With a current source the
  voltage and the two branch currents determine each other: Lean finds one
  cyclic block of three laws. The block is linear, and `linear_block` proves
  existence and uniqueness on its own (the determinant is 1 + R₂/R₁). The current divider rule then follows.
-/
import CausalPhys.Lang.Syntax

open CausalPhys CausalPhys.Lang

namespace CausalPhys.Examples

causal_model Divider where
  variables I I1 I2 U R1 R2
  domain 0 < R1 ∧ 0 < R2
  law kcl : I = I1 + I2
    solve I := I1 + I2
    solve I1 := I - I2
    solve I2 := I - I1
  law ohm1 : U = R1 * I1
    solve U := R1 * I1
    solve I1 := U / R1
  law ohm2 : U = R2 * I2
    solve U := R2 * I2
    solve I2 := U / R2
  setup currentSource fixes I R1 R2
  setup voltageSource fixes U R1 R2

#causal_order Divider.currentSource
#causal_check Divider.currentSource
#causal_order Divider.voltageSource
#causal_check Divider.voltageSource

namespace Divider

theorem currentSource_cyclic : ¬ currentSource.Acyclic := by struct_decide
theorem voltageSource_acyclic : voltageSource.Acyclic := by struct_decide

/-- With a current source and positive resistances there is exactly one state.
    `linear_block` proves this completely: it computes det(I − C) = 1 + R₂/R₁
    and sees that it is positive. -/
theorem currentSource_existsUnique (u : V → ℝ) (h1 : 0 < u .R1) (h2 : 0 < u .R2) :
    ∃! s, currentSource.scm.Solves u s := by
  linear_block

/-- The current divider rule: I₁ = R₂/(R₁ + R₂)·I. -/
theorem divider_rule {u s : V → ℝ} (h1 : 0 < u .R1) (h2 : 0 < u .R2)
    (hs : currentSource.scm.Solves u s) : s .I1 = u .R2 / (u .R1 + u .R2) * u .I := by
  have hR1 : s .R1 = u .R1 := currentSource.exo_eq hs (by simp [currentSource])
  have hR2 : s .R2 = u .R2 := currentSource.exo_eq hs (by simp [currentSource])
  have hI : s .I = u .I := currentSource.exo_eq hs (by simp [currentSource])
  have hD : model.dom s := by rw [show model.dom s = (0 < s .R1 ∧ 0 < s .R2) from rfl, hR1, hR2]; exact ⟨h1, h2⟩
  obtain ⟨hsat, -⟩ := (currentSource.solves_iff u s hD).1 hs
  have k : s .I = s .I1 + s .I2 := hsat .kcl
  have o1 : s .U = s .R1 * s .I1 := hsat .ohm1
  have o2 : s .U = s .R2 * s .I2 := hsat .ohm2
  rw [hR1, hR2, hI] at *
  have hsum : u .R1 + u .R2 ≠ 0 := by positivity
  rw [div_mul_eq_mul_div, eq_div_iff hsum]
  linear_combination (-(u .R2)) * k + o2 - o1

end Divider

end CausalPhys.Examples
