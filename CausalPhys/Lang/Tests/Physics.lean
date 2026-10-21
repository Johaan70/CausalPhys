/-
  Test suite, physics. Each model states the textbook answer as a theorem; the
  computed causal order and the uniqueness check are pinned with `#guard_msgs`,
  so any change in what the language computes makes the build fail.
-/
import CausalPhys.Lang.Syntax

open CausalPhys CausalPhys.Lang

namespace CausalPhys.Tests

/-! ## P1. Heat flow through two walls in series

  Expected: with both bath temperatures fixed, the heat flow Q and the
  temperature Tm between the walls determine each other (one cyclic block,
  linear). Exactly one steady state, and Q = (T₁ − T₂)/(R₁ + R₂): thermal
  resistances in series add. -/

causal_model ThermalWall where
  variables Q Tm T1 T2 R1 R2
  domain 0 < R1 ∧ 0 < R2
  law wall1 : T1 - Tm = R1 * Q
    solve Q := (T1 - Tm) / R1
    solve Tm := T1 - R1 * Q
  law wall2 : Tm - T2 = R2 * Q
    solve Q := (Tm - T2) / R2
    solve Tm := T2 + R2 * Q
  witness R1 := 1, R2 := 1
  setup baths fixes T1 T2 R1 R2

/--
info: wall1 determines Tm, reading [T1, R1, Q]
wall2 determines Q, reading [Tm, T2, R2]
cyclic block: [wall1, wall2]
-/
#guard_msgs in
#causal_order ThermalWall.baths
/--
info: cyclic, linear in each block: exactly one outcome of the causal model provided that
  ¬1 + (u ThermalWall.V.R2)⁻¹ * u ThermalWall.V.R1 = 0
(finish `block_linear` with a proof of this)
-/
#guard_msgs in
#causal_check ThermalWall.baths

namespace ThermalWall

theorem baths_cyclic : ¬ baths.Acyclic := by struct_decide

theorem baths_existsUnique (u : V → ℝ) (h1 : 0 < u .R1) (h2 : 0 < u .R2) :
    ∃! s, baths.scm.Solves u s := by
  linear_block

/-- Series resistances add. -/
theorem series {u s : V → ℝ} (h1 : 0 < u .R1) (h2 : 0 < u .R2) (hs : baths.scm.Solves u s) :
    s .Q = (u .T1 - u .T2) / (u .R1 + u .R2) := by
  have hR1 : s .R1 = u .R1 := baths.exo_eq hs (by simp [baths])
  have hR2 : s .R2 = u .R2 := baths.exo_eq hs (by simp [baths])
  have hT1 : s .T1 = u .T1 := baths.exo_eq hs (by simp [baths])
  have hT2 : s .T2 = u .T2 := baths.exo_eq hs (by simp [baths])
  have hD : model.dom s := by
    show 0 < s .R1 ∧ 0 < s .R2
    rw [hR1, hR2]; exact ⟨h1, h2⟩
  obtain ⟨hsat, -⟩ := (baths.solves_iff u s hD).1 hs
  have w1 : s .T1 - s .Tm = s .R1 * s .Q := hsat .wall1
  have w2 : s .Tm - s .T2 = s .R2 * s .Q := hsat .wall2
  rw [hR1, hR2, hT1, hT2] at *
  have hsum : u .R1 + u .R2 ≠ 0 := by positivity
  rw [eq_div_iff hsum]
  linear_combination (-1 : ℝ) * w1 - w2

end ThermalWall

/-! ## P2. A battery with internal resistance

  Expected: with EMF ε, internal resistance r and load R fixed, the loop law
  determines the current and Ohm's law at the load the terminal voltage; no
  cycles. A larger load resistance gives a higher terminal voltage
  U = εR/(R + r). -/

causal_model Battery where
  variables I U eps r R
  domain 0 < r ∧ 0 < R
  law loop : eps = (R + r) * I
    solve I := eps / (R + r)
  law load : U = R * I
    solve U := R * I
  witness I := 1, U := 1, eps := 2, r := 1, R := 1
  setup circuit fixes eps r R

/--
info: loop determines I, reading [eps, R, r]
load determines U, reading [R, I]
acyclic: every intervention has exactly one outcome of the causal model
-/
#guard_msgs in
#causal_order Battery.circuit
/--
info: acyclic: every intervention has exactly one outcome of the causal model (Setup.do_existsUnique; it satisfies the laws when it lies in the domain)
-/
#guard_msgs in
#causal_check Battery.circuit

namespace Battery

theorem circuit_acyclic : circuit.Acyclic := by struct_decide

theorem terminal_voltage (x : ℝ) (u s : V → ℝ) (h : (circuit.scm.doI .R x).Solves u s) :
    s .U = x * (u .eps / (x + u .r)) := by
  read_solution h
  rw [h_U, h_I, h_R, h_eps, h_r]

/-- Kirchhoff's loop law and Ohm's law have exactly one solution in the domain. -/
theorem circuit_laws (u : V → ℝ) (hr : 0 < u .r) (hR : 0 < u .R) :
    ∃! s, model.dom s ∧ model.Sat s ∧ ∀ v, v ∈ circuit.exo → s v = u v := by
  laws_unique

/-- A larger load resistance gives a higher terminal voltage. -/
theorem larger_load_higher_voltage (u s₁ s₂ : V → ℝ) {x₁ x₂ : ℝ}
    (he : 0 < u .eps) (hr : 0 < u .r) (hx₁ : 0 < x₁) (hx : x₁ < x₂)
    (h₁ : (circuit.scm.doI .R x₁).Solves u s₁) (h₂ : (circuit.scm.doI .R x₂).Solves u s₂) :
    s₁ .U < s₂ .U := by
  rw [terminal_voltage x₁ u s₁ h₁, terminal_voltage x₂ u s₂ h₂]
  have hx₂ : 0 < x₂ := hx₁.trans hx
  rw [mul_div_assoc', mul_div_assoc', div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos he hr]

end Battery

end CausalPhys.Tests
