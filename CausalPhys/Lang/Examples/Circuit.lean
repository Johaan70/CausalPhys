/-
  Physics: a resistor heated by a current, with a voltage source or a current
  source.

  Lean computes the two causal orders (with a voltage source the matching needs
  an augmenting path). The textbook puzzle "does a larger resistor get hotter?"
  then gets two opposite answers, both proved: cooler with a voltage source
  (P = U²/R), hotter with a current source (P = R·I²).
-/
import CausalPhys.Lang.Syntax

open CausalPhys CausalPhys.Lang

namespace CausalPhys.Examples

causal_model Circuit where
  variables U Rr I P T Ta k      -- voltage, resistance, current, power, temperature,
                                 -- ambient temperature, heat-transfer coefficient
  units U : V, Rr : ohm, I : A, P : W, T : K, Ta : K, k : K/W
  domain 0 < U ∧ 0 < Rr
  law joule : P = U * I
  law ohm : U = Rr * I
  law newton : T = Ta + k * P
  witness U := 1, Rr := 1, I := 1, P := 1
  setup voltageSource fixes U Rr Ta k
  setup currentSource fixes I Rr Ta k

/--
info: joule determines P, reading [U, I]
ohm determines I, reading [U, Rr]
newton determines T, reading [Ta, k, P]
acyclic: every intervention has exactly one outcome of the causal model
-/
#guard_msgs in
#causal_order Circuit.voltageSource
/--
info: joule determines P, reading [U, I]
ohm determines U, reading [Rr, I]
newton determines T, reading [Ta, k, P]
acyclic: every intervention has exactly one outcome of the causal model
-/
#guard_msgs in
#causal_order Circuit.currentSource

namespace Circuit

theorem voltage_order :
    voltageSource.determines .ohm = .I ∧ voltageSource.determines .joule = .P ∧
    voltageSource.determines .newton = .T := by struct_decide

theorem current_order :
    currentSource.determines .ohm = .U ∧ currentSource.determines .joule = .P ∧
    currentSource.determines .newton = .T := by struct_decide

theorem voltage_acyclic : voltageSource.Acyclic := by struct_decide
theorem current_acyclic : currentSource.Acyclic := by struct_decide

/-- With a voltage source, after do(R := r): T = Tₐ + k·U²/r. -/
theorem voltage_temp (r : ℝ) (u s : V → ℝ) (h : (voltageSource.scm.doI .Rr r).Solves u s) :
    s .T = u .Ta + u .k * (u .U * (u .U / r)) := by
  read_solution h
  rw [h_T, h_P, h_I, h_U, h_Rr, h_Ta, h_k]

/-- With a current source, after do(R := r): T = Tₐ + k·r·I². -/
theorem current_temp (r : ℝ) (u s : V → ℝ) (h : (currentSource.scm.doI .Rr r).Solves u s) :
    s .T = u .Ta + u .k * (r * u .I * u .I) := by
  read_solution h
  rw [h_T, h_P, h_U, h_I, h_Rr, h_Ta, h_k]

/-- Voltage source: a larger resistor runs cooler. -/
theorem voltage_larger_R_cooler (u s₁ s₂ : V → ℝ) {r₁ r₂ : ℝ}
    (hk : 0 < u .k) (hU : u .U ≠ 0) (hr₁ : 0 < r₁) (hr : r₁ < r₂)
    (h₁ : (voltageSource.scm.doI .Rr r₁).Solves u s₁)
    (h₂ : (voltageSource.scm.doI .Rr r₂).Solves u s₂) : s₂ .T < s₁ .T := by
  rw [voltage_temp r₁ u s₁ h₁, voltage_temp r₂ u s₂ h₂]
  have hU2 : 0 < u .U * u .U := mul_self_pos.2 hU
  have : u .U * u .U / r₂ < u .U * u .U / r₁ := div_lt_div_of_pos_left hU2 hr₁ hr
  rw [mul_div_assoc, mul_div_assoc] at this
  linarith [mul_lt_mul_of_pos_left this hk]

/-- Current source: a larger resistor runs hotter. -/
theorem current_larger_R_hotter (u s₁ s₂ : V → ℝ) {r₁ r₂ : ℝ}
    (hk : 0 < u .k) (hI : u .I ≠ 0) (hr : r₁ < r₂)
    (h₁ : (currentSource.scm.doI .Rr r₁).Solves u s₁)
    (h₂ : (currentSource.scm.doI .Rr r₂).Solves u s₂) : s₁ .T < s₂ .T := by
  rw [current_temp r₁ u s₁ h₁, current_temp r₂ u s₂ h₂]
  have hI2 : 0 < u .I * u .I := mul_self_pos.2 hI
  nlinarith [mul_lt_mul_of_pos_right hr hI2, mul_pos hk hI2]

end Circuit

end CausalPhys.Examples
