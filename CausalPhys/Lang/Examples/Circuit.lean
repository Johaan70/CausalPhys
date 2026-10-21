/-
  Physics: a resistor heated by a current.

  Three laws, written once:
      Joule   P = U·I
      Ohm     U = R·I
      Newton  T = Tₐ + k·P      (steady-state temperature of the resistor)

  Two lab setups:
    * voltage source (U, R, Tₐ, k fixed)  → Lean computes: Ohm determines I,
      Joule determines P (found by an augmenting path), Newton determines T;
    * current source (I, R, Tₐ, k fixed)  → Ohm determines U.

  The textbook puzzle "does a larger resistor get hotter?" then gets two
  opposite answers, both proved:
    * with a voltage source a larger R gives a COOLER resistor (P = U²/R);
    * with a current source a larger R gives a HOTTER resistor (P = R·I²).
-/
import CausalPhys.Lang.Core
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

namespace CausalPhys.Lang.Circuit

/-- Voltage, resistance, current, power, temperature, ambient temperature,
    heat-transfer coefficient. -/
inductive V | U | Rr | I | P | T | Ta | k
deriving DecidableEq, Repr

instance : Inhabited V := ⟨.U⟩

inductive Law | joule | ohm | newton
deriving DecidableEq, Repr

noncomputable section

def model : Model Law V ℝ where
  eqList := [.joule, .ohm, .newton]
  varList := [.U, .Rr, .I, .P, .T, .Ta, .k]
  law
    | .joule, s => s .P = s .U * s .I
    | .ohm, s => s .U = s .Rr * s .I
    | .newton, s => s .T = s .Ta + s .k * s .P
  dom s := 0 < s .U ∧ 0 < s .Rr
  solvers
    | .joule => [(.P, mech [.U, .I] fun s => s .U * s .I),
                 (.I, mech [.P, .U] fun s => s .P / s .U)]
    | .ohm => [(.I, mech [.U, .Rr] fun s => s .U / s .Rr),
               (.U, mech [.Rr, .I] fun s => s .Rr * s .I)]
    | .newton => [(.T, mech [.Ta, .k, .P] fun s => s .Ta + s .k * s .P)]
  sound := by
    intro e v m h s hD
    cases e <;> simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Iff.rfl
      · show s .P = s .U * s .I ↔ s .I = s .P / s .U
        rw [eq_div_iff hD.1.ne']
        constructor <;> intro h <;> linear_combination -h
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · show s .U = s .Rr * s .I ↔ s .I = s .U / s .Rr
        rw [eq_div_iff hD.2.ne']
        constructor <;> intro h <;> linear_combination -h
      · exact Iff.rfl
    · obtain ⟨rfl, rfl⟩ := h
      exact Iff.rfl

def voltageSource : Setup model := { exo := [.U, .Rr, .Ta, .k] }
def currentSource : Setup model := { exo := [.I, .Rr, .Ta, .k] }

end

/-! ## Computed by Lean -/

theorem voltage_order :
    voltageSource.determines .ohm = .I ∧ voltageSource.determines .joule = .P ∧
    voltageSource.determines .newton = .T := by decide

theorem current_order :
    currentSource.determines .ohm = .U ∧ currentSource.determines .joule = .P ∧
    currentSource.determines .newton = .T := by decide

theorem voltage_acyclic : voltageSource.Acyclic := by decide
theorem current_acyclic : currentSource.Acyclic := by decide

/-! ## The physics -/

/-- With a voltage source, after do(R := r): T = Tₐ + k·U²/r. -/
theorem voltage_temp (r : ℝ) (u s : V → ℝ) (h : (voltageSource.scm.doI .Rr r).Solves u s) :
    s .T = u .Ta + u .k * (u .U * (u .U / r)) := by
  rw [voltageSource.do_exo_iff (by decide)] at h
  have hU := voltageSource.exo_eq h (v := .U) (by decide)
  have hR := voltageSource.exo_eq h (v := .Rr) (by decide)
  have hTa := voltageSource.exo_eq h (v := .Ta) (by decide)
  have hk := voltageSource.exo_eq h (v := .k) (by decide)
  have hI := voltageSource.mech_eq h .ohm
  have hP := voltageSource.mech_eq h .joule
  have hT := voltageSource.mech_eq h .newton
  obtain ⟨h1, h2, h3⟩ := voltage_order
  rw [h1] at hI; rw [h2] at hP; rw [h3] at hT
  simp only [Function.update_apply, reduceCtorEq, ↓reduceIte] at hU hR hTa hk
  simp [Model.mechOf, Model.find, model, mech] at hI hP hT
  rw [hT, hP, hI, hU, hR, hTa, hk]

/-- With a current source, after do(R := r): T = Tₐ + k·r·I². -/
theorem current_temp (r : ℝ) (u s : V → ℝ) (h : (currentSource.scm.doI .Rr r).Solves u s) :
    s .T = u .Ta + u .k * (r * u .I * u .I) := by
  rw [currentSource.do_exo_iff (by decide)] at h
  have hI := currentSource.exo_eq h (v := .I) (by decide)
  have hR := currentSource.exo_eq h (v := .Rr) (by decide)
  have hTa := currentSource.exo_eq h (v := .Ta) (by decide)
  have hk := currentSource.exo_eq h (v := .k) (by decide)
  have hU := currentSource.mech_eq h .ohm
  have hP := currentSource.mech_eq h .joule
  have hT := currentSource.mech_eq h .newton
  obtain ⟨h1, h2, h3⟩ := current_order
  rw [h1] at hU; rw [h2] at hP; rw [h3] at hT
  simp only [Function.update_apply, reduceCtorEq, ↓reduceIte] at hI hR hTa hk
  simp [Model.mechOf, Model.find, model, mech] at hU hP hT
  rw [hT, hP, hU, hI, hR, hTa, hk]

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

end CausalPhys.Lang.Circuit
