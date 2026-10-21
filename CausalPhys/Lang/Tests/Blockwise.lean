/-
  Test suite, the blockwise linear criterion (physics). These are the two
  situations the independent review found the whole-setup linear criterion
  could not handle; each block is now treated on its own.
-/
import CausalPhys.Lang.Syntax

open CausalPhys CausalPhys.Lang

namespace CausalPhys.Tests

/-! ## B1. Current divider with the power dissipated in one resistor

  Expected: the divider is a linear block {U, I₁, I₂}; the power P₁ = R₁·I₁² is
  nonlinear, but downstream, so it does not matter: exactly one state. -/

causal_model DividerPower where
  variables I I1 I2 U R1 R2 P1
  units I : A, I1 : A, I2 : A, U : V, R1 : ohm, R2 : ohm, P1 : W
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
  law joule : P1 = R1 * I1 * I1
    solve P1 := R1 * I1 * I1
  witness I := 2, I1 := 1, I2 := 1, U := 1, R1 := 1, R2 := 1, P1 := 1
  setup currentSource fixes I R1 R2

/--
info: cyclic, linear in each block: exactly one outcome of the causal model provided that
  ¬1 + (u DividerPower.V.R1)⁻¹ * u DividerPower.V.R2 = 0
(finish `block_linear` with a proof of this)
-/
#guard_msgs in
#causal_check DividerPower.currentSource

theorem DividerPower.existsUnique (u : DividerPower.V → ℝ) (h1 : 0 < u .R1) (h2 : 0 < u .R2) :
    ∃! s, DividerPower.currentSource.scm.Solves u s := by
  block_linear

/-! ## B2. Current divider with a heated resistor

  The heater sets the temperature T = Tₐ + k·P_h, and the resistance of the
  first branch depends on it: R₁ = R₀·(1 + α·T). Both are upstream of the
  divider, so the divider's coefficients depend on an endogenous variable.

  Expected: the divider block is still linear; exactly one state as long as the
  heated resistance stays positive. `block_linear` substitutes the upstream laws
  and leaves exactly that condition: 1 + R₂/(R₀(1 + α(Tₐ + k·P_h))) ≠ 0. -/

causal_model HeatedDivider where
  variables Ta k Ph T R0 al R1 R2 I I1 I2 U
  units Ta : K, k : K/W, Ph : W, T : K, R0 : ohm, al : 1/K, R1 : ohm, R2 : ohm, I : A,
    I1 : A, I2 : A, U : V
  domain 0 < R1 ∧ 0 < R2
  law heat : T = Ta + k * Ph
    solve T := Ta + k * Ph
  law thermistor : R1 = R0 * (1 + al * T)
    solve R1 := R0 * (1 + al * T)
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
  witness R0 := 1, R1 := 1, R2 := 1, I := 2, I1 := 1, I2 := 1, U := 1
  setup circuit fixes Ta k Ph R0 al R2 I

/--
info: heat determines T, reading [Ta, k, Ph]
thermistor determines R1, reading [R0, al, T]
kcl determines I2, reading [I, I1]
ohm1 determines I1, reading [U, R1]
ohm2 determines U, reading [R2, I2]
cyclic block: [kcl, ohm1, ohm2]
-/
#guard_msgs in
#causal_order HeatedDivider.circuit
/--
info: cyclic, linear in each block: exactly one outcome of the causal model provided that
  ¬1 +
      (u HeatedDivider.V.R0 + u HeatedDivider.V.R0 * u HeatedDivider.V.al * u HeatedDivider.V.Ta +
            u HeatedDivider.V.R0 * u HeatedDivider.V.al * u HeatedDivider.V.k * u HeatedDivider.V.Ph)⁻¹ *
        u HeatedDivider.V.R2 =
    0
(finish `block_linear` with a proof of this)
-/
#guard_msgs in
#causal_check HeatedDivider.circuit

theorem HeatedDivider.existsUnique (u : HeatedDivider.V → ℝ) (h2 : 0 < u .R2)
    (hR : 0 < u .R0 * (1 + u .al * (u .Ta + u .k * u .Ph))) :
    ∃! s, HeatedDivider.circuit.scm.Solves u s := by
  block_linear
  have hR' : 0 < u .R0 + u .R0 * u .al * u .Ta + u .R0 * u .al * u .k * u .Ph := by
    linarith [hR, show u .R0 * (1 + u .al * (u .Ta + u .k * u .Ph)) =
      u .R0 + u .R0 * u .al * u .Ta + u .R0 * u .al * u .k * u .Ph by ring]
  have := mul_pos (inv_pos.2 hR') h2
  intro h
  linarith

end CausalPhys.Tests
