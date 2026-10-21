/-
  Test suite, economics. See `Physics.lean` for the format.
-/
import CausalPhys.Lang.Syntax

open CausalPhys CausalPhys.Lang

namespace CausalPhys.Tests

/-! ## E1. The Keynesian cross

  Laws: Y = C + I + G and C = c₀ + c₁·(Y − T), with marginal propensity to
  consume 0 < c₁ < 1.

  Expected:
  * short run (I, G, T fixed): income and consumption determine each other
    (one linear cyclic block); exactly one equilibrium because c₁ ≠ 1; the
    government spending multiplier is 1/(1 − c₁).
  * policy target (Y, I, T fixed): consumption follows from income, and the
    income identity then determines the G needed to reach the target; no
    cycles. -/

/-- Autonomous consumption and the marginal propensity to consume. -/
structure Keynes.Params where
  c0 : ℝ
  c1 : ℝ
  h0 : 0 ≤ c1
  h1 : c1 < 1

causal_model Keynes (k : Keynes.Params) where
  variables Y C I G Tax
  law income : Y = C + I + G
    solve Y := C + I + G
    solve G := Y - C - I
  law consumption : C = k.c0 + k.c1 * (Y - Tax)
    solve C := k.c0 + k.c1 * (Y - Tax)
  setup shortRun fixes I G Tax
  setup target fixes Y I Tax

namespace Keynes

variable (k : Params)

/--
info: income determines Y, reading [C, I, G]
consumption determines C, reading [Y, Tax]
cyclic block: [income, consumption]
-/
#guard_msgs in
#causal_order shortRun k
/--
info: cyclic, linear: exactly one outcome of the causal model provided that
  ¬1 - k.c1 = 0
(finish `linear_block` with a proof of this)
-/
#guard_msgs in
#causal_check shortRun k
/--
info: income determines G, reading [Y, C, I]
consumption determines C, reading [Y, Tax]
acyclic: every intervention has exactly one outcome of the causal model
-/
#guard_msgs in
#causal_order target k
/--
info: acyclic: every intervention has exactly one outcome of the causal model (Setup.do_existsUnique; it satisfies the laws when it lies in the domain)
-/
#guard_msgs in
#causal_check target k

theorem shortRun_cyclic : ¬ (shortRun k).Acyclic := by struct_decide
theorem target_acyclic : (target k).Acyclic := by struct_decide
theorem target_income_determines_G : (target k).determines .income = .G := by struct_decide

variable {k}

theorem shortRun_existsUnique (u : V → ℝ) : ∃! s, (shortRun k).scm.Solves u s := by
  linear_block
  have := k.h1
  intro h
  linarith

/-- Equilibrium income. -/
theorem income_eq {u s : V → ℝ} (hs : (shortRun k).scm.Solves u s) :
    s .Y = (k.c0 - k.c1 * u .Tax + u .I + u .G) / (1 - k.c1) := by
  obtain ⟨hsat, hex⟩ := ((shortRun k).solves_iff u s trivial).1 hs
  have y : s .Y = s .C + s .I + s .G := hsat .income
  have c : s .C = k.c0 + k.c1 * (s .Y - s .Tax) := hsat .consumption
  rw [hex .I (by simp [shortRun]), hex .G (by simp [shortRun]),
    hex .Tax (by simp [shortRun])] at *
  have : 1 - k.c1 ≠ 0 := by have := k.h1; linarith
  rw [eq_div_iff this]
  linear_combination y + c

/-- The multiplier: raising G by Δ raises income by Δ/(1 − c₁). -/
theorem multiplier {u s s' : V → ℝ} (Δ : ℝ) (hs : (shortRun k).scm.Solves u s)
    (hs' : ((shortRun k).scm.doI .G (u .G + Δ)).Solves u s') :
    s' .Y - s .Y = Δ / (1 - k.c1) := by
  rw [(shortRun k).do_exo_iff (by simp [shortRun])] at hs'
  rw [income_eq hs', income_eq hs]
  simp only [Function.update_apply, reduceCtorEq, ↓reduceIte]
  have : 1 - k.c1 ≠ 0 := by have := k.h1; linarith
  field_simp
  ring

/-- The spending needed to reach a target income. -/
theorem target_G {u s : V → ℝ} (hs : (target k).scm.Solves u s) :
    s .G = u .Y - (k.c0 + k.c1 * (u .Y - u .Tax)) - u .I := by
  read_solution hs
  rw [hs_G, hs_C, hs_Y, hs_I, hs_Tax]

end Keynes

/-! ## E2. The quantity theory of money

  Law: M·V = P·Y.

  Expected (the same structure as the gas law):
  * classical, flexible prices (M, V, Y fixed): the law determines P;
    doubling the money supply doubles the price level and leaves output.
  * fixed prices (M, V, P fixed): the law determines Y; doubling the money
    supply doubles output and leaves prices. -/

causal_model Quantity where
  variables M Vel P Y
  domain 0 < P ∧ 0 < Y
  law fisher : M * Vel = P * Y
    solve P := M * Vel / Y
    solve Y := M * Vel / P
  setup classical fixes M Vel Y
  setup fixedPrice fixes M Vel P

/--
info: fisher determines P, reading [M, Vel, Y]
acyclic: every intervention has exactly one outcome of the causal model
-/
#guard_msgs in
#causal_order Quantity.classical
/--
info: fisher determines Y, reading [M, Vel, P]
acyclic: every intervention has exactly one outcome of the causal model
-/
#guard_msgs in
#causal_order Quantity.fixedPrice

namespace Quantity

theorem classical_determines_P : classical.determines .fisher = .P := by struct_decide
theorem fixedPrice_determines_Y : fixedPrice.determines .fisher = .Y := by struct_decide

theorem classical_money (u s s' : V → ℝ) (hs : classical.scm.Solves u s)
    (hs' : (classical.scm.doI .M (2 * u .M)).Solves u s') :
    s' .P = 2 * s .P ∧ s' .Y = s .Y := by
  read_solution hs
  read_solution hs'
  refine ⟨?_, by rw [hs'_Y, hs_Y]⟩
  rw [hs'_P, hs_P, hs'_M, hs_M, hs'_Vel, hs_Vel, hs'_Y, hs_Y]
  ring

theorem fixedPrice_money (u s s' : V → ℝ) (hs : fixedPrice.scm.Solves u s)
    (hs' : (fixedPrice.scm.doI .M (2 * u .M)).Solves u s') :
    s' .Y = 2 * s .Y ∧ s' .P = s .P := by
  read_solution hs
  read_solution hs'
  refine ⟨?_, by rw [hs'_P, hs_P]⟩
  rw [hs'_Y, hs_Y, hs'_M, hs_M, hs'_Vel, hs_Vel, hs'_P, hs_P]
  ring

end Quantity

end CausalPhys.Tests
