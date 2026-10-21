/-
  Test suite, chemistry. See `Physics.lean` for the format.
-/
import CausalPhys.Lang.Syntax
import CausalPhys.Physics
import Mathlib.Analysis.Complex.Exponential

open CausalPhys CausalPhys.Lang

namespace CausalPhys.Tests

/-! ## C1. A weak acid, titrated or buffered

  Laws: Ka·[HA] = [H⁺][A⁻], mass balance C = [HA] + [A⁻], and charge balance
  [H⁺] + [Na⁺] = [A⁻] (water neglected).

  Expected:
  * titration (C, added Na⁺ and Ka fixed): [H⁺], [A⁻] and [HA] form one cyclic
    block that is nonlinear ([H⁺]·[A⁻]); uniqueness needs a chemical argument.
  * buffer (C, [H⁺] and Ka fixed): the acid law and the mass balance form a
    linear block; the charge balance only reports how much base was needed.
    The dissociated fraction is [A⁻] = C·Ka/([H⁺] + Ka) (Henderson–Hasselbalch). -/

causal_model WeakAcid where
  variables H A HA Na C Ka
  domain 0 < H ∧ 0 < Ka
  law acid : Ka * HA = H * A
    solve A := Ka * HA / H
    solve HA := H * A / Ka
  law mass : C = HA + A
    solve HA := C - A
    solve A := C - HA
    solve C := HA + A
  law charge : H + Na = A
    solve Na := A - H
    solve H := A - Na
  witness H := 1, A := 1, HA := 1, C := 2, Ka := 1
  setup titration fixes C Na Ka
  setup buffer fixes C H Ka

/--
info: acid determines A, reading [Ka, HA, H]
mass determines HA, reading [C, A]
charge determines H, reading [A, Na]
cyclic block: [acid, mass, charge]
-/
#guard_msgs in
#causal_order WeakAcid.titration
/--
info: cyclic: neither criterion applies (some formula is not affine in its own block, and not affine in each variable separately); uniqueness needs a domain-specific argument (monotonicity, Gale–Nikaido, Minty–Browder), plugged in with Setup.unique_of_laws
-/
#guard_msgs in
#causal_check WeakAcid.titration
/--
info: acid determines A, reading [Ka, HA, H]
mass determines HA, reading [C, A]
charge determines Na, reading [A, H]
cyclic block: [acid, mass]
-/
#guard_msgs in
#causal_order WeakAcid.buffer
/--
info: cyclic, linear in each block: exactly one outcome of the causal model provided that
  ¬1 + (u WeakAcid.V.H)⁻¹ * u WeakAcid.V.Ka = 0
(finish `block_linear` with a proof of this)
-/
#guard_msgs in
#causal_check WeakAcid.buffer

namespace WeakAcid

theorem titration_cyclic : ¬ titration.Acyclic := by struct_decide
theorem buffer_charge_determines_Na : buffer.determines .charge = .Na := by struct_decide
theorem buffer_block : buffer.block .acid = [.acid, .mass] := by struct_decide

theorem buffer_existsUnique (u : V → ℝ) (hH : 0 < u .H) (hK : 0 < u .Ka) :
    ∃! s, buffer.scm.Solves u s := by
  linear_block

/-- Henderson–Hasselbalch: the dissociated fraction. -/
theorem dissociated {u s : V → ℝ} (hH : 0 < u .H) (hK : 0 < u .Ka)
    (hs : buffer.scm.Solves u s) : s .A = u .C * u .Ka / (u .H + u .Ka) := by
  have eH : s .H = u .H := buffer.exo_eq hs (by simp [buffer])
  have eK : s .Ka = u .Ka := buffer.exo_eq hs (by simp [buffer])
  have eC : s .C = u .C := buffer.exo_eq hs (by simp [buffer])
  have hD : model.dom s := by
    show 0 < s .H ∧ 0 < s .Ka
    rw [eH, eK]; exact ⟨hH, hK⟩
  obtain ⟨hsat, -⟩ := (buffer.solves_iff u s hD).1 hs
  have a : s .Ka * s .HA = s .H * s .A := hsat .acid
  have m : s .C = s .HA + s .A := hsat .mass
  rw [eH, eK, eC] at *
  have hsum : u .H + u .Ka ≠ 0 := by positivity
  rw [eq_div_iff hsum]
  linear_combination (-1 : ℝ) * a - u .Ka * m

end WeakAcid

/-! ## C2. Beer–Lambert after dilution

  Laws: A = ε·l·c and c·V = n.

  Expected:
  * prepared sample (ε, l, n, V fixed): c follows from n and V, then A from c;
    doubling the volume halves the absorbance.
  * flow cell fed from a reservoir (ε, l, c, V fixed): the amount n in the
    cell follows from c and V; doubling the volume doubles n and leaves A. -/

causal_model BeerLambert where
  variables Abs eps l c n vol
  domain 0 < vol
  law beer : Abs = eps * l * c
    solve Abs := eps * l * c
  law conc : c * vol = n
    solve c := n / vol
    solve n := c * vol
  witness vol := 1
  setup prepared fixes eps l n vol
  setup flowCell fixes eps l c vol

/--
info: beer determines Abs, reading [eps, l, c]
conc determines c, reading [n, vol]
acyclic: every intervention has exactly one outcome of the causal model
-/
#guard_msgs in
#causal_order BeerLambert.prepared
/--
info: beer determines Abs, reading [eps, l, c]
conc determines n, reading [c, vol]
acyclic: every intervention has exactly one outcome of the causal model
-/
#guard_msgs in
#causal_order BeerLambert.flowCell

namespace BeerLambert

theorem prepared_acyclic : prepared.Acyclic := by struct_decide
theorem flowCell_acyclic : flowCell.Acyclic := by struct_decide

theorem prepared_dilute (u s s' : V → ℝ) (hv : u .vol ≠ 0)
    (hs : prepared.scm.Solves u s) (hs' : (prepared.scm.doI .vol (2 * u .vol)).Solves u s') :
    s' .Abs = s .Abs / 2 := by
  read_solution hs
  read_solution hs'
  rw [hs'_Abs, hs_Abs, hs'_c, hs_c, hs'_eps, hs_eps, hs'_l, hs_l, hs'_n, hs_n, hs'_vol, hs_vol]
  field_simp

theorem flowCell_dilute (u s s' : V → ℝ)
    (hs : flowCell.scm.Solves u s) (hs' : (flowCell.scm.doI .vol (2 * u .vol)).Solves u s') :
    s' .Abs = s .Abs ∧ s' .n = 2 * s .n := by
  read_solution hs
  read_solution hs'
  constructor
  · rw [hs'_Abs, hs_Abs, hs'_c, hs_c, hs'_eps, hs_eps, hs'_l, hs_l]
  · rw [hs'_n, hs_n, hs'_c, hs_c, hs'_vol, hs_vol]; ring

end BeerLambert

/-! ## C3. Arrhenius

  Laws: k = A·exp(−Eₐ/(R·T)) and rate = k·[X].

  Expected: no cycles; at a higher temperature the reaction runs faster
  (for positive A, Eₐ and [X]). -/

causal_model Arrhenius where
  variables k Pre Ea T X rate
  domain 0 < T
  law arrhenius : k = Pre * Real.exp (-(Ea / (R * T)))
    solve k := Pre * Real.exp (-(Ea / (R * T)))
  law rateLaw : rate = k * X
    solve rate := k * X
  witness T := 1
  setup lab fixes Pre Ea T X

/--
info: arrhenius determines k, reading [Pre, Ea, T]
rateLaw determines rate, reading [k, X]
acyclic: every intervention has exactly one outcome of the causal model
-/
#guard_msgs in
#causal_order Arrhenius.lab

namespace Arrhenius

theorem lab_acyclic : lab.Acyclic := by struct_decide

theorem hotter_faster (u s₁ s₂ : V → ℝ) {T₁ T₂ : ℝ}
    (hA : 0 < u .Pre) (hE : 0 < u .Ea) (hX : 0 < u .X) (hT₁ : 0 < T₁) (hT : T₁ < T₂)
    (h₁ : (lab.scm.doI .T T₁).Solves u s₁) (h₂ : (lab.scm.doI .T T₂).Solves u s₂) :
    s₁ .rate < s₂ .rate := by
  read_solution h₁
  read_solution h₂
  rw [h₁_rate, h₂_rate, h₁_k, h₂_k, h₁_Pre, h₂_Pre, h₁_Ea, h₂_Ea, h₁_T, h₂_T, h₁_X, h₂_X]
  have hR := R_pos
  have hT₂ : 0 < T₂ := hT₁.trans hT
  have key : -(u .Ea / (R * T₁)) < -(u .Ea / (R * T₂)) := by
    apply neg_lt_neg
    apply div_lt_div_of_pos_left hE (by positivity)
    exact mul_lt_mul_of_pos_left hT hR
  have := Real.exp_lt_exp.2 key
  have := mul_lt_mul_of_pos_left this hA
  exact mul_lt_mul_of_pos_right this hX

end Arrhenius

end CausalPhys.Tests
