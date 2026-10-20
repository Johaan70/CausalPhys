/-
  CausalPhys.BrowderMinty — eksistens for monotone systemer.

  Det fulle Minty–Browder-teoremet (kontinuerlig, monoton, koersiv ⇒ surjektiv)
  hviler på Brouwers fikspunktteorem, som ikke finnes i Mathlib. Her
  formaliseres den sterkt monotone varianten (Zarantonello 1960), som ikke
  trenger Brouwer og gjelder i ethvert reelt Hilbert-rom:

    1. `exists_unique_of_strongMono` : er F sterkt monoton,
          ⟪F x − F y, x − y⟫ ≥ c‖x − y‖²,
       og L-Lipschitz, har F x = b nøyaktig én løsning for hver b.
       Bevis: T x = x − t(F x − b) med t = c/L² er en kontraksjon,
          ‖T x − T y‖² ≤ (1 − c²/L²)‖x − y‖²,
       og Banachs fikspunktteorem gir resten.

    2. `SCM.exists_unique_of_residual` : for en kausal modell over endelig
       mange reelle variabler gir sterk monotonitet og Lipschitz-kontinuitet
       av residualen, i en vektet norm, nøyaktig én løsning.

    3. Markedet: residualen er sterkt monoton med c = 1 i vektene (e·b, 1) for
       ALLE b, e > 0 (`Market.exists_unique_of_browderMinty`). Kontraksjon
       klarte bare b < e.
-/
import CausalPhys.Existence
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option linter.unusedSectionVars false

open RealInnerProductSpace

namespace CausalPhys

/-! ## 1. Abstrakt: Browder–Minty for sterkt monotone Lipschitz-operatorer -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem contraction_step (F : E → E) (b : E) {c L : ℝ} (hc : 0 < c) (hL : 0 < L)
    (hmono : ∀ x y, c * ‖x - y‖ ^ 2 ≤ ⟪F x - F y, x - y⟫)
    (hlip : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) (x y : E) :
    ‖(x - (c / L ^ 2) • (F x - b)) - (y - (c / L ^ 2) • (F y - b))‖ ^ 2
      ≤ (1 - c ^ 2 / L ^ 2) * ‖x - y‖ ^ 2 := by
  set t := c / L ^ 2 with ht
  have hrw : (x - t • (F x - b)) - (y - t • (F y - b)) = (x - y) - t • (F x - F y) := by
    rw [smul_sub, smul_sub, smul_sub]; abel
  rw [hrw, norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < t)]
  have h1 := hmono x y
  rw [real_inner_comm] at h1
  have h2 : ‖F x - F y‖ ^ 2 ≤ L ^ 2 * ‖x - y‖ ^ 2 := by
    have := hlip x y
    have h0 := norm_nonneg (F x - F y)
    calc ‖F x - F y‖ ^ 2 ≤ (L * ‖x - y‖) ^ 2 := pow_le_pow_left₀ h0 this 2
      _ = L ^ 2 * ‖x - y‖ ^ 2 := by ring
  have htpos : 0 < t := by positivity
  have hL2 : 0 < L ^ 2 := by positivity
  have key : 1 - c ^ 2 / L ^ 2 = 1 - 2 * t * c + t ^ 2 * L ^ 2 := by
    rw [ht]; field_simp; ring
  rw [key]
  nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 2 * t),
    mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ t ^ 2)]

/-- Browder–Minty, sterkt monoton versjon: F x = b har nøyaktig én løsning. -/
theorem exists_unique_of_strongMono (F : E → E) {c L : ℝ} (hc : 0 < c) (hcL : c ≤ L)
    (hmono : ∀ x y, c * ‖x - y‖ ^ 2 ≤ ⟪F x - F y, x - y⟫)
    (hlip : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) (b : E) : ∃! x, F x = b := by
  have hL : 0 < L := lt_of_lt_of_le hc hcL
  set t := c / L ^ 2 with ht
  set a := c ^ 2 / L ^ 2 with ha
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 := by
    rw [ha, div_le_one (by positivity)]
    exact pow_le_pow_left₀ hc.le hcL 2
  set K := 1 - a / 2 with hK
  have hK0 : 0 ≤ K := by linarith
  have hK1 : K < 1 := by linarith
  let T : E → E := fun x => x - t • (F x - b)
  have hlipT : ∀ x y, dist (T x) (T y) ≤ K * dist x y := by
    intro x y
    rw [dist_eq_norm, dist_eq_norm]
    have h := contraction_step F b hc hL hmono hlip x y
    have hsq : ‖T x - T y‖ ^ 2 ≤ (K * ‖x - y‖) ^ 2 := by
      calc ‖T x - T y‖ ^ 2 ≤ (1 - a) * ‖x - y‖ ^ 2 := h
        _ ≤ K ^ 2 * ‖x - y‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [hK]; nlinarith [sq_nonneg a]
        _ = (K * ‖x - y‖) ^ 2 := by ring
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hK0 (norm_nonneg _)) two_ne_zero).1 hsq
  set K' : NNReal := ⟨K, hK0⟩
  have hcon : ContractingWith K' T := ⟨by exact_mod_cast hK1, LipschitzWith.of_dist_le_mul hlipT⟩
  have htpos : 0 < t := by positivity
  have fixed_iff : ∀ x, T x = x ↔ F x = b := by
    intro x
    constructor
    · intro h
      have : t • (F x - b) = 0 := by
        have h' : x - t • (F x - b) = x := h
        have := congrArg (fun z => x - z) h'
        simpa using this
      rcases smul_eq_zero.1 this with h0 | h0
      · exact absurd h0 htpos.ne'
      · exact sub_eq_zero.1 h0
    · intro h
      show x - t • (F x - b) = x
      rw [h, sub_self, smul_zero, sub_zero]
  refine ⟨ContractingWith.fixedPoint T hcon, (fixed_iff _).1 hcon.fixedPoint_isFixedPt, ?_⟩
  intro y hy
  exact hcon.fixedPoint_unique ((fixed_iff y).2 hy)

end Abstract

/-! ## 2. Kausale modeller: vektet residual -/

namespace SCM

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Residualen: eksogene v ↦ s v − u v; endogene v ↦ s v − f_v(s med eksogene satt til u). -/
noncomputable def resid' (M : SCM V ℝ) (u s : V → ℝ) (v : V) : ℝ :=
  match M.mech v with
  | none => s v - u v
  | some m => s v - m.f (fixExo M u s)

theorem solves_iff_resid_zero (M : SCM V ℝ) (u s : V → ℝ) :
    M.Solves u s ↔ resid' M u s = 0 := by
  constructor
  · intro h
    have hfix : fixExo M u s = s := by
      funext w
      have hw := h w
      unfold fixExo
      cases hm : M.mech w with
      | none => simp only [hm] at hw ⊢; exact hw.symm
      | some _ => rfl
    funext v
    have hv := h v
    unfold resid'
    cases hm : M.mech v with
    | none => simp only [hm] at hv ⊢; simp [hv]
    | some m => simp only [hm, hfix] at hv ⊢; simp [← hv]
  · intro h
    have hexo : ∀ w, M.mech w = none → s w = u w := by
      intro w hw
      have := congrFun h w
      unfold resid' at this
      simp only [hw, Pi.zero_apply] at this
      linarith
    have hfix : fixExo M u s = s := by
      funext w
      unfold fixExo
      cases hm : M.mech w with
      | none => exact (hexo w hm).symm
      | some _ => rfl
    intro v
    have := congrFun h v
    unfold resid' at this
    cases hm : M.mech v with
    | none => exact hexo v hm
    | some m =>
      simp only [hm, hfix, Pi.zero_apply] at this
      show s v = m.f s
      linarith

/-- Vektet kvadratnorm og vektet indreprodukt på V → ℝ. -/
def wsq (lam : V → ℝ) (s : V → ℝ) : ℝ := ∑ v, lam v * s v ^ 2
def winner (lam : V → ℝ) (s t : V → ℝ) : ℝ := ∑ v, lam v * s v * t v

/-- Skaleringen til EuclideanSpace: x_v = √λ_v · s_v. -/
noncomputable def toE (lam : V → ℝ) (s : V → ℝ) : EuclideanSpace ℝ V :=
  WithLp.toLp 2 fun v => Real.sqrt (lam v) * s v

noncomputable def ofE (lam : V → ℝ) (x : EuclideanSpace ℝ V) : V → ℝ :=
  fun v => x v / Real.sqrt (lam v)

theorem ofE_toE {lam : V → ℝ} (hl : ∀ v, 0 < lam v) (s : V → ℝ) : ofE lam (toE lam s) = s := by
  funext v
  have : 0 < Real.sqrt (lam v) := Real.sqrt_pos.2 (hl v)
  simp only [ofE, toE]
  field_simp

theorem toE_ofE {lam : V → ℝ} (hl : ∀ v, 0 < lam v) (x : EuclideanSpace ℝ V) : toE lam (ofE lam x) = x := by
  ext v
  have : 0 < Real.sqrt (lam v) := Real.sqrt_pos.2 (hl v)
  simp only [ofE, toE]
  field_simp

theorem norm_sq_toE {lam : V → ℝ} (hl : ∀ v, 0 < lam v) (s : V → ℝ) :
    ‖toE lam s‖ ^ 2 = wsq lam s := by
  rw [EuclideanSpace.real_norm_sq_eq]
  unfold wsq
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [toE]
  rw [mul_pow, Real.sq_sqrt (hl v).le]

theorem inner_toE {lam : V → ℝ} (hl : ∀ v, 0 < lam v) (s t : V → ℝ) :
    ⟪toE lam s, toE lam t⟫ = winner lam s t := by
  rw [PiLp.inner_apply]
  unfold winner
  refine Finset.sum_congr rfl fun v _ => ?_
  have h := Real.mul_self_sqrt (hl v).le
  simp [toE]
  linear_combination (s v * t v) * h

theorem toE_sub (lam : V → ℝ) (s t : V → ℝ) : toE lam s - toE lam t = toE lam (s - t) := by
  ext v; simp only [toE, PiLp.sub_apply, Pi.sub_apply]; ring

/-- Browder–Minty for kausale modeller: er residualen sterkt monoton og
    Lipschitz i en vektet norm, har modellen nøyaktig én løsning. -/
theorem exists_unique_of_residual (M : SCM V ℝ) (u : V → ℝ) (lam : V → ℝ) (hl : ∀ v, 0 < lam v)
    {c L : ℝ} (hc : 0 < c) (hcL : c ≤ L)
    (hmono : ∀ s t, c * wsq lam (s - t) ≤ winner lam (resid' M u s - resid' M u t) (s - t))
    (hlip : ∀ s t, wsq lam (resid' M u s - resid' M u t) ≤ L ^ 2 * wsq lam (s - t)) :
    ∃! s, M.Solves u s := by
  let F : EuclideanSpace ℝ V → EuclideanSpace ℝ V := fun x => toE lam (resid' M u (ofE lam x))
  have hL : 0 < L := lt_of_lt_of_le hc hcL
  have hF : ∀ s, F (toE lam s) = toE lam (resid' M u s) := by
    intro s; simp only [F, ofE_toE hl]
  have hsurj : ∀ x, ∃ s, toE lam s = x := fun x => ⟨_, toE_ofE hl x⟩
  have hFmono : ∀ x y, c * ‖x - y‖ ^ 2 ≤ ⟪F x - F y, x - y⟫ := by
    intro x y
    obtain ⟨s, rfl⟩ := hsurj x
    obtain ⟨t, rfl⟩ := hsurj y
    rw [hF, hF, toE_sub, toE_sub, norm_sq_toE hl, inner_toE hl]
    exact hmono _ _
  have hFlip : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖ := by
    intro x y
    obtain ⟨s, rfl⟩ := hsurj x
    obtain ⟨t, rfl⟩ := hsurj y
    have hsq : ‖F (toE lam s) - F (toE lam t)‖ ^ 2 ≤ (L * ‖toE lam s - toE lam t‖) ^ 2 := by
      rw [mul_pow, hF, hF, toE_sub, toE_sub, norm_sq_toE hl, norm_sq_toE hl]
      exact hlip _ _
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq
  obtain ⟨x, hx, huniq⟩ := exists_unique_of_strongMono F hc hcL hFmono hFlip 0
  have hres : ∀ s, resid' M u s = 0 ↔ F (toE lam s) = 0 := by
    intro s
    simp only [F, ofE_toE hl]
    constructor
    · intro h; rw [h]; ext v; simp [toE]
    · intro h
      funext v
      have := congrArg (fun z : EuclideanSpace ℝ V => z v) h
      simp only [toE] at this
      have hs : 0 < Real.sqrt (lam v) := Real.sqrt_pos.2 (hl v)
      simpa [hs.ne'] using this
  refine ⟨ofE lam x, ?_, ?_⟩
  · show M.Solves u (ofE lam x)
    rw [solves_iff_resid_zero, hres, toE_ofE hl]; exact hx
  · intro t ht
    rw [solves_iff_resid_zero, hres] at ht
    have := huniq _ ht
    rw [← this, ofE_toE hl]

end SCM

/-! ## 3. Markedet for alle b, e > 0 -/

namespace Market

variable (m : Market)

/-- Vektene: e·b på prisen, 1 ellers. -/
def lamM : MV → ℝ := fun | .P => m.e * m.b | _ => 1

theorem lamM_pos (v : MV) : 0 < m.lamM v := by
  have := m.hb; have := m.he
  cases v <;> simp [lamM]; positivity

/-- Residualens differanser, uttrykt ved differansene i tilstanden. -/
theorem resid_diff (u s t : MV → ℝ) :
    (SCM.resid' m.scm u s - SCM.resid' m.scm u t) .P = (s .P - t .P) - (s .Q - t .Q) / m.e ∧
    (SCM.resid' m.scm u s - SCM.resid' m.scm u t) .Q = (s .Q - t .Q) + m.b * (s .P - t .P) ∧
    (SCM.resid' m.scm u s - SCM.resid' m.scm u t) .t = s .t - t .t ∧
    (SCM.resid' m.scm u s - SCM.resid' m.scm u t) .y = s .y - t .y ∧
    (SCM.resid' m.scm u s - SCM.resid' m.scm u t) .w = s .w - t .w := by
  have he := m.he.ne'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Pi.sub_apply, SCM.resid', scm, SCM.fixExo, supplyMech, demandMech] <;>
    first | (field_simp; ring) | ring

theorem sum_MV (f : MV → ℝ) : ∑ v, f v = f .t + f .y + f .w + f .P + f .Q := by
  rw [show (Finset.univ : Finset MV) = {.t, .y, .w, .P, .Q} from rfl]
  simp [Finset.sum_insert, add_assoc]

/-- Sterk monotonitet med c = 1: det vektede indreproduktet er nøyaktig den
    vektede normen i annen. -/
theorem resid_mono (u s t : MV → ℝ) :
    1 * SCM.wsq m.lamM (s - t) ≤
      SCM.winner m.lamM (SCM.resid' m.scm u s - SCM.resid' m.scm u t) (s - t) := by
  obtain ⟨hP, hQ, ht, hy, hw⟩ := m.resid_diff u s t
  have he := m.he.ne'
  simp only [SCM.wsq, SCM.winner, sum_MV, lamM]
  rw [hP, hQ, ht, hy, hw]
  simp only [Pi.sub_apply]
  field_simp
  ring_nf
  nlinarith [sq_nonneg (s .P - t .P)]

/-- Lipschitz med L² = 2 + 2b/e. -/
theorem resid_lip (u s t : MV → ℝ) :
    SCM.wsq m.lamM (SCM.resid' m.scm u s - SCM.resid' m.scm u t)
      ≤ (Real.sqrt (2 + 2 * m.b / m.e)) ^ 2 * SCM.wsq m.lamM (s - t) := by
  have hb := m.hb
  have he := m.he
  rw [Real.sq_sqrt (by positivity)]
  obtain ⟨hP, hQ, ht, hy, hw⟩ := m.resid_diff u s t
  simp only [SCM.wsq, sum_MV, lamM]
  rw [hP, hQ, ht, hy, hw]
  simp only [Pi.sub_apply]
  set dP := s .P - t .P
  set dQ := s .Q - t .Q
  set dt := s .t - t .t
  set dy := s .y - t .y
  set dw := s .w - t .w
  have h1 : m.e * m.b * (dP - dQ / m.e) ^ 2 ≤ 2 * (m.e * m.b) * dP ^ 2 + 2 * (m.b / m.e) * dQ ^ 2 := by
    have : m.e * m.b * (dP - dQ / m.e) ^ 2 = m.e * m.b * dP ^ 2 - 2 * m.b * dP * dQ + m.b / m.e * dQ ^ 2 := by
      field_simp; ring
    have hsq : m.b / m.e * (m.e * dP + dQ) ^ 2
        = m.e * m.b * dP ^ 2 + 2 * m.b * dP * dQ + m.b / m.e * dQ ^ 2 := by
      field_simp; ring
    rw [this]
    nlinarith [mul_nonneg (div_nonneg hb.le he.le) (sq_nonneg (m.e * dP + dQ))]
  have h2 : (dQ + m.b * dP) ^ 2 ≤ 2 * dQ ^ 2 + 2 * m.b / m.e * (m.e * m.b * dP ^ 2) := by
    have : 2 * m.b / m.e * (m.e * m.b * dP ^ 2) = 2 * (m.b ^ 2 * dP ^ 2) := by field_simp
    rw [this]
    nlinarith [sq_nonneg (dQ - m.b * dP)]
  have hbe : 0 ≤ 2 * m.b / m.e := by positivity
  have h3 : 0 ≤ (1 + 2 * m.b / m.e) * (dt ^ 2 + dy ^ 2 + dw ^ 2) := by positivity
  have key : (2 + 2 * m.b / m.e) * (1 * dt ^ 2 + 1 * dy ^ 2 + 1 * dw ^ 2 + m.e * m.b * dP ^ 2 + 1 * dQ ^ 2)
      - (1 * dt ^ 2 + 1 * dy ^ 2 + 1 * dw ^ 2 + m.e * m.b * (dP - dQ / m.e) ^ 2 + 1 * (dQ + m.b * dP) ^ 2)
      = (1 + 2 * m.b / m.e) * (dt ^ 2 + dy ^ 2 + dw ^ 2)
        + (2 * (m.e * m.b) * dP ^ 2 + 2 * (m.b / m.e) * dQ ^ 2 - m.e * m.b * (dP - dQ / m.e) ^ 2)
        + (2 * dQ ^ 2 + 2 * m.b / m.e * (m.e * m.b * dP ^ 2) - (dQ + m.b * dP) ^ 2) := by ring
  rw [← sub_nonneg, key]
  linarith

/-- Eksistens og entydighet fra Browder–Minty, for alle b, e > 0. -/
theorem exists_unique_of_browderMinty (u : MV → ℝ) : ∃! s, m.scm.Solves u s := by
  have hb := m.hb
  have he := m.he
  refine SCM.exists_unique_of_residual m.scm u m.lamM m.lamM_pos one_pos ?_
    (m.resid_mono u) (m.resid_lip u)
  rw [Real.le_sqrt (by norm_num) (by positivity)]
  have : 0 ≤ 2 * m.b / m.e := by positivity
  linarith

end Market
end CausalPhys
