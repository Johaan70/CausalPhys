/-
  CausalPhys.LpMeasure — Lᵖ(μ) over et vilkårlig målrom er refleksivt.

  Ruten går via uniform konveksitet, ikke via Radon–Nikodym:

    1. Clarksons ulikhet for p ≥ 2:
         ‖f + g‖ᵖ + ‖f − g‖ᵖ ≤ 2^{p−1}(‖f‖ᵖ + ‖g‖ᵖ),
       først punktvis for reelle tall, så integrert.
    2. Dermed er Lᵖ(μ) uniformt konvekst for 2 ≤ p < ∞, og refleksivt ved
       Milman–Pettis (CausalPhys.Reflexivity).
    3. For 1 < p < 2: Hölder-paringen gir en isometrisk innbygging
       Lᵖ → (L^q)* med q > 2. Normen oppnås med testfunksjonen
       sign(f)|f|^{p−1}. Siden L^q er refleksivt, er (L^q)* det også, og et
       lukket isometrisk underrom av et refleksivt rom er refleksivt.

  Ingen σ-endelighet eller andre antakelser om målet trengs.
-/
import CausalPhysAnalysis.Reflexivity
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.MeanInequalitiesPow

set_option linter.unusedSectionVars false

open MeasureTheory
open scoped ENNReal

namespace CausalPhys
namespace LpMeasure

/-! ## 1. Clarksons ulikhet punktvis -/

theorem abs_rpow_eq (x : ℝ) {r : ℝ} : |x| ^ r = (x ^ 2) ^ (r / 2) := by
  rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg x)]
  congr 1; push_cast; ring

theorem clarkson_pt {r : ℝ} (hr : 2 ≤ r) (a b : ℝ) :
    |a + b| ^ r + |a - b| ^ r ≤ 2 ^ (r - 1) * (|a| ^ r + |b| ^ r) := by
  have hk : 1 ≤ r / 2 := by linarith
  rw [abs_rpow_eq (a + b), abs_rpow_eq (a - b), abs_rpow_eq a, abs_rpow_eq b]
  have h1 := Real.add_rpow_le_rpow_add (sq_nonneg (a + b)) (sq_nonneg (a - b)) hk
  have hconv := (convexOn_rpow hk).2 (Set.mem_Ici.2 (sq_nonneg a)) (Set.mem_Ici.2 (sq_nonneg b))
    (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hconv
  have e2 : ((a + b) ^ 2 + (a - b) ^ 2) ^ (r / 2)
      = 4 ^ (r / 2) * (1 / 2 * a ^ 2 + 1 / 2 * b ^ 2) ^ (r / 2) := by
    rw [← Real.mul_rpow (by norm_num) (by positivity)]; congr 1; ring
  have e3 : (4:ℝ) ^ (r / 2) = 2 ^ r := by
    rw [show (4:ℝ) = 2 ^ (2:ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; congr 1; ring
  have e4 : (2:ℝ) ^ (r - 1) = 2 ^ r / 2 := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_one]
  have h2r : (0:ℝ) < 2 ^ r := by positivity
  calc ((a + b) ^ 2) ^ (r / 2) + ((a - b) ^ 2) ^ (r / 2)
      ≤ ((a + b) ^ 2 + (a - b) ^ 2) ^ (r / 2) := h1
    _ = 2 ^ r * (1 / 2 * a ^ 2 + 1 / 2 * b ^ 2) ^ (r / 2) := by rw [e2, e3]
    _ ≤ 2 ^ r * (1 / 2 * (a ^ 2) ^ (r / 2) + 1 / 2 * (b ^ 2) ^ (r / 2)) :=
        mul_le_mul_of_nonneg_left hconv h2r.le
    _ = 2 ^ (r - 1) * ((a ^ 2) ^ (r / 2) + (b ^ 2) ^ (r / 2)) := by rw [e4]; ring

/-! ## 2. Clarkson i Lᵖ(μ) -/

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem p_ne_zero : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'

theorem integrable_rpow (hp : p ≠ ∞) (h : Lp ℝ p μ) :
    Integrable (fun x => |h x| ^ p.toReal) μ := by
  simpa [Real.norm_eq_abs] using (Lp.memLp h).integrable_norm_rpow p_ne_zero hp

theorem norm_rpow (hp : p ≠ ∞) (h : Lp ℝ p μ) :
    ‖h‖ ^ p.toReal = ∫ x, |h x| ^ p.toReal ∂μ := by
  have hr : 0 < p.toReal := ENNReal.toReal_pos p_ne_zero hp
  rw [Lp.norm_def, toReal_eLpNorm,
    lpNorm_eq_integral_norm_rpow_toReal p_ne_zero hp (Lp.aestronglyMeasurable h)]
  simp only [Real.norm_eq_abs]
  rw [← Real.rpow_mul (integral_nonneg fun x => by positivity), inv_mul_cancel₀ hr.ne',
    Real.rpow_one]

/-- **Clarksons ulikhet** i Lᵖ(μ) for 2 ≤ p < ∞. -/
theorem clarkson (hp : p ≠ ∞) (hp2 : 2 ≤ p.toReal) (f g : Lp ℝ p μ) :
    ‖f + g‖ ^ p.toReal + ‖f - g‖ ^ p.toReal
      ≤ 2 ^ (p.toReal - 1) * (‖f‖ ^ p.toReal + ‖g‖ ^ p.toReal) := by
  set r := p.toReal
  rw [norm_rpow hp, norm_rpow hp, norm_rpow hp, norm_rpow hp]
  have hadd : ∫ x, |(f + g) x| ^ r ∂μ = ∫ x, |f x + g x| ^ r ∂μ :=
    integral_congr_ae ((Lp.coeFn_add f g).mono fun x hx => by dsimp only; rw [hx, Pi.add_apply])
  have hsub : ∫ x, |(f - g) x| ^ r ∂μ = ∫ x, |f x - g x| ^ r ∂μ :=
    integral_congr_ae ((Lp.coeFn_sub f g).mono fun x hx => by dsimp only; rw [hx, Pi.sub_apply])
  have iadd : Integrable (fun x => |f x + g x| ^ r) μ :=
    (integrable_rpow hp (f + g)).congr ((Lp.coeFn_add f g).mono fun x hx => by dsimp only; rw [hx, Pi.add_apply])
  have isub : Integrable (fun x => |f x - g x| ^ r) μ :=
    (integrable_rpow hp (f - g)).congr ((Lp.coeFn_sub f g).mono fun x hx => by dsimp only; rw [hx, Pi.sub_apply])
  rw [hadd, hsub, ← integral_add iadd isub, ← integral_add (integrable_rpow hp f)
    (integrable_rpow hp g), ← integral_const_mul]
  exact integral_mono (iadd.add isub) (((integrable_rpow hp f).add (integrable_rpow hp g)).const_mul _)
    fun x => clarkson_pt hp2 (f x) (g x)

/-- **Lᵖ(μ) er uniformt konvekst** for 2 ≤ p < ∞. -/
theorem uniformConvex (hp : p ≠ ∞) (hp2 : 2 ≤ p.toReal) : UniformConvexSpace (Lp ℝ p μ) := by
  set r := p.toReal with hrdef
  have hr : 0 < r := by linarith
  refine ⟨fun ε hε => ?_⟩
  set ε' := min ε 2
  have hε' : 0 < ε' := lt_min hε (by norm_num)
  set a := (ε' / 2) ^ r with ha
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 := by
    rw [ha]
    exact Real.rpow_le_one (by positivity) (by
      have := min_le_right ε 2; linarith) hr.le
  refine ⟨2 - 2 * (1 - a) ^ (1 / r), ?_, fun x hx y hy hxy => ?_⟩
  · have : (1 - a) ^ (1 / r) < 1 := by
      rcases (sub_nonneg.2 ha1).lt_or_eq with h | h
      · exact Real.rpow_lt_one h.le (by linarith) (by positivity)
      · rw [← h, Real.zero_rpow (by positivity)]; norm_num
    linarith
  · have hc := clarkson hp hp2 x y
    rw [hx, hy, Real.one_rpow] at hc
    have hε'xy : ε' ≤ ‖x - y‖ := (min_le_left _ _).trans hxy
    have h1 : ε' ^ r ≤ ‖x - y‖ ^ r := Real.rpow_le_rpow hε'.le hε'xy hr.le
    have h2r : (2:ℝ) ^ (r - 1) * (1 + 1) = 2 ^ r := by
      rw [Real.rpow_sub (by norm_num), Real.rpow_one]; ring
    have hε'r : ε' ^ r = 2 ^ r * a := by
      rw [ha, Real.div_rpow hε'.le (by norm_num)]; field_simp
    have h3 : ‖x + y‖ ^ r ≤ 2 ^ r * (1 - a) := by nlinarith
    have h4 : ‖x + y‖ ≤ (2 ^ r * (1 - a)) ^ (1 / r) := by
      have := Real.rpow_le_rpow (by positivity) h3 (by positivity : (0:ℝ) ≤ 1 / r)
      rwa [← Real.rpow_mul (norm_nonneg _), mul_one_div_cancel hr.ne', Real.rpow_one] at this
    rw [Real.mul_rpow (by positivity) (by linarith), ← Real.rpow_mul (by norm_num),
      mul_one_div_cancel hr.ne', Real.rpow_one] at h4
    linarith

/-- **Lᵖ(μ) er refleksivt** for 2 ≤ p < ∞ (Clarkson + Milman–Pettis). -/
theorem reflexive_of_two_le (hp : p ≠ ∞) (hp2 : 2 ≤ p.toReal) :
    Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ (Lp ℝ p μ)) := by
  have := uniformConvex (μ := μ) hp hp2
  exact Reflexivity.milman_pettis


/-! ## 3. Hölder-innbyggingen Lᵖ → (L^q)* er en isometri -/

section Embedding

variable {q : ℝ≥0∞} [Fact (1 ≤ q)] [hpqE : p.HolderConjugate q]

theorem norm_eq_rpow_integral (hp : p ≠ ∞) (h : Lp ℝ p μ) :
    ‖h‖ = (∫ x, |h x| ^ p.toReal ∂μ) ^ (1 / p.toReal) := by
  have hr : 0 < p.toReal := ENNReal.toReal_pos p_ne_zero hp
  rw [← norm_rpow hp, ← Real.rpow_mul (norm_nonneg _), mul_one_div_cancel hr.ne', Real.rpow_one]

/-- Hölder: |∫ f g| ≤ ‖f‖ ‖g‖. -/
theorem abs_integral_mul_le (hp : p ≠ ∞) (hq : q ≠ ∞) (hpq : p.toReal.HolderConjugate q.toReal)
    (f : Lp ℝ p μ) (g : Lp ℝ q μ) : |∫ x, f x * g x ∂μ| ≤ ‖f‖ * ‖g‖ := by
  have hf : MemLp (fun x => |f x|) (ENNReal.ofReal p.toReal) μ := by
    rw [ENNReal.ofReal_toReal hp]; simpa [Real.norm_eq_abs] using (Lp.memLp f).norm
  have hg : MemLp (fun x => |g x|) (ENNReal.ofReal q.toReal) μ := by
    rw [ENNReal.ofReal_toReal hq]; simpa [Real.norm_eq_abs] using (Lp.memLp g).norm
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq (.of_forall fun x => abs_nonneg (f x))
    (.of_forall fun x => abs_nonneg (g x)) hf hg
  rw [← norm_eq_rpow_integral hp f, ← norm_eq_rpow_integral hq g] at h
  calc |∫ x, f x * g x ∂μ| ≤ ∫ x, |f x * g x| ∂μ := abs_integral_le_integral_abs
    _ = ∫ x, |f x| * |g x| ∂μ := by simp [abs_mul]
    _ ≤ ‖f‖ * ‖g‖ := h

/-- Paringen f ↦ (g ↦ ∫ f g). -/
noncomputable def P : Lp ℝ p μ →L[ℝ] Lp ℝ q μ →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ p q

theorem P_apply (f : Lp ℝ p μ) (g : Lp ℝ q μ) : P (μ := μ) f g = ∫ x, f x * g x ∂μ := by
  rw [P, ContinuousLinearMap.lpPairing_eq_integral]; rfl

/-- Normen til P f er nøyaktig ‖f‖: testfunksjonen f|f|^{p−2} oppnår den. -/
theorem norm_P (hp : p ≠ ∞) (hq : q ≠ ∞) (hpq : p.toReal.HolderConjugate q.toReal)
    (f : Lp ℝ p μ) : ‖P (μ := μ) (q := q) f‖ = ‖f‖ := by
  set r := p.toReal with hrdef
  set s := q.toReal with hsdef
  have hr1 : 1 < r := hpq.lt
  have hs0 : 0 < s := hpq.symm.pos
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun g => ?_
    rw [P_apply, Real.norm_eq_abs]
    exact abs_integral_mul_le hp hq hpq f g
  rcases eq_or_ne f 0 with hf0 | hf0
  · rw [hf0, norm_zero]; exact norm_nonneg _
  have hfpos : 0 < ‖f‖ := norm_pos_iff.2 hf0
  -- testfunksjonen
  let g0 : α → ℝ := fun x => f x * |f x| ^ (r - 2)
  have hg0abs : ∀ x, |g0 x| = |f x| ^ (r - 1) := by
    intro x
    simp only [g0, abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg (f x)) _)]
    rcases eq_or_ne (f x) 0 with h | h
    · rw [h, abs_zero, zero_mul, Real.zero_rpow (by linarith : r - 1 ≠ 0)]
    · have hpos : 0 < |f x| := abs_pos.2 h
      rw [← Real.rpow_one_add' hpos.le (by linarith)]
      congr 1; ring
  have hfg0 : ∀ x, f x * g0 x = |f x| ^ r := by
    intro x
    simp only [g0]
    rcases eq_or_ne (f x) 0 with h | h
    · rw [h, zero_mul, abs_zero, Real.zero_rpow (by linarith)]
    · have hpos : 0 < |f x| := abs_pos.2 h
      rw [← mul_assoc, ← sq, ← sq_abs, ← Real.rpow_natCast, ← Real.rpow_add hpos]
      congr 1; push_cast; ring
  have hmeas : AEStronglyMeasurable g0 μ := by
    have hfm := (Lp.aestronglyMeasurable f).aemeasurable
    exact (hfm.mul ((continuous_abs.measurable.comp_aemeasurable hfm).pow_const (r - 2))).aestronglyMeasurable
  have hmem0 : MemLp (fun x => ‖f x‖ ^ (ENNReal.ofReal (r - 1)).toReal) (p / ENNReal.ofReal (r - 1)) μ :=
    (Lp.memLp f).norm_rpow_div (ENNReal.ofReal (r - 1))
  have hexp : p / ENNReal.ofReal (r - 1) = q := by
    rw [← ENNReal.ofReal_toReal hp, ← ENNReal.ofReal_toReal hq,
      ← ENNReal.ofReal_div_of_pos (by linarith)]
    congr 1
    rw [← hrdef, ← hsdef, hpq.conjugate_eq]
  rw [hexp, ENNReal.toReal_ofReal (by linarith)] at hmem0
  have hmem : MemLp g0 q μ := hmem0.mono hmeas (.of_forall fun x => by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, hg0abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)])
  set G : Lp ℝ q μ := hmem.toLp g0
  have hG : (G : α → ℝ) =ᵐ[μ] g0 := MemLp.coeFn_toLp hmem
  -- P f G = ‖f‖^r
  have hPG : P (μ := μ) f G = ‖f‖ ^ r := by
    rw [P_apply, norm_rpow hp]
    exact integral_congr_ae (hG.mono fun x hx => by dsimp only; rw [hx, hfg0])
  -- ‖G‖ = ‖f‖^{r−1}
  have hGs : ‖G‖ ^ s = ‖f‖ ^ r := by
    rw [norm_rpow hq, norm_rpow hp]
    refine integral_congr_ae (hG.mono fun x hx => ?_)
    dsimp only
    rw [hx, hg0abs, ← Real.rpow_mul (abs_nonneg _)]
    congr 1
    exact hpq.sub_one_mul_conj
  have hGn : ‖G‖ = ‖f‖ ^ (r - 1) := by
    have h1 : ‖G‖ = (‖f‖ ^ r) ^ (1 / s) := by
      rw [← hGs, ← Real.rpow_mul (norm_nonneg _), mul_one_div_cancel hs0.ne', Real.rpow_one]
    rw [h1, ← Real.rpow_mul (norm_nonneg _)]
    congr 1
    have := hpq.inv_add_inv_eq_one
    field_simp
    have h3 := hpq.mul_eq_add
    nlinarith
  have hbound := (P (μ := μ) f).le_opNorm G
  rw [hPG, Real.norm_eq_abs, abs_of_nonneg (by positivity), hGn] at hbound
  have hpow : ‖f‖ ^ r = ‖f‖ * ‖f‖ ^ (r - 1) := by
    rw [← Real.rpow_one_add' (norm_nonneg _) (by linarith)]; congr 1; ring
  rw [hpow] at hbound
  have hpos : 0 < ‖f‖ ^ (r - 1) := Real.rpow_pos_of_pos hfpos _
  exact le_of_mul_le_mul_right hbound hpos

/-- Innbyggingen som lineær isometri. -/
noncomputable def embed (hp : p ≠ ∞) (hq : q ≠ ∞) (hpq : p.toReal.HolderConjugate q.toReal) :
    Lp ℝ p μ →ₗᵢ[ℝ] StrongDual ℝ (Lp ℝ q μ) where
  toLinearMap := (P (μ := μ) (q := q)).toLinearMap
  norm_map' := norm_P hp hq hpq

end Embedding

/-! ## 4. Hovedteoremet -/

/-- **Lᵖ(μ) er refleksivt for 1 < p < ∞**, over et vilkårlig målrom. -/
theorem reflexive {q : ℝ≥0∞} [Fact (1 ≤ q)] [p.HolderConjugate q] (hp : p ≠ ∞) (hq : q ≠ ∞)
    (hpq : p.toReal.HolderConjugate q.toReal) :
    Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ (Lp ℝ p μ)) := by
  by_cases hp2 : 2 ≤ p.toReal
  · exact reflexive_of_two_le hp hp2
  · push Not at hp2
    have hq2 : 2 ≤ q.toReal := by
      have h1 := hpq.inv_add_inv_eq_one
      have hr0 : 0 < p.toReal := hpq.pos
      have hs0 : 0 < q.toReal := hpq.symm.pos
      have : 1 / 2 < p.toReal⁻¹ := by
        rw [one_div]; exact inv_strictAnti₀ hr0 hp2
      have : q.toReal⁻¹ < 1 / 2 := by linarith
      by_contra h
      push Not at h
      have : 1 / 2 < q.toReal⁻¹ := by rw [one_div]; exact inv_strictAnti₀ hs0 h
      linarith
    have hqrefl := reflexive_of_two_le (μ := μ) hq hq2
    have hdual := Reflexivity.dual_reflexive hqrefl
    let e := embed (μ := μ) hp hq hpq
    have hcl : IsClosed (Set.range e) :=
      (e.isometry.isUniformInducing.isComplete_range).isClosed
    exact Reflexivity.reflexive_of_isometry e hcl hdual

/-- **Minty–Browder på Lᵖ(μ)** for 1 < p < ∞, uten refleksivitetsantakelse. -/
theorem minty_browder {q : ℝ≥0∞} [Fact (1 ≤ q)] [p.HolderConjugate q] (hp : p ≠ ∞) (hq : q ≠ ∞)
    (hpq : p.toReal.HolderConjugate q.toReal)
    (F : Lp ℝ p μ → StrongDual ℝ (Lp ℝ p μ)) (hhemi : MintyBrowderHemi.Hemicontinuous F)
    (hmono : ∀ x y, 0 ≤ (F x - F y) (x - y)) (hcoer : MintyBrowderBanach.Coercive F) :
    Function.Surjective F :=
  MintyBrowderHemi.surjective (reflexive hp hq hpq) F hhemi hmono hcoer

end LpMeasure
end CausalPhys
