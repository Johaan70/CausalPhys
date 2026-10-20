/-
  CausalPhys.MintyBrowder — Minty–Browder-teoremet i endelig dimensjon.

    1. Metrisk projeksjon på en lukket konveks mengde: variasjonsulikheten
       og 1-Lipschitz-kontinuitet.
    2. Brouwer for kompakte konvekse mengder i et endeligdimensjonalt reelt
       indreproduktrom (fra Brouwer for rektangler + projeksjon).
    3. Spissvinkel-lemmaet: er ⟪F x, x⟫ ≥ 0 på sfæren ‖x‖ = R, har F et
       nullpunkt i kula.
    4. Minty–Browder: F kontinuerlig, monoton og koersiv ⇒ for hver b er
       løsningsmengden {x | F x = b} ikke-tom, lukket og konveks (Mintys
       triks). Er F strengt monoton, er løsningen entydig.
    5. Kausale modeller: kontinuerlig, koersiv og strengt monoton residual
       (i en vektet norm) ⇒ nøyaktig én løsning.
    6. Eksempel: F(x, y) = (x³ − y, y³ + x), som verken er Lipschitz, sterkt
       monoton eller har P-matrise-Jacobi i origo.

  Uendeligdimensjonale Minty–Browder (Galerkin-tilnærming og svak
  kompakthet) er IKKE formalisert.
-/
import CausalPhys.Brouwer
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

set_option linter.unusedSectionVars false

open RealInnerProductSpace Filter Topology

namespace CausalPhys
namespace MintyBrowder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## 1. Projeksjon på en lukket konveks mengde -/

section Proj

variable {K : Set E} (hne : K.Nonempty) (hc : IsComplete K) (hconv : Convex ℝ K)

noncomputable def proj (u : E) : E :=
  Classical.choose (exists_norm_eq_iInf_of_complete_convex hne hc hconv u)

theorem proj_mem (u : E) : proj hne hc hconv u ∈ K :=
  (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex hne hc hconv u)).1

theorem proj_var (u : E) : ∀ w ∈ K, ⟪u - proj hne hc hconv u, w - proj hne hc hconv u⟫ ≤ 0 :=
  (norm_eq_iInf_iff_real_inner_le_zero hconv (proj_mem hne hc hconv u)).1
    (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex hne hc hconv u)).2

theorem proj_self {u : E} (hu : u ∈ K) : proj hne hc hconv u = u := by
  have h := proj_var hne hc hconv u u hu
  rw [real_inner_self_eq_norm_sq] at h
  have : ‖u - proj hne hc hconv u‖ = 0 := by nlinarith [norm_nonneg (u - proj hne hc hconv u)]
  exact (sub_eq_zero.1 (norm_eq_zero.1 this)).symm

theorem proj_lip (x y : E) : ‖proj hne hc hconv x - proj hne hc hconv y‖ ≤ ‖x - y‖ := by
  set px := proj hne hc hconv x
  set py := proj hne hc hconv y
  have h1 := proj_var hne hc hconv x py (proj_mem hne hc hconv y)
  have h2 := proj_var hne hc hconv y px (proj_mem hne hc hconv x)
  have e1 : ⟪x - px, py - px⟫ = -⟪x - px, px - py⟫ := by rw [← inner_neg_right, neg_sub]
  have e2 : ⟪x - y, px - py⟫ = ⟪x - px, px - py⟫ - ⟪y - py, px - py⟫ + ⟪px - py, px - py⟫ := by
    rw [← inner_sub_left, ← inner_add_left]; congr 1; abel
  rw [real_inner_self_eq_norm_sq] at e2
  have h3 := real_inner_le_norm (x - y) (px - py)
  have hd := norm_nonneg (px - py)
  have hxy := norm_nonneg (x - y)
  by_contra hlt
  push Not at hlt
  nlinarith

theorem proj_continuous : Continuous (proj hne hc hconv) := by
  refine (LipschitzWith.of_dist_le_mul fun x y => ?_).continuous (K := 1)
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
  exact proj_lip hne hc hconv x y

end Proj

/-! ## 2. Brouwer for kompakte konvekse mengder -/

/-- **Brouwer** for en kompakt, konveks, ikke-tom mengde i et endeligdimensjonalt
    reelt indreproduktrom. -/
theorem brouwer_convex {K : Set E} (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (f : E → E) (hf : ContinuousOn f K) (hmap : Set.MapsTo f K K) : ∃ x ∈ K, f x = x := by
  set d := Module.finrank ℝ E
  let φ : E ≃L[ℝ] (Fin d → ℝ) := (Module.finBasis ℝ E).equivFun.toContinuousLinearEquiv
  have hc : IsComplete K := hK.isComplete
  set P := proj hne hc hconv with hPdef
  have hPc : Continuous P := proj_continuous hne hc hconv
  have hPK : ∀ u, P u ∈ K := proj_mem hne hc hconv
  have hφK : IsCompact (φ '' K) := hK.image φ.continuous
  obtain ⟨R, hR⟩ := hφK.isBounded.subset_closedBall 0
  let a : Fin d → ℝ := fun _ => -|R|
  let b : Fin d → ℝ := fun _ => |R|
  have hab : a ≤ b := fun _ => by simp only [a, b]; linarith [abs_nonneg R]
  have hbox : ∀ x ∈ K, φ x ∈ Set.Icc a b := by
    intro x hx
    have h1 := hR ⟨x, hx, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have := abs_le.1 ((GN.abs_le_norm (φ x) i).trans (h1.trans (le_abs_self R)))
      simp only [a]; linarith
    · have := abs_le.1 ((GN.abs_le_norm (φ x) i).trans (h1.trans (le_abs_self R)))
      simp only [b]; linarith
  let g : (Fin d → ℝ) → (Fin d → ℝ) := fun t => φ (f (P (φ.symm t)))
  have hgc : ContinuousOn g (Set.Icc a b) :=
    (φ.continuous.comp (hf.comp_continuous (hPc.comp φ.symm.continuous) fun t => hPK _)).continuousOn
  have hgmap : Set.MapsTo g (Set.Icc a b) (Set.Icc a b) := fun t _ => hbox _ (hmap (hPK _))
  obtain ⟨t, -, ht⟩ := Brouwer.brouwer_box hab g hgc hgmap
  set x := φ.symm t with hxdef
  have hx : f (P x) = x := by
    apply φ.injective
    rw [hxdef, ContinuousLinearEquiv.apply_symm_apply]
    exact ht
  have hxK : x ∈ K := hx ▸ hmap (hPK _)
  refine ⟨x, hxK, ?_⟩
  have := proj_self hne hc hconv hxK
  rw [← hPdef] at this
  rw [this] at hx
  exact hx

/-! ## 3. Spissvinkel-lemmaet -/

theorem exists_zero_of_acute (F : E → E) {R : ℝ} (hR : 0 < R)
    (hF : ContinuousOn F (Metric.closedBall 0 R)) (hacute : ∀ x, ‖x‖ = R → 0 ≤ ⟪F x, x⟫) :
    ∃ x, ‖x‖ ≤ R ∧ F x = 0 := by
  by_contra hno
  push Not at hno
  set B := Metric.closedBall (0 : E) R
  have hFne : ∀ x ∈ B, ‖F x‖ ≠ 0 := fun x hx =>
    norm_ne_zero_iff.2 (hno x (mem_closedBall_zero_iff.1 hx))
  let g : E → E := fun x => (-R / ‖F x‖) • F x
  have hgnorm : ∀ x ∈ B, ‖g x‖ = R := by
    intro x hx
    simp only [g, norm_smul, Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos hR, abs_norm]
    exact div_mul_cancel₀ _ (hFne x hx)
  have hgc : ContinuousOn g B :=
    (continuousOn_const.div hF.norm hFne).smul hF
  have hgmap : Set.MapsTo g B B := fun x hx => by
    rw [mem_closedBall_zero_iff, hgnorm x hx]
  obtain ⟨x, hxB, hx⟩ := brouwer_convex (isCompact_closedBall 0 R) (convex_closedBall 0 R)
    ⟨0, Metric.mem_closedBall_self hR.le⟩ g hgc hgmap
  have hn : ‖x‖ = R := by rw [← hx]; exact hgnorm x hxB
  have h := hacute x hn
  have heq : ⟪F x, x⟫ = -R * ‖F x‖ := by
    have hxg : x = (-R / ‖F x‖) • F x := hx.symm
    have : ⟪F x, x⟫ = ⟪F x, (-R / ‖F x‖) • F x⟫ := congrArg _ hxg
    rw [this, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp [hFne x hxB]
  have hpos : 0 < ‖F x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm (hFne x hxB))
  rw [heq] at h
  nlinarith

/-! ## 4. Minty–Browder -/

/-- Koersivitet: ⟪F x, x⟫ vokser raskere enn enhver M‖x‖. -/
def Coercive (F : E → E) : Prop :=
  ∀ M : ℝ, ∃ R > 0, ∀ x, R ≤ ‖x‖ → M * ‖x‖ ≤ ⟪F x, x⟫

/-- Eksistens: kontinuerlig og koersiv ⇒ surjektiv (Brouwer). -/
theorem surjective_of_coercive (F : E → E) (hF : Continuous F) (hcoer : Coercive F) :
    Function.Surjective F := by
  intro b
  obtain ⟨R, hR, h⟩ := hcoer ‖b‖
  obtain ⟨x, -, hx⟩ := exists_zero_of_acute (fun x => F x - b) hR
    (hF.sub continuous_const).continuousOn (fun x hx => by
      have h1 := h x hx.ge
      have h2 := real_inner_le_norm b x
      rw [inner_sub_left]
      linarith)
  exact ⟨x, sub_eq_zero.1 hx⟩

/-- Mintys lemma: for monoton, kontinuerlig F er F x = b ekvivalent med en
    familie lineære ulikheter i x. -/
theorem minty_iff (F : E → E) (hF : Continuous F) (hmono : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    (b x : E) : F x = b ↔ ∀ y, 0 ≤ ⟪F y - b, y - x⟫ := by
  constructor
  · intro h y; rw [← h]; exact hmono y x
  · intro h
    have hw : ∀ w, 0 ≤ ⟪F x - b, w⟫ := by
      intro w
      have hcont : Continuous (fun t : ℝ => ⟪F (x + t • w) - b, w⟫) := by fun_prop
      have hlim : Tendsto (fun t : ℝ => ⟪F (x + t • w) - b, w⟫) (𝓝[>] 0) (𝓝 ⟪F x - b, w⟫) := by
        have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
        simpa using this
      apply ge_of_tendsto hlim
      filter_upwards [self_mem_nhdsWithin] with t ht
      have h1 := h (x + t • w)
      rw [add_sub_cancel_left, real_inner_smul_right] at h1
      exact nonneg_of_mul_nonneg_right (by linarith) (Set.mem_Ioi.1 ht) |> fun h => by
        nlinarith [Set.mem_Ioi.1 ht]
    have := hw (-(F x - b))
    rw [inner_neg_right, real_inner_self_eq_norm_sq] at this
    have : ‖F x - b‖ = 0 := by nlinarith [norm_nonneg (F x - b)]
    exact sub_eq_zero.1 (norm_eq_zero.1 this)

/-- **Minty–Browder** (endelig dimensjon). For kontinuerlig, monoton og koersiv
    F er løsningsmengden for F x = b ikke-tom, lukket og konveks. -/
theorem minty_browder (F : E → E) (hF : Continuous F) (hmono : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    (hcoer : Coercive F) (b : E) :
    {x | F x = b}.Nonempty ∧ IsClosed {x | F x = b} ∧ Convex ℝ {x | F x = b} := by
  refine ⟨surjective_of_coercive F hF hcoer b, isClosed_eq hF continuous_const, ?_⟩
  have hset : {x | F x = b} = {x | ∀ y, 0 ≤ ⟪F y - b, y - x⟫} := by
    ext x; exact minty_iff F hF hmono b x
  rw [hset]
  intro x₁ h₁ x₂ h₂ s t hs ht hst y
  have : y - (s • x₁ + t • x₂) = s • (y - x₁) + t • (y - x₂) := by
    calc y - (s • x₁ + t • x₂) = (s + t) • y - (s • x₁ + t • x₂) := by rw [hst, one_smul]
      _ = s • (y - x₁) + t • (y - x₂) := by rw [add_smul, smul_sub, smul_sub]; abel
  rw [this, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  have := h₁ y; have := h₂ y
  positivity

/-- Strengt monoton: nøyaktig én løsning. -/
theorem minty_browder_unique (F : E → E) (hF : Continuous F)
    (hmono : ∀ x y, x ≠ y → 0 < ⟪F x - F y, x - y⟫) (hcoer : Coercive F) (b : E) :
    ∃! x, F x = b := by
  obtain ⟨x, hx⟩ := surjective_of_coercive F hF hcoer b
  refine ⟨x, hx, fun y hy => ?_⟩
  by_contra hne
  have := hmono y x hne
  rw [hy, hx, sub_self, inner_zero_left] at this
  exact lt_irrefl _ this

end MintyBrowder

/-! ## 5. Kausale modeller -/

namespace SCM

variable {V : Type} [Fintype V] [DecidableEq V]

theorem toE_continuous (lam : V → ℝ) : Continuous (toE lam) := by
  unfold toE; fun_prop

theorem ofE_continuous (lam : V → ℝ) : Continuous (ofE lam) := by
  unfold ofE; fun_prop

theorem norm_toE {lam : V → ℝ} (hl : ∀ v, 0 < lam v) (s : V → ℝ) :
    ‖toE lam s‖ = Real.sqrt (wsq lam s) := by
  rw [← norm_sq_toE hl, Real.sqrt_sq (norm_nonneg _)]

/-- Minty–Browder for kausale modeller: er residualen kontinuerlig, strengt
    monoton og koersiv i en vektet norm, har modellen nøyaktig én løsning. -/
theorem exists_unique_of_minty (M : SCM V ℝ) (u lam : V → ℝ) (hl : ∀ v, 0 < lam v)
    (hcont : Continuous (resid' M u))
    (hmono : ∀ s t, s ≠ t → 0 < winner lam (resid' M u s - resid' M u t) (s - t))
    (hcoer : ∀ C : ℝ, ∃ R > 0, ∀ s, R ≤ Real.sqrt (wsq lam s) →
      C * Real.sqrt (wsq lam s) ≤ winner lam (resid' M u s) s) :
    ∃! s, M.Solves u s := by
  let F : EuclideanSpace ℝ V → EuclideanSpace ℝ V := fun x => toE lam (resid' M u (ofE lam x))
  have hF : ∀ s, F (toE lam s) = toE lam (resid' M u s) := by
    intro s; simp only [F, ofE_toE hl]
  have hsurj : ∀ x, ∃ s, toE lam s = x := fun x => ⟨_, toE_ofE hl x⟩
  have hFc : Continuous F := (toE_continuous lam).comp (hcont.comp (ofE_continuous lam))
  have hFmono : ∀ x y, x ≠ y → 0 < ⟪F x - F y, x - y⟫ := by
    intro x y hxy
    obtain ⟨s, rfl⟩ := hsurj x
    obtain ⟨t, rfl⟩ := hsurj y
    have hst : s ≠ t := fun h => hxy (by rw [h])
    rw [hF, hF, toE_sub, toE_sub, inner_toE hl]
    exact hmono s t hst
  have hFcoer : MintyBrowder.Coercive F := by
    intro C
    obtain ⟨R, hR, h⟩ := hcoer C
    refine ⟨R, hR, fun x hx => ?_⟩
    obtain ⟨s, rfl⟩ := hsurj x
    rw [hF, inner_toE hl, norm_toE hl] at *
    exact h s hx
  obtain ⟨x, hx, huniq⟩ := MintyBrowder.minty_browder_unique F hFc hFmono hFcoer 0
  have hres : ∀ s, resid' M u s = 0 ↔ F (toE lam s) = 0 := by
    intro s
    rw [hF]
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

/-! ## 6. Eksempel utenfor de tidligere kriteriene -/

namespace CubicExample

open MintyBrowder

/-- F(x, y) = (x³ − y, y³ + x). -/
noncomputable def F (z : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![z 0 ^ 3 - z 1, z 1 ^ 3 + z 0]

theorem inner2 (z w : EuclideanSpace ℝ (Fin 2)) : ⟪z, w⟫ = z 0 * w 0 + z 1 * w 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

theorem norm2 (z : EuclideanSpace ℝ (Fin 2)) : ‖z‖ ^ 2 = z 0 ^ 2 + z 1 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

theorem F_apply (z : EuclideanSpace ℝ (Fin 2)) : F z 0 = z 0 ^ 3 - z 1 ∧ F z 1 = z 1 ^ 3 + z 0 := by
  simp [F]

theorem F_continuous : Continuous F := by
  unfold F
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  fin_cases i <;> simp <;> fun_prop

theorem cube_mono (a b : ℝ) : 0 ≤ (a ^ 3 - b ^ 3) * (a - b) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), mul_self_nonneg (a - b),
    mul_nonneg (sq_nonneg (a - b)) (add_nonneg (sq_nonneg a) (sq_nonneg b))]

theorem cube_mono_strict (a b : ℝ) (h : a ≠ b) : 0 < (a ^ 3 - b ^ 3) * (a - b) := by
  have h1 : 0 < (a - b) ^ 2 := by positivity
  have : (a ^ 3 - b ^ 3) * (a - b) = (a - b) ^ 2 * ((a + b / 2) ^ 2 + 3 * b ^ 2 / 4) := by ring
  rw [this]
  have h2 : 0 < (a + b / 2) ^ 2 + 3 * b ^ 2 / 4 := by
    by_contra hle
    push Not at hle
    have hb : b = 0 := by nlinarith [sq_nonneg (a + b / 2), sq_nonneg b]
    have ha : a = 0 := by subst hb; nlinarith [sq_nonneg a]
    exact h (by rw [ha, hb])
  positivity

theorem F_mono (z w : EuclideanSpace ℝ (Fin 2)) (h : z ≠ w) : 0 < ⟪F z - F w, z - w⟫ := by
  rw [inner2]
  simp only [PiLp.sub_apply, (F_apply z).1, (F_apply z).2, (F_apply w).1, (F_apply w).2]
  have hz : z 0 ≠ w 0 ∨ z 1 ≠ w 1 := by
    by_contra hc
    push Not at hc
    apply h
    ext i; fin_cases i
    · exact hc.1
    · exact hc.2
  have key : (z 0 ^ 3 - z 1 - (w 0 ^ 3 - w 1)) * (z 0 - w 0) + (z 1 ^ 3 + z 0 - (w 1 ^ 3 + w 0)) * (z 1 - w 1)
      = (z 0 ^ 3 - w 0 ^ 3) * (z 0 - w 0) + (z 1 ^ 3 - w 1 ^ 3) * (z 1 - w 1) := by ring
  rw [key]
  rcases hz with h0 | h1
  · have := cube_mono_strict _ _ h0; have := cube_mono (z 1) (w 1); linarith
  · have := cube_mono (z 0) (w 0); have := cube_mono_strict _ _ h1; linarith

theorem F_coercive : Coercive F := by
  intro M
  refine ⟨2 * |M| + 1, by positivity, fun z hz => ?_⟩
  rw [inner2, (F_apply z).1, (F_apply z).2]
  have hn := norm2 z
  set r := ‖z‖
  have hr1 : 1 ≤ r := by linarith [abs_nonneg M]
  have h4 : r ^ 4 ≤ 2 * (z 0 ^ 4 + z 1 ^ 4) := by
    have : r ^ 4 = (z 0 ^ 2 + z 1 ^ 2) ^ 2 := by rw [← hn]; ring
    rw [this]; nlinarith [sq_nonneg (z 0 ^ 2 - z 1 ^ 2)]
  have hval : (z 0 ^ 3 - z 1) * z 0 + (z 1 ^ 3 + z 0) * z 1 = z 0 ^ 4 + z 1 ^ 4 := by ring
  rw [hval]
  have hr3 : 2 * |M| + 1 ≤ r ^ 3 := by
    calc 2 * |M| + 1 ≤ r := hz
      _ = r * 1 * 1 := by ring
      _ ≤ r * r * r := by gcongr
      _ = r ^ 3 := by ring
  have hM : M * r ≤ |M| * r := mul_le_mul_of_nonneg_right (le_abs_self M) (by linarith)
  nlinarith [abs_nonneg M]

/-- F(x, y) = b har nøyaktig én løsning for hver b. -/
theorem exists_unique (b : EuclideanSpace ℝ (Fin 2)) : ∃! z, F z = b :=
  minty_browder_unique F F_continuous F_mono F_coercive b

end CubicExample
end CausalPhys
