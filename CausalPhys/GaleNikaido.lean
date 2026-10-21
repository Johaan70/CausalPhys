/-
  CausalPhys.GaleNikaido — Gale–Nikaido-teoremet (1965).

  En P-matrise er en kvadratisk matrise der alle prinsipale minorer er
  positive. Gale og Nikaido viste:

    Er F deriverbar på et lukket rektangel Ω ⊆ ℝⁿ, og er Jacobi-matrisen en
    P-matrise i hvert punkt, så er F injektiv på Ω.

  Bevisets gang her:
    1. Lineær algebra: P-matriser bevares av prinsipale delmatriser,
       transponering, fortegnskonjugering D·A·D og tillegg av ikke-negativ
       diagonal; en P-matrise snur ikke fortegnet til noen vektor
       (∃ i, vᵢ(Av)ᵢ > 0); og en P-matrise er semipositiv
       (∃ u ≥ 0 med Au > 0), via Hahn–Banach-separasjon (Villes alternativ).
    2. Analyse: et «ingen fortegnsreversering»-resultat for F, bevist ved
       sterk induksjon på mengden av frie koordinater, med isolasjon nær
       basispunktet (kompakthet) og et minimeringsargument (kompakthet av Ω).
    3. Injektivitet ved å velge fortegnsmønster etter hvilken vei hver
       koordinat går.

  Merk: teoremet gir ENTYDIGHET (injektivitet), ikke eksistens.
-/
import CausalPhys.BrowderMinty
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Prod

set_option linter.unusedSectionVars false

open Matrix Finset

namespace CausalPhys
namespace PMat

/-! ## 1. P-matriser -/

/-- P-matrise: alle prinsipale minorer er positive. -/
def IsP {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) : Prop :=
  ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (f : κ → ι), Function.Injective f →
    0 < (A.submatrix f f).det

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem IsP.det_pos {A : Matrix ι ι ℝ} (h : IsP A) : 0 < A.det := by
  simpa using h ι id Function.injective_id

theorem IsP.submatrix {A : Matrix ι ι ℝ} (h : IsP A) {κ : Type} [Fintype κ] [DecidableEq κ]
    (g : κ → ι) (hg : Function.Injective g) : IsP (A.submatrix g g) := by
  intro μ _ _ f hf
  rw [Matrix.submatrix_submatrix]
  exact h μ (g ∘ f) (hg.comp hf)

theorem IsP.transpose {A : Matrix ι ι ℝ} (h : IsP A) : IsP Aᵀ := by
  intro κ _ _ f hf
  rw [← Matrix.transpose_submatrix, Matrix.det_transpose]
  exact h κ f hf

/-- Fortegnskonjugering D·A·D med D = diag(σ), σᵢ = ±1. -/
def sconj (σ : ι → ℝ) (A : Matrix ι ι ℝ) : Matrix ι ι ℝ := Matrix.of fun i j => σ i * A i j * σ j

theorem IsP.sconj {A : Matrix ι ι ℝ} (h : IsP A) {σ : ι → ℝ} (hσ : ∀ i, σ i * σ i = 1) :
    IsP (PMat.sconj σ A) := by
  intro κ _ _ f hf
  have heq : (PMat.sconj σ A).submatrix f f
      = diagonal (σ ∘ f) * A.submatrix f f * diagonal (σ ∘ f) := by
    ext i j
    simp [PMat.sconj, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [heq, det_mul, det_mul, det_diagonal]
  have h1 : (∏ i, (σ ∘ f) i) * (∏ i, (σ ∘ f) i) = 1 := by
    rw [← Finset.prod_mul_distrib]; simp [hσ]
  have hd := h κ f hf
  have : (∏ i, (σ ∘ f) i) * (A.submatrix f f).det * (∏ i, (σ ∘ f) i) = (A.submatrix f f).det := by
    linear_combination (A.submatrix f f).det * h1
  rw [this]; exact hd

/-- Raden k byttet ut med enhetsvektoren: determinanten er minoren uten k. -/
theorem det_updateRow_single_eq {κ : Type} [Fintype κ] [DecidableEq κ] (N : Matrix κ κ ℝ) (k : κ) :
    (N.updateRow k (Pi.single k 1)).det
      = (N.submatrix (Subtype.val : {j // ¬ j = k} → κ) Subtype.val).det := by
  set M := N.updateRow k (Pi.single k 1)
  let e : {j // j = k} ⊕ {j // ¬ j = k} ≃ κ := Equiv.sumCompl (· = k)
  rw [← det_submatrix_equiv_self e M]
  have : Subsingleton {j // j = k} := ⟨fun a b => Subtype.ext (a.2.trans b.2.symm)⟩
  have h12 : (M.submatrix e e).toBlocks₁₂ = 0 := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    subst hi
    simp [toBlocks₁₂, M, e, hj]
  have h11 : ((M.submatrix e e).toBlocks₁₁).det = 1 := by
    rw [det_eq_elem_of_subsingleton _ ⟨k, rfl⟩]
    simp [toBlocks₁₁, M, e]
  have h22 : (M.submatrix e e).toBlocks₂₂ = N.submatrix Subtype.val Subtype.val := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp [toBlocks₂₂, M, e, updateRow_ne hi]
  rw [← Matrix.fromBlocks_toBlocks (M.submatrix e e), h12, det_fromBlocks_zero₁₂, h11, h22, one_mul]

theorem det_add_single_pos {κ : Type} [Fintype κ] [DecidableEq κ] (N : Matrix κ κ ℝ) (hN : IsP N)
    (k : κ) {t : ℝ} (ht : 0 ≤ t) : 0 < (N + diagonal (Pi.single k t)).det := by
  have hrow : N + diagonal (Pi.single k t) = N.updateRow k (N k + t • Pi.single k 1) := by
    ext i j
    by_cases hi : i = k
    · subst hi
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj, Ne.symm hj]
    · simp [diagonal_apply, hi]
  rw [hrow, det_updateRow_add, det_updateRow_smul, updateRow_eq_self, det_updateRow_single_eq]
  have h1 := hN.det_pos
  have h2 := hN _ (Subtype.val : {j // ¬ j = k} → κ) Subtype.val_injective
  nlinarith [mul_nonneg ht h2.le]

theorem IsP.add_single {κ : Type} [Fintype κ] [DecidableEq κ] {M : Matrix κ κ ℝ} (hM : IsP M)
    (a : κ) {t : ℝ} (ht : 0 ≤ t) : IsP (M + diagonal (Pi.single a t)) := by
  intro μ _ _ f hf
  by_cases ha : ∃ k, f k = a
  · obtain ⟨k, rfl⟩ := ha
    have heq : (M + diagonal (Pi.single (f k) t)).submatrix f f
        = M.submatrix f f + diagonal (Pi.single k t) := by
      ext i j
      simp [diagonal_apply, Pi.single_apply, hf.eq_iff]
    rw [heq]
    exact det_add_single_pos _ (hM.submatrix f hf) k ht
  · have heq : (M + diagonal (Pi.single a t)).submatrix f f = M.submatrix f f := by
      ext i j
      have : f i ≠ a := fun h => ha ⟨i, h⟩
      simp [diagonal_apply, this]
    rw [heq]; exact hM μ f hf

/-- Ikke-negativ diagonal bevarer P-egenskapen. -/
theorem IsP.add_diag {κ : Type} [Fintype κ] [DecidableEq κ] {N : Matrix κ κ ℝ} (hN : IsP N)
    (d : κ → ℝ) (hd : ∀ i, 0 ≤ d i) : IsP (N + diagonal d) := by
  suffices h : ∀ T : Finset κ, IsP (N + diagonal (fun i => if i ∈ T then d i else 0)) by
    simpa using h univ
  intro T
  induction T using Finset.induction_on with
  | empty => simpa using hN
  | insert a T ha ih =>
    have heq : N + diagonal (fun i => if i ∈ insert a T then d i else 0) =
        (N + diagonal (fun i => if i ∈ T then d i else 0)) + diagonal (Pi.single a (d a)) := by
      rw [add_assoc, diagonal_add]
      congr 2
      funext i
      by_cases hi : i = a
      · subst hi; simp [ha]
      · simp [hi]
    rw [heq]
    exact ih.add_single a (hd a)

/-- En P-matrise snur ikke fortegnet til noen vektor ≠ 0. -/
theorem IsP.nonrev {A : Matrix ι ι ℝ} (h : IsP A) (v : ι → ℝ) (hv : v ≠ 0) :
    ∃ i, 0 < v i * (A *ᵥ v) i := by
  by_contra hcon
  push Not at hcon
  let S := {i // v i ≠ 0}
  let d : S → ℝ := fun i => -(A *ᵥ v) i.1 / v i.1
  have hd : ∀ i, 0 ≤ d i := by
    intro ⟨i, hi⟩
    show 0 ≤ -(A *ᵥ v) i / v i
    rw [show -(A *ᵥ v) i / v i = -(v i * (A *ᵥ v) i) / (v i) ^ 2 by field_simp]
    exact div_nonneg (by linarith [hcon i]) (sq_nonneg _)
  have hP := (h.submatrix (Subtype.val : S → ι) Subtype.val_injective).add_diag d hd
  have hdet := hP.det_pos
  have hzero : (A.submatrix (Subtype.val : S → ι) Subtype.val + diagonal d) *ᵥ (fun i : S => v i.1) = 0 := by
    funext ⟨i, hi⟩
    rw [add_mulVec, Pi.add_apply, mulVec_diagonal]
    have hsum : (A.submatrix (Subtype.val : S → ι) Subtype.val *ᵥ fun i : S => v i.1) ⟨i, hi⟩
        = (A *ᵥ v) i := by
      simp only [mulVec, dotProduct, submatrix_apply]
      rw [← Finset.sum_subtype (univ.filter (fun j => v j ≠ 0)) (by simp) (fun j => A i j * v j)]
      rw [Finset.sum_filter_of_ne]
      intro j _ hj h0
      exact hj (by simp [h0])
    rw [hsum]
    simp only [d, Pi.zero_apply]
    field_simp
    ring
  have hne : (fun i : S => v i.1) ≠ 0 := by
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra hc; push Not at hc; exact hv (funext hc)
    intro h0
    exact hi (congrFun h0 ⟨i, hi⟩)
  have := (Matrix.exists_mulVec_eq_zero_iff).1 ⟨_, hne, hzero⟩
  linarith

/-- Villes alternativ: snur Bᵀ ikke fortegn, finnes u ≥ 0 med Bu > 0. -/
theorem semipos {κ : Type} [Fintype κ] [DecidableEq κ] (B : Matrix κ κ ℝ)
    (hB : ∀ y : κ → ℝ, y ≠ 0 → ∃ i, 0 < y i * (Bᵀ *ᵥ y) i) :
    ∃ u : κ → ℝ, (∀ i, 0 ≤ u i) ∧ ∀ i, 0 < (B *ᵥ u) i := by
  by_contra hcon
  let s : Set (κ → ℝ) := Set.univ.pi fun _ => Set.Ioi 0
  let t : Set (κ → ℝ) := (Matrix.mulVecLin B) '' Set.Ici 0
  have hs1 : Convex ℝ s := convex_pi fun _ _ => convex_Ioi 0
  have hs2 : IsOpen s := isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioi
  have ht : Convex ℝ t := (convex_Ici 0).linear_image _
  have hdisj : Disjoint s t := by
    rw [Set.disjoint_left]
    rintro z hz ⟨u, hu, rfl⟩
    apply hcon
    refine ⟨u, fun i => hu i, fun i => ?_⟩
    simpa using hz i (Set.mem_univ _)
  obtain ⟨f, c, hfs, hft⟩ := geometric_hahn_banach_open hs1 hs2 ht hdisj
  have hc0 : c ≤ 0 := by
    have := hft 0 ⟨0, Set.mem_Ici.2 le_rfl, by simp⟩
    simpa using this
  -- f i koordinater
  let g : κ → ℝ := fun i => f (fun j => if i = j then 1 else 0)
  have hf_apply : ∀ z, f z = ∑ i, z i * g i := by
    intro z
    have := (f : (κ → ℝ) →ₗ[ℝ] ℝ).pi_apply_eq_sum_univ z
    simpa [g, smul_eq_mul] using this
  have hmem : ∀ z : κ → ℝ, (∀ i, 0 < z i) → z ∈ s := fun z hz i _ => hz i
  have hone : f (fun _ => 1) < 0 := lt_of_lt_of_le (hfs _ (hmem _ fun _ => one_pos)) hc0
  -- g ≤ 0
  have hg : ∀ i, g i ≤ 0 := by
    intro i
    by_contra hpos
    push Not at hpos
    set δ := g i / (-f (fun _ => 1)) with hδ
    have hδpos : 0 < δ := div_pos hpos (by linarith)
    have hz := hfs (fun j => (if i = j then 1 else 0) + δ) (hmem _ fun j => by
      split_ifs <;> linarith)
    have hlin : f (fun j => (if i = j then 1 else 0) + δ) = g i + δ * f (fun _ => 1) := by
      have : (fun j => (if i = j then (1:ℝ) else 0) + δ) = (fun j => if i = j then (1:ℝ) else 0) + δ • (fun _ => (1:ℝ)) := by
        funext j; simp
      rw [this, map_add, map_smul, smul_eq_mul]
    rw [hlin] at hz
    have : δ * f (fun _ => 1) = -g i := by
      rw [hδ]; field_simp [show f (fun _ => 1) ≠ 0 from hone.ne]
    linarith
  -- y := -g
  set y : κ → ℝ := fun i => -g i with hy
  have hy0 : y ≠ 0 := by
    intro h0
    have : f (fun _ => 1) = 0 := by
      rw [hf_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      have := congrFun h0 i
      simp only [hy, Pi.zero_apply, neg_eq_zero] at this
      simp [this]
    linarith
  -- Bᵀ y ≤ 0
  have hBty : ∀ j, (Bᵀ *ᵥ y) j ≤ 0 := by
    intro j
    have hval : f (B *ᵥ Pi.single j 1) = -(Bᵀ *ᵥ y) j := by
      rw [hf_apply]
      simp only [mulVec, dotProduct, transpose_apply, hy]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Pi.single_apply]
    by_contra hpos
    push Not at hpos
    have hneg : f (B *ᵥ Pi.single j 1) < 0 := by rw [hval]; linarith
    set lam := (c - 1) / f (B *ᵥ Pi.single j 1)
    have hlam : 0 < lam := div_pos_of_neg_of_neg (by linarith) hneg
    have hin : B *ᵥ (lam • Pi.single j 1) ∈ t := by
      refine ⟨lam • Pi.single j 1, ?_, rfl⟩
      intro i
      simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg hlam.le (by simp [Pi.single_apply]; split_ifs <;> norm_num)
    have := hft _ hin
    rw [mulVec_smul, map_smul, smul_eq_mul] at this
    have : lam * f (B *ᵥ Pi.single j 1) = c - 1 := by
      simp only [lam]; exact div_mul_cancel₀ _ hneg.ne
    linarith
  obtain ⟨i, hi⟩ := hB y hy0
  have h1 : 0 ≤ y i := by simp only [hy]; linarith [hg i]
  nlinarith [hBty i]

theorem IsP.semipos {κ : Type} [Fintype κ] [DecidableEq κ] {B : Matrix κ κ ℝ} (h : IsP B) :
    ∃ u : κ → ℝ, (∀ i, 0 ≤ u i) ∧ ∀ i, 0 < (B *ᵥ u) i :=
  PMat.semipos B fun y hy => h.transpose.nonrev y hy

end PMat

/-! ## 2. Analyse: ingen fortegnsreversering på et rektangel -/

namespace GN
open PMat

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Matrisen som kontinuerlig lineær avbildning. -/
noncomputable def clm (A : Matrix ι ι ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)

@[simp] theorem clm_apply (A : Matrix ι ι ℝ) (v : ι → ℝ) : clm A v = A *ᵥ v := rfl

theorem abs_le_norm (v : ι → ℝ) (i : ι) : |v i| ≤ ‖v‖ := by
  have := norm_le_pi_norm v i
  rwa [Real.norm_eq_abs] at this

/-- Førsteordens Taylor: restleddet er lite i forhold til avstanden. -/
theorem taylor {F : (ι → ℝ) → (ι → ℝ)} {A : Matrix ι ι ℝ} {Ω : Set (ι → ℝ)} {x : ι → ℝ}
    (h : HasFDerivWithinAt F (clm A) Ω x) {η : ℝ} (hη : 0 < η) :
    ∃ ε > 0, ∀ y ∈ Ω, ‖y - x‖ < ε → ‖F y - F x - A *ᵥ (y - x)‖ ≤ η * ‖y - x‖ := by
  have h1 := h.isLittleO.def hη
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h1
  obtain ⟨ε, hε, hball⟩ := h1
  refine ⟨ε, hε, fun y hy hyx => ?_⟩
  have := hball (by rwa [dist_eq_norm]) hy
  simpa using this

/-- Måler hvor mye A bevarer fortegn: Σ max(0, vᵢ(Av)ᵢ). -/
def gfun (A : Matrix ι ι ℝ) (v : ι → ℝ) : ℝ := ∑ i, max 0 (v i * (A *ᵥ v) i)

theorem gfun_smul (A : Matrix ι ι ℝ) {t : ℝ} (_ht : 0 ≤ t) (v : ι → ℝ) :
    gfun A (t • v) = t ^ 2 * gfun A v := by
  unfold gfun
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec_smul, mul_max_of_nonneg _ _ (sq_nonneg t)]
  simp only [Pi.smul_apply, smul_eq_mul]
  congr 1
  · ring
  · ring

/-- Isolasjon: nær basispunktet finnes ingen fortegnsreversering. -/
theorem iso {F : (ι → ℝ) → (ι → ℝ)} {A : Matrix ι ι ℝ} {Ω : Set (ι → ℝ)} {a : ι → ℝ}
    (h : HasFDerivWithinAt F (clm A) Ω a) (hA : IsP A) :
    ∃ ε > 0, ∀ x ∈ Ω, ‖x - a‖ < ε → (∀ i, (x i - a i) * (F x i - F a i) ≤ 0) → x = a := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun x _ _ _ => Subsingleton.elim _ _⟩
  have hS : IsCompact (Metric.sphere (0 : ι → ℝ) 1) := isCompact_sphere 0 1
  have hSne : (Metric.sphere (0 : ι → ℝ) 1).Nonempty := NormedSpace.sphere_nonempty.2 zero_le_one
  have hcont : Continuous (gfun A) := by unfold gfun; fun_prop
  obtain ⟨v0, hv0, hmin⟩ := hS.exists_isMinOn hSne hcont.continuousOn
  set δ := gfun A v0 with hδdef
  have hδ : 0 < δ := by
    have hne : v0 ≠ 0 := by
      intro h0; rw [h0] at hv0; simp at hv0
    obtain ⟨i, hi⟩ := hA.nonrev v0 hne
    calc 0 < max 0 (v0 i * (A *ᵥ v0) i) := lt_max_of_lt_right hi
      _ ≤ δ := Finset.single_le_sum (f := fun i => max 0 (v0 i * (A *ᵥ v0) i))
          (fun j _ => le_max_left _ _) (Finset.mem_univ i)
  have hlow : ∀ v : ι → ℝ, δ * ‖v‖ ^ 2 ≤ gfun A v := by
    intro v
    by_cases hv : v = 0
    · subst hv; simp [gfun]
    · have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
      have hmem : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : ι → ℝ) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
      have h1 : δ ≤ gfun A (‖v‖⁻¹ • v) := hmin hmem
      have h2 : gfun A v = ‖v‖ ^ 2 * gfun A (‖v‖⁻¹ • v) := by
        rw [gfun_smul A (inv_nonneg.2 hn.le), ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hn.ne',
          one_pow, one_mul]
      rw [h2]; nlinarith [sq_nonneg ‖v‖]
  set N : ℝ := (Fintype.card ι : ℝ) with hNdef
  have hN : 0 < N := by simp [N, Fintype.card_pos]
  obtain ⟨ε, hε, htay⟩ := taylor h (show 0 < δ / (2 * N) by positivity)
  refine ⟨ε, hε, fun x hx hxa hrev => ?_⟩
  have hr := htay x hx hxa
  set v := x - a with hvdef
  set r := F x - F a - A *ᵥ v with hrdef
  have hterm : ∀ i, max 0 (v i * (A *ᵥ v) i) ≤ δ / (2 * N) * ‖v‖ ^ 2 := by
    intro i
    have hAv : (A *ᵥ v) i = (F x i - F a i) - r i := by
      simp only [hrdef, Pi.sub_apply]; ring
    have hvi : v i = x i - a i := rfl
    have h1 : v i * (A *ᵥ v) i ≤ |v i| * |r i| := by
      rw [hAv, mul_sub]
      have h0 := hrev i
      rw [← hvi] at h0
      have h3 : -(v i * r i) ≤ |v i| * |r i| := by rw [← abs_mul]; exact neg_le_abs _
      linarith
    have h2 : |v i| * |r i| ≤ δ / (2 * N) * ‖v‖ ^ 2 := by
      calc |v i| * |r i| ≤ ‖v‖ * (δ / (2 * N) * ‖v‖) :=
            mul_le_mul (abs_le_norm v i) ((abs_le_norm r i).trans hr) (abs_nonneg _) (norm_nonneg _)
        _ = _ := by ring
    exact max_le (by positivity) (h1.trans h2)
  have hsum : gfun A v ≤ N * (δ / (2 * N) * ‖v‖ ^ 2) := by
    unfold gfun
    calc ∑ i, max 0 (v i * (A *ᵥ v) i) ≤ ∑ _i : ι, δ / (2 * N) * ‖v‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = _ := by simp [N]
  have hl := hlow v
  have hv0' : ‖v‖ ^ 2 = 0 := by
    have : N * (δ / (2 * N) * ‖v‖ ^ 2) = δ / 2 * ‖v‖ ^ 2 := by field_simp
    nlinarith [sq_nonneg ‖v‖]
  have : v = 0 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hv0'
    exact norm_eq_zero.1 this
  exact sub_eq_zero.1 this

/-- Tillatte punkter: x ligger «over» a i fortegnsmønsteret σ på koordinatene i I,
    er lik a utenfor I, og F går ikke opp (i σ-retning) på I. -/
def Adm (F : (ι → ℝ) → (ι → ℝ)) (σ : ι → ℝ) (I : Finset ι) (a x : ι → ℝ) : Prop :=
  (∀ j, j ∉ I → x j = a j) ∧ (∀ i, 0 ≤ σ i * (x i - a i)) ∧ (∀ i ∈ I, σ i * (F x i - F a i) ≤ 0)

theorem Adm.rev {F : (ι → ℝ) → (ι → ℝ)} {σ : ι → ℝ} {I : Finset ι} {a x : ι → ℝ}
    (hσ : ∀ i, σ i * σ i = 1) (h : Adm F σ I a x) :
    ∀ i, (x i - a i) * (F x i - F a i) ≤ 0 := by
  intro i
  by_cases hi : i ∈ I
  · have h1 := h.2.1 i
    have h2 := h.2.2 i hi
    have : (x i - a i) * (F x i - F a i) = (σ i * (x i - a i)) * (σ i * (F x i - F a i)) := by
      linear_combination (-(x i - a i) * (F x i - F a i)) * hσ i
    rw [this]; exact mul_nonpos_of_nonneg_of_nonpos h1 h2
  · rw [h.1 i hi, sub_self, zero_mul]

/-- Standardforutsetningene: F er deriverbar på rektangelet med Jacobi-matrise J,
    og J er en P-matrise i hvert punkt. -/
structure Hyp (F : (ι → ℝ) → (ι → ℝ)) (J : (ι → ℝ) → Matrix ι ι ℝ) (lo hi : ι → ℝ) : Prop where
  deriv : ∀ x ∈ Set.Icc lo hi, HasFDerivWithinAt F (clm (J x)) (Set.Icc lo hi) x
  isP : ∀ x ∈ Set.Icc lo hi, IsP (J x)

/-- Gale–Nikaidos hovedlemma (generalisert til alle fortegnsmønstre). -/
theorem main {F : (ι → ℝ) → (ι → ℝ)} {J : (ι → ℝ) → Matrix ι ι ℝ} {lo hi : ι → ℝ}
    (H : Hyp F J lo hi) {σ : ι → ℝ} (hσ : ∀ i, σ i = 1 ∨ σ i = -1) :
    ∀ I : Finset ι, ∀ a ∈ Set.Icc lo hi, ∀ x ∈ Set.Icc lo hi, Adm F σ I a x → x = a := by
  have hσσ : ∀ i, σ i * σ i = 1 := fun i => by rcases hσ i with h | h <;> rw [h] <;> norm_num
  set Ω := Set.Icc lo hi with hΩ
  have hFc : ContinuousOn F Ω := fun x hx => (H.deriv x hx).continuousWithinAt
  intro I
  induction I using Finset.strongInduction with
  | H I ih =>
  intro a ha
  -- trinn 0: er én koordinat i I uendret, gir induksjonen x = a
  have red : ∀ x ∈ Ω, Adm F σ I a x → x ≠ a → ∀ i ∈ I, 0 < σ i * (x i - a i) := by
    intro x hx hadm hne i hi
    rcases (hadm.2.1 i).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have hxi : x i = a i := by
        rcases mul_eq_zero.1 heq.symm with h0 | h0
        · have := hσσ i; rw [h0] at this; simp at this
        · linarith
      apply hne
      refine ih (I.filter fun j => x j ≠ a j) ?_ a ha x hx ⟨?_, hadm.2.1, ?_⟩
      · refine (Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).2 ⟨i, hi, ?_⟩
        simp [hxi]
      · intro j hj
        by_cases hjI : j ∈ I
        · simp only [Finset.mem_filter, not_and, not_not] at hj; exact hj hjI
        · exact hadm.1 j hjI
      · intro j hj
        exact hadm.2.2 j (Finset.mem_of_mem_filter j hj)
  -- trinn 1: isolasjon nær a
  obtain ⟨ε, hε, hiso⟩ := iso (H.deriv a ha) (H.isP a ha)
  intro x0 hx0 hadm0
  by_contra hne0
  have hfar : ε ≤ ‖x0 - a‖ := by
    by_contra hlt; push Not at hlt
    exact hne0 (hiso x0 hx0 hlt (hadm0.rev hσσ))
  -- trinn 2: minimer Σ σᵢ yᵢ over de tillatte punktene med avstand ≥ ε
  let T : Set (ι → ℝ) := {y | y ∈ Ω ∧ Adm F σ I a y ∧ ε ≤ ‖y - a‖}
  have hTsub : T ⊆ Ω := fun y hy => hy.1
  have hTclosed : IsClosed T := by
    have e1 : T = (Ω ∩ {y | ∀ j, j ∉ I → y j = a j} ∩ {y | ∀ i, 0 ≤ σ i * (y i - a i)}
        ∩ {y | ε ≤ ‖y - a‖}) ∩ ⋂ i ∈ I, (Ω ∩ (fun y => σ i * (F y i - F a i)) ⁻¹' Set.Iic 0) := by
      ext y
      simp only [T, Adm, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
        Set.mem_Iic]
      constructor
      · rintro ⟨hy, ⟨h1, h2, h3⟩, h4⟩
        exact ⟨⟨⟨⟨hy, h1⟩, h2⟩, h4⟩, fun i hi => ⟨hy, h3 i hi⟩⟩
      · rintro ⟨⟨⟨⟨hy, h1⟩, h2⟩, h4⟩, h5⟩
        exact ⟨hy, ⟨h1, h2, fun i hi => (h5 i hi).2⟩, h4⟩
    rw [e1]
    refine IsClosed.inter (IsClosed.inter (IsClosed.inter (IsClosed.inter isClosed_Icc ?_) ?_) ?_) ?_
    · simp only [Set.ofPred_forall]
      exact isClosed_iInter fun j => isClosed_iInter fun _ =>
        isClosed_eq (continuous_apply j) continuous_const
    · simp only [Set.ofPred_forall]
      exact isClosed_iInter fun i => isClosed_le continuous_const (by fun_prop)
    · exact isClosed_le continuous_const (by fun_prop)
    · refine isClosed_biInter fun i _ => ?_
      have hci : ContinuousOn (fun y => σ i * (F y i - F a i)) Ω :=
        continuousOn_const.mul (((continuous_apply i).comp_continuousOn hFc).sub continuousOn_const)
      exact hci.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hTc : IsCompact T := isCompact_Icc.of_isClosed_subset hTclosed hTsub
  have hTne : T.Nonempty := ⟨x0, hx0, hadm0, hfar⟩
  let φ : (ι → ℝ) → ℝ := fun y => ∑ i, σ i * y i
  have hφ : Continuous φ := by fun_prop
  obtain ⟨c, hcT, hcmin⟩ := hTc.exists_isMinOn hTne hφ.continuousOn
  obtain ⟨hcΩ, hcadm, hcfar⟩ := hcT
  have hca : c ≠ a := by
    intro h; rw [h, sub_self, norm_zero] at hcfar; linarith
  have hpos := red c hcΩ hcadm hca
  have hIne : I.Nonempty := by
    by_contra hI
    rw [Finset.not_nonempty_iff_eq_empty] at hI
    apply hca; funext j; exact hcadm.1 j (by simp [hI])
  -- en nedoverretning w: semipositivitet for den prinsipale delmatrisen
  set B := (PMat.sconj σ (J c)).submatrix (Subtype.val : I → ι) Subtype.val with hBdef
  have hB : IsP B := ((H.isP c hcΩ).sconj hσσ).submatrix _ Subtype.val_injective
  obtain ⟨u, hu0, huB⟩ := hB.semipos
  let w : ι → ℝ := fun j => if h : j ∈ I then σ j * u ⟨j, h⟩ else 0
  have hw_off : ∀ j, j ∉ I → w j = 0 := fun j hj => by simp [w, hj]
  have hw_on : ∀ j (h : j ∈ I), σ j * w j = u ⟨j, h⟩ := fun j h => by
    simp only [w, dite_eq_left h]; rw [← mul_assoc, hσσ, one_mul]
  have hsw_nonneg : ∀ j, 0 ≤ σ j * w j := by
    intro j
    by_cases h : j ∈ I
    · rw [hw_on j h]; exact hu0 _
    · rw [hw_off j h, mul_zero]
  have hd : ∀ i (hi : i ∈ I), σ i * (J c *ᵥ w) i = (B *ᵥ u) ⟨i, hi⟩ := by
    intro i hi
    have hsub := Finset.sum_subset (f := fun j => σ i * (J c i j * w j)) (Finset.subset_univ I)
      (fun j _ hj => by simp [hw_off j hj])
    simp only [mulVec, dotProduct, hBdef, submatrix_apply, PMat.sconj, Matrix.of_apply]
    rw [Finset.mul_sum, ← hsub, ← Finset.sum_coe_sort I]
    refine Finset.sum_congr rfl fun ⟨j, hj⟩ _ => ?_
    simp only [w, dite_eq_left hj]
    ring
  -- kvantitative størrelser
  obtain ⟨i1, hi1⟩ := hIne
  obtain ⟨k0, -, hk0⟩ := Finset.exists_min_image Finset.univ (fun k : I => (B *ᵥ u) k)
    ⟨⟨i1, hi1⟩, Finset.mem_univ _⟩
  set m := (B *ᵥ u) k0 with hmdef
  have hm : 0 < m := huB k0
  have hmle : ∀ k, m ≤ (B *ᵥ u) k := fun k => hk0 k (Finset.mem_univ _)
  obtain ⟨i2, hi2, hgap⟩ := Finset.exists_min_image I (fun i => σ i * (c i - a i)) ⟨i1, hi1⟩
  set g0 := σ i2 * (c i2 - a i2) with hg0def
  have hg0 : 0 < g0 := hpos i2 hi2
  have hW : 0 < ‖w‖ + 1 := by positivity
  obtain ⟨ε2, hε2, htay⟩ := taylor (H.deriv c hcΩ) (show 0 < m / (2 * (‖w‖ + 1)) by positivity)
  set s := min ε2 g0 / (2 * (‖w‖ + 1)) with hsdef
  have hmin0 : 0 < min ε2 g0 := lt_min hε2 hg0
  have hs : 0 < s := by positivity
  have hsW : s * (‖w‖ + 1) = min ε2 g0 / 2 := by rw [hsdef]; field_simp
  have hsw1 : s * ‖w‖ < ε2 := by
    have := min_le_left ε2 g0; nlinarith
  have hsw2 : s * ‖w‖ < g0 := by
    have := min_le_right ε2 g0; nlinarith
  have hu_le : ∀ j (h : j ∈ I), u ⟨j, h⟩ ≤ ‖w‖ := by
    intro j h
    rw [← hw_on j h]
    calc σ j * w j ≤ |σ j * w j| := le_abs_self _
      _ = |w j| := by
        rw [abs_mul]; rcases hσ j with h' | h' <;> rw [h'] <;> norm_num
      _ ≤ ‖w‖ := abs_le_norm w j
  -- det nye punktet
  set y := c - s • w with hydef
  have hy_apply : ∀ j, y j = c j - s * w j := fun j => by simp [hydef]
  have hyc : ‖y - c‖ = s * ‖w‖ := by
    rw [hydef, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
  have hsign : ∀ j, 0 ≤ σ j * (y j - a j) := by
    intro j
    rw [hy_apply]
    by_cases h : j ∈ I
    · have h1 := hpos j h
      have h2 : σ j * (s * w j) = s * u ⟨j, h⟩ := by rw [← hw_on j h]; ring
      have h3 := hu_le j h
      have h4 := hgap j h
      have : σ j * (c j - s * w j - a j) = σ j * (c j - a j) - s * u ⟨j, h⟩ := by linear_combination -h2
      rw [this]; nlinarith
    · rw [hw_off j h, hcadm.1 j h]; simp
  have hyΩ : y ∈ Ω := by
    constructor
    · intro j
      have h1 := hsign j
      have h2 := hsw_nonneg j
      have hlo1 := ha.1 j
      have hlo2 := hcΩ.1 j
      rw [hy_apply] at h1 ⊢
      rcases hσ j with h' | h' <;> rw [h'] at h1 h2
      · nlinarith
      · nlinarith
    · intro j
      have h1 := hsign j
      have h2 := hsw_nonneg j
      have hhi1 := ha.2 j
      have hhi2 := hcΩ.2 j
      rw [hy_apply] at h1 ⊢
      rcases hσ j with h' | h' <;> rw [h'] at h1 h2
      · nlinarith
      · nlinarith
  have hyF : ∀ i ∈ I, σ i * (F y i - F a i) < 0 := by
    intro i hi
    have hr := htay y hyΩ (by rw [hyc]; exact hsw1)
    set r := F y - F c - J c *ᵥ (y - c) with hrdef
    have hyc' : y - c = (-s) • w := by rw [hydef]; simp [neg_smul]
    have hFi : F y i - F c i = r i - s * (J c *ᵥ w) i := by
      have : (J c *ᵥ (y - c)) i = -s * (J c *ᵥ w) i := by
        rw [hyc', mulVec_smul]; simp
      simp only [hrdef, Pi.sub_apply] at this ⊢
      linarith
    have hri : |r i| ≤ m / (2 * (‖w‖ + 1)) * (s * ‖w‖) := by
      rw [← hyc]; exact (abs_le_norm r i).trans hr
    have hσr : σ i * r i ≤ |r i| := by
      calc σ i * r i ≤ |σ i * r i| := le_abs_self _
        _ = |r i| := by rw [abs_mul]; rcases hσ i with h' | h' <;> rw [h'] <;> norm_num
    have hdi := hd i hi
    have hmi := hmle ⟨i, hi⟩
    have hcF := hcadm.2.2 i hi
    have hbound : m / (2 * (‖w‖ + 1)) * (s * ‖w‖) ≤ s * m / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [norm_nonneg w]
    have : σ i * (F y i - F c i) = σ i * r i - s * (σ i * (J c *ᵥ w) i) := by rw [hFi]; ring
    have h5 : σ i * (F y i - F a i) = σ i * (F y i - F c i) + σ i * (F c i - F a i) := by ring
    rw [h5, this, hdi]
    nlinarith
  have hyadm : Adm F σ I a y :=
    ⟨fun j hj => by rw [hy_apply, hw_off j hj, hcadm.1 j hj]; ring, hsign,
      fun i hi => (hyF i hi).le⟩
  have hya : y ≠ a := by
    intro h
    have := hsign i2
    have h1 := hpos i2 hi2
    have h2 : σ i2 * (s * w i2) = s * u ⟨i2, hi2⟩ := by rw [← hw_on i2 hi2]; ring
    have h3 := hu_le i2 hi2
    have h6 : σ i2 * (y i2 - a i2) = 0 := by rw [h]; ring
    rw [hy_apply] at h6
    nlinarith
  by_cases hfar' : ε ≤ ‖y - a‖
  · have hle : φ c ≤ φ y := hcmin ⟨hyΩ, hyadm, hfar'⟩
    have hupos : ∃ k, 0 < u k := by
      by_contra hcon; push Not at hcon
      have : u = 0 := funext fun k => le_antisymm (hcon k) (hu0 k)
      have h0 : (B *ᵥ u) k0 = 0 := by rw [this, mulVec_zero]; rfl
      linarith
    obtain ⟨⟨k, hk⟩, hku⟩ := hupos
    have hsum : 0 < ∑ i, σ i * w i := by
      refine Finset.sum_pos' (fun i _ => hsw_nonneg i) ⟨k, Finset.mem_univ _, ?_⟩
      rw [hw_on k hk]; exact hku
    have : φ y = φ c - s * ∑ i, σ i * w i := by
      simp only [φ, hy_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_; ring
    nlinarith
  · push Not at hfar'
    exact hya (hiso y hyΩ hfar' (hyadm.rev hσσ))

/-! ## 3. Gale–Nikaido -/

/-- **Gale–Nikaido.** Er Jacobi-matrisen en P-matrise overalt på et lukket
    rektangel, er F injektiv der. -/
theorem injOn {F : (ι → ℝ) → (ι → ℝ)} {J : (ι → ℝ) → Matrix ι ι ℝ} {lo hi : ι → ℝ}
    (H : Hyp F J lo hi) : Set.InjOn F (Set.Icc lo hi) := by
  intro x hx y hy hxy
  let σ : ι → ℝ := fun i => if y i ≤ x i then 1 else -1
  have hσ : ∀ i, σ i = 1 ∨ σ i = -1 := fun i => by
    simp only [σ]; split_ifs <;> simp
  refine main H hσ Finset.univ y hy x hx ⟨fun j hj => absurd (Finset.mem_univ j) hj, ?_, ?_⟩
  · intro i
    simp only [σ]
    split_ifs with h
    · linarith
    · push Not at h; linarith
  · intro i _
    rw [hxy, sub_self, mul_zero]

/-- Globalt: P-matrise overalt ⇒ F er injektiv på hele ℝⁿ. -/
theorem injective {F : (ι → ℝ) → (ι → ℝ)} {J : (ι → ℝ) → Matrix ι ι ℝ}
    (hd : ∀ x, HasFDerivAt F (clm (J x)) x) (hP : ∀ x, IsP (J x)) : Function.Injective F := by
  intro x y hxy
  have H : Hyp F J (x ⊓ y) (x ⊔ y) :=
    ⟨fun z _ => (hd z).hasFDerivWithinAt, fun z _ => hP z⟩
  exact injOn H ⟨inf_le_left, le_sup_left⟩ ⟨inf_le_right, le_sup_right⟩ hxy

end GN

/-! ## 4. Kausale modeller -/

namespace SCM

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Har residualen en P-matrise som Jacobi-matrise overalt, har modellen høyst
    én løsning for hver verdi av de eksogene variablene. -/
theorem unique_of_P (M : SCM V ℝ) (u : V → ℝ) (J : (V → ℝ) → Matrix V V ℝ)
    (hd : ∀ s, HasFDerivAt (resid' M u) (GN.clm (J s)) s) (hP : ∀ s, PMat.IsP (J s))
    {s t : V → ℝ} (hs : M.Solves u s) (ht : M.Solves u t) : s = t := by
  apply GN.injective hd hP
  rw [(solves_iff_resid_zero M u s).1 hs, (solves_iff_resid_zero M u t).1 ht]

end SCM

/-! ## 5. Eksempel: en negativ tilbakekoblingssløyfe -/

namespace PMat

/-- For 2×2-matriser: P-matrise ⇔ positive diagonalelementer og positiv determinant. -/
theorem isP_two (A : Matrix (Fin 2) (Fin 2) ℝ) (h0 : 0 < A 0 0) (h1 : 0 < A 1 1)
    (hd : 0 < A.det) : IsP A := by
  intro κ _ _ f hf
  have hcard : Fintype.card κ ≤ 2 := by simpa using Fintype.card_le_of_injective f hf
  interval_cases hc : Fintype.card κ
  · have : IsEmpty κ := Fintype.card_eq_zero_iff.1 hc
    simp [det_isEmpty]
  · obtain ⟨k, hk⟩ := Fintype.card_eq_one_iff.1 hc
    have : Subsingleton κ := ⟨fun a b => (hk a).trans (hk b).symm⟩
    rw [det_eq_elem_of_subsingleton _ k, submatrix_apply]
    rcases Fin.exists_fin_two.1 ⟨f k, rfl⟩ with h | h <;> rw [h] <;> assumption
  · have hbij : Function.Bijective f :=
      (Fintype.bijective_iff_injective_and_card f).2 ⟨hf, by simp [hc]⟩
    rw [show A.submatrix f f = A.submatrix (Equiv.ofBijective f hbij) (Equiv.ofBijective f hbij)
      from rfl, det_submatrix_equiv_self]
    exact hd

end PMat

namespace Feedback

/-- X := 3Y + Y³ + b₁ og Y := b₂ − X (variabel 0 = X, 1 = Y). Sløyfeforsterkningen
    er −(3 + 3Y²), så den er aldri en kontraksjon. -/
noncomputable def scm (b₁ b₂ : ℝ) : SCM (Fin 2) ℝ :=
  ⟨fun v => some (if v = 0 then
      ⟨[1], fun s => 3 * s 1 + s 1 ^ 3 + b₁, fun s t h => by rw [h 1 (by simp)]⟩
    else ⟨[0], fun s => b₂ - s 0, fun s t h => by rw [h 0 (by simp)]⟩)⟩

theorem resid_eq (b₁ b₂ : ℝ) (u : Fin 2 → ℝ) :
    SCM.resid' (scm b₁ b₂) u = fun s => ![s 0 - (3 * s 1 + s 1 ^ 3 + b₁), s 1 - (b₂ - s 0)] := by
  funext s v
  fin_cases v <;> simp [SCM.resid', scm, SCM.fixExo]

/-- Jacobi-matrisen til residualen. -/
def jac (s : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, -(3 + 3 * s 1 ^ 2); 1, 1]

theorem jac_isP (s : Fin 2 → ℝ) : PMat.IsP (jac s) := by
  refine PMat.isP_two _ (by simp [jac]) (by simp [jac]) ?_
  simp [jac, Matrix.det_fin_two]
  nlinarith [sq_nonneg (s 1)]

theorem hasDeriv (b₁ b₂ : ℝ) (u s : Fin 2 → ℝ) :
    HasFDerivAt (SCM.resid' (scm b₁ b₂) u) (GN.clm (jac s)) s := by
  rw [resid_eq, hasFDerivAt_pi']
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) s
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) s
  intro i
  fin_cases i
  · have := h0.sub (((h1.const_mul 3).add (h1.pow 3)).add_const b₁)
    refine this.congr_fderiv ?_
    ext v
    simp [jac, dotProduct, Fin.sum_univ_two]
    ring
  · have := h1.sub (h0.const_sub b₂)
    refine this.congr_fderiv ?_
    ext v
    simp [jac, dotProduct, Fin.sum_univ_two]
    ring

/-- Tilbakekoblingssløyfen har høyst én likevekt, for alle b₁, b₂. -/
theorem unique (b₁ b₂ : ℝ) (u : Fin 2 → ℝ) {s t : Fin 2 → ℝ}
    (hs : (scm b₁ b₂).Solves u s) (ht : (scm b₁ b₂).Solves u t) : s = t :=
  SCM.unique_of_P (scm b₁ b₂) u jac (fun s => hasDeriv b₁ b₂ u s) jac_isP hs ht

end Feedback
end CausalPhys
