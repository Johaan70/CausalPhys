/-
  CausalPhys.MintyBrowderHilbert — Minty–Browder i (uendeligdimensjonale)
  reelle Hilbert-rom.

    Teorem. La H være et reelt Hilbert-rom og F : H → H kontinuerlig,
    monoton og koersiv. Da er F surjektiv, og løsningsmengden til F x = b
    er lukket og konveks. Er F strengt monoton, er løsningen entydig.

  Beviset er Galerkin + svak kompakthet, uten følger og uten separabilitet:

    1. Galerkin: på hvert endeligdimensjonale underrom V finnes v ∈ V med
       ‖v‖ ≤ R og ⟪F v − b, w⟫ = 0 for alle w ∈ V (spissvinkel-lemmaet,
       altså Brouwer, anvendt på den ortogonale projeksjonen av F − b).
    2. Monotonitet gjør Galerkin-løsningen til et punkt i mengdene
       C_y = {x : ⟪F y − b, y − x⟫ ≥ 0} for alle y ∈ V.
    3. Svak kompakthet: via Riesz ligger kula ‖x‖ ≤ R i det svake*-kompakte
       kulelegemet i dualrommet (Banach–Alaoglu fra Mathlib); C_y er svakt*
       lukket. Endelig snitt-egenskapen gir x i alle C_y.
    4. Mintys triks gir F x = b.
-/
import CausalPhys.MintyBrowder
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

set_option linter.unusedSectionVars false

open RealInnerProductSpace Filter Topology

namespace CausalPhys
namespace MintyBrowderHilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Koersivitet i et vilkårlig indreproduktrom. -/
def Coercive (F : H → H) : Prop :=
  ∀ M : ℝ, ∃ R > 0, ∀ x, R ≤ ‖x‖ → M * ‖x‖ ≤ ⟪F x, x⟫

omit [CompleteSpace H] in
/-- Mintys lemma (gjelder i alle reelle indreproduktrom). -/
theorem minty_iff (F : H → H) (hF : Continuous F) (hmono : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    (b x : H) : F x = b ↔ ∀ y, 0 ≤ ⟪F y - b, y - x⟫ := by
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
      have ht' : 0 < t := ht
      nlinarith
    have := hw (-(F x - b))
    rw [inner_neg_right, real_inner_self_eq_norm_sq] at this
    have : ‖F x - b‖ = 0 := by nlinarith [norm_nonneg (F x - b)]
    exact sub_eq_zero.1 (norm_eq_zero.1 this)

omit [CompleteSpace H] in
/-- **Galerkin-trinnet.** På et endeligdimensjonalt underrom V finnes en
    tilnærmet løsning: v ∈ V, ‖v‖ ≤ R og F v − b ⊥ V. -/
theorem galerkin (F : H → H) (hF : Continuous F) (b : H) {R : ℝ} (hR : 0 < R)
    (hacute : ∀ x, ‖x‖ = R → 0 ≤ ⟪F x - b, x⟫) (V : Submodule ℝ H) [FiniteDimensional ℝ V] :
    ∃ v ∈ V, ‖v‖ ≤ R ∧ ∀ w ∈ V, ⟪F v - b, w⟫ = 0 := by
  let G : V → V := fun v => V.orthogonalProjectionOnto (F v - b)
  have hGc : Continuous G :=
    V.orthogonalProjectionOnto.continuous.comp
      ((hF.comp continuous_subtype_val).sub continuous_const)
  have hG : ∀ v w : V, ⟪G v, w⟫ = ⟪F v - b, (w : H)⟫ := fun v w =>
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right w _
  obtain ⟨v, hv, hGv⟩ := MintyBrowder.exists_zero_of_acute G hR hGc.continuousOn (fun v hv => by
    rw [hG]
    exact hacute v (by rw [← hv]; rfl))
  refine ⟨v, v.2, hv, fun w hw => ?_⟩
  have := hG v ⟨w, hw⟩
  rw [hGv, inner_zero_left] at this
  exact this.symm

/-- **Minty–Browder i Hilbert-rom (eksistens).** -/
theorem surjective (F : H → H) (hF : Continuous F) (hmono : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    (hcoer : Coercive F) : Function.Surjective F := by
  intro b
  obtain ⟨R, hR, hRc⟩ := hcoer ‖b‖
  have hacute : ∀ x, ‖x‖ = R → 0 ≤ ⟪F x - b, x⟫ := by
    intro x hx
    have h1 := hRc x hx.ge
    have h2 := real_inner_le_norm b x
    rw [inner_sub_left]
    linarith
  -- kulelegemet i dualrommet, svakt* kompakt (Banach–Alaoglu)
  set K : Set (WeakDual ℝ H) :=
    WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ H) R with hKdef
  have hKc : IsCompact K := WeakDual.isCompact_closedBall 0 R
  -- de svakt* lukkede mengdene C_y
  let C : H → Set (WeakDual ℝ H) := fun y => {φ | φ (F y - b) ≤ ⟪F y - b, y⟫}
  have hCc : ∀ y, IsClosed (C y) := fun y =>
    isClosed_le (WeakDual.eval_continuous (F y - b)) continuous_const
  -- endelig snitt-egenskapen, fra Galerkin
  have hfip : ∀ u : Finset H, (K ∩ ⋂ y ∈ u, C y).Nonempty := by
    intro u
    set V := Submodule.span ℝ (u : Set H)
    obtain ⟨v, hvV, hvR, hvperp⟩ := galerkin F hF b hR hacute V
    refine ⟨StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H v), ?_, ?_⟩
    · show InnerProductSpace.toDual ℝ H v ∈ Metric.closedBall (0 : StrongDual ℝ H) R
      rw [mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map]
      exact hvR
    · simp only [Set.mem_iInter]
      intro y hy
      show (InnerProductSpace.toDual ℝ H v) (F y - b) ≤ ⟪F y - b, y⟫
      rw [InnerProductSpace.toDual_apply_apply]
      have hyV : y ∈ V := Submodule.subset_span hy
      have h1 := hmono y v
      have h2 := hvperp (y - v) (V.sub_mem hyV hvV)
      have e : ⟪F y - b, y - v⟫ = ⟪F y - F v, y - v⟫ + ⟪F v - b, y - v⟫ := by
        rw [← inner_add_left]; congr 1; abel
      rw [inner_sub_right, real_inner_comm v] at e
      linarith
  obtain ⟨φ, -, hφ⟩ := hKc.inter_iInter_nonempty C hCc hfip
  -- tilbake til H med Riesz
  set x := (InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual φ)
  have hx : ∀ z, ⟪x, z⟫ = φ z := fun z => InnerProductSpace.toDual_symm_apply
  refine ⟨x, (minty_iff F hF hmono b x).2 fun y => ?_⟩
  have := Set.mem_iInter.1 hφ y
  change φ (F y - b) ≤ ⟪F y - b, y⟫ at this
  rw [← hx, real_inner_comm] at this
  rw [inner_sub_right]
  linarith

/-- **Minty–Browder i Hilbert-rom.** Løsningsmengden er ikke-tom, lukket og konveks. -/
theorem minty_browder (F : H → H) (hF : Continuous F) (hmono : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    (hcoer : Coercive F) (b : H) :
    {x | F x = b}.Nonempty ∧ IsClosed {x | F x = b} ∧ Convex ℝ {x | F x = b} := by
  refine ⟨surjective F hF hmono hcoer b, isClosed_eq hF continuous_const, ?_⟩
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
theorem minty_browder_unique (F : H → H) (hF : Continuous F)
    (hmono : ∀ x y, x ≠ y → 0 < ⟪F x - F y, x - y⟫) (hcoer : Coercive F) (b : H) :
    ∃! x, F x = b := by
  have hmono' : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫ := by
    intro x y
    by_cases h : x = y
    · rw [h, sub_self, inner_zero_left]
    · exact (hmono x y h).le
  obtain ⟨x, hx⟩ := surjective F hF hmono' hcoer b
  refine ⟨x, hx, fun y hy => ?_⟩
  by_contra hne
  have := hmono y x hne
  rw [hy, hx, sub_self, inner_zero_left] at this
  exact lt_irrefl _ this

/-! ## Eksempel: en kubisk rang-én-perturbasjon av identiteten

  F x = x + ⟪a, x⟫³ · a, i ethvert reelt Hilbert-rom (for eksempel ℓ² eller L²).
  F er sterkt monoton, men ikke Lipschitz, så Zarantonellos teorem (Theorem 24)
  gjelder ikke. Minty–Browder gir likevel nøyaktig én løsning for hver b.
-/

theorem cube_mono' (s t : ℝ) : 0 ≤ (s ^ 3 - t ^ 3) * (s - t) := by
  nlinarith [sq_nonneg (s - t), sq_nonneg (s + t),
    mul_nonneg (sq_nonneg (s - t)) (add_nonneg (sq_nonneg s) (sq_nonneg t))]

theorem rankOne_exists_unique (a b : H) :
    ∃! x, x + ⟪a, x⟫ ^ 3 • a = b := by
  refine minty_browder_unique (fun x => x + ⟪a, x⟫ ^ 3 • a) (by fun_prop) ?_ ?_ b
  · intro x y hxy
    have e : ⟪(x + ⟪a, x⟫ ^ 3 • a) - (y + ⟪a, y⟫ ^ 3 • a), x - y⟫
        = ‖x - y‖ ^ 2 + (⟪a, x⟫ ^ 3 - ⟪a, y⟫ ^ 3) * (⟪a, x⟫ - ⟪a, y⟫) := by
      have : (x + ⟪a, x⟫ ^ 3 • a) - (y + ⟪a, y⟫ ^ 3 • a) = (x - y) + (⟪a, x⟫ ^ 3 - ⟪a, y⟫ ^ 3) • a := by
        rw [sub_smul]; abel
      rw [this, inner_add_left, real_inner_self_eq_norm_sq, real_inner_smul_left, inner_sub_right]
    rw [e]
    have h1 : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
    have := cube_mono' ⟪a, x⟫ ⟪a, y⟫
    positivity
  · intro M
    refine ⟨|M| + 1, by positivity, fun x hx => ?_⟩
    have e : ⟪x + ⟪a, x⟫ ^ 3 • a, x⟫ = ‖x‖ ^ 2 + ⟪a, x⟫ ^ 4 := by
      rw [inner_add_left, real_inner_self_eq_norm_sq, real_inner_smul_left]; ring
    rw [e]
    have h4 : 0 ≤ ⟪a, x⟫ ^ 4 := by positivity
    have hM : M ≤ |M| := le_abs_self M
    have hn : 0 ≤ ‖x‖ := norm_nonneg x
    nlinarith

end MintyBrowderHilbert
end CausalPhys
