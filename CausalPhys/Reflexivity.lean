/-
  CausalPhys.Reflexivity — generelle refleksivitetsresultater.

    1. Goldstines teorem: kula i X ligger svakt*-tett i kula i X**.
    2. Milman–Pettis: et uniformt konvekst Banach-rom er refleksivt.
       (Står som TODO i Mathlib.)
    3. Dualrommet til et refleksivt rom er refleksivt.
    4. Et rom som kan legges isometrisk inn som et lukket underrom av et
       refleksivt rom, er refleksivt.
-/
import CausalPhys.LpReflexive
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Uniform
import Mathlib.Analysis.Normed.Module.HahnBanach

set_option linter.unusedSectionVars false

open Metric


namespace CausalPhys
namespace Reflexivity

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

instance instLCS (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    LocallyConvexSpace ℝ (WeakDual ℝ E) :=
  inferInstanceAs (LocallyConvexSpace ℝ (WeakBilin (topDualPairing ℝ E)))

/-- J : X → X** som avbildning inn i den svake*-topologien. -/
noncomputable def Jw (x : X) : WeakDual ℝ (StrongDual ℝ X) :=
  StrongDual.toWeakDual (NormedSpace.inclusionInDoubleDual ℝ X x)

theorem Jw_apply (x : X) (g : StrongDual ℝ X) : Jw x g = g x := rfl

theorem norm_J (x : X) : ‖NormedSpace.inclusionInDoubleDual ℝ X x‖ = ‖x‖ :=
  (NormedSpace.inclusionInDoubleDualLi ℝ (E := X)).norm_map x

/-! ## 1. Goldstine -/

theorem goldstine (Φ : StrongDual ℝ (StrongDual ℝ X)) (hΦ : ‖Φ‖ ≤ 1) :
    StrongDual.toWeakDual Φ ∈ closure (Jw '' closedBall (0 : X) 1) := by
  by_contra hno
  set S := Jw '' closedBall (0 : X) 1 with hS
  have hconvS : Convex ℝ S := by
    have hlin : (Jw : X → WeakDual ℝ (StrongDual ℝ X)) =
        ⇑((StrongDual.toWeakDual (𝕜 := ℝ) (E := StrongDual ℝ X)).toLinearMap.comp
          (NormedSpace.inclusionInDoubleDual ℝ X).toLinearMap) := rfl
    rw [hS, hlin]
    exact (convex_closedBall (0 : X) 1).linear_image _
  obtain ⟨f, u, hf, hu⟩ := geometric_hahn_banach_closed_point hconvS.closure isClosed_closure hno
  obtain ⟨g, hg⟩ := LinearMap.dualEmbedding_surjective (𝕜 := ℝ) (topDualPairing ℝ (StrongDual ℝ X))
    ⟨⟨⟨fun Ψ => f Ψ, fun a b => by exact f.map_add a b⟩, fun c a => by exact f.map_smul c a⟩,
      by exact f.continuous⟩
  have hfeval : ∀ Ψ : WeakDual ℝ (StrongDual ℝ X), f Ψ = Ψ g := fun Ψ => by
    have := congrArg (fun T => T Ψ) hg
    exact this.symm
  have hgx : ∀ x : X, ‖x‖ ≤ 1 → g x < u := fun x hx => by
    have := hf _ (subset_closure ⟨x, mem_closedBall_zero_iff.2 hx, rfl⟩)
    rwa [hfeval] at this
  have hu0 : 0 < u := by simpa using hgx 0 (by simp)
  have hgnorm : ‖g‖ ≤ u := by
    refine ContinuousLinearMap.opNorm_le_bound _ hu0.le fun x => ?_
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
      have h1 := hgx (‖x‖⁻¹ • x) (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne'])
      have h2 := hgx (-(‖x‖⁻¹ • x)) (by rw [norm_neg, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ hn.ne'])
      rw [map_smul, smul_eq_mul] at h1
      rw [map_neg, map_smul, smul_eq_mul] at h2
      rw [Real.norm_eq_abs, abs_le]
      have hx' : 0 < ‖x‖⁻¹ := inv_pos.2 hn
      constructor
      · have : -(u * ‖x‖) < g x := by
          have := mul_lt_mul_of_pos_left h2 hn
          field_simp at this
          linarith
        linarith
      · have := mul_lt_mul_of_pos_left h1 hn
        field_simp at this
        linarith
  rw [hfeval] at hu
  have h3 : Φ g ≤ ‖g‖ := by
    calc Φ g ≤ |Φ g| := le_abs_self _
      _ = ‖Φ g‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖Φ‖ * ‖g‖ := Φ.le_opNorm g
      _ ≤ 1 * ‖g‖ := mul_le_mul_of_nonneg_right hΦ (norm_nonneg _)
      _ = ‖g‖ := one_mul _
  change u < Φ g at hu
  linarith

/-! ## 2. Milman–Pettis -/

theorem range_J_closed [CompleteSpace X] :
    IsClosed (Set.range (NormedSpace.inclusionInDoubleDual ℝ X)) := by
  have hiso : Isometry (NormedSpace.inclusionInDoubleDual ℝ X) :=
    (NormedSpace.inclusionInDoubleDualLi ℝ (E := X)).isometry
  exact (hiso.isUniformInducing.isComplete_range).isClosed

/-- **Milman–Pettis**: et uniformt konvekst Banach-rom er refleksivt. -/
theorem milman_pettis [CompleteSpace X] [UniformConvexSpace X] :
    Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ X) := by
  have key : ∀ Φ : StrongDual ℝ (StrongDual ℝ X), ‖Φ‖ = 1 → ∀ ε > 0,
      ∃ x : X, ‖Φ - NormedSpace.inclusionInDoubleDual ℝ X x‖ ≤ ε := by
    intro Φ hΦ ε hε
    obtain ⟨δ, hδ, hUC⟩ := exists_forall_closed_ball_dist_add_le_two_sub X hε
    -- et funksjonal g med ‖g‖ ≤ 1 og Φ g > 1 − δ/4
    obtain ⟨g, hg1, hgΦ⟩ : ∃ g : StrongDual ℝ X, ‖g‖ ≤ 1 ∧ 1 - δ / 4 < Φ g := by
      obtain ⟨g, hg, hr⟩ := Φ.exists_lt_apply_of_lt_opNorm (r := 1 - δ / 4) (by rw [hΦ]; linarith)
      rw [Real.norm_eq_abs] at hr
      rcases le_or_gt 0 (Φ g) with h | h
      · exact ⟨g, hg.le, by rwa [abs_of_nonneg h] at hr⟩
      · refine ⟨-g, by rw [norm_neg]; exact hg.le, ?_⟩
        rw [map_neg]; rw [abs_of_neg h] at hr; exact hr
    set N : Set (WeakDual ℝ (StrongDual ℝ X)) := {Ψ | |Ψ g - Φ g| < δ / 4} with hN
    have hNo : IsOpen N :=
      isOpen_lt (((WeakDual.eval_continuous g).sub continuous_const).abs) continuous_const
    have hΦN : StrongDual.toWeakDual Φ ∈ N := by
      show |Φ g - Φ g| < δ / 4
      simp; positivity
    have hgold := goldstine Φ hΦ.le
    rw [_root_.mem_closure_iff] at hgold
    obtain ⟨_, hy0N, ⟨x0, hx0, rfl⟩⟩ := hgold N hNo hΦN
    have hx0' : ‖x0‖ ≤ 1 := mem_closedBall_zero_iff.1 hx0
    have hgx0 : 1 - δ / 2 < g x0 := by
      have : |g x0 - Φ g| < δ / 4 := hy0N
      have := (abs_lt.1 this).1
      linarith
    refine ⟨x0, ?_⟩
    by_contra hfar
    push Not at hfar
    set D : Set (WeakDual ℝ (StrongDual ℝ X)) :=
      WeakDual.toStrongDual ⁻¹' closedBall (NormedSpace.inclusionInDoubleDual ℝ X x0) ε
    have hDc : IsClosed D := WeakDual.isClosed_closedBall _ _
    have hΦD : StrongDual.toWeakDual Φ ∉ D := by
      intro h
      have : dist Φ (NormedSpace.inclusionInDoubleDual ℝ X x0) ≤ ε := h
      rw [dist_eq_norm (E := StrongDual ℝ (StrongDual ℝ X))] at this
      linarith
    obtain ⟨_, ⟨hyD, hyN⟩, ⟨x, hx, rfl⟩⟩ :=
      _root_.mem_closure_iff.1 (goldstine Φ hΦ.le) (Dᶜ ∩ N) (hDc.isOpen_compl.inter hNo) ⟨hΦD, hΦN⟩
    have hx' : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.1 hx
    have hgx : 1 - δ / 2 < g x := by
      have : |g x - Φ g| < δ / 4 := hyN
      have := (abs_lt.1 this).1
      linarith
    have hsep : ε ≤ ‖x - x0‖ := by
      have : ¬ dist (NormedSpace.inclusionInDoubleDual ℝ X x)
          (NormedSpace.inclusionInDoubleDual ℝ X x0) ≤ ε := hyD
      rw [dist_eq_norm (E := StrongDual ℝ (StrongDual ℝ X)),
        show NormedSpace.inclusionInDoubleDual ℝ X x - NormedSpace.inclusionInDoubleDual ℝ X x0
          = NormedSpace.inclusionInDoubleDual ℝ X (x - x0) from (map_sub _ _ _).symm, norm_J] at this
      linarith
    have h1 := hUC hx' hx0' hsep
    have h2 : g (x + x0) ≤ ‖x + x0‖ := by
      calc g (x + x0) ≤ |g (x + x0)| := le_abs_self _
        _ = ‖g (x + x0)‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖g‖ * ‖x + x0‖ := g.le_opNorm _
        _ ≤ 1 * ‖x + x0‖ := mul_le_mul_of_nonneg_right hg1 (norm_nonneg _)
        _ = ‖x + x0‖ := one_mul _
    rw [map_add] at h2
    linarith
  intro Φ
  rcases eq_or_ne Φ 0 with h0 | h0
  · exact ⟨0, by rw [h0, map_zero]⟩
  have hn : 0 < ‖Φ‖ := norm_pos_iff (E := StrongDual ℝ (StrongDual ℝ X)) |>.2 h0
  set Φ1 := ‖Φ‖⁻¹ • Φ with hΦ1
  have hΦ1n : ‖Φ1‖ = 1 := by
    have h1 : ‖Φ1‖ ≤ ‖Φ‖⁻¹ * ‖Φ‖ := by
      have := ContinuousLinearMap.opNorm_smul_le (‖Φ‖⁻¹) Φ
      rwa [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hn)] at this
    have h2 : ‖Φ‖ ≤ ‖Φ‖ * ‖Φ1‖ := by
      have := ContinuousLinearMap.opNorm_smul_le (‖Φ‖) Φ1
      rw [Real.norm_eq_abs, abs_of_pos hn, hΦ1, smul_inv_smul₀ hn.ne'] at this
      exact this
    rw [inv_mul_cancel₀ hn.ne'] at h1
    have : 1 ≤ ‖Φ1‖ := by
      by_contra hc; push Not at hc; nlinarith
    linarith
  have hmem : Φ1 ∈ closure (Set.range (NormedSpace.inclusionInDoubleDual ℝ X)) := by
    rw [Metric.mem_closure_iff (α := StrongDual ℝ (StrongDual ℝ X))]
    intro ε hε
    obtain ⟨x, hx⟩ := key Φ1 hΦ1n (ε / 2) (by positivity)
    exact ⟨_, ⟨x, rfl⟩, by rw [dist_eq_norm (E := StrongDual ℝ (StrongDual ℝ X))]; linarith⟩
  rw [range_J_closed.closure_eq] at hmem
  obtain ⟨x, hx⟩ := hmem
  refine ⟨‖Φ‖ • x, ?_⟩
  rw [map_smul, hx, hΦ1, smul_inv_smul₀ hn.ne']

/-! ## 3. Dualrommet til et refleksivt rom -/

theorem dual_reflexive (h : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ X)) :
    Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ (StrongDual ℝ X)) := by
  intro Ψ
  refine ⟨Ψ.comp (NormedSpace.inclusionInDoubleDual ℝ X), ?_⟩
  ext Φ
  obtain ⟨x, rfl⟩ := h Φ
  rfl

/-! ## 4. Lukkede isometriske underrom -/

theorem reflexive_of_isometry {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (e : Y →ₗᵢ[ℝ] X) (hcl : IsClosed (Set.range e))
    (hX : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ X)) :
    Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ Y) := by
  intro Φ
  -- restriksjon X* → Y*
  let R : StrongDual ℝ X →L[ℝ] StrongDual ℝ Y :=
    (ContinuousLinearMap.compL ℝ Y X ℝ).flip e.toContinuousLinearMap
  have hR : ∀ f y, R f y = f (e y) := fun f y => rfl
  obtain ⟨x, hx⟩ := hX (Φ.comp R)
  have hxf : ∀ f : StrongDual ℝ X, f x = Φ (R f) := fun f => by
    have := congrArg (fun T => T f) hx
    simpa using this
  -- x ligger i bildet av e
  have hxr : x ∈ Set.range e := by
    by_contra hno
    have hconv : Convex ℝ (Set.range e) := by
      have := (convex_univ : Convex ℝ (Set.univ : Set Y)).linear_image e.toLinearMap
      simpa using this
    obtain ⟨f, u, hf, hu⟩ := geometric_hahn_banach_closed_point hconv hcl hno
    have hzero : ∀ y, f (e y) = 0 := by
      intro y
      by_contra hne
      have h1 := hf (e (((u + 1) / f (e y)) • y)) ⟨_, rfl⟩
      rw [map_smul, map_smul, smul_eq_mul, div_mul_cancel₀ _ hne] at h1
      linarith
    have hu0 : 0 < u := by
      have := hf (e 0) ⟨0, rfl⟩
      rw [map_zero, map_zero] at this
      exact this
    have hRf : R f = 0 := by ext y; rw [hR, hzero]; rfl
    have := hxf f
    rw [hRf, map_zero] at this
    linarith
  obtain ⟨y, rfl⟩ := hxr
  refine ⟨y, ?_⟩
  ext h
  rw [NormedSpace.dual_def]
  -- utvid h fra bildet av e til hele X (Hahn–Banach)
  let p : Subspace ℝ X := LinearMap.range e.toLinearMap
  let eq : Y ≃ₗ[ℝ] p := LinearEquiv.ofInjective e.toLinearMap e.injective
  have heq : ∀ z : Y, (eq z : X) = e z := fun z => rfl
  let hp : StrongDual ℝ p := LinearMap.mkContinuous (h.toLinearMap.comp eq.symm.toLinearMap) ‖h‖
    (fun z => by
      simp only [LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe,
        LinearEquiv.coe_coe]
      calc ‖h (eq.symm z)‖ ≤ ‖h‖ * ‖eq.symm z‖ := h.le_opNorm _
        _ = ‖h‖ * ‖z‖ := by
          congr 1
          have : (z : X) = e (eq.symm z) := by rw [← heq, LinearEquiv.apply_symm_apply]
          rw [Submodule.coe_norm, this, LinearIsometry.norm_map])
  obtain ⟨f, hf, -⟩ := exists_extension_norm_eq p hp
  have hRf : R f = h := by
    ext z
    rw [hR]
    have := hf (eq z)
    rw [heq] at this
    rw [this]
    simp [hp]
  rw [← hRf, ← hxf, hR]

end Reflexivity
end CausalPhys
