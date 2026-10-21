/-
  CausalPhys.MintyBrowderBanach — Minty–Browder i refleksive Banach-rom.

    Teorem. La X være et reelt normert rom som er refleksivt (inklusjonen
    X → X** er surjektiv), og F : X → X* kontinuerlig, monoton
      (F x − F y)(x − y) ≥ 0
    og koersiv
      (F x)(x) ≥ M‖x‖ for enhver M når ‖x‖ er stor nok.
    Da er F surjektiv: for hver b ∈ X* finnes x med F x = b. Er F strengt
    monoton, er løsningen entydig.

  Beviset:
    1. Galerkin på et endeligdimensjonalt underrom V (vilkårlig norm):
       overfør til et euklidsk rom, finn en løsning av variasjonsulikheten
       (Hartman–Stampacchia: Brouwer brukt på P_K(e − G e)), og bruk
       koersiviteten til å utelukke randen. Resultat: v ∈ V, ‖v‖ ≤ R og
       (F v − b)(w) = 0 for alle w ∈ V.
    2. Monotonitet: (F y − b)(y − v) ≥ 0 for alle y ∈ V.
    3. Svak kompakthet: kula i X** er svakt*-kompakt (Banach–Alaoglu);
       mengdene {Φ : Φ(F y − b) ≤ (F y − b)(y)} er svakt*-lukkede; endelig
       snitt-egenskapen gir Φ, og refleksiviteten gir Φ = J x.
    4. Mintys triks gir F x = b.
-/
import CausalPhysAnalysis.MintyBrowderHilbert
import Mathlib.Analysis.Normed.Module.DoubleDual

set_option linter.unusedSectionVars false

open RealInnerProductSpace Filter Topology

namespace CausalPhys
namespace MintyBrowderBanach

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Koersivitet for F : X → X*. -/
def Coercive (F : X → StrongDual ℝ X) : Prop :=
  ∀ M : ℝ, ∃ R > 0, ∀ x, R ≤ ‖x‖ → M * ‖x‖ ≤ F x x

/-- Mintys lemma for F : X → X*. -/
theorem minty_iff (F : X → StrongDual ℝ X) (hF : Continuous F)
    (hmono : ∀ x y, 0 ≤ (F x - F y) (x - y)) (b : StrongDual ℝ X) (x : X) :
    F x = b ↔ ∀ y, 0 ≤ (F y - b) (y - x) := by
  constructor
  · intro h y; rw [← h]; exact hmono y x
  · intro h
    have hw : ∀ w, 0 ≤ (F x - b) w := by
      intro w
      have hcont : Continuous (fun t : ℝ => (F (x + t • w) - b) w) :=
        (ContinuousLinearMap.apply ℝ ℝ w).continuous.comp
          ((hF.comp (continuous_const.add (continuous_id.smul continuous_const))).sub continuous_const)
      have hlim : Tendsto (fun t : ℝ => (F (x + t • w) - b) w) (𝓝[>] 0) (𝓝 ((F x - b) w)) := by
        have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
        simpa using this
      apply ge_of_tendsto hlim
      filter_upwards [self_mem_nhdsWithin] with t ht
      have h1 := h (x + t • w)
      rw [add_sub_cancel_left, map_smul, smul_eq_mul] at h1
      have ht' : 0 < t := ht
      nlinarith
    ext w
    have h1 := hw w
    have h2 := hw (-w)
    rw [map_neg] at h2
    have : (F x - b) w = 0 := by linarith
    rw [sub_apply] at this
    linarith

/-! ## 1. Galerkin-trinnet i et endeligdimensjonalt underrom -/

theorem galerkin (F : X → StrongDual ℝ X) (hF : Continuous F) (b : StrongDual ℝ X) {R : ℝ}
    (hR : 0 < R) (hstrict : ∀ x, ‖x‖ = R → 0 < (F x - b) x)
    (V : Submodule ℝ X) [FiniteDimensional ℝ V] :
    ∃ v ∈ V, ‖v‖ ≤ R ∧ ∀ w ∈ V, (F v - b) w = 0 := by
  set d := Module.finrank ℝ V
  let E := EuclideanSpace ℝ (Fin d)
  have hd : Module.finrank ℝ V = Module.finrank ℝ E := by simp [E, d]
  let ψ : V ≃L[ℝ] E := Classical.choice (FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq hd)
  -- operatoren i E
  let L : E →L[ℝ] X := V.subtypeL.comp (ψ.symm : E →L[ℝ] V)
  have hL : ∀ e, L e = (ψ.symm e : X) := fun e => rfl
  let G : E → E := fun e => (InnerProductSpace.toDual ℝ E).symm ((F (L e) - b).comp L)
  have hG : ∀ e e', ⟪G e, e'⟫ = (F (L e) - b) (L e') := fun e e' =>
    InnerProductSpace.toDual_symm_apply
  have hGc : Continuous G :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp
      (((hF.comp L.continuous).sub continuous_const).clm_comp_const L)
  -- K = ψ(kula), kompakt og konveks
  let B : Set V := Metric.closedBall 0 R
  let K : Set E := ψ '' B
  have hKc : IsCompact K := (isCompact_closedBall (0 : V) R).image ψ.continuous
  have hKconv : Convex ℝ K := (convex_closedBall (0 : V) R).linear_image (ψ : V →ₗ[ℝ] E)
  have hKne : K.Nonempty := ⟨ψ 0, 0, Metric.mem_closedBall_self hR.le, rfl⟩
  set P := MintyBrowder.proj hKne hKc.isComplete hKconv with hPdef
  have hPc : Continuous P := MintyBrowder.proj_continuous hKne hKc.isComplete hKconv
  have hPK : ∀ u, P u ∈ K := MintyBrowder.proj_mem hKne hKc.isComplete hKconv
  -- Hartman–Stampacchia via Brouwer
  obtain ⟨e, heK, he⟩ := MintyBrowder.brouwer_convex hKc hKconv hKne (fun e => P (e - G e))
    (hPc.comp (continuous_id.sub hGc)).continuousOn (fun e _ => hPK _)
  have hvi : ∀ w ∈ K, 0 ≤ ⟪G e, w - e⟫ := by
    intro w hw
    have := MintyBrowder.proj_var hKne hKc.isComplete hKconv (e - G e) w hw
    rw [← hPdef] at this
    rw [he] at this
    have e1 : e - G e - e = -G e := by abel
    rw [e1, inner_neg_left] at this
    linarith
  -- tilbake i V
  obtain ⟨v₀, hv₀B, hv₀⟩ := heK
  set v : X := (v₀ : X) with hvdef
  have hLe : L e = v := by rw [hL, ← hv₀, ContinuousLinearEquiv.symm_apply_apply]
  have hvR : ‖v‖ ≤ R := by
    have := mem_closedBall_zero_iff.1 hv₀B
    simpa [hvdef] using this
  -- (F v − b)(u − v) ≥ 0 for u ∈ V med ‖u‖ ≤ R
  have hvi' : ∀ u : V, ‖(u : X)‖ ≤ R → 0 ≤ (F v - b) ((u : X) - v) := by
    intro u hu
    have h1 := hvi (ψ u) ⟨u, mem_closedBall_zero_iff.2 (by simpa using hu), rfl⟩
    rw [hG, hLe] at h1
    have : L (ψ u - e) = (u : X) - v := by
      rw [map_sub, hL, hL, ContinuousLinearEquiv.symm_apply_apply, ← hv₀,
        ContinuousLinearEquiv.symm_apply_apply]
    rw [this] at h1
    exact h1
  refine ⟨v, v₀.2, hvR, fun w hw => ?_⟩
  rcases hvR.lt_or_eq with hlt | heq
  · -- indre punkt: begge retninger
    set ε := (R - ‖v‖) / (‖w‖ + 1) with hε
    have hε0 : 0 < ε := div_pos (by linarith) (by positivity)
    have hεw : ε * ‖w‖ < R - ‖v‖ := by
      rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg w]
    have hp := hvi' ⟨v + ε • w, V.add_mem v₀.2 (V.smul_mem ε hw)⟩ (by
      calc ‖v + ε • w‖ ≤ ‖v‖ + ‖ε • w‖ := norm_add_le _ _
        _ = ‖v‖ + ε * ‖w‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε0]
        _ ≤ R := by linarith)
    have hm := hvi' ⟨v - ε • w, V.sub_mem v₀.2 (V.smul_mem ε hw)⟩ (by
      calc ‖v - ε • w‖ ≤ ‖v‖ + ‖ε • w‖ := norm_sub_le _ _
        _ = ‖v‖ + ε * ‖w‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε0]
        _ ≤ R := by linarith)
    simp only [add_sub_cancel_left, sub_sub_cancel_left, map_neg, map_smul, smul_eq_mul] at hp hm
    have h1 : 0 ≤ (F v - b) w := by
      by_contra hc; push Not at hc; nlinarith
    have h2 : (F v - b) w ≤ 0 := by
      by_contra hc; push Not at hc; nlinarith
    linarith
  · -- randpunkt: umulig ved koersiviteten
    exfalso
    have h0 := hvi' 0 (by simp [hR.le])
    simp only [ZeroMemClass.coe_zero, zero_sub, map_neg] at h0
    have := hstrict v heq
    linarith

/-! ## 2. Hovedteoremet -/

/-- **Minty–Browder i refleksive Banach-rom.** -/
theorem surjective (hrefl : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ X))
    (F : X → StrongDual ℝ X) (hF : Continuous F) (hmono : ∀ x y, 0 ≤ (F x - F y) (x - y))
    (hcoer : Coercive F) : Function.Surjective F := by
  intro b
  obtain ⟨R, hR, hRc⟩ := hcoer (‖b‖ + 1)
  have hstrict : ∀ x, ‖x‖ = R → 0 < (F x - b) x := by
    intro x hx
    have h1 := hRc x hx.ge
    have h2 : b x ≤ ‖b‖ * ‖x‖ := (le_abs_self _).trans (b.le_opNorm x)
    rw [sub_apply]
    rw [hx] at h1 h2
    nlinarith
  -- kula i X** (svakt*-kompakt)
  set K : Set (WeakDual ℝ (StrongDual ℝ X)) :=
    WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ (StrongDual ℝ X)) R
  have hKc : IsCompact K := WeakDual.isCompact_closedBall 0 R
  let C : X → Set (WeakDual ℝ (StrongDual ℝ X)) := fun y => {Φ | Φ (F y - b) ≤ (F y - b) y}
  have hCc : ∀ y, IsClosed (C y) := fun y =>
    isClosed_le (WeakDual.eval_continuous (F y - b)) continuous_const
  have hfip : ∀ u : Finset X, (K ∩ ⋂ y ∈ u, C y).Nonempty := by
    intro u
    set V := Submodule.span ℝ (u : Set X)
    obtain ⟨v, hvV, hvR, hvperp⟩ := galerkin F hF b hR hstrict V
    refine ⟨StrongDual.toWeakDual (NormedSpace.inclusionInDoubleDual ℝ X v), ?_, ?_⟩
    · show NormedSpace.inclusionInDoubleDual ℝ X v ∈ Metric.closedBall 0 R
      rw [Metric.mem_closedBall]
      have := (NormedSpace.double_dual_bound ℝ X v).trans hvR
      rw [dist_zero_right (E := StrongDual ℝ (StrongDual ℝ X))]
      exact this
    · simp only [Set.mem_iInter]
      intro y hy
      show NormedSpace.inclusionInDoubleDual ℝ X v (F y - b) ≤ (F y - b) y
      rw [NormedSpace.dual_def]
      have hyV : y ∈ V := Submodule.subset_span hy
      have h1 := hmono y v
      have h2 := hvperp (y - v) (V.sub_mem hyV hvV)
      have e : (F y - b) (y - v) = (F y - F v) (y - v) + (F v - b) (y - v) := by
        simp only [sub_apply]; ring
      rw [map_sub] at e
      linarith
  obtain ⟨Φ, -, hΦ⟩ := hKc.inter_iInter_nonempty C hCc hfip
  obtain ⟨x, hx⟩ := hrefl (WeakDual.toStrongDual Φ)
  have hxΦ : ∀ f : StrongDual ℝ X, f x = Φ f := by
    intro f
    have := congrArg (fun T : StrongDual ℝ (StrongDual ℝ X) => T f) hx
    simpa using this
  refine ⟨x, (minty_iff F hF hmono b x).2 fun y => ?_⟩
  have := Set.mem_iInter.1 hΦ y
  change Φ (F y - b) ≤ (F y - b) y at this
  rw [← hxΦ] at this
  rw [map_sub]
  linarith

/-- Strengt monoton: nøyaktig én løsning. -/
theorem exists_unique (hrefl : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ X))
    (F : X → StrongDual ℝ X) (hF : Continuous F)
    (hmono : ∀ x y, x ≠ y → 0 < (F x - F y) (x - y)) (hcoer : Coercive F) (b : StrongDual ℝ X) :
    ∃! x, F x = b := by
  have hmono' : ∀ x y, 0 ≤ (F x - F y) (x - y) := by
    intro x y
    by_cases h : x = y
    · rw [h]; simp
    · exact (hmono x y h).le
  obtain ⟨x, hx⟩ := surjective hrefl F hF hmono' hcoer b
  refine ⟨x, hx, fun y hy => ?_⟩
  by_contra hne
  have := hmono y x hne
  rw [hy, hx, sub_self, zero_apply] at this
  exact lt_irrefl _ this

end MintyBrowderBanach
end CausalPhys
