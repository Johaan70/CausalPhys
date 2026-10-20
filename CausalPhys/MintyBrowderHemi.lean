/-
  CausalPhys.MintyBrowderHemi — Minty–Browder med HEMIkontinuitet.

  Den klassiske formuleringen krever bare at F er hemikontinuerlig:
    t ↦ (F (x + t w)) z er kontinuerlig for alle x, w, z.
  Kontinuitet ble brukt ett sted i det forrige beviset: Galerkin-trinnet
  brukte Brouwer på en avbildning bygd av F. Her erstattes det med KKM:

    1. KKM-lemmaet (Knaster–Kuratowski–Mazurkiewicz) for et endelig antall
       punkter, bevist fra Brouwer på simplekset via en partisjon av enheten.
    2. Monotonitet alene gjør y ↦ {x : (F y − b)(y − x) ≥ 0} til en KKM-
       avbildning (dobbelsum-argumentet). Ingen kontinuitet trengs.
    3. Endelig snitt-egenskapen på den kompakte kula i V gir en løsning av
       Mintys variasjonsulikhet; hemikontinuitet gjør den til en løsning av
       Stampacchias; koersivitet utelukker randen. Dette er Galerkin-trinnet.
    4. Resten (Banach–Alaoglu, refleksivitet, Mintys triks) som før, men
       Mintys triks bruker bare hemikontinuitet.

  Dermed: monoton + hemikontinuerlig + koersiv ⇒ surjektiv, i refleksive
  Banach-rom og (som korollar) i Hilbert-rom.

  Lemmaet «monoton og hemikontinuerlig ⇒ demikontinuerlig» trengs dermed
  ikke: KKM-ruten omgår det.
-/
import CausalPhys.MintyBrowderBanach

set_option linter.unusedSectionVars false

open RealInnerProductSpace Filter Topology

namespace CausalPhys
namespace MintyBrowderHemi

/-! ## 1. KKM-lemmaet -/

/-- **KKM** for endelig mange punkter. Hvis hvert punkt Σ λⱼ yⱼ i simplekset
    ligger i en mengde C k med λ k > 0, har alle C k et felles punkt av den
    formen. -/
theorem kkm {ι X : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (y : ι → X) (C : ι → Set X) (hC : ∀ k, IsClosed (C k))
    (hkkm : ∀ lam : ι → ℝ, (∀ i, 0 ≤ lam i) → ∑ i, lam i = 1 →
      ∃ k, 0 < lam k ∧ ∑ j, lam j • y j ∈ C k) :
    ∃ lam : ι → ℝ, (∀ i, 0 ≤ lam i) ∧ ∑ i, lam i = 1 ∧ ∀ k, ∑ j, lam j • y j ∈ C k := by
  by_contra hno
  push Not at hno
  let Δ : Set (EuclideanSpace ℝ ι) := {μ | (∀ i, 0 ≤ μ i) ∧ ∑ i, μ i = 1}
  have hΔc : IsCompact Δ := by
    apply Metric.isCompact_of_isClosed_isBounded
    · have h1 : IsClosed {μ : (EuclideanSpace ℝ ι) | ∀ i, 0 ≤ μ i} := by
        simp only [Set.ofPred_forall]
        exact isClosed_iInter fun i => isClosed_le continuous_const (PiLp.continuous_apply 2 _ i)
      have h2 : IsClosed {μ : (EuclideanSpace ℝ ι) | ∑ i, μ i = 1} :=
        isClosed_eq (by fun_prop) continuous_const
      exact h1.inter h2
    · refine (Metric.isBounded_closedBall (x := (0 : (EuclideanSpace ℝ ι))) (r := 1)).subset fun μ hμ => ?_
      rw [mem_closedBall_zero_iff]
      have hle : ∀ i, μ i ≤ 1 := fun i => by
        have := Finset.single_le_sum (f := fun i => μ i) (fun j _ => hμ.1 j) (Finset.mem_univ i)
        rw [hμ.2] at this; exact this
      have hsq : ‖μ‖ ^ 2 ≤ 1 := by
        rw [EuclideanSpace.real_norm_sq_eq, ← hμ.2]
        exact Finset.sum_le_sum fun i _ => by nlinarith [hμ.1 i, hle i]
      nlinarith [norm_nonneg μ]
  have hΔconv : Convex ℝ Δ := by
    intro μ hμ ν hν a b ha hb hab
    refine ⟨fun i => ?_, ?_⟩
    · simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := hμ.1 i; have := hν.1 i; positivity
    · simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [hμ.2, hν.2]; linarith
  have hΔne : Δ.Nonempty := by
    refine ⟨WithLp.toLp 2 (fun _ => 1 / (Fintype.card ι : ℝ)), fun i => by simp, ?_⟩
    simp only [PiLp.toLp_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    field_simp
  let ψ : (EuclideanSpace ℝ ι) → X := fun μ => ∑ j, μ j • y j
  have hψc : Continuous ψ := by
    simp only [ψ]; fun_prop
  let C' : ι → Set (EuclideanSpace ℝ ι) := fun k => ψ ⁻¹' C k
  have hC'c : ∀ k, IsClosed (C' k) := fun k => (hC k).preimage hψc
  -- hjørnene ligger i sine mengder, så C' k er ikke-tom
  have hC'ne : ∀ k, (C' k).Nonempty := by
    intro k
    refine ⟨WithLp.toLp 2 (Pi.single k 1), ?_⟩
    obtain ⟨k', hk', hmem⟩ := hkkm (fun i => (WithLp.toLp 2 (Pi.single k (1:ℝ)) : (EuclideanSpace ℝ ι)) i)
      (fun i => by simp only [PiLp.toLp_apply, Pi.single_apply]; split_ifs <;> norm_num)
      (by simp)
    have : k' = k := by
      by_contra hne
      simp [Pi.single_apply, hne] at hk'
    subst this
    exact hmem
  -- partisjon av enheten
  let d : ι → (EuclideanSpace ℝ ι) → ℝ := fun k μ => Metric.infDist μ (C' k)
  have hdc : ∀ k, Continuous (d k) := fun k => Metric.continuous_infDist_pt _
  have hd0 : ∀ k μ, 0 ≤ d k μ := fun k μ => Metric.infDist_nonneg
  have hdpos : ∀ k μ, μ ∉ C' k → 0 < d k μ := fun k μ h =>
    ((hC'c k).notMem_iff_infDist_pos (hC'ne k)).1 h
  let s : (EuclideanSpace ℝ ι) → ℝ := fun μ => ∑ k, d k μ
  have hspos : ∀ μ ∈ Δ, 0 < s μ := by
    intro μ hμ
    obtain ⟨k, hk⟩ := hno (fun i => μ i) hμ.1 hμ.2
    exact lt_of_lt_of_le (hdpos k μ hk)
      (Finset.single_le_sum (f := fun k => d k μ) (fun j _ => hd0 j μ) (Finset.mem_univ k))
  let f : (EuclideanSpace ℝ ι) → (EuclideanSpace ℝ ι) := fun μ => WithLp.toLp 2 (fun k => d k μ / s μ)
  have hfc : ContinuousOn f Δ := by
    refine (PiLp.continuous_toLp 2 _).comp_continuousOn (continuousOn_pi.2 fun k => ?_)
    have hsc : Continuous s := by simp only [s]; fun_prop
    exact (hdc k).continuousOn.div hsc.continuousOn
      (fun μ hμ => (hspos μ hμ).ne')
  have hfmap : Set.MapsTo f Δ Δ := by
    intro μ hμ
    refine ⟨fun k => div_nonneg (hd0 k μ) (hspos μ hμ).le, ?_⟩
    simp only [f, PiLp.toLp_apply]
    rw [← Finset.sum_div]
    exact div_self (hspos μ hμ).ne'
  obtain ⟨μ, hμ, hfix⟩ := MintyBrowder.brouwer_convex hΔc hΔconv hΔne f hfc hfmap
  obtain ⟨k, hk, hmem⟩ := hkkm (fun i => μ i) hμ.1 hμ.2
  have hμk : μ k = d k μ / s μ := by
    have := congrArg (fun z : (EuclideanSpace ℝ ι) => z k) hfix
    simp only [f, PiLp.toLp_apply] at this
    exact this.symm
  have hdk : 0 < d k μ := by
    rw [hμk] at hk
    exact (div_pos_iff_of_pos_right (hspos μ hμ)).1 hk
  have : μ ∈ C' k := hmem
  have := ((hC'c k).mem_iff_infDist_zero (hC'ne k)).1 this
  simp only [d] at hdk
  linarith

/-! ## 2. Monotonitet gir KKM-egenskapen -/

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem kkm_of_mono (F : X → StrongDual ℝ X) (hmono : ∀ x y, 0 ≤ (F x - F y) (x - y))
    (b : StrongDual ℝ X) {ι : Type*} [Fintype ι] (y : ι → X) (lam : ι → ℝ)
    (h0 : ∀ i, 0 ≤ lam i) (h1 : ∑ i, lam i = 1) :
    ∃ k, 0 < lam k ∧ ∑ j, lam j • y j ∈ {x | 0 ≤ (F (y k) - b) (y k - x)} := by
  by_contra hcon
  push Not at hcon
  simp only [Set.mem_ofPred_eq, not_le] at hcon
  set x := ∑ j, lam j • y j
  let a : ι → ι → ℝ := fun k j => (F (y k) - b) (y k - y j)
  have e1 : ∀ k, (F (y k) - b) (y k - x) = ∑ j, lam j * a k j := by
    intro k
    have : y k - x = ∑ j, lam j • (y k - y j) := by
      simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, h1, one_smul, x]
    rw [this, map_sum]
    simp only [map_smul, smul_eq_mul, a]
  -- S < 0
  obtain ⟨k0, hk0⟩ : ∃ k, 0 < lam k := by
    by_contra h
    push Not at h
    have : ∑ i, lam i ≤ 0 := Finset.sum_nonpos fun i _ => h i
    linarith
  have hS : ∑ k, lam k * (F (y k) - b) (y k - x) < ∑ _k : ι, (0 : ℝ) := by
    apply Finset.sum_lt_sum
    · intro k _
      rcases (h0 k).lt_or_eq with hpos | hzero
      · exact (mul_neg_of_pos_of_neg hpos (hcon k hpos)).le
      · rw [← hzero, zero_mul]
    · exact ⟨k0, Finset.mem_univ _, mul_neg_of_pos_of_neg hk0 (hcon k0 hk0)⟩
  -- S ≥ 0 ved symmetrisering
  have hsym : ∀ k j, 0 ≤ a k j + a j k := by
    intro k j
    have := hmono (y k) (y j)
    have e : a k j + a j k = (F (y k) - F (y j)) (y k - y j) := by
      simp only [a, ContinuousLinearMap.sub_apply, map_sub]
      ring
    rw [e]; exact this
  have hS' : 0 ≤ ∑ k, lam k * (F (y k) - b) (y k - x) := by
    simp only [e1, Finset.mul_sum]
    have h2 : 2 * ∑ k, ∑ j, lam k * (lam j * a k j)
        = ∑ k, ∑ j, lam k * lam j * (a k j + a j k) := by
      rw [two_mul]
      conv_lhs => arg 2; rw [Finset.sum_comm]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have h3 : 0 ≤ ∑ k, ∑ j, lam k * lam j * (a k j + a j k) :=
      Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun j _ =>
        mul_nonneg (mul_nonneg (h0 k) (h0 j)) (hsym k j)
    linarith
  rw [Finset.sum_const_zero] at hS
  linarith

/-! ## 3. Galerkin med hemikontinuitet -/

/-- Hemikontinuitet: kontinuitet langs linjer, testet mot hver vektor. -/
def Hemicontinuous (F : X → StrongDual ℝ X) : Prop :=
  ∀ x w z : X, Continuous fun t : ℝ => F (x + t • w) z

theorem galerkin (F : X → StrongDual ℝ X) (hhemi : Hemicontinuous F)
    (hmono : ∀ x y, 0 ≤ (F x - F y) (x - y)) (b : StrongDual ℝ X) {R : ℝ}
    (hR : 0 < R) (hstrict : ∀ x, ‖x‖ = R → 0 < (F x - b) x)
    (V : Submodule ℝ X) [FiniteDimensional ℝ V] :
    ∃ v ∈ V, ‖v‖ ≤ R ∧ ∀ w ∈ V, (F v - b) w = 0 := by
  classical
  set KV : Set X := V.subtype '' Metric.closedBall (0 : V) R with hKVdef
  have hKVc : IsCompact KV := (isCompact_closedBall (0 : V) R).image continuous_subtype_val
  have hKVconv : Convex ℝ KV := (convex_closedBall (0 : V) R).linear_image V.subtype
  have hmemKV : ∀ x, x ∈ KV ↔ x ∈ V ∧ ‖x‖ ≤ R := by
    intro x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u.2, by simpa using mem_closedBall_zero_iff.1 hu⟩
    · rintro ⟨hxV, hx⟩
      exact ⟨⟨x, hxV⟩, mem_closedBall_zero_iff.2 (by simpa using hx), rfl⟩
  let D : KV → Set X := fun y => {x | 0 ≤ (F y - b) (y - x)}
  have hDc : ∀ y, IsClosed (D y) := fun y =>
    isClosed_le continuous_const ((F y - b).continuous.comp (continuous_const.sub continuous_id))
  -- endelig snitt-egenskapen via KKM
  have hfip : ∀ u : Finset KV, (KV ∩ ⋂ y ∈ u, D y).Nonempty := by
    intro u
    rcases u.eq_empty_or_nonempty with hu | hu
    · refine ⟨0, (hmemKV 0).2 ⟨V.zero_mem, by simp [hR.le]⟩, ?_⟩
      simp [hu]
    · have : Nonempty u := ⟨⟨hu.choose, hu.choose_spec⟩⟩
      let yy : u → X := fun i => (i.1 : X)
      obtain ⟨lam, h0, h1, hall⟩ := kkm yy (fun k => D k.1) (fun k => hDc _)
        (fun lam h0 h1 => kkm_of_mono F hmono b yy lam h0 h1)
      refine ⟨∑ j, lam j • yy j, ?_, ?_⟩
      · exact hKVconv.sum_mem (fun i _ => h0 i) h1 (fun i _ => (i.1).2)
      · simp only [Set.mem_iInter]
        intro y hy
        exact hall ⟨y, hy⟩
  obtain ⟨x, hxK, hx⟩ := hKVc.inter_iInter_nonempty D hDc hfip
  have hminty : ∀ y ∈ KV, 0 ≤ (F y - b) (y - x) := fun y hy => Set.mem_iInter.1 hx ⟨y, hy⟩
  -- Mintys ulikhet ⇒ Stampacchias ulikhet (hemikontinuitet)
  have hstamp : ∀ u ∈ KV, 0 ≤ (F x - b) (u - x) := by
    intro u hu
    have hcont : Continuous (fun t : ℝ => (F (x + t • (u - x)) - b) (u - x)) := by
      exact (hhemi x (u - x) (u - x)).sub continuous_const
    have hlim : Tendsto (fun t : ℝ => (F (x + t • (u - x)) - b) (u - x)) (𝓝[>] 0)
        (𝓝 ((F x - b) (u - x))) := by
      have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      simpa using this
    apply ge_of_tendsto hlim
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
      nhdsWithin_le_nhds (Iio_mem_nhds one_pos)
    filter_upwards [self_mem_nhdsWithin, hev] with t ht ht1
    have ht0 : 0 < t := ht
    have hyt : x + t • (u - x) ∈ KV := by
      have := hKVconv.add_smul_sub_mem hxK hu ⟨ht0.le, ht1.le⟩
      simpa using this
    have h1 := hminty _ hyt
    rw [add_sub_cancel_left, map_smul, smul_eq_mul] at h1
    nlinarith
  -- tilbake til V
  obtain ⟨hxV, hxR⟩ := (hmemKV x).1 hxK
  have hvi' : ∀ u ∈ V, ‖u‖ ≤ R → 0 ≤ (F x - b) (u - x) := fun u huV hu =>
    hstamp u ((hmemKV u).2 ⟨huV, hu⟩)
  refine ⟨x, hxV, hxR, fun w hw => ?_⟩
  rcases hxR.lt_or_eq with hlt | heq
  · set ε := (R - ‖x‖) / (‖w‖ + 1) with hε
    have hε0 : 0 < ε := div_pos (by linarith) (by positivity)
    have hεw : ε * ‖w‖ < R - ‖x‖ := by
      rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg w]
    have hp := hvi' (x + ε • w) (V.add_mem hxV (V.smul_mem ε hw)) (by
      calc ‖x + ε • w‖ ≤ ‖x‖ + ‖ε • w‖ := norm_add_le _ _
        _ = ‖x‖ + ε * ‖w‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε0]
        _ ≤ R := by linarith)
    have hm := hvi' (x - ε • w) (V.sub_mem hxV (V.smul_mem ε hw)) (by
      calc ‖x - ε • w‖ ≤ ‖x‖ + ‖ε • w‖ := norm_sub_le _ _
        _ = ‖x‖ + ε * ‖w‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε0]
        _ ≤ R := by linarith)
    simp only [add_sub_cancel_left, sub_sub_cancel_left, map_neg, map_smul, smul_eq_mul] at hp hm
    have h1 : 0 ≤ (F x - b) w := by
      by_contra hc; push Not at hc; nlinarith
    have h2 : (F x - b) w ≤ 0 := by
      by_contra hc; push Not at hc; nlinarith
    linarith
  · exfalso
    have h0 := hvi' 0 V.zero_mem (by simp [hR.le])
    simp only [zero_sub, map_neg] at h0
    have := hstrict x heq
    linarith

/-! ## 4. Hovedteoremet -/

/-- Mintys triks med bare hemikontinuitet. -/
theorem minty_iff (F : X → StrongDual ℝ X) (hhemi : Hemicontinuous F)
    (hmono : ∀ x y, 0 ≤ (F x - F y) (x - y)) (b : StrongDual ℝ X) (x : X) :
    F x = b ↔ ∀ y, 0 ≤ (F y - b) (y - x) := by
  constructor
  · intro h y; rw [← h]; exact hmono y x
  · intro h
    have hw : ∀ w, 0 ≤ (F x - b) w := by
      intro w
      have hcont : Continuous (fun t : ℝ => (F (x + t • w) - b) w) := by
        exact (hhemi x w w).sub continuous_const
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
    rw [ContinuousLinearMap.sub_apply] at this
    linarith

/-- **Minty–Browder** i refleksive Banach-rom: monoton, hemikontinuerlig og
    koersiv ⇒ surjektiv. -/
theorem surjective (hrefl : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ X))
    (F : X → StrongDual ℝ X) (hhemi : Hemicontinuous F)
    (hmono : ∀ x y, 0 ≤ (F x - F y) (x - y)) (hcoer : MintyBrowderBanach.Coercive F) :
    Function.Surjective F := by
  intro b
  obtain ⟨R, hR, hRc⟩ := hcoer (‖b‖ + 1)
  have hstrict : ∀ x, ‖x‖ = R → 0 < (F x - b) x := by
    intro x hx
    have h1 := hRc x hx.ge
    have h2 : b x ≤ ‖b‖ * ‖x‖ := (le_abs_self _).trans (b.le_opNorm x)
    rw [ContinuousLinearMap.sub_apply]
    rw [hx] at h1 h2
    nlinarith
  set K : Set (WeakDual ℝ (StrongDual ℝ X)) :=
    WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ (StrongDual ℝ X)) R
  have hKc : IsCompact K := WeakDual.isCompact_closedBall 0 R
  let C : X → Set (WeakDual ℝ (StrongDual ℝ X)) := fun y => {Φ | Φ (F y - b) ≤ (F y - b) y}
  have hCc : ∀ y, IsClosed (C y) := fun y =>
    isClosed_le (WeakDual.eval_continuous (F y - b)) continuous_const
  have hfip : ∀ u : Finset X, (K ∩ ⋂ y ∈ u, C y).Nonempty := by
    intro u
    set V := Submodule.span ℝ (u : Set X)
    obtain ⟨v, hvV, hvR, hvperp⟩ := galerkin F hhemi hmono b hR hstrict V
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
        simp only [ContinuousLinearMap.sub_apply]; ring
      rw [map_sub] at e
      linarith
  obtain ⟨Φ, -, hΦ⟩ := hKc.inter_iInter_nonempty C hCc hfip
  obtain ⟨x, hx⟩ := hrefl (WeakDual.toStrongDual Φ)
  have hxΦ : ∀ f : StrongDual ℝ X, f x = Φ f := by
    intro f
    have := congrArg (fun T : StrongDual ℝ (StrongDual ℝ X) => T f) hx
    simpa using this
  refine ⟨x, (minty_iff F hhemi hmono b x).2 fun y => ?_⟩
  have := Set.mem_iInter.1 hΦ y
  change Φ (F y - b) ≤ (F y - b) y at this
  rw [← hxΦ] at this
  rw [map_sub]
  linarith

/-! ## 5. Hilbert-rom som korollar -/

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Hilbert-rom er refleksive (Riesz to ganger). -/
theorem hilbert_reflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ H) := by
  intro Φ
  let f : StrongDual ℝ H := Φ.comp (InnerProductSpace.toDual ℝ H).toContinuousLinearEquiv.toContinuousLinearMap
  refine ⟨(InnerProductSpace.toDual ℝ H).symm f, ?_⟩
  refine ContinuousLinearMap.ext fun φ => ?_
  rw [NormedSpace.dual_def]
  set z := (InnerProductSpace.toDual ℝ H).symm φ with hz
  have hφ : φ = InnerProductSpace.toDual ℝ H z := by simp [hz]
  calc φ ((InnerProductSpace.toDual ℝ H).symm f)
      = InnerProductSpace.toDual ℝ H z ((InnerProductSpace.toDual ℝ H).symm f) := by
        conv_lhs => rw [hφ]
    _ = ⟪z, (InnerProductSpace.toDual ℝ H).symm f⟫ := InnerProductSpace.toDual_apply_apply
    _ = ⟪(InnerProductSpace.toDual ℝ H).symm f, z⟫ := real_inner_comm _ _
    _ = f z := InnerProductSpace.toDual_symm_apply
    _ = Φ (InnerProductSpace.toDual ℝ H z) := rfl
    _ = Φ φ := by rw [← hφ]

/-- **Minty–Browder i Hilbert-rom** med hemikontinuitet. -/
theorem hilbert_surjective (F : H → H)
    (hhemi : ∀ x w z : H, Continuous fun t : ℝ => ⟪F (x + t • w), z⟫)
    (hmono : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫) (hcoer : MintyBrowderHilbert.Coercive F) :
    Function.Surjective F := by
  let T := InnerProductSpace.toDual ℝ H
  let G : H → StrongDual ℝ H := fun x => T (F x)
  have hG : ∀ x z, G x z = ⟪F x, z⟫ := fun x z => InnerProductSpace.toDual_apply_apply
  have hsurj := surjective hilbert_reflexive G
    (fun x w z => by simpa only [hG] using hhemi x w z)
    (fun x y => by
      have : (G x - G y) (x - y) = ⟪F x - F y, x - y⟫ := by
        simp only [ContinuousLinearMap.sub_apply, hG, inner_sub_left]
      rw [this]; exact hmono x y)
    (fun M => by
      obtain ⟨R, hR, h⟩ := hcoer M
      exact ⟨R, hR, fun x hx => by rw [hG]; exact h x hx⟩)
  intro b
  obtain ⟨x, hx⟩ := hsurj (T b)
  exact ⟨x, T.injective hx⟩

end Hilbert

end MintyBrowderHemi
end CausalPhys
