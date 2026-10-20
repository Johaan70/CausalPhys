/-
  CausalPhys.LpReflexive — refleksivitet for konkrete Banach-rom.

  Minty–Browder-teoremene (Theorem 28–29) antar refleksivitet, det vil si at
  inklusjonen X → X** er surjektiv. Her bevises det for:

    1. ℓᵖ(α) for 1 < p < ∞, for en vilkårlig indeksmengde α.
       Nøkkelen er dualitetsteoremet (ℓᵖ)* ≅ ℓ^q: hvert kontinuerlig lineært
       funksjonal φ er gitt ved φ x = Σ xᵢ gᵢ med g ∈ ℓ^q, der
       gᵢ = φ(eᵢ). At g ∈ ℓ^q vises med testvektoren xᵢ = sign(gᵢ)|gᵢ|^{q−1}.
       Refleksiviteten følger ved å bruke dualitetsteoremet to ganger
       (for p og for q).
    2. Alle endeligdimensjonale normerte rom.

  Lᵖ(μ) over et generelt målrom er IKKE dekket; der krever dualiteten
  Radon–Nikodym-teoremet anvendt på funksjonaler, som ikke er formalisert her.
-/
import CausalPhys.MintyBrowderHemi
import Mathlib.Analysis.Normed.Lp.lpSpace

set_option linter.unusedSectionVars false

open scoped ENNReal NNReal

namespace CausalPhys
namespace LpReflexive

/-- ℓᵖ(α) med reelle koordinater. -/
abbrev L (α : Type*) (p : ℝ≥0∞) := lp (fun _ : α => ℝ) p

theorem rpow_sub_one_mul {a r : ℝ} (ha : 0 ≤ a) (hr : 1 < r) : a ^ (r - 1) * a = a ^ r := by
  rcases ha.lt_or_eq with h | h
  · rw [Real.rpow_sub_one h.ne', div_mul_cancel₀ _ h.ne']
  · subst h; rw [Real.zero_rpow (by linarith), Real.zero_rpow (by linarith), zero_mul]

variable {α : Type*} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-! ## 1. Paringen ⟨x, g⟩ = Σ xᵢ gᵢ -/

section Pairing

variable (hpq : p.toReal.HolderConjugate q.toReal)
include hpq

theorem pair_summable (x : L α p) (g : L α q) : Summable fun i => x i * g i := by
  refine Summable.of_norm ?_
  simpa [norm_mul] using lp.summable_mul hpq x g

theorem pair_bound (x : L α p) (g : L α q) : |∑' i, x i * g i| ≤ ‖x‖ * ‖g‖ := by
  rw [← Real.norm_eq_abs]
  calc ‖∑' i, x i * g i‖ ≤ ∑' i, ‖x i * g i‖ :=
        norm_tsum_le_tsum_norm (by simpa [norm_mul] using lp.summable_mul hpq x g)
    _ = ∑' i, ‖x i‖ * ‖g i‖ := by simp [norm_mul]
    _ ≤ ‖x‖ * ‖g‖ := lp.tsum_mul_le_mul_norm' hpq x g

/-- g ∈ ℓ^q som funksjonal på ℓᵖ. -/
noncomputable def T (g : L α q) : StrongDual ℝ (L α p) :=
  LinearMap.mkContinuous
    { toFun := fun x => ∑' i, x i * g i
      map_add' := fun x y => by
        simp only [lp.coeFn_add, Pi.add_apply, add_mul]
        exact (pair_summable hpq x g).tsum_add (pair_summable hpq y g)
      map_smul' := fun c x => by
        simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
        exact tsum_mul_left }
    ‖g‖ (fun x => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Real.norm_eq_abs]
      have := pair_bound hpq x g
      linarith [mul_comm ‖x‖ ‖g‖])

theorem T_apply (g : L α q) (x : L α p) : T hpq g x = ∑' i, x i * g i := rfl

theorem T_norm_le (g : L α q) : ‖T hpq g‖ ≤ ‖g‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg g) _

/-- T som kontinuerlig lineær avbildning ℓ^q → (ℓᵖ)*. -/
noncomputable def TL : L α q →L[ℝ] StrongDual ℝ (L α p) :=
  LinearMap.mkContinuous
    { toFun := T hpq
      map_add' := fun g h => by
        ext x
        simp only [T_apply, ContinuousLinearMap.add_apply, lp.coeFn_add, Pi.add_apply, mul_add]
        exact (pair_summable hpq x g).tsum_add (pair_summable hpq x h)
      map_smul' := fun c g => by
        ext x
        simp only [T_apply, ContinuousLinearMap.smul_apply, lp.coeFn_smul, Pi.smul_apply,
          smul_eq_mul, RingHom.id_apply]
        rw [← tsum_mul_left]
        congr 1; funext i; ring }
    1 (fun g => by simpa using T_norm_le hpq g)

theorem TL_apply (g : L α q) (x : L α p) : TL hpq g x = ∑' i, x i * g i := rfl

end Pairing

/-! ## 2. Dualitetsteoremet (ℓᵖ)* ≅ ℓ^q -/

/-- Hvert kontinuerlig lineært funksjonal på ℓᵖ er gitt ved et element av ℓ^q. -/
theorem repr (hpq : p.toReal.HolderConjugate q.toReal) (hp : p ≠ ⊤)
    (φ : StrongDual ℝ (L α p)) : ∃ g : L α q, ∀ x : L α p, φ x = ∑' i, x i * g i := by
  classical
  set r := p.toReal with hrdef
  set s := q.toReal with hsdef
  have hs1 : 1 < s := hpq.symm.lt
  let g0 : α → ℝ := fun i => φ (lp.single p i (1 : ℝ))
  have hφs : ∀ i (c : ℝ), φ (lp.single p i c) = c * g0 i := by
    intro i c
    have : lp.single (E := fun _ : α => ℝ) p i c = c • lp.single (E := fun _ : α => ℝ) p i (1 : ℝ) := by
      rw [← lp.single_smul, smul_eq_mul, mul_one]
    rw [this, map_smul, smul_eq_mul]
  have hmem : Memℓp g0 q := by
    refine memℓp_gen' (C := ‖φ‖ ^ s) fun t => ?_
    set A := ∑ i ∈ t, ‖g0 i‖ ^ s with hAdef
    -- testvektoren w = sign(g)|g|^{s−1}
    let w : α → ℝ := fun i => if 0 ≤ g0 i then |g0 i| ^ (s - 1) else -(|g0 i| ^ (s - 1))
    have hw_mul : ∀ i, w i * g0 i = ‖g0 i‖ ^ s := by
      intro i
      simp only [w, Real.norm_eq_abs]
      split_ifs with h
      · rw [abs_of_nonneg h]; exact rpow_sub_one_mul h hs1
      · push Not at h
        rw [abs_of_neg h]
        have := rpow_sub_one_mul (neg_nonneg.2 h.le) hs1
        linarith
    have hw_abs : ∀ i, ‖w i‖ ^ r = ‖g0 i‖ ^ s := by
      intro i
      have h1 : ‖w i‖ = |g0 i| ^ (s - 1) := by
        have hnn : 0 ≤ |g0 i| ^ (s - 1) := Real.rpow_nonneg (abs_nonneg _) _
        simp only [w, Real.norm_eq_abs]
        split_ifs
        · exact abs_of_nonneg hnn
        · rw [abs_neg]; exact abs_of_nonneg hnn
      rw [h1, ← Real.rpow_mul (abs_nonneg _), hpq.symm.sub_one_mul_conj, Real.norm_eq_abs]
    set x : L α p := ∑ i ∈ t, lp.single p i (w i) with hxdef
    have hφx : φ x = A := by
      rw [hxdef, map_sum]
      simp only [hφs, hw_mul]
      exact hAdef.symm
    have hxnorm : ‖x‖ ^ r = A := by
      rw [hxdef, lp.norm_sum_single hpq.pos]
      exact (Finset.sum_congr rfl fun i _ => hw_abs i).trans hAdef.symm
    have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => by positivity
    have hle : A ≤ ‖φ‖ * ‖x‖ := by
      rw [← hφx]
      exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using φ.le_opNorm x)
    have hxA : ‖x‖ = A ^ r⁻¹ := by
      rw [← hxnorm, ← Real.rpow_mul (norm_nonneg _), mul_inv_cancel₀ hpq.ne_zero, Real.rpow_one]
    rcases hA0.lt_or_eq with hA | hA
    · have hpos : 0 < A ^ r⁻¹ := Real.rpow_pos_of_pos hA _
      have h1 : A = A ^ r⁻¹ * A ^ s⁻¹ := by
        rw [← Real.rpow_add hA, hpq.inv_add_inv_eq_one, Real.rpow_one]
      have key : A ^ s⁻¹ ≤ ‖φ‖ := by
        rw [hxA] at hle
        have : A ^ r⁻¹ * A ^ s⁻¹ ≤ A ^ r⁻¹ * ‖φ‖ := by
          rw [← h1]; linarith [mul_comm ‖φ‖ (A ^ r⁻¹)]
        exact le_of_mul_le_mul_left this hpos
      calc A = (A ^ s⁻¹) ^ s := by
            rw [← Real.rpow_mul hA0, inv_mul_cancel₀ hpq.symm.ne_zero, Real.rpow_one]
        _ ≤ ‖φ‖ ^ s := Real.rpow_le_rpow (by positivity) key hpq.symm.nonneg
    · rw [← hA]; positivity
  refine ⟨⟨g0, hmem⟩, fun x => ?_⟩
  have hs := (lp.hasSum_single hp x).mapL φ
  rw [← hs.tsum_eq]
  congr 1
  funext i
  simp only [Function.comp_apply, hφs]

/-! ## 3. Refleksivitet -/

/-- **ℓᵖ er refleksivt** for 1 < p < ∞. -/
theorem reflexive (hpq : p.toReal.HolderConjugate q.toReal) (hp : p ≠ ⊤) (hq : q ≠ ⊤) :
    Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ (L α p)) := by
  intro Φ
  let ψ : StrongDual ℝ (L α q) := Φ.comp (TL hpq)
  obtain ⟨x, hx⟩ := repr hpq.symm hq ψ
  refine ⟨x, ?_⟩
  ext φ
  rw [NormedSpace.dual_def]
  obtain ⟨g, hg⟩ := repr hpq hp φ
  have hφ : φ = TL hpq g := by
    ext y; rw [hg y, TL_apply]
  rw [hφ, TL_apply]
  show ∑' i, x i * g i = ψ g
  rw [hx g]
  congr 1; funext i; ring

/-- Spesialtilfellet ℓ²: p = q = 2. -/
theorem reflexive_two : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ (L α 2)) := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  exact reflexive (p := 2) (q := 2) (by simpa using Real.HolderConjugate.two_two) (by simp) (by simp)

end LpReflexive

/-! ## 4. Endeligdimensjonale rom -/

namespace FinDimReflexive

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

theorem finrank_strongDual (Y : Type*) [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ Y] :
    FiniteDimensional ℝ (StrongDual ℝ Y) ∧ Module.finrank ℝ (StrongDual ℝ Y) = Module.finrank ℝ Y := by
  let e : Module.Dual ℝ Y ≃ₗ[ℝ] StrongDual ℝ Y := LinearMap.toContinuousLinearMap
  exact ⟨LinearEquiv.finiteDimensional e, e.finrank_eq.symm.trans Subspace.dual_finrank_eq⟩

/-- **Endeligdimensjonale normerte rom er refleksive.** -/
theorem reflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ X) := by
  obtain ⟨h1, e1⟩ := finrank_strongDual X
  haveI := h1
  obtain ⟨h2, e2⟩ := finrank_strongDual (StrongDual ℝ X)
  haveI := h2
  have hinj : Function.Injective (NormedSpace.inclusionInDoubleDual ℝ X) :=
    (NormedSpace.inclusionInDoubleDualLi ℝ (E := X)).injective
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (e2.trans e1).symm
    (f := (NormedSpace.inclusionInDoubleDual ℝ X : X →ₗ[ℝ] _))).1 hinj

end FinDimReflexive

/-! ## 5. Minty–Browder på ℓᵖ, uten refleksivitetsantakelse -/

namespace LpReflexive

variable {α : Type*} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- **Minty–Browder på ℓᵖ** (1 < p < ∞): monoton, hemikontinuerlig og koersiv
    F : ℓᵖ → (ℓᵖ)* er surjektiv. Refleksiviteten er nå bevist, ikke antatt. -/
theorem minty_browder_lp (hpq : p.toReal.HolderConjugate q.toReal) (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (F : L α p → StrongDual ℝ (L α p)) (hhemi : MintyBrowderHemi.Hemicontinuous F)
    (hmono : ∀ x y, 0 ≤ (F x - F y) (x - y)) (hcoer : MintyBrowderBanach.Coercive F) :
    Function.Surjective F :=
  MintyBrowderHemi.surjective (reflexive hpq hp hq) F hhemi hmono hcoer

end LpReflexive

namespace FinDimReflexive

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

/-- Minty–Browder i ethvert endeligdimensjonalt normert rom (vilkårlig norm). -/
theorem minty_browder (F : X → StrongDual ℝ X) (hhemi : MintyBrowderHemi.Hemicontinuous F)
    (hmono : ∀ x y, 0 ≤ (F x - F y) (x - y)) (hcoer : MintyBrowderBanach.Coercive F) :
    Function.Surjective F :=
  MintyBrowderHemi.surjective reflexive F hhemi hmono hcoer

end FinDimReflexive
end CausalPhys
