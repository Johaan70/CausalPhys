/-
  CausalPhys.InfiniteSCM — kausale modeller med uendelig mange variabler.

  Tilstandsrommet er ℓ²(V) for en vilkårlig (gjerne uendelig) variabelmengde V.
  Residualen til modellen, R(s)_v = s_v − f_v(s), blir en operator på ℓ²(V)
  når den sender ℓ² inn i ℓ². Minty–Browder i Hilbert-rom (Theorem 28–29)
  gir da:

    `exists_unique_l2`: er residualen hemikontinuerlig, strengt monoton og
    koersiv på ℓ²(V), har modellen nøyaktig én løsning i ℓ²(V).

  Merk: entydigheten gjelder blant ℓ²-løsningene. Modellen kan ha andre
  løsninger utenfor ℓ² (for eksempel ubegrensede); de fanges ikke opp.

  Eksempel (`Lattice`): et uendelig gitter av variabler X_n, n ∈ ℤ, med
  mekanismene
      X_n := b_n + (c/2)(X_{n−1} + X_{n+1}) − X_n³,      0 ≤ c < 1,
  det vil si likevektsligningene x_n³ + x_n = b_n + (c/2)(x_{n−1} + x_{n+1}).
  Hver variabel avhenger av begge naboene, så modellen har uendelig mange
  sykler og ingen rekursiv rang. Residualen er sterkt monoton, men ikke
  Lipschitz (kubikkleddet), så verken Banach eller Zarantonello gjelder.
  For hver b ∈ ℓ²(ℤ) finnes nøyaktig én likevekt i ℓ²(ℤ).
-/
import CausalPhys.MintyBrowderHemi
import Mathlib.Analysis.InnerProductSpace.l2Space

set_option linter.unusedSectionVars false

open scoped ENNReal
open RealInnerProductSpace

namespace CausalPhys
namespace InfSCM

/-- ℓ²(V) med reelle koordinater. -/
abbrev L2 (V : Type) := lp (fun _ : V => ℝ) 2

variable {V : Type}

/-! ## 1. Residualen uten endelighetsantakelser -/

def fixExo (M : SCM V ℝ) (u s : V → ℝ) : V → ℝ :=
  fun w => match M.mech w with
    | none => u w
    | some _ => s w

def resid (M : SCM V ℝ) (u s : V → ℝ) : V → ℝ :=
  fun v => match M.mech v with
    | none => s v - u v
    | some m => s v - m.f (fixExo M u s)

theorem solves_iff_resid_zero (M : SCM V ℝ) (u s : V → ℝ) :
    M.Solves u s ↔ resid M u s = 0 := by
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
    unfold resid
    cases hm : M.mech v with
    | none => simp only [hm] at hv ⊢; simp [hv]
    | some m => simp only [hm, hfix] at hv ⊢; simp [← hv]
  · intro h
    have hexo : ∀ w, M.mech w = none → s w = u w := by
      intro w hw
      have := congrFun h w
      unfold resid at this
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
    unfold resid at this
    cases hm : M.mech v with
    | none => exact hexo v hm
    | some m =>
      simp only [hm, hfix, Pi.zero_apply] at this
      show s v = m.f s
      linarith

/-- Residualen som operator på ℓ²(V), når den sender ℓ² inn i ℓ². -/
noncomputable def F (M : SCM V ℝ) (u : V → ℝ) (hmem : ∀ x : L2 V, Memℓp (resid M u x) 2)
    (x : L2 V) : L2 V :=
  ⟨resid M u x, hmem x⟩

/-! ## 2. Hovedteoremet -/

/-- **Minty–Browder for kausale modeller med uendelig mange variabler.** -/
theorem exists_unique_l2 (M : SCM V ℝ) (u : V → ℝ) (hmem : ∀ x : L2 V, Memℓp (resid M u x) 2)
    (hhemi : ∀ x w z : L2 V, Continuous fun t : ℝ => ⟪F M u hmem (x + t • w), z⟫)
    (hmono : ∀ x y : L2 V, x ≠ y → 0 < ⟪F M u hmem x - F M u hmem y, x - y⟫)
    (hcoer : MintyBrowderHilbert.Coercive (F M u hmem)) :
    ∃! x : L2 V, M.Solves u x := by
  have hmono' : ∀ x y : L2 V, 0 ≤ ⟪F M u hmem x - F M u hmem y, x - y⟫ := by
    intro x y
    by_cases h : x = y
    · rw [h, sub_self, inner_zero_left]
    · exact (hmono x y h).le
  obtain ⟨x, hx⟩ := MintyBrowderHemi.hilbert_surjective (F M u hmem) hhemi hmono' hcoer 0
  have hsol : ∀ y : L2 V, M.Solves u y ↔ F M u hmem y = 0 := by
    intro y
    rw [solves_iff_resid_zero]
    constructor
    · intro h; ext v; simp [F, h]
    · intro h; funext v
      have := congrArg (fun z : L2 V => z v) h
      simpa [F] using this
  refine ⟨x, (hsol x).2 hx, fun y hy => ?_⟩
  by_contra hne
  have := hmono y x hne
  rw [(hsol y).1 hy, hx, sub_self, inner_zero_left] at this
  exact lt_irrefl _ this

/-- Sterk monotonitet gir koersivitet. -/
theorem coercive_of_strongMono {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (G : H → H) {c : ℝ} (hc : 0 < c)
    (hmono : ∀ x y, c * ‖x - y‖ ^ 2 ≤ ⟪G x - G y, x - y⟫) : MintyBrowderHilbert.Coercive G := by
  intro M
  refine ⟨(|M| + ‖G 0‖ + 1) / c, by positivity, fun x hx => ?_⟩
  have h1 := hmono x 0
  rw [sub_zero, inner_sub_left] at h1
  have h2 : -(‖G 0‖ * ‖x‖) ≤ ⟪G 0, x⟫ := neg_le_of_abs_le (abs_real_inner_le_norm _ _)
  have hxc : |M| + ‖G 0‖ + 1 ≤ c * ‖x‖ := by
    rw [div_le_iff₀ hc] at hx; linarith
  have hn := norm_nonneg x
  have h3 : c * ‖x‖ ^ 2 ≥ (|M| + ‖G 0‖ + 1) * ‖x‖ := by nlinarith
  have h4 : M * ‖x‖ ≤ |M| * ‖x‖ := mul_le_mul_of_nonneg_right (le_abs_self M) hn
  nlinarith

/-! ## 3. Verktøy for ℓ² -/

section Tools

theorem abs_apply_le (x : L2 V) (n : V) : |x n| ≤ ‖x‖ := by
  have := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) x n
  rwa [Real.norm_eq_abs] at this

theorem two_toReal : (2 : ℝ≥0∞).toReal = 2 := by norm_num

/-- Punktvis dominert av C|g| ⇒ i ℓ². -/
theorem mem_of_le (f : V → ℝ) (g : L2 V) {C : ℝ} (hC : 0 ≤ C) (h : ∀ n, |f n| ≤ C * |g n|) :
    Memℓp f 2 := by
  refine memℓp_gen' (C := (C * ‖g‖) ^ (2 : ℝ)) fun s => ?_
  rw [two_toReal]
  calc ∑ i ∈ s, ‖f i‖ ^ (2 : ℝ) ≤ ∑ i ∈ s, C ^ (2 : ℝ) * ‖g i‖ ^ (2 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← Real.mul_rpow hC (norm_nonneg _), Real.norm_eq_abs, Real.norm_eq_abs]
        exact Real.rpow_le_rpow (abs_nonneg _) (h i) (by norm_num)
    _ = C ^ (2 : ℝ) * ∑ i ∈ s, ‖g i‖ ^ (2 : ℝ) := by rw [Finset.mul_sum]
    _ ≤ C ^ (2 : ℝ) * ‖g‖ ^ (2 : ℝ) := by
        have := lp.sum_rpow_le_norm_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal) g s
        rw [two_toReal] at this
        exact mul_le_mul_of_nonneg_left this (by positivity)
    _ = (C * ‖g‖) ^ (2 : ℝ) := by rw [Real.mul_rpow hC (norm_nonneg _)]

/-- Punktvis dominert av C|g| ⇒ normen er høyst C‖g‖. -/
theorem norm_le_of_le (f g : L2 V) {C : ℝ} (hC : 0 ≤ C) (h : ∀ n, |f n| ≤ C * |g n|) :
    ‖f‖ ≤ C * ‖g‖ := by
  refine lp.norm_le_of_forall_sum_le (by norm_num) (by positivity) fun s => ?_
  rw [two_toReal]
  calc ∑ i ∈ s, ‖f i‖ ^ (2 : ℝ) ≤ ∑ i ∈ s, C ^ (2 : ℝ) * ‖g i‖ ^ (2 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← Real.mul_rpow hC (norm_nonneg _), Real.norm_eq_abs, Real.norm_eq_abs]
        exact Real.rpow_le_rpow (abs_nonneg _) (h i) (by norm_num)
    _ = C ^ (2 : ℝ) * ∑ i ∈ s, ‖g i‖ ^ (2 : ℝ) := by rw [Finset.mul_sum]
    _ ≤ C ^ (2 : ℝ) * ‖g‖ ^ (2 : ℝ) := by
        have := lp.sum_rpow_le_norm_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal) g s
        rw [two_toReal] at this
        exact mul_le_mul_of_nonneg_left this (by positivity)
    _ = (C * ‖g‖) ^ (2 : ℝ) := by rw [Real.mul_rpow hC (norm_nonneg _)]

theorem inner_eq (x y : L2 V) : ⟪x, y⟫ = ∑' n, x n * y n := by
  rw [lp.inner_eq_tsum]
  congr 1; funext n
  simp only [RCLike.inner_apply, conj_trivial]
  ring

end Tools

/-! ## 4. Eksempel: et uendelig ikke-lineært gitter -/

namespace Lattice

/-- Forskyvning (Sx)_n = x_{n+k}, en isometri på ℓ²(ℤ). -/
noncomputable def shift (k : ℤ) (x : L2 ℤ) : L2 ℤ :=
  ⟨fun n => x (n + k), by
    have hs := (lp.memℓp x).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    refine memℓp_gen ?_
    exact (Equiv.addRight k).summable_iff.2 hs⟩

theorem shift_apply (k : ℤ) (x : L2 ℤ) (n : ℤ) : shift k x n = x (n + k) := rfl

theorem shift_norm (k : ℤ) (x : L2 ℤ) : ‖shift k x‖ = ‖x‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
  congr 1
  exact (Equiv.addRight k).tsum_eq (fun n => ‖x n‖ ^ (2 : ℝ≥0∞).toReal)

theorem shift_sub (k : ℤ) (x y : L2 ℤ) : shift k (x - y) = shift k x - shift k y := by
  ext n; simp [shift_apply]

/-- Kubikkavbildningen (x_n) ↦ (x_n³) på ℓ²(ℤ). -/
noncomputable def cube (x : L2 ℤ) : L2 ℤ :=
  ⟨fun n => x n ^ 3, mem_of_le _ x (sq_nonneg ‖x‖) fun n => by
    have h := abs_apply_le x n
    rw [abs_pow, show |x n| ^ 3 = |x n| ^ 2 * |x n| by ring]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) h 2) (abs_nonneg _)⟩

theorem cube_apply (x : L2 ℤ) (n : ℤ) : cube x n = x n ^ 3 := rfl

theorem cube_lip (x y : L2 ℤ) {M : ℝ} (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) :
    ‖cube x - cube y‖ ≤ 3 * M ^ 2 * ‖x - y‖ := by
  have hM : 0 ≤ M := (norm_nonneg x).trans hx
  refine norm_le_of_le _ _ (by positivity) fun n => ?_
  simp only [lp.coeFn_sub, Pi.sub_apply, cube_apply]
  have ha := (abs_apply_le x n).trans hx
  have hb := (abs_apply_le y n).trans hy
  have e : x n ^ 3 - y n ^ 3 = (x n - y n) * (x n ^ 2 + x n * y n + y n ^ 2) := by ring
  rw [e, abs_mul, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  have h1 : |x n ^ 2 + x n * y n + y n ^ 2| ≤ |x n| ^ 2 + |x n| * |y n| + |y n| ^ 2 := by
    calc _ ≤ |x n ^ 2| + |x n * y n| + |y n ^ 2| := abs_add_three _ _ _
      _ = _ := by rw [abs_pow, abs_mul, abs_pow]
  have h2 : |x n| * |y n| ≤ M * M := mul_le_mul ha hb (abs_nonneg _) hM
  nlinarith [abs_nonneg (x n), abs_nonneg (y n)]

theorem cube_mono (x y : L2 ℤ) : 0 ≤ ⟪cube x - cube y, x - y⟫ := by
  rw [inner_eq]
  refine tsum_nonneg fun n => ?_
  simp only [lp.coeFn_sub, Pi.sub_apply, cube_apply]
  nlinarith [sq_nonneg (x n - y n), sq_nonneg (x n + y n),
    mul_nonneg (sq_nonneg (x n - y n)) (add_nonneg (sq_nonneg (x n)) (sq_nonneg (y n)))]

variable (c : ℝ) (b : L2 ℤ)

/-- Residualen som operator: F(x) = x³ + x − (c/2)(S₋x + S₊x) − b. -/
noncomputable def Fop (x : L2 ℤ) : L2 ℤ :=
  cube x + x - (c / 2) • (shift (-1) x + shift 1 x) - b

/-- Den kausale modellen: X_n := b_n + (c/2)(X_{n−1} + X_{n+1}) − X_n³. -/
noncomputable def scm : SCM ℤ ℝ :=
  ⟨fun n => some ⟨[n - 1, n, n + 1],
    fun s => b n + c / 2 * (s (n - 1) + s (n + 1)) - s n ^ 3,
    fun s t h => by
      rw [h (n - 1) (by simp), h n (by simp), h (n + 1) (by simp)]⟩⟩

theorem resid_eq (u : ℤ → ℝ) (x : L2 ℤ) : resid (scm c b) u x = Fop c b x := by
  funext n
  simp only [resid, scm, fixExo, Fop, lp.coeFn_sub, lp.coeFn_add, lp.coeFn_smul, Pi.sub_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, cube_apply, shift_apply]
  rw [show n + -1 = n - 1 by ring]
  ring

theorem hmem (u : ℤ → ℝ) : ∀ x : L2 ℤ, Memℓp (resid (scm c b) u x) 2 := fun x => by
  rw [resid_eq]; exact lp.memℓp _

theorem F_eq (u : ℤ → ℝ) (x : L2 ℤ) : F (scm c b) u (hmem c b u) x = Fop c b x := by
  ext n; simp [F, resid_eq]

theorem Fop_continuous : Continuous (Fop c b) := by
  rw [Metric.continuous_iff]
  intro x ε hε
  set K := 3 * (‖x‖ + 1) ^ 2 + 1 + |c|
  have hK : 0 < K := by positivity
  refine ⟨min 1 (ε / K), by positivity, fun y hy => ?_⟩
  rw [dist_eq_norm] at hy ⊢
  have hy1 : ‖y - x‖ < 1 := lt_of_lt_of_le hy (min_le_left _ _)
  have hyK : ‖y - x‖ < ε / K := lt_of_lt_of_le hy (min_le_right _ _)
  have hyn : ‖y‖ ≤ ‖x‖ + 1 := by
    calc ‖y‖ = ‖(y - x) + x‖ := by rw [sub_add_cancel]
      _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
      _ ≤ ‖x‖ + 1 := by linarith
  have e : Fop c b y - Fop c b x = (cube y - cube x) + (y - x)
      - (c / 2) • (shift (-1) (y - x) + shift 1 (y - x)) := by
    simp only [Fop, shift_sub, smul_add, smul_sub]; abel
  have h1 := cube_lip y x hyn (by linarith : ‖x‖ ≤ ‖x‖ + 1)
  have h2 : ‖(c / 2) • (shift (-1) (y - x) + shift 1 (y - x))‖ ≤ |c| * ‖y - x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_div, abs_two]
    calc |c| / 2 * ‖shift (-1) (y - x) + shift 1 (y - x)‖
        ≤ |c| / 2 * (‖shift (-1) (y - x)‖ + ‖shift 1 (y - x)‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
      _ = |c| * ‖y - x‖ := by rw [shift_norm, shift_norm]; ring
  have h3 : ‖Fop c b y - Fop c b x‖ ≤ K * ‖y - x‖ := by
    rw [e]
    calc ‖cube y - cube x + (y - x) - (c / 2) • (shift (-1) (y - x) + shift 1 (y - x))‖
        ≤ ‖cube y - cube x‖ + ‖y - x‖ + |c| * ‖y - x‖ := by
          refine (norm_sub_le _ _).trans ?_
          have := norm_add_le (cube y - cube x) (y - x)
          linarith
      _ ≤ 3 * (‖x‖ + 1) ^ 2 * ‖y - x‖ + ‖y - x‖ + |c| * ‖y - x‖ := by linarith
      _ = K * ‖y - x‖ := by ring
  calc ‖Fop c b y - Fop c b x‖ ≤ K * ‖y - x‖ := h3
    _ < K * (ε / K) := mul_lt_mul_of_pos_left hyK hK
    _ = ε := by field_simp

theorem Fop_strongMono (hc0 : 0 ≤ c) (x y : L2 ℤ) :
    (1 - c) * ‖x - y‖ ^ 2 ≤ ⟪Fop c b x - Fop c b y, x - y⟫ := by
  set d := x - y
  have e : Fop c b x - Fop c b y = (cube x - cube y) + d
      - (c / 2) • (shift (-1) d + shift 1 d) := by
    simp only [Fop, d, shift_sub, smul_add, smul_sub]; abel
  rw [e, inner_sub_left, inner_add_left, real_inner_self_eq_norm_sq, real_inner_smul_left]
  have h1 := cube_mono x y
  have h2 : ⟪shift (-1) d + shift 1 d, d⟫ ≤ 2 * ‖d‖ ^ 2 := by
    calc ⟪shift (-1) d + shift 1 d, d⟫ ≤ ‖shift (-1) d + shift 1 d‖ * ‖d‖ := real_inner_le_norm _ _
      _ ≤ (‖shift (-1) d‖ + ‖shift 1 d‖) * ‖d‖ :=
          mul_le_mul_of_nonneg_right (norm_add_le _ _) (norm_nonneg _)
      _ = 2 * ‖d‖ ^ 2 := by rw [shift_norm, shift_norm]; ring
  nlinarith

/-- **Det uendelige gitteret har nøyaktig én likevekt i ℓ²(ℤ)**, for alle
    b ∈ ℓ²(ℤ) og 0 ≤ c < 1. -/
theorem exists_unique (hc0 : 0 ≤ c) (hc1 : c < 1) (u : ℤ → ℝ) :
    ∃! x : L2 ℤ, (scm c b).Solves u x := by
  have hFc : Continuous (F (scm c b) u (hmem c b u)) := by
    have : F (scm c b) u (hmem c b u) = Fop c b := funext (F_eq c b u)
    rw [this]; exact Fop_continuous c b
  refine exists_unique_l2 (scm c b) u (hmem c b u)
    (fun x w z => by fun_prop) (fun x y hxy => ?_) ?_
  · rw [F_eq, F_eq]
    have h := Fop_strongMono c b hc0 x y
    have hpos : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
    have : 0 < (1 - c) * ‖x - y‖ ^ 2 := by
      have : 0 < 1 - c := by linarith
      positivity
    linarith
  · have hfun : F (scm c b) u (hmem c b u) = Fop c b := funext (F_eq c b u)
    rw [hfun]
    exact coercive_of_strongMono (Fop c b) (by linarith : (0:ℝ) < 1 - c)
      (Fop_strongMono c b hc0)

end Lattice
end InfSCM
end CausalPhys
