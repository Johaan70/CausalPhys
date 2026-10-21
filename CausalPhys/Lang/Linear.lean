/-
  CausalPhys.Lang.Linear — the linear criterion for cyclic blocks (phase 4).

  Many cyclic blocks are linear in their own variables, with coefficients that
  may depend on the exogenous ones: a market equilibrium, a current divider,
  a linear feedback. For those the question "exactly one outcome?" has a
  complete answer: write the solved forms as

        x = C·x + d          (C and d may depend only on the exogenous values,
                              not on endogenous variables of other blocks)

  then the setup has exactly one solution when det(I − C) ≠ 0.

  `linear_existsUnique` proves this once for every model. It is stated for an
  enumeration of the endogenous variables (`Enum`, checked by evaluation), and
  needs the formulas to be affine (`IsAffine`, proved by `ring` after
  unfolding). Both side conditions, and the determinant, are produced by the
  tactic `linear_block` in `CausalPhys.Lang.Tactic`, so for a concrete model
  what is left is a statement like `b + e ≠ 0`, i.e. the economics.

  The criterion is applied to the whole setup at once, so every formula of the
  setup must be affine in this sense; a linear block next to a nonlinear one,
  or whose coefficients come from an upstream block, is not covered yet. The
  result is about the causal model; `Setup.laws_existsUnique` carries it over
  to the laws when the outcome lies in the domain.
-/
import CausalPhys.Lang.Core
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

set_option linter.unusedSectionVars false

namespace CausalPhys.Lang
namespace Setup

open CausalPhys.Order

variable {E V : Type} [DecidableEq E] [DecidableEq V] [Inhabited V] {M : Model E V ℝ}
  (S : Setup M)

/-- Keep the exogenous values, set the endogenous ones to zero. -/
def base (s : V → ℝ) : V → ℝ := fun v => if v ∈ S.exo then s v else 0

variable {n : ℕ} (laws : Fin n → E) (vars : Fin n → V)

/-- The solved form of the `i`-th law. -/
@[nolint unusedArguments]
def formula (_S : Setup M) (i : Fin n) (s : V → ℝ) : ℝ := (M.mechOf (laws i) (vars i)).f s

/-- Coefficient of `vars j` in the `i`-th formula (exact when the formula is affine). -/
def coef (s : V → ℝ) (i j : Fin n) : ℝ :=
  S.formula laws vars i (Function.update (S.base s) (vars j) 1) - S.formula laws vars i (S.base s)

/-- Constant part of the `i`-th formula. -/
def const (s : V → ℝ) (i : Fin n) : ℝ := S.formula laws vars i (S.base s)

/-- Every formula is affine in the endogenous variables. -/
def IsAffine : Prop :=
  ∀ i s, S.formula laws vars i s = S.const laws vars s i + ∑ j, S.coef laws vars s i j * s (vars j)

/-- The matrix I − C. -/
def linMatrix (u : V → ℝ) : Matrix (Fin n) (Fin n) ℝ := 1 - Matrix.of (S.coef laws vars u)

/-- `laws`/`vars` enumerate the computed matching: law `i` determines `vars i`,
    every endogenous variable occurs, and none twice. -/
def Enum : Prop :=
  (∀ i, S.cert.σ (laws i) = vars i) ∧
  (∀ v ∈ M.varList, v ∉ S.exo → ∃ i, vars i = v) ∧
  (∀ i j, vars i = vars j → i = j)

instance : Decidable (S.Enum laws vars) := by unfold Enum; infer_instance

variable {S laws vars}

theorem Enum.inv (hE : S.Enum laws vars) (i : Fin n) : S.cert.inv (vars i) = some (laws i) :=
  (S.valid.inv_iff _ _).2 (hE.1 i)

theorem Enum.not_exo (hE : S.Enum laws vars) (i : Fin n) : vars i ∉ S.exo := by
  intro h
  have h1 := hE.inv i
  have h2 : S.cert.inv (vars i) = none := (S.valid.inv_none _).2 h
  rw [h1] at h2
  cases h2

theorem Enum.cover (hE : S.Enum laws vars) {v : V} (hv : v ∉ S.exo) : ∃ i, vars i = v :=
  hE.2.1 v (M.var_complete v) hv

theorem rhs_exo {u s : V → ℝ} {v : V} (hv : v ∈ S.exo) : S.rhs u s v = u v :=
  S.rhs_none ((S.valid.inv_none _).2 hv)

theorem Enum.rhs (hE : S.Enum laws vars) (u s : V → ℝ) (i : Fin n) :
    S.rhs u s (vars i) = S.formula laws vars i s :=
  S.rhs_some (hE.inv i)

/-- Solutions, described through the enumeration. -/
theorem Enum.solves_iff (hE : S.Enum laws vars) (u s : V → ℝ) :
    S.scm.Solves u s ↔
      (∀ v, v ∈ S.exo → s v = u v) ∧ ∀ i, s (vars i) = S.formula laws vars i s := by
  constructor
  · intro h
    refine ⟨fun v hv => (S.value_eq h v).trans (rhs_exo hv), fun i => ?_⟩
    exact (S.value_eq h (vars i)).trans (hE.rhs u s i)
  · rintro ⟨h1, h2⟩
    apply S.solves_of_values
    intro v
    by_cases hv : v ∈ S.exo
    · rw [rhs_exo hv]; exact h1 v hv
    · obtain ⟨i, rfl⟩ := hE.cover hv
      rw [hE.rhs u s i]; exact h2 i

theorem base_congr {u s : V → ℝ} (h : ∀ v, v ∈ S.exo → s v = u v) : S.base s = S.base u := by
  funext v
  unfold base
  split_ifs with hv
  · exact h v hv
  · rfl

/-- On the exogenous values `u`, the laws are the linear system (I − C)·x = d. -/
theorem lin_iff (haff : S.IsAffine laws vars) {u s : V → ℝ} (h : ∀ v, v ∈ S.exo → s v = u v) :
    (∀ i, s (vars i) = S.formula laws vars i s) ↔
      (S.linMatrix laws vars u).mulVec (fun i => s (vars i)) = S.const laws vars u := by
  have hb := base_congr h
  have hc : S.coef laws vars s = S.coef laws vars u := by
    funext i j; simp only [coef, hb]
  have hd : S.const laws vars s = S.const laws vars u := by
    funext i; simp only [const, hb]
  rw [funext_iff]
  apply forall_congr'
  intro i
  rw [haff i s, hc, hd]
  rw [linMatrix, Matrix.sub_mulVec, Matrix.one_mulVec]
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Matrix.of_apply]
  constructor <;> intro h' <;> linarith

/-- The linear criterion: affine formulas and det(I − C) ≠ 0 give exactly one
    outcome. -/
theorem linear_existsUnique (hE : S.Enum laws vars) (haff : S.IsAffine laws vars) (u : V → ℝ)
    (hdet : (S.linMatrix laws vars u).det ≠ 0) : ∃! s, S.scm.Solves u s := by
  set A := S.linMatrix laws vars u
  set c := S.const laws vars u
  have hA : IsUnit A.det := isUnit_iff_ne_zero.2 hdet
  -- existence
  let x : Fin n → ℝ := A⁻¹.mulVec c
  have hx : A.mulVec x = c := by
    simp only [x, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hA, Matrix.one_mulVec]
  classical
  let s : V → ℝ := fun v => if h : ∃ i, vars i = v then x (Classical.choose h) else u v
  have hs_var : ∀ i, s (vars i) = x i := by
    intro i
    have h : ∃ j, vars j = vars i := ⟨i, rfl⟩
    simp only [s, h, ↓reduceDIte]
    rw [hE.2.2 _ _ (Classical.choose_spec h)]
  have hs_exo : ∀ v, v ∈ S.exo → s v = u v := by
    intro v hv
    have h : ¬ ∃ i, vars i = v := by
      rintro ⟨i, rfl⟩; exact hE.not_exo i hv
    simp only [s, h, ↓reduceDIte]
  have hsol : S.scm.Solves u s := by
    rw [hE.solves_iff]
    refine ⟨hs_exo, ?_⟩
    rw [lin_iff haff hs_exo]
    have : (fun i => s (vars i)) = x := funext hs_var
    rw [this]; exact hx
  refine ⟨s, hsol, fun t ht => ?_⟩
  -- uniqueness
  obtain ⟨ht1, ht2⟩ := (hE.solves_iff u t).1 ht
  obtain ⟨hs1, hs2⟩ := (hE.solves_iff u s).1 hsol
  have et := (lin_iff haff ht1).1 ht2
  have es := (lin_iff haff hs1).1 hs2
  have hdiff : A.mulVec ((fun i => t (vars i)) - fun i => s (vars i)) = 0 := by
    rw [Matrix.mulVec_sub, et, es, sub_self]
  have h0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hdiff
  funext v
  by_cases hv : v ∈ S.exo
  · rw [ht1 v hv, hs1 v hv]
  · obtain ⟨i, rfl⟩ := hE.cover hv
    have := congrFun h0 i
    simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at this
    exact this

/-- Intervening on an exogenous variable keeps exactly one outcome. -/
theorem do_exo_existsUnique {x : V} (hx : x ∈ S.exo) (c : ℝ) (u : V → ℝ)
    (h : ∃! s, S.scm.Solves (Function.update u x c) s) :
    ∃! s, (S.scm.doI x c).Solves u s := by
  simp only [S.do_exo_iff hx]
  exact h

end Setup
end CausalPhys.Lang
