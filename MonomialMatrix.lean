/-
  Monomial matrices over a field: a permutation of the coordinates and a nonzero
  scale factor for each.

  * They form a group (`Group (MonomialMatrix 𝕜 k)`), and `toMatrix` turns the group
    product into the matrix product.
  * They are exactly the invertible matrices that map every diagonal matrix to a
    diagonal one by congruence, `A ↦ Aᵀ * D * A` (`preserves_iff_monomial`).
  * The orthogonal ones are the permutations with signs (`rotation_preserves_iff`).

  Read with a diagonal `D` as the covariance of uncorrelated coordinates: these are the
  changes of coordinates that never create a correlation where there was none. The
  application to learned representations is in `Platonic.Monomial`.

  Over any field: the proofs use only inverses of nonzero elements and the absence of
  zero divisors. This file imports nothing from the rest of the repository.
-/
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

open Matrix


/-- An invertible monomial matrix: a permutation and nonzero scale factors. -/
@[ext]
structure MonomialMatrix (𝕜 : Type*) [Field 𝕜] (k : ℕ) where
  perm : Equiv.Perm (Fin k)
  scale : Fin k → 𝕜
  scale_ne_zero : ∀ j, scale j ≠ 0

namespace MonomialMatrix

variable {𝕜 : Type*} [Field 𝕜] {k : ℕ}

/-- Entry `scale j` in row `perm j` of column `j`, zeros elsewhere. -/
def toMatrix (m : MonomialMatrix 𝕜 k) : Matrix (Fin k) (Fin k) 𝕜 :=
  Matrix.of fun i j => if i = m.perm j then m.scale j else 0

/-- First `m₂`, then `m₁`: the permutations compose as `m₁.perm ∘ m₂.perm`. -/
def mul (m₁ m₂ : MonomialMatrix 𝕜 k) : MonomialMatrix 𝕜 k where
  perm := m₁.perm * m₂.perm
  scale := fun j => m₁.scale (m₂.perm j) * m₂.scale j
  scale_ne_zero := fun _ => mul_ne_zero (m₁.scale_ne_zero _) (m₂.scale_ne_zero _)

def one (k : ℕ) : MonomialMatrix 𝕜 k where
  perm := 1
  scale := fun _ => 1
  scale_ne_zero := fun _ => one_ne_zero

def inv (m : MonomialMatrix 𝕜 k) : MonomialMatrix 𝕜 k where
  perm := m.perm⁻¹
  scale := fun j => 1 / m.scale (m.perm⁻¹ j)
  scale_ne_zero := fun _ => div_ne_zero one_ne_zero (m.scale_ne_zero _)

instance : Mul (MonomialMatrix 𝕜 k) := ⟨mul⟩
instance : One (MonomialMatrix 𝕜 k) := ⟨one k⟩
instance : Inv (MonomialMatrix 𝕜 k) := ⟨inv⟩

@[simp] theorem mul_perm (a b : MonomialMatrix 𝕜 k) : (a * b).perm = a.perm * b.perm := rfl
@[simp] theorem mul_scale (a b : MonomialMatrix 𝕜 k) (j : Fin k) :
    (a * b).scale j = a.scale (b.perm j) * b.scale j := rfl
@[simp] theorem one_perm : (1 : MonomialMatrix 𝕜 k).perm = 1 := rfl
@[simp] theorem one_scale (j : Fin k) : (1 : MonomialMatrix 𝕜 k).scale j = 1 := rfl
@[simp] theorem inv_perm (a : MonomialMatrix 𝕜 k) : a⁻¹.perm = a.perm⁻¹ := rfl
@[simp] theorem inv_scale (a : MonomialMatrix 𝕜 k) (j : Fin k) :
    a⁻¹.scale j = 1 / a.scale (a.perm⁻¹ j) := rfl

instance : Group (MonomialMatrix 𝕜 k) where
  mul_assoc a b c := by ext j <;> simp [_root_.mul_assoc]
  one_mul a := by ext j <;> simp
  mul_one a := by ext j <;> simp
  inv_mul_cancel m := by ext j <;> simp [m.scale_ne_zero]

/-- `toMatrix` turns the group product into the matrix product … -/
theorem toMatrix_mul (a b : MonomialMatrix 𝕜 k) : toMatrix (a * b) = toMatrix a * toMatrix b := by
  ext i j
  simp only [toMatrix, mul_perm, mul_scale, Matrix.mul_apply, of_apply, Equiv.Perm.coe_mul,
    Function.comp_apply]
  rw [Finset.sum_eq_single (b.perm j) (fun l _ hl => by simp [hl]) (by simp)]
  split_ifs with h <;> simp [h]

/-- … and the unit into the identity matrix. -/
theorem toMatrix_one : toMatrix (1 : MonomialMatrix 𝕜 k) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [toMatrix, Matrix.one_apply, h]

/-- So the matrix of an inverse is the inverse matrix. -/
theorem toMatrix_inv_mul (a : MonomialMatrix 𝕜 k) : toMatrix a⁻¹ * toMatrix a = 1 := by
  rw [← toMatrix_mul, inv_mul_cancel, toMatrix_one]

theorem toMatrix_mul_inv (a : MonomialMatrix 𝕜 k) : toMatrix a * toMatrix a⁻¹ = 1 := by
  rw [← toMatrix_mul, mul_inv_cancel, toMatrix_one]

/-! ## The converse: only monomial matrices keep uncorrelated coordinates uncorrelated -/

/-- `A` never creates a correlation where there was none: whenever the coordinates are
    uncorrelated (a diagonal covariance `D`), they are uncorrelated after `A` too. Over a
    general field: `A` maps every diagonal matrix to a diagonal one by congruence. -/
def PreservesUncorrelated (A : Matrix (Fin k) (Fin k) 𝕜) : Prop :=
  ∀ D : Fin k → 𝕜, ∀ i j, i ≠ j → (Aᵀ * Matrix.diagonal D * A) i j = 0

theorem congr_diagonal_apply (A : Matrix (Fin k) (Fin k) 𝕜) (D : Fin k → 𝕜) (i j : Fin k) :
    (Aᵀ * Matrix.diagonal D * A) i j = ∑ a, A a i * D a * A a j := by
  simp [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, Finset.sum_ite_eq']

/-- Step 1: each row has at most one nonzero entry. -/
theorem row_single {A : Matrix (Fin k) (Fin k) 𝕜} (hA : PreservesUncorrelated A)
    (a i j : Fin k) (hij : i ≠ j) : A a i * A a j = 0 := by
  have h := hA (fun b => if b = a then 1 else 0) i j hij
  rw [congr_diagonal_apply] at h
  simpa [Finset.sum_ite_eq'] using h

/-- Monomial matrices keep uncorrelated coordinates uncorrelated. -/
theorem preserves_of_monomial (m : MonomialMatrix 𝕜 k) : PreservesUncorrelated m.toMatrix := by
  intro D i j hij
  rw [congr_diagonal_apply]
  refine Finset.sum_eq_zero fun a _ => ?_
  simp only [toMatrix, Matrix.of_apply]
  split_ifs with h1 h2
  · exact absurd (m.perm.injective (h1.symm.trans h2)) hij
  · simp
  · simp
  · simp

/-- **Only monomial matrices keep uncorrelated coordinates uncorrelated.** An invertible
    matrix never creates a correlation where there was none exactly when it renames and
    rescales the coordinates. -/
theorem preserves_iff_monomial (A : Matrix (Fin k) (Fin k) 𝕜) (hinv : ∃ B, B * A = 1) :
    PreservesUncorrelated A ↔ ∃ m : MonomialMatrix 𝕜 k, A = m.toMatrix := by
  constructor
  swap
  · rintro ⟨m, rfl⟩; exact preserves_of_monomial m
  intro hA
  obtain ⟨B, hBA⟩ := hinv
  have hAB : A * B = 1 := _root_.mul_eq_one_comm.1 hBA
  -- no row is zero
  have hrow : ∀ a, ∃ j, A a j ≠ 0 := by
    intro a
    by_contra hz
    push Not at hz
    have := congrFun (congrFun hAB a) a
    simp [Matrix.mul_apply, hz] at this
  choose f hf using hrow
  -- the nonzero entry of row `a` is in column `f a`
  have huniq : ∀ a i, A a i ≠ 0 → i = f a := by
    intro a i hi
    by_contra hne
    exact (mul_ne_zero hi (hf a)) (row_single hA a i (f a) hne)
  -- no column is missed, so `f` is a permutation
  have hsurj : Function.Surjective f := by
    intro c
    by_contra hc
    push Not at hc
    have hcol : ∀ a, A a c = 0 := fun a => by
      by_contra h
      exact hc a (huniq a c h).symm
    have := congrFun (congrFun hBA c) c
    simp [Matrix.mul_apply, hcol] at this
  have hinj : Function.Injective f := Finite.injective_iff_surjective.2 hsurj
  let σ : Equiv.Perm (Fin k) := Equiv.ofBijective f ⟨hinj, hsurj⟩
  have hσ : ∀ j, f (σ.symm j) = j := fun j => σ.apply_symm_apply j
  refine ⟨⟨σ.symm, fun j => A (σ.symm j) j, fun j => by
    have := hf (σ.symm j); rwa [hσ] at this⟩, ?_⟩
  ext i j
  simp only [toMatrix, Matrix.of_apply]
  split_ifs with h
  · rw [h]
  · by_contra hne
    apply h
    have : j = f i := huniq i j hne
    rw [this]
    exact (σ.symm_apply_apply i).symm

/-- **The rotations that keep causal structure.** A rotation never creates a correlation
    where there was none exactly when it is monomial, and then every scale factor is
    `1` or `-1`: it is a permutation of the coordinates with signs. -/
theorem rotation_preserves_iff (Q : Matrix (Fin k) (Fin k) 𝕜) (hQ : Qᵀ * Q = 1) :
    PreservesUncorrelated Q ↔
      ∃ m : MonomialMatrix 𝕜 k, Q = m.toMatrix ∧ ∀ j, m.scale j = 1 ∨ m.scale j = -1 := by
  rw [preserves_iff_monomial Q ⟨Qᵀ, hQ⟩]
  constructor
  · rintro ⟨m, rfl⟩
    refine ⟨m, rfl, fun j => ?_⟩
    have h := congrFun (congrFun hQ j) j
    have hsum : (m.toMatrixᵀ * m.toMatrix) j j = m.scale j * m.scale j := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, toMatrix, Matrix.of_apply]
      rw [Finset.sum_eq_single (m.perm j) (fun b _ hb => by simp [hb]) (by simp)]
      simp
    rw [hsum, Matrix.one_apply_eq] at h
    rcases mul_self_eq_one_iff.1 h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  · rintro ⟨m, hm, -⟩; exact ⟨m, hm⟩

end MonomialMatrix
