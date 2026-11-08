/-
  Monomial matrices and the Platonic Representation Theorem.

  A monomial matrix is the renaming and rescaling `Platonic.relabel` (`toMatrix_eq_relabel`),
  so every monomial change of coordinates keeps which coordinates of a learned
  representation are uncorrelated (`monomial_preserves_zeros`), unlike the rotations
  that the Platonic theorem allows (`Platonic.rotation_breaks_independence`). By
  `MonomialMatrix.preserves_iff_monomial`, no other invertible change of coordinates
  does. Over `ℝ`, where second moments are covariances.
-/
import MonomialMatrix
import Platonic.Basic

open Matrix

namespace MonomialMatrix

variable {k : ℕ}

/-! ## Connection to `Platonic` -/

open Platonic

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- A monomial matrix is the renaming and rescaling `relabel perm scale`. -/
theorem toMatrix_eq_relabel (m : MonomialMatrix ℝ k) : m.toMatrix = relabel m.perm m.scale := rfl

/-- The second moments after a monomial change of coordinates. -/
theorem secondMoment_transform (p : W → ℝ) (E : Emb W k) (m : MonomialMatrix ℝ k) (i j : Fin k) :
    secondMoment p (E * m.toMatrix) i j =
      m.scale i * m.scale j * secondMoment p E (m.perm i) (m.perm j) := by
  rw [toMatrix_eq_relabel, secondMoment_relabel]

/-- **A monomial change of coordinates keeps the pattern of correlations.** Coordinates
    `i` and `j` are uncorrelated afterwards exactly when the coordinates they came from
    were. -/
theorem monomial_preserves_zeros (p : W → ℝ) (E : Emb W k) (m : MonomialMatrix ℝ k)
    (i j : Fin k) :
    secondMoment p (E * m.toMatrix) i j = 0 ↔ secondMoment p E (m.perm i) (m.perm j) = 0 := by
  rw [secondMoment_transform]
  constructor
  · intro h
    rcases mul_eq_zero.1 h with h1 | h2
    · rcases mul_eq_zero.1 h1 with h3 | h3
      · exact absurd h3 (m.scale_ne_zero i)
      · exact absurd h3 (m.scale_ne_zero j)
    · exact h2
  · intro h
    rw [h, mul_zero]

omit [Fintype W] [DecidableEq W] in
/-- The embeddings reachable by monomial changes of coordinates are exactly those that
    are renamed and rescaled in the sense of `Platonic`. -/
theorem relabeled_iff (E E' : Emb W k) :
    (∃ m : MonomialMatrix ℝ k, E' = E * m.toMatrix) ↔
      ∃ (σ : Equiv.Perm (Fin k)) (d : Fin k → ℝ), (∀ j, d j ≠ 0) ∧ E' = E * relabel σ d := by
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨m.perm, m.scale, m.scale_ne_zero, rfl⟩
  · rintro ⟨σ, d, hd, rfl⟩
    exact ⟨⟨σ, d, hd⟩, rfl⟩

end MonomialMatrix
