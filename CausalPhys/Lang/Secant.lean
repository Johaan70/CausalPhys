/-
  CausalPhys.Lang.Secant — uniqueness for nonlinear blocks (point 3b).

  Gale and Nikaido showed that a map whose Jacobian is a P-matrix (all
  principal minors positive) everywhere on a rectangle is injective there. Their
  proof needs derivatives. Many laws in chemistry and economics are
  *multi-affine*: affine in each variable separately (mass action K·[A]·[B],
  balances, linear demand). For those the difference of two states is exact:

      F(x) − F(y) = A(x, y) · (x − y),

  where A(x, y) is a "secant matrix" whose entries are slopes taken at states
  that mix the coordinates of x and y. If A(x, y) is a P-matrix for all states
  x, y in the domain, two different solutions are impossible: a P-matrix never
  reverses the sign of a nonzero vector (`PMat.IsP.nonrev`, proved in
  `CausalPhys.GaleNikaido`), while A(x, y)(x − y) = 0 for two solutions.

  This gives uniqueness among solutions in the domain, with no calculus, and
  with conditions (positive principal minors) that a tactic can compute.
-/
import CausalPhys.Lang.Linear
import CausalPhys.GaleNikaido
import Mathlib.Data.Fintype.Pi

set_option linter.unusedSectionVars false

namespace CausalPhys.Lang

open CausalPhys.Order

/-- The determinant of a 4 × 4 matrix, expanded along the first row. -/
theorem det_fin_four (A : Matrix (Fin 4) (Fin 4) ℝ) : A.det =
    A 0 0 * (A 1 1 * A 2 2 * A 3 3 - A 1 1 * A 2 3 * A 3 2 - A 1 2 * A 2 1 * A 3 3
      + A 1 2 * A 2 3 * A 3 1 + A 1 3 * A 2 1 * A 3 2 - A 1 3 * A 2 2 * A 3 1)
  - A 0 1 * (A 1 0 * A 2 2 * A 3 3 - A 1 0 * A 2 3 * A 3 2 - A 1 2 * A 2 0 * A 3 3
      + A 1 2 * A 2 3 * A 3 0 + A 1 3 * A 2 0 * A 3 2 - A 1 3 * A 2 2 * A 3 0)
  + A 0 2 * (A 1 0 * A 2 1 * A 3 3 - A 1 0 * A 2 3 * A 3 1 - A 1 1 * A 2 0 * A 3 3
      + A 1 1 * A 2 3 * A 3 0 + A 1 3 * A 2 0 * A 3 1 - A 1 3 * A 2 1 * A 3 0)
  - A 0 3 * (A 1 0 * A 2 1 * A 3 2 - A 1 0 * A 2 2 * A 3 1 - A 1 1 * A 2 0 * A 3 2
      + A 1 1 * A 2 2 * A 3 0 + A 1 2 * A 2 0 * A 3 1 - A 1 2 * A 2 1 * A 3 0) := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-! ## P-matrices from their minors -/

/-- A matrix whose principal minors on strictly increasing index lists are all
    positive is a P-matrix. -/
theorem isP_of_minors {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ)
    (h : ∀ (r : ℕ) (idx : Fin r → Fin k), StrictMono idx → 0 < (A.submatrix idx idx).det) :
    PMat.IsP A := by
  intro κ _ _ f hf
  classical
  let s : Finset (Fin k) := Finset.univ.map ⟨f, hf⟩
  have hmem : ∀ x, f x ∈ s := by intro x; simp [s]
  let iso := s.orderIsoOfFin rfl
  let g : Fin s.card → Fin k := fun i => (iso i).1
  have hg : StrictMono g := fun a b hab => iso.strictMono hab
  have hpos := h s.card g hg
  let e : κ ≃ Fin s.card := Equiv.ofBijective (fun x => iso.symm ⟨f x, hmem x⟩)
    ⟨fun a b hab => hf (by simpa using congrArg Subtype.val (iso.symm.injective hab)),
     fun i => by
      obtain ⟨x, -, hx⟩ := Finset.mem_map.1 (iso i).2
      refine ⟨x, ?_⟩
      apply iso.injective
      rw [OrderIso.apply_symm_apply]
      exact Subtype.ext (by simpa using hx)⟩
  have hge : ∀ x, g (e x) = f x := by
    intro x
    show ((iso (iso.symm ⟨f x, hmem x⟩)) : Fin k) = f x
    rw [OrderIso.apply_symm_apply]
  have : A.submatrix f f = (A.submatrix g g).submatrix e e := by
    ext a b; simp [hge]
  rw [this, Matrix.det_submatrix_equiv_self]
  exact hpos

namespace Setup

variable {E V : Type} [DecidableEq E] [DecidableEq V] [Inhabited V] {M : Model E V ℝ}
  (S : Setup M) {n : ℕ} (laws : Fin n → E) (vars : Fin n → V)

/-- The state that takes the first `j` endogenous coordinates from `x` and the
    rest from `y`. -/
def zmix (vars : Fin n → V) (j : ℕ) (x y : V → ℝ) : V → ℝ :=
  fun v => if v ∈ (List.ofFn vars).take j then x v else y v

/-- Slope of formula `i` in coordinate `j`, at the mixed state where the first
    `j` coordinates come from `x`. -/
def slope (x y : V → ℝ) (i j : Fin n) : ℝ :=
  S.formula laws vars i (Function.update (zmix vars j x y) (vars j) (y (vars j) + 1)) -
    S.formula laws vars i (zmix vars j x y)

/-- The secant matrix I − (slopes). -/
def secMat (x y : V → ℝ) : Matrix (Fin n) (Fin n) ℝ := 1 - Matrix.of (S.slope laws vars x y)

/-- Every formula is affine in each endogenous variable separately. -/
def MultiAffine : Prop :=
  ∀ i j (z : V → ℝ) (t : ℝ),
    S.formula laws vars i (Function.update z (vars j) t) =
      S.formula laws vars i (Function.update z (vars j) 0) +
        t * (S.formula laws vars i (Function.update z (vars j) 1) -
          S.formula laws vars i (Function.update z (vars j) 0))

variable {S laws vars}

theorem zmix_zero (x y : V → ℝ) : zmix vars 0 x y = y := by
  funext v; simp [zmix]

theorem zmix_succ (x y : V → ℝ) (j : Fin n) :
    zmix vars (j + 1) x y = Function.update (zmix vars j x y) (vars j) (x (vars j)) := by
  funext v
  unfold zmix
  have htake : (List.ofFn vars).take (j + 1) = (List.ofFn vars).take j ++ [vars j] := by
    rw [List.take_add_one]
    simp
  by_cases hv : v = vars j
  · subst hv
    simp [htake]
  · rw [Function.update_of_ne hv, htake]
    simp [hv]

theorem vars_mem_take_n (j : Fin n) : vars j ∈ (List.ofFn vars).take n := by
  rw [List.take_of_length_le (by simp)]
  simp

/-- One step of the telescope: changing coordinate `j` from `y` to `x` changes
    formula `i` by slope · (x − y). -/
theorem step_eq (hma : S.MultiAffine laws vars) (hinj : ∀ i j, vars i = vars j → i = j)
    (x y : V → ℝ) (i j : Fin n) :
    S.formula laws vars i (zmix vars (j + 1) x y) - S.formula laws vars i (zmix vars j x y) =
      S.slope laws vars x y i j * (x (vars j) - y (vars j)) := by
  have hz : zmix vars j x y (vars j) = y (vars j) := by
    unfold zmix
    have : vars j ∉ (List.ofFn vars).take j := by
      intro h
      obtain ⟨a, ha⟩ := List.mem_iff_get.1 h
      simp only [List.get_eq_getElem, List.getElem_take, List.getElem_ofFn] at ha
      have := hinj _ _ ha
      have hlt := a.2
      simp only [List.length_take, List.length_ofFn] at hlt
      have h2 := congrArg Fin.val this
      simp only at h2
      omega
    simp [this]
  rw [zmix_succ, slope]
  set z := zmix vars j x y
  have hzz : Function.update z (vars j) (y (vars j)) = z := by
    rw [← hz]; exact Function.update_eq_self _ _
  have e1 := hma i j z (x (vars j))
  have e2 := hma i j z (y (vars j) + 1)
  have e3 := hma i j z (y (vars j))
  rw [hzz] at e3
  rw [e1, e2, e3]
  ring

/-- The exact secant identity for two states with the same exogenous values. -/
theorem secant_identity (hE : S.Enum laws vars) (hma : S.MultiAffine laws vars) (x y : V → ℝ)
    (hexo : ∀ v, v ∈ S.exo → x v = y v) (i : Fin n) :
    S.formula laws vars i x - S.formula laws vars i y =
      ∑ j, S.slope laws vars x y i j * (x (vars j) - y (vars j)) := by
  have hinj := hE.2.2
  have htel : ∀ K : ℕ, K ≤ n →
      S.formula laws vars i (zmix vars K x y) - S.formula laws vars i y =
        ∑ j : Fin n, if (j : ℕ) < K then
          S.slope laws vars x y i j * (x (vars j) - y (vars j)) else 0 := by
    intro K
    induction K with
    | zero => intro _; simp [zmix_zero]
    | succ K ih =>
      intro hK
      have hj : K < n := hK
      have := step_eq hma hinj x y i ⟨K, hj⟩
      simp only at this
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (⟨K, hj⟩ : Fin n))]
      have hsplit : ∑ j ∈ Finset.univ.erase (⟨K, hj⟩ : Fin n), (if (j : ℕ) < K + 1 then
          S.slope laws vars x y i j * (x (vars j) - y (vars j)) else 0) =
          ∑ j : Fin n, if (j : ℕ) < K then
            S.slope laws vars x y i j * (x (vars j) - y (vars j)) else 0 := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (⟨K, hj⟩ : Fin n))]
        simp only [lt_irrefl, ite_false, add_zero]
        apply Finset.sum_congr rfl
        intro j hjm
        have hne : (j : ℕ) ≠ K := fun h => (Finset.mem_erase.1 hjm).1 (Fin.ext h)
        by_cases hlt : (j : ℕ) < K
        · simp [hlt, Nat.lt_succ_of_lt hlt]
        · have : ¬ (j : ℕ) < K + 1 := by omega
          simp [hlt, this]
      rw [hsplit, ← ih (Nat.le_of_succ_le hK)]
      simp only [Nat.lt_succ_self, ite_true]
      linarith
  have hn := htel n le_rfl
  have hx : S.formula laws vars i (zmix vars n x y) = S.formula laws vars i x := by
    unfold formula
    apply Mech.local_
    intro p _
    unfold zmix
    by_cases hp : p ∈ S.exo
    · split_ifs <;> simp [hexo p hp]
    · obtain ⟨j, rfl⟩ := hE.cover hp
      simp [vars_mem_take_n j]
  rw [hx] at hn
  rw [hn]
  apply Finset.sum_congr rfl
  intro j _
  simp [j.2]

/-- Uniqueness for multi-affine setups whose secant matrices are P-matrices on
    the domain. -/
theorem secant_unique (hE : S.Enum laws vars) (hma : S.MultiAffine laws vars)
    (hP : ∀ x y, M.dom x → M.dom y → (∀ v, v ∈ S.exo → x v = y v) →
      PMat.IsP (S.secMat laws vars x y))
    {u x y : V → ℝ} (hx : S.scm.Solves u x) (hy : S.scm.Solves u y)
    (hDx : M.dom x) (hDy : M.dom y) : x = y := by
  obtain ⟨hx1, hx2⟩ := (hE.solves_iff u x).1 hx
  obtain ⟨hy1, hy2⟩ := (hE.solves_iff u y).1 hy
  have hexo : ∀ v, v ∈ S.exo → x v = y v := fun v hv => (hx1 v hv).trans (hy1 v hv).symm
  let w : Fin n → ℝ := fun i => x (vars i) - y (vars i)
  have hw : (S.secMat laws vars x y).mulVec w = 0 := by
    funext i
    have hid := secant_identity hE hma x y hexo i
    rw [← hx2 i, ← hy2 i] at hid
    rw [secMat, Matrix.sub_mulVec, Matrix.one_mulVec]
    simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply, w]
    rw [← hid]
    ring
  have hw0 : w = 0 := by
    by_contra hne
    obtain ⟨i, hi⟩ := (hP x y hDx hDy hexo).nonrev w hne
    rw [hw] at hi
    simp at hi
  funext v
  by_cases hv : v ∈ S.exo
  · exact hexo v hv
  · obtain ⟨j, rfl⟩ := hE.cover hv
    have := congrFun hw0 j
    simp only [w, Pi.zero_apply, sub_eq_zero] at this
    exact this

end Setup
end CausalPhys.Lang
