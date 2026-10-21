/-
  CausalPhys.Lang.Blockwise — the linear criterion, block by block (phase 3a).

  `Linear.lean` needs every formula of a setup to be affine in all endogenous
  variables. Here each block is treated on its own, in causal order:

    * a formula of block b must be affine in the variables of block b; its
      coefficients may depend on exogenous variables and on variables of
      LOWER blocks (whose values are already settled), in any nonlinear way;
    * for every block, det(I − C_b) ≠ 0 whenever the exogenous values are fixed
      and the lower blocks satisfy their laws.

  Then the setup has exactly one outcome. Acyclic parts are blocks of size one
  with C_b = 0, so they cost nothing; a nonlinear formula downstream of a
  linear block is fine as long as it is affine in its own block's variables.

  Proof: uniqueness by induction on the blocks (two solutions that agree below
  block b have the same C_b and d_b there, so their difference on block b is in
  the kernel of I − C_b); existence by iterating "solve every block given the
  current values below it", which settles block b after b + 1 rounds, exactly
  like the existence proof for acyclic models in `Core.lean`.
-/
import CausalPhys.Lang.Linear

set_option linter.unusedSectionVars false

namespace CausalPhys.Lang
namespace Setup

open CausalPhys.Order

variable {E V : Type} [DecidableEq E] [DecidableEq V] [Inhabited V] {M : Model E V ℝ}
  (S : Setup M)

variable {n m : ℕ} (laws : Fin n → E) (vars : Fin n → V) (blk : Fin n → Fin m)
  (bv : Fin m → List V)

/-- Zero the variables of block `b`, keep everything else. -/
@[nolint unusedArguments]
def bbase (_S : Setup M) (b : Fin m) (s : V → ℝ) : V → ℝ :=
  fun v => if v ∈ bv b then 0 else s v

/-- Coefficient of `vars j` in formula `i`, relative to the block of `i`. -/
def bcoef (s : V → ℝ) (i j : Fin n) : ℝ :=
  S.formula laws vars i (Function.update (S.bbase bv (blk i) s) (vars j) 1) -
    S.formula laws vars i (S.bbase bv (blk i) s)

/-- Constant part of formula `i`, relative to its block. -/
def bconst (s : V → ℝ) (i : Fin n) : ℝ := S.formula laws vars i (S.bbase bv (blk i) s)

/-- Every formula is affine in the variables of its own block. -/
def BlockAffine : Prop :=
  ∀ i s, S.formula laws vars i s = S.bconst laws vars blk bv s i +
    ∑ j, if blk j = blk i then S.bcoef laws vars blk bv s i j * s (vars j) else 0

/-- I − C on block `b`, the identity elsewhere. -/
def bmat (b : Fin m) (s : V → ℝ) : Matrix (Fin n) (Fin n) ℝ := fun i j =>
  if blk i = b ∧ blk j = b then (if i = j then 1 else 0) - S.bcoef laws vars blk bv s i j
  else (if i = j then 1 else 0)

/-- The constants on block `b`, zero elsewhere. -/
def bvec (b : Fin m) (s : V → ℝ) : Fin n → ℝ := fun i =>
  if blk i = b then S.bconst laws vars blk bv s i else 0

/-- The enumeration, its blocks, and the causal order between blocks: a formula
    reads only exogenous variables and variables of its own or lower blocks. -/
def BlockEnum : Prop :=
  S.Enum laws vars ∧
  (∀ j, vars j ∈ bv (blk j)) ∧
  (∀ b, ∀ v ∈ bv b, ∃ j, vars j = v ∧ blk j = b) ∧
  (∀ i, ∀ p ∈ (M.mechOf (laws i) (vars i)).parents,
    p ∈ S.exo ∨ ∃ j, vars j = p ∧ blk j ≤ blk i)

instance : Decidable (S.BlockEnum laws vars blk bv) := by unfold BlockEnum; infer_instance

variable {S laws vars blk bv}

/-! ### Locality: block `b` only sees the exogenous values and lower blocks -/

/-- `s` and `t` agree on the exogenous variables and on all blocks below `b`. -/
def AgreeBelow (vars : Fin n → V) (blk : Fin n → Fin m) (S : Setup M) (b : Fin m)
    (s t : V → ℝ) : Prop :=
  (∀ v, v ∈ S.exo → s v = t v) ∧ ∀ j, blk j < b → s (vars j) = t (vars j)


/-- The formula of `i`, evaluated on two states that agree on its block-reads. -/
theorem formula_congr (hE : S.BlockEnum laws vars blk bv) (i : Fin n) {x y : V → ℝ}
    (hxy : ∀ v, (v ∈ S.exo ∨ ∃ j, vars j = v ∧ blk j ≤ blk i) → x v = y v) :
    S.formula laws vars i x = S.formula laws vars i y := by
  unfold formula
  apply Mech.local_
  intro p hp
  exact hxy p (hE.2.2.2 i p hp)

theorem bbase_agree (hE : S.BlockEnum laws vars blk bv) {i : Fin n} {s t : V → ℝ}
    (h : AgreeBelow vars blk S (blk i) s t) :
    ∀ v, (v ∈ S.exo ∨ ∃ j, vars j = v ∧ blk j ≤ blk i) →
      S.bbase bv (blk i) s v = S.bbase bv (blk i) t v := by
  intro v hv
  unfold bbase
  by_cases hb : v ∈ bv (blk i)
  · simp [hb]
  · simp only [hb, ite_false]
    rcases hv with hv | ⟨j, rfl, hj⟩
    · exact h.1 v hv
    · have hne : blk j ≠ blk i := by
        intro he; exact hb (he ▸ hE.2.1 j)
      exact h.2 j (lt_of_le_of_ne hj hne)

theorem bconst_congr (hE : S.BlockEnum laws vars blk bv) {i : Fin n} {s t : V → ℝ}
    (h : AgreeBelow vars blk S (blk i) s t) :
    S.bconst laws vars blk bv s i = S.bconst laws vars blk bv t i :=
  formula_congr hE i (bbase_agree hE h)

theorem bcoef_congr (hE : S.BlockEnum laws vars blk bv) {i : Fin n} {s t : V → ℝ}
    (h : AgreeBelow vars blk S (blk i) s t) (j : Fin n) :
    S.bcoef laws vars blk bv s i j = S.bcoef laws vars blk bv t i j := by
  unfold bcoef
  rw [bconst_congr hE h |> fun _ => formula_congr hE i (bbase_agree hE h)]
  congr 1
  apply formula_congr hE i
  intro v hv
  by_cases hvj : v = vars j
  · subst hvj; simp
  · rw [Function.update_of_ne hvj, Function.update_of_ne hvj]
    exact bbase_agree hE h v hv

theorem bmat_congr (hE : S.BlockEnum laws vars blk bv) {b : Fin m} {s t : V → ℝ}
    (h : AgreeBelow vars blk S b s t) : S.bmat laws vars blk bv b s = S.bmat laws vars blk bv b t := by
  funext i j
  unfold bmat
  by_cases hij : blk i = b ∧ blk j = b
  · simp only [hij, and_self, ite_true]
    rw [bcoef_congr hE (by rw [hij.1]; exact h) j]
  · simp only [hij, ite_false]

theorem bvec_congr (hE : S.BlockEnum laws vars blk bv) {b : Fin m} {s t : V → ℝ}
    (h : AgreeBelow vars blk S b s t) : S.bvec laws vars blk bv b s = S.bvec laws vars blk bv b t := by
  funext i
  unfold bvec
  by_cases hi : blk i = b
  · simp only [hi, ite_true]
    rw [bconst_congr hE (by rw [hi]; exact h)]
  · simp only [hi, ite_false]

/-- On block `b`, the laws are the linear system `bmat b s · x = bvec b s`
    (rows outside `b` are trivial when `x` vanishes there). -/
theorem bmat_row (b : Fin m) (s : V → ℝ)
    (x : Fin n → ℝ) (i : Fin n) (hi : blk i = b) :
    (S.bmat laws vars blk bv b s).mulVec x i =
      x i - ∑ j, if blk j = b then S.bcoef laws vars blk bv s i j * x j else 0 := by
  simp only [Matrix.mulVec, dotProduct, bmat, hi, true_and]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  have : ∀ j ∈ Finset.univ.erase i,
      (if blk j = b then (if i = j then (1 : ℝ) else 0) - S.bcoef laws vars blk bv s i j
        else if i = j then 1 else 0) * x j =
      -(if blk j = b then S.bcoef laws vars blk bv s i j * x j else 0) := by
    intro j hj
    have hij : i ≠ j := fun h => (Finset.mem_erase.1 hj).1 h.symm
    split_ifs <;> simp_all
  rw [Finset.sum_congr rfl this, Finset.sum_neg_distrib]
  rw [← Finset.sum_erase_add (s := Finset.univ)
    (f := fun j => if blk j = b then S.bcoef laws vars blk bv s i j * x j else 0)
    (Finset.mem_univ i)]
  simp only [hi, ite_true]
  ring

/-! ### Uniqueness, block by block -/

theorem block_unique (hE : S.BlockEnum laws vars blk bv) (haff : S.BlockAffine laws vars blk bv)
    {u : V → ℝ} (hdet : ∀ b s, (∀ v, v ∈ S.exo → s v = u v) →
      (∀ j, blk j < b → s (vars j) = S.formula laws vars j s) →
      (S.bmat laws vars blk bv b s).det ≠ 0)
    {s t : V → ℝ} (hs : S.scm.Solves u s) (ht : S.scm.Solves u t) : s = t := by
  obtain ⟨hs1, hs2⟩ := (hE.1.solves_iff u s).1 hs
  obtain ⟨ht1, ht2⟩ := (hE.1.solves_iff u t).1 ht
  have hexo : ∀ v, v ∈ S.exo → s v = t v := fun v hv => (hs1 v hv).trans (ht1 v hv).symm
  have key : ∀ r : ℕ, ∀ j : Fin n, (blk j).val = r → s (vars j) = t (vars j) := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro j hj
      set b := blk j
      have hbelow : AgreeBelow vars blk S b s t :=
        ⟨hexo, fun j' hj' => ih (blk j').val (hj ▸ hj') j' rfl⟩
      let w : Fin n → ℝ := fun k => if blk k = b then s (vars k) - t (vars k) else 0
      have hw : (S.bmat laws vars blk bv b s).mulVec w = 0 := by
        funext i
        by_cases hi : blk i = b
        · rw [bmat_row b s w i hi]
          have es := haff i s
          have et := haff i t
          rw [← hs2 i] at es
          rw [← ht2 i] at et
          rw [bconst_congr hE (hi ▸ hbelow)] at es
          have hc : ∀ k, S.bcoef laws vars blk bv s i k = S.bcoef laws vars blk bv t i k :=
            bcoef_congr hE (hi ▸ hbelow)
          simp only [w, Pi.zero_apply, hi, ite_true]
          simp only [hi] at es et
          have : ∑ k, (if blk k = b then S.bcoef laws vars blk bv s i k *
              (if blk k = b then s (vars k) - t (vars k) else 0) else 0) =
              (∑ k, if blk k = b then S.bcoef laws vars blk bv s i k * s (vars k) else 0) -
              ∑ k, if blk k = b then S.bcoef laws vars blk bv t i k * t (vars k) else 0 := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro k _
            by_cases hk : blk k = b
            · simp only [hk, ite_true, hc k]; ring
            · simp [hk]
          rw [this]
          linarith
        · simp only [Matrix.mulVec, dotProduct, bmat, hi, false_and, ite_false, Pi.zero_apply]
          rw [Finset.sum_eq_single i]
          · simp [w, hi]
          · intro k _ hk; simp [Ne.symm hk]
          · simp
      have hdet' := hdet b s hs1 (fun j' _ => hs2 j')
      have h0 := Matrix.eq_zero_of_mulVec_eq_zero hdet' hw
      have := congrFun h0 j
      simp only [w, Pi.zero_apply] at this
      rw [ite_eq_left_of_eq_true _ _ (eq_self _), sub_eq_zero] at this
      exact this
  funext v
  by_cases hv : v ∈ S.exo
  · exact hexo v hv
  · obtain ⟨j, rfl⟩ := hE.1.cover hv
    exact key _ j rfl

/-! ### Existence: solve the blocks in order -/

variable (S laws vars blk bv) in
/-- One round: every block solved with the current values below it. -/
noncomputable def step (u : V → ℝ) (s : V → ℝ) : V → ℝ := by
  classical
  exact fun v =>
    if v ∈ S.exo then u v
    else if h : ∃ j, vars j = v then
      ((S.bmat laws vars blk bv (blk (Classical.choose h)) s)⁻¹.mulVec
        (S.bvec laws vars blk bv (blk (Classical.choose h)) s)) (Classical.choose h)
    else u v

theorem step_var (hE : S.BlockEnum laws vars blk bv) (u s : V → ℝ) (j : Fin n) :
    S.step laws vars blk bv u s (vars j) =
      ((S.bmat laws vars blk bv (blk j) s)⁻¹.mulVec (S.bvec laws vars blk bv (blk j) s)) j := by
  classical
  have hne : vars j ∉ S.exo := hE.1.not_exo j
  have h : ∃ j', vars j' = vars j := ⟨j, rfl⟩
  have hj : Classical.choose h = j := hE.1.2.2 _ _ (Classical.choose_spec h)
  unfold step
  simp only [hne, ite_false, h, dite_true]
  rw [hj]

theorem step_exo (u s : V → ℝ) {v : V} (hv : v ∈ S.exo) :
    S.step laws vars blk bv u s v = u v := by
  unfold step; simp [hv]

theorem iter_exo (u : V → ℝ) (k : ℕ) {v : V} (hv : v ∈ S.exo) :
    (S.step laws vars blk bv u)^[k] u v = u v := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact step_exo u _ hv

/-- After `blk j + 1` rounds the value of `vars j` no longer changes. -/
theorem iter_stable (hE : S.BlockEnum laws vars blk bv) (u : V → ℝ) :
    ∀ r : ℕ, ∀ j : Fin n, (blk j).val = r → ∀ k, r < k →
      (S.step laws vars blk bv u)^[k] u (vars j) =
        (S.step laws vars blk bv u)^[r + 1] u (vars j) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro j hj k hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', step_var hE, step_var hE]
    have hag : AgreeBelow vars blk S (blk j) ((S.step laws vars blk bv u)^[k] u)
        ((S.step laws vars blk bv u)^[r] u) := by
      refine ⟨fun v hv => by rw [iter_exo u k hv, iter_exo u r hv], fun j' hj' => ?_⟩
      have hlt : (blk j').val < r := hj ▸ hj'
      rw [ih _ hlt j' rfl k (by omega), ih _ hlt j' rfl r hlt]
    rw [bmat_congr hE hag, bvec_congr hE hag]

theorem block_exists (hE : S.BlockEnum laws vars blk bv) (haff : S.BlockAffine laws vars blk bv)
    {u : V → ℝ} (hdet : ∀ b s, (∀ v, v ∈ S.exo → s v = u v) →
      (∀ j, blk j < b → s (vars j) = S.formula laws vars j s) →
      (S.bmat laws vars blk bv b s).det ≠ 0) :
    ∃ s, S.scm.Solves u s := by
  refine ⟨(S.step laws vars blk bv u)^[m] u, ?_⟩
  have hexo : ∀ v, v ∈ S.exo → (S.step laws vars blk bv u)^[m] u v = u v :=
    fun v hv => iter_exo u m hv
  -- the state after m rounds is a fixed point on the endogenous variables
  have hfix : ∀ j, S.step laws vars blk bv u ((S.step laws vars blk bv u)^[m] u) (vars j) =
      (S.step laws vars blk bv u)^[m] u (vars j) := by
    intro j
    have hjm : (blk j).val < m := (blk j).isLt
    rw [← Function.iterate_succ_apply' (S.step laws vars blk bv u) m u,
      iter_stable hE u _ j rfl (m + 1) (by omega), iter_stable hE u _ j rfl m hjm]
  refine (hE.1.solves_iff u _).2 ⟨hexo, ?_⟩
  have key : ∀ r : ℕ, ∀ i : Fin n, (blk i).val = r →
      (S.step laws vars blk bv u)^[m] u (vars i) =
        S.formula laws vars i ((S.step laws vars blk bv u)^[m] u) := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
    intro i hi
    have hlow : ∀ j, blk j < blk i → (S.step laws vars blk bv u)^[m] u (vars j) =
        S.formula laws vars j ((S.step laws vars blk bv u)^[m] u) :=
      fun j hj => ih (blk j).val (hi ▸ hj) j rfl
    have hA : IsUnit (S.bmat laws vars blk bv (blk i)
        ((S.step laws vars blk bv u)^[m] u)).det :=
      isUnit_iff_ne_zero.2 (hdet (blk i) _ hexo hlow)
    have hy := Matrix.mulVec_mulVec (S.bvec laws vars blk bv (blk i)
        ((S.step laws vars blk bv u)^[m] u))
      (S.bmat laws vars blk bv (blk i) ((S.step laws vars blk bv u)^[m] u))
      (S.bmat laws vars blk bv (blk i) ((S.step laws vars blk bv u)^[m] u))⁻¹
    rw [Matrix.mul_nonsing_inv _ hA, Matrix.one_mulVec] at hy
    have hsy : ∀ j, blk j = blk i → (S.step laws vars blk bv u)^[m] u (vars j) =
        ((S.bmat laws vars blk bv (blk i) ((S.step laws vars blk bv u)^[m] u))⁻¹.mulVec
          (S.bvec laws vars blk bv (blk i) ((S.step laws vars blk bv u)^[m] u))) j := by
      intro j hj
      rw [← hfix j, step_var hE, hj]
    have row := congrFun hy i
    rw [bmat_row (blk i) _ _ i rfl] at row
    simp only [bvec, ite_true] at row
    rw [haff i _, hsy i rfl]
    have : (∑ j, if blk j = blk i then S.bcoef laws vars blk bv
        ((S.step laws vars blk bv u)^[m] u) i j * (S.step laws vars blk bv u)^[m] u (vars j)
        else 0) =
        ∑ j, if blk j = blk i then S.bcoef laws vars blk bv
          ((S.step laws vars blk bv u)^[m] u) i j *
          ((S.bmat laws vars blk bv (blk i) ((S.step laws vars blk bv u)^[m] u))⁻¹.mulVec
            (S.bvec laws vars blk bv (blk i) ((S.step laws vars blk bv u)^[m] u))) j
          else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : blk j = blk i
      · simp only [hj, ite_true, hsy j hj]
      · simp only [hj, ite_false]
    rw [this]
    linarith
  exact fun i => key _ i rfl

/-! ### Computing the determinant of one block -/

/-- A matrix that is the identity outside the rows and columns `idx` has the
    determinant of its `idx × idx` part. -/
theorem det_eq_submatrix_of_one_outside {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (idx : Fin k → Fin n) (hinj : Function.Injective idx)
    (hout : ∀ i j, ((∀ a, idx a ≠ i) ∨ (∀ a, idx a ≠ j)) → A i j = if i = j then 1 else 0) :
    A.det = (A.submatrix idx idx).det := by
  classical
  let p : Fin n → Prop := fun i => ∃ a, idx a = i
  let e := (Equiv.sumCompl p).symm
  rw [← Matrix.det_reindex_self e A, ← Matrix.fromBlocks_toBlocks (Matrix.reindex e e A)]
  have h21 : (Matrix.reindex e e A).toBlocks₂₁ = 0 := by
    ext i j
    simp only [Matrix.toBlocks₂₁, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
      Matrix.zero_apply, e, Equiv.symm_symm, Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr]
    rw [hout _ _ (Or.inl fun a ha => i.2 ⟨a, ha⟩)]
    have : (i : Fin n) ≠ j := fun h => i.2 (h ▸ j.2)
    simp [this]
  have h22 : (Matrix.reindex e e A).toBlocks₂₂ = 1 := by
    ext i j
    simp only [Matrix.toBlocks₂₂, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
      e, Equiv.symm_symm, Equiv.sumCompl_apply_inr]
    rw [hout _ _ (Or.inl fun a ha => i.2 ⟨a, ha⟩), Matrix.one_apply]
    by_cases hij : i = j
    · simp [hij]
    · have : (i : Fin n) ≠ j := fun h => hij (Subtype.ext h)
      simp [hij, this]
  rw [h21, Matrix.det_fromBlocks_zero₂₁, h22, Matrix.det_one, mul_one]
  let f : Fin k ≃ {x // p x} :=
    Equiv.ofBijective (fun a => ⟨idx a, a, rfl⟩)
      ⟨fun a b h => hinj (congrArg Subtype.val h), fun ⟨_, a, ha⟩ => ⟨a, Subtype.ext ha⟩⟩
  rw [← Matrix.det_submatrix_equiv_self f]
  congr 1

/-- The determinant of `bmat b s` is the determinant of block `b` alone, given an
    enumeration `idx` of the laws in block `b`. -/
theorem det_bmat {b : Fin m} {k : ℕ} (idx : Fin k → Fin n) (hinj : Function.Injective idx)
    (hrange : ∀ i, blk i = b → ∃ a, idx a = i) (s : V → ℝ) :
    (S.bmat laws vars blk bv b s).det =
      ((S.bmat laws vars blk bv b s).submatrix idx idx).det := by
  apply det_eq_submatrix_of_one_outside _ idx hinj
  intro i j h
  unfold bmat
  have : ¬ (blk i = b ∧ blk j = b) := by
    rintro ⟨hi, hj⟩
    rcases h with h | h
    · obtain ⟨a, ha⟩ := hrange i hi; exact h a ha
    · obtain ⟨a, ha⟩ := hrange j hj; exact h a ha
  simp only [this, ite_false]

/-- The blockwise linear criterion: exactly one outcome. -/
theorem block_existsUnique (hE : S.BlockEnum laws vars blk bv)
    (haff : S.BlockAffine laws vars blk bv) (u : V → ℝ)
    (hdet : ∀ b s, (∀ v, v ∈ S.exo → s v = u v) →
      (∀ j, blk j < b → s (vars j) = S.formula laws vars j s) →
      (S.bmat laws vars blk bv b s).det ≠ 0) :
    ∃! s, S.scm.Solves u s := by
  obtain ⟨s, hs⟩ := block_exists hE haff hdet
  exact ⟨s, hs, fun t ht => block_unique hE haff hdet ht hs⟩

end Setup
end CausalPhys.Lang
