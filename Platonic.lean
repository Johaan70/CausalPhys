/-
  Platonic: the Platonic Representation Theorem (Balestriero and LeCun, 2026),
  formalized in its finite, exact form.

  Setting. The world has finitely many states `W`. A modality observes the
  world through a map `obs : W → X` and learns an encoder `f : X → ℝᵏ`; what it
  represents of the world is the composite `f ∘ obs`, a `W × k` matrix (row `w`
  is the embedding of state `w`). Every modality is trained separately, with
  the same objective `L` on world embeddings.

  1. `platonic`: if every observation map is injective and the optimum of `L`
     is unique up to rotation, then any two modalities' optimal encoders give
     the same world embedding up to an orthogonal matrix. This holds for any
     number of modalities (`platonic_family`).
     Injectivity is needed: a modality that cannot tell two states apart gives
     them the same embedding, whatever it learns (`blind`).

  2. `frames_rotate`: two orthonormal `k`-frames whose columns lie in the same
     `k`-dimensional subspace differ by an orthogonal matrix. This is why the
     optimum is unique up to rotation in the spectral case.

  3. `spectral_unique` and `platonic_spectral`: if the optimal world embeddings
     of `L` are exactly the orthonormal frames in a fixed `k`-dimensional
     subspace `V`, then `L` meets the hypothesis of 1, so all modalities agree
     up to rotation.

  4. `rotation_breaks_independence` and `relabel_keeps_zeros`: agreement up to
     rotation is not causal agreement. A rotation can turn uncorrelated coordinates
     (no edge, in a linear-Gaussian model) into correlated ones; renaming and
     rescaling the coordinates keep which pairs are uncorrelated. Reading a causal
     graph off a learned representation needs it determined up to renaming and
     rescaling, which the theorem above does not give.

  Not formalized: that the spectral objective's optimal frames are exactly
  those spanning the top-`k` eigenspace when there is an eigengap (Ky Fan's
  maximum principle). It is a hypothesis of part 3, as uniqueness is a
  hypothesis in the paper. Nor the paper's perturbation bound for different
  positive pairs, its experiments, or its claims about next-token prediction.
-/
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Basic.Real.Basic

open Function Matrix

namespace Platonic

universe u v

variable {W : Type u} {k : ℕ}

/-- A world embedding: row `w` is the vector the representation gives state `w`. -/
abbrev Emb (W : Type u) (k : ℕ) := Matrix W (Fin k) ℝ

/-- `E'` is `E` rotated: `E' = E * Q` for an orthogonal `Q` (each row is rotated by `Qᵀ`). -/
def Rotated (E E' : Emb W k) : Prop :=
  ∃ Q : Matrix (Fin k) (Fin k) ℝ, Qᵀ * Q = 1 ∧ E' = E * Q

/-- `E` minimizes the objective over all world embeddings. -/
def WorldOptimal (L : Emb W k → ℝ) (E : Emb W k) : Prop :=
  ∀ E', L E ≤ L E'

/-- The optimum of `L` is unique up to rotation. -/
def UniqueUpToRotation (L : Emb W k → ℝ) : Prop :=
  ∀ E E', WorldOptimal L E → WorldOptimal L E' → Rotated E E'

/-- A modality: what it observes of each world state. -/
structure Modality (W : Type u) where
  X : Type v
  obs : W → X

/-- What an encoder makes of the world through a modality. -/
def Modality.embed (M : Modality.{u, v} W) (f : M.X → Fin k → ℝ) : Emb W k :=
  Matrix.of fun w => f (M.obs w)

/-- The encoder is optimal among all encoders on this modality. -/
def Optimal (L : Emb W k → ℝ) (M : Modality.{u, v} W) (f : M.X → Fin k → ℝ) : Prop :=
  ∀ g : M.X → Fin k → ℝ, L (M.embed f) ≤ L (M.embed g)

/-- Through an injective modality, every world embedding is some encoder's. -/
theorem realizable (M : Modality.{u, v} W) (hinj : Injective M.obs) (E : Emb W k) :
    ∃ g : M.X → Fin k → ℝ, M.embed g = E := by
  refine ⟨extend M.obs (fun w => E w) 0, ?_⟩
  ext w j
  simp [Modality.embed, hinj.extend_apply]

/-- So an optimal encoder on an injective modality is optimal over all world embeddings. -/
theorem optimal_world (L : Emb W k → ℝ) (M : Modality.{u, v} W) (hinj : Injective M.obs)
    {f : M.X → Fin k → ℝ} (hf : Optimal L M f) : WorldOptimal L (M.embed f) := by
  intro E
  obtain ⟨g, rfl⟩ := realizable M hinj E
  exact hf g

/-- **Platonic Representation Theorem.** Two modalities, trained separately with the
    same objective, through injective observations: their optimal encoders represent
    the world the same way up to rotation. -/
theorem platonic (L : Emb W k → ℝ) (hL : UniqueUpToRotation L)
    (M : Modality.{u, v} W) (M' : Modality.{u, v} W)
    (hM : Injective M.obs) (hM' : Injective M'.obs)
    {f : M.X → Fin k → ℝ} {f' : M'.X → Fin k → ℝ}
    (hf : Optimal L M f) (hf' : Optimal L M' f') :
    Rotated (M.embed f) (M'.embed f') :=
  hL _ _ (optimal_world L M hM hf) (optimal_world L M' hM' hf')

/-- Any number of modalities. -/
theorem platonic_family {ι : Type*} (L : Emb W k → ℝ) (hL : UniqueUpToRotation L)
    (M : ι → Modality.{u, v} W) (hM : ∀ i, Injective (M i).obs)
    (f : ∀ i, (M i).X → Fin k → ℝ) (hf : ∀ i, Optimal L (M i) (f i)) (i j : ι) :
    Rotated ((M i).embed (f i)) ((M j).embed (f j)) :=
  platonic L hL (M i) (M j) (hM i) (hM j) (hf i) (hf j)

/-- Why injectivity is needed: a modality that sees two states as the same gives
    them the same embedding, whatever encoder it learns. -/
theorem blind (M : Modality.{u, v} W) {w₁ w₂ : W} (h : M.obs w₁ = M.obs w₂)
    (f : M.X → Fin k → ℝ) : M.embed f w₁ = M.embed f w₂ := by
  show f (M.obs w₁) = f (M.obs w₂)
  rw [h]

/-! ## The spectral case -/

variable [Fintype W]

/-- Two orthonormal frames, the second in the span of the first, differ by a rotation. -/
theorem frames_rotate_of_factor {E₁ E₂ : Emb W k} (h₂ : E₂ᵀ * E₂ = 1)
    (h₁ : E₁ᵀ * E₁ = 1) {C : Matrix (Fin k) (Fin k) ℝ} (hC : E₂ = E₁ * C) :
    Rotated E₁ E₂ := by
  refine ⟨C, ?_, hC⟩
  calc Cᵀ * C = Cᵀ * (E₁ᵀ * E₁) * C := by rw [h₁, Matrix.mul_one]
    _ = (E₁ * C)ᵀ * (E₁ * C) := by
        rw [Matrix.transpose_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
    _ = 1 := by rw [← hC]; exact h₂

/-- The columns of an orthonormal frame span a subspace of dimension `k`. -/
theorem finrank_range_frame {E : Emb W k} (h : Eᵀ * E = 1) :
    Module.finrank ℝ (LinearMap.range E.mulVecLin) = k := by
  have hinj : Injective E.mulVecLin := by
    intro a b hab
    have : Eᵀ *ᵥ (E *ᵥ a) = Eᵀ *ᵥ (E *ᵥ b) := by
      simpa [Matrix.mulVecLin_apply] using congrArg (fun v => Eᵀ *ᵥ v) hab
    simpa [Matrix.mulVec_mulVec, h] using this
  rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun]

/-- **Frames in the same subspace differ by a rotation.** If the columns of two
    orthonormal `k`-frames lie in a subspace `V` of dimension `k`, the frames
    differ by an orthogonal matrix. -/
theorem frames_rotate (V : Submodule ℝ (W → ℝ)) (hV : Module.finrank ℝ V = k)
    {E₁ E₂ : Emb W k} (h₁ : E₁ᵀ * E₁ = 1) (h₂ : E₂ᵀ * E₂ = 1)
    (hin₁ : ∀ j, E₁.col j ∈ V) (hin₂ : ∀ j, E₂.col j ∈ V) :
    Rotated E₁ E₂ := by
  -- the columns of E₁ span V
  have hle : LinearMap.range E₁.mulVecLin ≤ V := by
    rw [Matrix.range_mulVecLin, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hin₁ j
  have hEq : LinearMap.range E₁.mulVecLin = V :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_range_frame h₁, hV])
  -- so each column of E₂ is E₁ times some coefficient vector
  have hc : ∀ j, ∃ c : Fin k → ℝ, E₁ *ᵥ c = E₂.col j := by
    intro j
    have : E₂.col j ∈ LinearMap.range E₁.mulVecLin := hEq ▸ hin₂ j
    obtain ⟨c, hc⟩ := this
    exact ⟨c, by simpa [Matrix.mulVecLin_apply] using hc⟩
  choose c hc using hc
  refine frames_rotate_of_factor h₂ h₁ (C := Matrix.of fun i j => c j i) ?_
  ext w j
  have := congrFun (hc j) w
  simp only [Matrix.mulVec, dotProduct, Matrix.col_apply] at this
  simp [Matrix.mul_apply, this]

/-- An objective whose optimal world embeddings are exactly the orthonormal frames
    with columns in `V`. For the spectral objective with an eigengap, `V` is the
    top-`k` eigenspace (Ky Fan); that step is assumed here, not proved. -/
def OptimaAreFramesIn (L : Emb W k → ℝ) (V : Submodule ℝ (W → ℝ)) : Prop :=
  ∀ E, WorldOptimal L E ↔ (Eᵀ * E = 1 ∧ ∀ j, E.col j ∈ V)

theorem spectral_unique (L : Emb W k → ℝ) (V : Submodule ℝ (W → ℝ))
    (hV : Module.finrank ℝ V = k) (hL : OptimaAreFramesIn L V) : UniqueUpToRotation L := by
  intro E E' hE hE'
  obtain ⟨h₁, hin₁⟩ := (hL E).1 hE
  obtain ⟨h₂, hin₂⟩ := (hL E').1 hE'
  exact frames_rotate V hV h₁ h₂ hin₁ hin₂

/-- **The spectral Platonic theorem.** All modalities trained with a spectral objective
    whose optimum is the `k`-dimensional subspace `V` represent the world the same way,
    up to rotation. -/
theorem platonic_spectral {ι : Type*} (L : Emb W k → ℝ) (V : Submodule ℝ (W → ℝ))
    (hV : Module.finrank ℝ V = k) (hL : OptimaAreFramesIn L V)
    (M : ι → Modality.{u, v} W) (hM : ∀ i, Injective (M i).obs)
    (f : ∀ i, (M i).X → Fin k → ℝ) (hf : ∀ i, Optimal L (M i) (f i)) (i j : ι) :
    Rotated ((M i).embed (f i)) ((M j).embed (f j)) :=
  platonic_family L (spectral_unique L V hV hL) M hM f hf i j

/-- The hypothesis of `platonic_spectral` is not empty: whenever some orthonormal frame
    lies in `V`, the objective that is `0` on such frames and `1` elsewhere meets it. -/
theorem framesIn_objective (V : Submodule ℝ (W → ℝ))
    (hex : ∃ E₀ : Emb W k, E₀ᵀ * E₀ = 1 ∧ ∀ j, E₀.col j ∈ V) :
    OptimaAreFramesIn (k := k)
      (fun E => by classical exact if Eᵀ * E = 1 ∧ ∀ j, E.col j ∈ V then 0 else 1) V := by
  classical
  obtain ⟨E₀, h₀⟩ := hex
  intro E
  constructor
  · intro hE
    by_contra hn
    have := hE E₀
    simp only [ite_eq_left h₀, ite_eq_right hn] at this
    norm_num at this
  · intro hE E'
    simp only [ite_eq_left hE]
    split_ifs <;> norm_num

/-! ## Agreement up to rotation is not causal agreement

The theorem above says that modalities agree up to rotation. Causal statements about
the coordinates of a representation do not survive rotations: in a linear-Gaussian
model, two coordinates are independent exactly when their covariance is zero, and a
rotation can turn zero covariance into nonzero covariance. Renaming and rescaling the
coordinates, on the other hand, keeps the pattern of zeros. So to read a causal graph
off a learned representation, it must be determined up to renaming and rescaling, not
just up to rotation. -/

/-- Second moments of the coordinates over the world, with weights `p` (the covariance
    when the coordinates have mean zero). -/
def secondMoment [DecidableEq W] (p : W → ℝ) (E : Emb W k) : Matrix (Fin k) (Fin k) ℝ :=
  Eᵀ * Matrix.diagonal p * E

/-- Mean of each coordinate over the world, with weights `p`. -/
def mean (p : W → ℝ) (E : Emb W k) (j : Fin k) : ℝ := ∑ w, p w * E w j

/-- Rotating the representation rotates its second moments. -/
theorem secondMoment_mul [DecidableEq W] (p : W → ℝ) (E : Emb W k) (Q : Matrix (Fin k) (Fin k) ℝ) :
    secondMoment p (E * Q) = Qᵀ * secondMoment p E * Q := by
  simp only [secondMoment, Matrix.transpose_mul, Matrix.mul_assoc]

/-- Equal variances and no correlations survive every rotation. -/
theorem isotropic_rotated [DecidableEq W] (p : W → ℝ) (E : Emb W k) {Q : Matrix (Fin k) (Fin k) ℝ}
    (hQ : Qᵀ * Q = 1) {c : ℝ} (hE : secondMoment p E = c • 1) :
    secondMoment p (E * Q) = c • 1 := by
  rw [secondMoment_mul, hE, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hQ]

/-- **A rotation turns uncorrelated coordinates into correlated ones.** In a world of four
    states, an embedding whose two coordinates have mean zero and no correlation, and a
    rotation of it (by the orthogonal matrix with entries ±3/5, ±4/5) whose coordinates
    still have mean zero but are correlated. Two modalities that agree up to this rotation
    disagree about whether there is an edge between the coordinates. -/
theorem rotation_breaks_independence :
    ∃ (p : Fin 4 → ℝ) (E : Emb (Fin 4) 2) (Q : Matrix (Fin 2) (Fin 2) ℝ),
      (∀ w, 0 < p w) ∧ ∑ w, p w = 1 ∧ Qᵀ * Q = 1 ∧ Rotated E (E * Q) ∧
      (∀ j, mean p E j = 0) ∧ (∀ j, mean p (E * Q) j = 0) ∧
      secondMoment p E 0 1 = 0 ∧ secondMoment p (E * Q) 0 1 ≠ 0 := by
  let p : Fin 4 → ℝ := ![1/6, 1/6, 1/3, 1/3]
  let E : Emb (Fin 4) 2 := !![1, 0; -1, 0; 0, 1; 0, -1]
  let Q : Matrix (Fin 2) (Fin 2) ℝ := !![3/5, -4/5; 4/5, 3/5]
  have hQ : Qᵀ * Q = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Q, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  refine ⟨p, E, Q, ?_, ?_, hQ, ⟨Q, hQ, rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro w; fin_cases w <;> simp [p]
  · simp [p, Fin.sum_univ_four]; norm_num
  · intro j; fin_cases j <;> simp [mean, p, E, Fin.sum_univ_four]
  · intro j; fin_cases j <;>
      simp [mean, p, E, Q, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]
  · simp [secondMoment, p, E, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal]
  · rw [secondMoment_mul]
    simp [secondMoment, p, E, Q, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two,
      Matrix.diagonal]
    norm_num

/-- Renaming the coordinates by `σ` and rescaling each by `d`: new coordinate `j` is
    `d j` times old coordinate `σ j`. -/
def relabel (σ : Equiv.Perm (Fin k)) (d : Fin k → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun a j => if a = σ j then d j else 0

theorem secondMoment_relabel [DecidableEq W] (p : W → ℝ) (E : Emb W k) (σ : Equiv.Perm (Fin k))
    (d : Fin k → ℝ) (i j : Fin k) :
    secondMoment p (E * relabel σ d) i j = d i * d j * secondMoment p E (σ i) (σ j) := by
  rw [secondMoment_mul]
  simp only [relabel, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
    ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- **Renaming and rescaling keep the pattern of correlations.** Coordinates `i` and `j`
    are uncorrelated after renaming and rescaling (by nonzero factors) exactly when the
    coordinates they came from were. -/
theorem relabel_keeps_zeros [DecidableEq W] (p : W → ℝ) (E : Emb W k) (σ : Equiv.Perm (Fin k))
    {d : Fin k → ℝ} (hd : ∀ j, d j ≠ 0) (i j : Fin k) :
    secondMoment p (E * relabel σ d) i j = 0 ↔ secondMoment p E (σ i) (σ j) = 0 := by
  rw [secondMoment_relabel]
  constructor
  · intro h
    rcases mul_eq_zero.1 h with h' | h'
    · exact absurd h' (mul_ne_zero (hd i) (hd j))
    · exact h'
  · intro h; rw [h, mul_zero]

end Platonic
