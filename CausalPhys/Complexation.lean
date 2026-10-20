/-
  CausalPhys.Complexation — et ikke-lineært system med to koblede reaksjoner.

  Trinnvis kompleksdannelse (f.eks. Ag⁺ + NH₃):
      M + L  ⇌ ML     [ML]  = K₁·[M]·[L]
      ML + L ⇌ ML₂    [ML₂] = K₂·[ML]·[L]
  med massebalanser
      m₀ = [M] + [ML] + [ML₂]          (metall)
      l₀ = [L] + [ML] + 2·[ML₂]        (ligand)

  Bevist:
    1. Struktur: Lean finner at alle fire ukjente danner ÉN syklisk blokk
       (`complex_one_block`), og strukturen er uniform, så blokken er den
       samme for enhver lesning.
    2. Eksistens og entydighet på det fysiske domenet (`eq_exists_unique`).
       Beviset reduserer systemet til én ligning i fri ligand L,
           F(L) = L + m₀·g(L) − l₀ = 0,  g(L) = (K₁L + 2K₁K₂L²)/(1 + K₁L + K₁K₂L²),
       viser at F er strengt voksende (en eksakt polynomidentitet), og finner
       roten med mellomverdisetningen.
    3. Le Chatelier (`more_metal_less_free_ligand`): mer metall gir mindre fri
       ligand og mer bundet ligand.
    4. Buffer (`buffered_eq`): holder labben [L] fast, faller ligandbalansen
       bort, blokken krymper til tre, og løsningen får lukket form.
-/
import CausalPhys.DulmageMendelsohn
import CausalPhys.Physics

set_option linter.unusedSectionVars false
set_option linter.ambiguousOpen false

namespace CausalPhys
namespace Complex

/-! ## 1. Struktur og blokker -/

inductive Sp | M | L | ML | ML2
deriving DecidableEq, Repr

instance : Inhabited Sp := ⟨.M⟩

inductive Eq4 | k1 | k2 | metal | ligand
deriving DecidableEq, Repr

open CausalPhys.Order in
def complexS : Struct Eq4 Sp where
  eqList := [.k1, .k2, .metal, .ligand]
  varList := [.M, .L, .ML, .ML2]
  eq_complete := by intro e; cases e <;> simp
  var_complete := by intro v; cases v <;> simp
  canSolve
    | .k1 => [.ML]
    | .k2 => [.ML2]
    | .metal => [.M]
    | .ligand => [.L]
  deps
    | .k1, .ML => [.M, .L]
    | .k2, .ML2 => [.ML, .L]
    | .metal, .M => [.ML, .ML2]
    | .ligand, .L => [.ML, .ML2]
    | _, _ => []
  exo := []

def complexVars : Eq4 → List Sp
  | .k1 => [.ML, .M, .L]
  | .k2 => [.ML2, .ML, .L]
  | .metal => [.M, .ML, .ML2]
  | .ligand => [.L, .ML, .ML2]

open CausalPhys.Order in
theorem complex_valid : Valid complexS (computeC complexS) := by decide
theorem complex_uniform : DM.Uniform complexS complexVars := by decide
open CausalPhys.Order in
/-- Alle fire ukjente danner én syklisk blokk. -/
theorem complex_one_block : blockOf complexS .k1 = [.k1, .k2, .metal, .ligand] := by decide
open CausalPhys.Order in
theorem complex_cyclic : ¬ OrderedLT complexS (computeC complexS) := by decide

/-- Bufret: labben holder [L] fast; ligandbalansen faller bort. -/
inductive Eq3 | k1 | k2 | metal
deriving DecidableEq, Repr

open CausalPhys.Order in
def bufferedS : Struct Eq3 Sp where
  eqList := [.k1, .k2, .metal]
  varList := [.M, .L, .ML, .ML2]
  eq_complete := by intro e; cases e <;> simp
  var_complete := by intro v; cases v <;> simp
  canSolve
    | .k1 => [.ML]
    | .k2 => [.ML2]
    | .metal => [.M]
  deps
    | .k1, .ML => [.M, .L]
    | .k2, .ML2 => [.ML, .L]
    | .metal, .M => [.ML, .ML2]
    | _, _ => []
  exo := [.L]

open CausalPhys.Order in
theorem buffered_valid : Valid bufferedS (computeC bufferedS) := by decide
open CausalPhys.Order in
/-- Med buffer krymper blokken til {M, ML, ML₂}. -/
theorem buffered_block : blockOf bufferedS .k1 = [.k1, .k2, .metal] := by decide

/-! ## 2. Eksistens og entydighet -/

structure Sys where
  m0 : ℝ
  l0 : ℝ
  K1 : ℝ
  K2 : ℝ
  hm : 0 < m0
  hl : 0 < l0
  hK1 : 0 < K1
  hK2 : 0 < K2

namespace Sys

variable (r : Sys)

/-- Likevekt: positive konsentrasjoner, to massevirkningslover, to balanser. -/
def IsEq (M L ML ML2 : ℝ) : Prop :=
  0 < M ∧ 0 < L ∧ ML = r.K1 * M * L ∧ ML2 = r.K2 * ML * L ∧
  r.m0 = M + ML + ML2 ∧ r.l0 = L + ML + 2 * ML2

noncomputable def den (b : ℝ) : ℝ := 1 + r.K1 * b + r.K1 * r.K2 * b ^ 2
noncomputable def num (b : ℝ) : ℝ := r.K1 * b + 2 * (r.K1 * r.K2) * b ^ 2
noncomputable def g (b : ℝ) : ℝ := r.num b / r.den b
noncomputable def F (b : ℝ) : ℝ := b + r.m0 * r.g b - r.l0

theorem den_pos {b : ℝ} (hb : 0 ≤ b) : 0 < r.den b := by
  unfold den; have := r.hK1; have := r.hK2; positivity

theorem g_nonneg {b : ℝ} (hb : 0 ≤ b) : 0 ≤ r.g b := by
  unfold g num; have := r.hK1; have := r.hK2; have := r.den_pos hb; positivity

theorem g_pos {b : ℝ} (hb : 0 < b) : 0 < r.g b := by
  unfold g num; have := r.hK1; have := r.hK2; have := r.den_pos hb.le; positivity

/-- Nøkkelidentiteten: N(x)D(y) − N(y)D(x) = (x − y)(K₁ + 2K₁K₂(x + y) + K₁²K₂·xy). -/
theorem cross (x y : ℝ) :
    r.num x * r.den y - r.num y * r.den x
      = (x - y) * (r.K1 + 2 * (r.K1 * r.K2) * (x + y) + r.K1 * (r.K1 * r.K2) * x * y) := by
  unfold num den; ring

/-- g er voksende på [0, ∞). -/
theorem g_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : r.g x ≤ r.g y := by
  have hy : 0 ≤ y := le_trans hx hxy
  have dx := r.den_pos hx
  have dy := r.den_pos hy
  unfold g
  rw [div_le_div_iff₀ dx dy]
  have hc := r.cross x y
  have hbr : 0 ≤ r.K1 + 2 * (r.K1 * r.K2) * (x + y) + r.K1 * (r.K1 * r.K2) * x * y := by
    have := r.hK1; have := r.hK2; positivity
  nlinarith [mul_nonneg (sub_nonneg.2 hxy) hbr]

/-- F er strengt voksende på [0, ∞). -/
theorem F_strictMono {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) : r.F x < r.F y := by
  unfold F
  have := r.g_mono hx hxy.le
  have := r.hm
  nlinarith

/-- Fra likevekt til F(L) = 0. -/
theorem F_zero_of_eq {M L ML ML2 : ℝ} (h : r.IsEq M L ML ML2) :
    r.F L = 0 ∧ M = r.m0 / r.den L := by
  obtain ⟨hM, hL, h1, h2, hm, hl⟩ := h
  have hd := r.den_pos hL.le
  have hMd : M * r.den L = r.m0 := by
    rw [hm, h2, h1]; unfold den; ring
  have hMe : M = r.m0 / r.den L := by rw [eq_div_iff hd.ne']; exact hMd
  refine ⟨?_, hMe⟩
  unfold F g num
  rw [hl, h2, h1]
  rw [← hMd]
  field_simp
  ring

/-- Fra en rot L > 0 av F til en likevekt. -/
theorem eq_of_F_zero {L : ℝ} (hL : 0 < L) (hF : r.F L = 0) :
    r.IsEq (r.m0 / r.den L) L (r.K1 * (r.m0 / r.den L) * L)
      (r.K2 * (r.K1 * (r.m0 / r.den L) * L) * L) := by
  have hd := r.den_pos hL.le
  refine ⟨div_pos r.hm hd, hL, rfl, rfl, ?_, ?_⟩
  · have key : r.m0 / r.den L + r.K1 * (r.m0 / r.den L) * L + r.K2 * (r.K1 * (r.m0 / r.den L) * L) * L
        = r.m0 / r.den L * r.den L := by unfold den; ring
    rw [key, div_mul_cancel₀ _ hd.ne']
  · have : r.l0 = L + r.m0 * r.g L := by unfold F at hF; linarith
    rw [this]
    unfold g num
    ring

/-- Eksistens: F har en positiv rot (mellomverdisetningen). -/
theorem F_root : ∃ L, 0 < L ∧ r.F L = 0 := by
  have hl := r.hl
  have hcont : ContinuousOn r.F (Set.Icc 0 r.l0) := by
    unfold F g num den
    apply ContinuousOn.sub _ continuousOn_const
    apply ContinuousOn.add continuousOn_id
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx
    exact (r.den_pos hx.1).ne'
  have h0 : r.F 0 = -r.l0 := by unfold F g num den; simp
  have hl0 : 0 ≤ r.F r.l0 := by
    unfold F
    have hg := r.g_nonneg hl.le
    nlinarith [mul_nonneg r.hm.le hg]
  obtain ⟨L, ⟨hL0, _⟩, hFL⟩ :=
    intermediate_value_Icc hl.le hcont ⟨by rw [h0]; linarith, hl0⟩
  refine ⟨L, ?_, hFL⟩
  rcases hL0.lt_or_eq with h | h
  · exact h
  · subst h; rw [h0] at hFL; linarith

/-- Hovedteoremet: likevekten finnes og er entydig. -/
theorem eq_exists_unique :
    ∃! x : ℝ × ℝ × ℝ × ℝ, r.IsEq x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  obtain ⟨L, hL, hF⟩ := r.F_root
  refine ⟨(r.m0 / r.den L, L, r.K1 * (r.m0 / r.den L) * L, r.K2 * (r.K1 * (r.m0 / r.den L) * L) * L),
    r.eq_of_F_zero hL hF, ?_⟩
  rintro ⟨M', L', ML', ML2'⟩ h'
  dsimp only at h'
  obtain ⟨hF', hM'⟩ := r.F_zero_of_eq h'
  have hL' : L' = L := by
    rcases lt_trichotomy L' L with hlt | heq | hgt
    · have := r.F_strictMono h'.2.1.le hlt; linarith
    · exact heq
    · have := r.F_strictMono hL.le hgt; linarith
  obtain ⟨_, _, h1, h2, _, _⟩ := h'
  subst hL'
  simp only [Prod.mk.injEq, true_and]
  refine ⟨hM', ?_, ?_⟩
  · rw [h1, hM']
  · rw [h2, h1, hM']

/-! ## 3. Le Chatelier: mer metall gir mindre fri ligand -/

theorem more_metal_less_free_ligand (r r' : Sys) (hl : r'.l0 = r.l0) (h1 : r'.K1 = r.K1)
    (h2 : r'.K2 = r.K2) (hm : r.m0 < r'.m0)
    {M L ML ML2 M' L' ML' ML2' : ℝ} (h : r.IsEq M L ML ML2) (h' : r'.IsEq M' L' ML' ML2') :
    L' < L ∧ ML + 2 * ML2 < ML' + 2 * ML2' := by
  have hF := (r.F_zero_of_eq h).1
  have hF' := (r'.F_zero_of_eq h').1
  have hg : r'.g L' = r.g L' := by unfold g num den; rw [h1, h2]
  have hpos := r.g_pos h'.2.1
  have hlt : r.F L' < r.F L := by
    have : r.F L' = r'.F L' - (r'.m0 - r.m0) * r.g L' := by
      unfold F; rw [hg, hl]; ring
    rw [this, hF', hF]
    nlinarith [mul_pos (sub_pos.2 hm) hpos]
  have hLL : L' < L := by
    by_contra hc
    push Not at hc
    rcases hc.lt_or_eq with hc | hc
    · have := r.F_strictMono h.2.1.le hc; linarith
    · rw [hc] at hlt; exact lt_irrefl _ hlt
  refine ⟨hLL, ?_⟩
  have e1 := h.2.2.2.2.2
  have e2 := h'.2.2.2.2.2
  rw [hl] at e2
  linarith

/-! ## 4. Buffer: [L] holdt fast gir lukket form -/

/-- Med [L] = c fast (buffer) er resten entydig og eksplisitt. -/
theorem buffered_eq (c : ℝ) (hc : 0 < c) (M ML ML2 : ℝ) :
    (0 < M ∧ ML = r.K1 * M * c ∧ ML2 = r.K2 * ML * c ∧ r.m0 = M + ML + ML2) ↔
    (M = r.m0 / r.den c ∧ ML = r.K1 * M * c ∧ ML2 = r.K2 * ML * c) := by
  have hd := r.den_pos hc.le
  constructor
  · rintro ⟨_, h1, h2, hm⟩
    refine ⟨?_, h1, h2⟩
    rw [eq_div_iff hd.ne', hm, h2, h1]
    unfold den; ring
  · rintro ⟨hM, h1, h2⟩
    refine ⟨by rw [hM]; exact div_pos r.hm hd, h1, h2, ?_⟩
    rw [h2, h1, hM]
    have key : r.m0 / r.den c + r.K1 * (r.m0 / r.den c) * c + r.K2 * (r.K1 * (r.m0 / r.den c) * c) * c
        = r.m0 / r.den c * r.den c := by unfold den; ring
    rw [key, div_mul_cancel₀ _ hd.ne']

end Sys
end Complex
end CausalPhys
