/-
  CausalPhys.PoincareMiranda — the Poincaré–Miranda theorem, from Brouwer.

  If F : [a, b] → ℝⁿ is continuous on the box, F i ≤ 0 on the face x i = a i
  and F i ≥ 0 on the face x i = b i, then F has a zero in the box.

  Proof: G x = clamp (x − F x) maps the box to itself and is continuous, so it
  has a fixed point (`Brouwer.brouwer_box`). At a fixed point, F i > 0 would
  push coordinate i down to the face a i, where F i ≤ 0; F i < 0 would push it
  up to b i, where F i ≥ 0. So F = 0 there.

  It is the existence half of the criterion for nonlinear cyclic blocks
  (`block_exists` in `CausalPhys.Lang.Tactic`).
-/
import CausalPhys.Brouwer

namespace CausalPhys

/-- Clamp `t` to the interval `[a, b]`. -/
noncomputable def clamp (a b t : ℝ) : ℝ := max a (min b t)

theorem clamp_mem {a b : ℝ} (hab : a ≤ b) (t : ℝ) : clamp a b t ∈ Set.Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

theorem clamp_of_mem {a b t : ℝ} (h : t ∈ Set.Icc a b) : clamp a b t = t := by
  unfold clamp; rw [min_eq_right h.2, max_eq_right h.1]

theorem clamp_lt {a b t : ℝ} (h : t < a) : clamp a b t = a := by
  unfold clamp; rw [max_eq_left (le_trans (min_le_right _ _) h.le)]

theorem clamp_gt {a b t : ℝ} (hab : a ≤ b) (h : b < t) : clamp a b t = b := by
  unfold clamp; rw [min_eq_left h.le, max_eq_right hab]

/-- **Poincaré–Miranda.** -/
theorem poincare_miranda {m : ℕ} {a b : Fin m → ℝ} (hab : a ≤ b)
    (F : (Fin m → ℝ) → (Fin m → ℝ)) (hF : ContinuousOn F (Set.Icc a b))
    (hlo : ∀ x ∈ Set.Icc a b, ∀ i, x i = a i → F x i ≤ 0)
    (hhi : ∀ x ∈ Set.Icc a b, ∀ i, x i = b i → 0 ≤ F x i) :
    ∃ x ∈ Set.Icc a b, F x = 0 := by
  let G : (Fin m → ℝ) → (Fin m → ℝ) := fun x i => clamp (a i) (b i) (x i - F x i)
  have hG : ContinuousOn G (Set.Icc a b) := by
    refine continuousOn_pi.2 fun i => ?_
    have hFi : ContinuousOn (fun x => F x i) (Set.Icc a b) :=
      (continuous_apply i).comp_continuousOn hF
    have hxi : ContinuousOn (fun x : Fin m → ℝ => x i) (Set.Icc a b) :=
      (continuous_apply i).continuousOn
    have hc : Continuous (clamp (a i) (b i)) :=
      Continuous.max continuous_const (Continuous.min continuous_const continuous_id)
    exact hc.comp_continuousOn (hxi.sub hFi)
  have hmap : Set.MapsTo G (Set.Icc a b) (Set.Icc a b) := by
    intro x _
    exact ⟨fun i => (clamp_mem (hab i) _).1, fun i => (clamp_mem (hab i) _).2⟩
  obtain ⟨x, hx, hfix⟩ := Brouwer.brouwer_box hab G hG hmap
  refine ⟨x, hx, funext fun i => ?_⟩
  have hxi : clamp (a i) (b i) (x i - F x i) = x i := congrFun hfix i
  have hai := hx.1 i
  have hbi := hx.2 i
  rcases lt_trichotomy (F x i) 0 with hneg | hzero | hpos
  · -- x i − F x i > x i: either it stays inside (then F x i = 0) or x i = b i
    by_cases hin : x i - F x i ≤ b i
    · rw [clamp_of_mem ⟨by linarith, hin⟩] at hxi; linarith
    · rw [clamp_gt (hab i) (not_le.1 hin)] at hxi
      have := hhi x hx i hxi.symm
      linarith
  · exact hzero
  · by_cases hin : a i ≤ x i - F x i
    · rw [clamp_of_mem ⟨hin, by linarith⟩] at hxi; linarith
    · rw [clamp_lt (not_le.1 hin)] at hxi
      have := hlo x hx i hxi.symm
      linarith

/-- The version used for causal models: if the lower faces are strict
    (F i < 0 where x i = a i), the zero lies strictly above every lower face. -/
theorem poincare_miranda_strict {m : ℕ} {a b : Fin m → ℝ} (hab : a ≤ b)
    (F : (Fin m → ℝ) → (Fin m → ℝ)) (hF : ContinuousOn F (Set.Icc a b))
    (hlo : ∀ x ∈ Set.Icc a b, ∀ i, x i = a i → F x i < 0)
    (hhi : ∀ x ∈ Set.Icc a b, ∀ i, x i = b i → 0 ≤ F x i) :
    ∃ x ∈ Set.Icc a b, (∀ i, a i < x i) ∧ F x = 0 := by
  obtain ⟨x, hx, h0⟩ := poincare_miranda hab F hF (fun x hx i hi => (hlo x hx i hi).le) hhi
  refine ⟨x, hx, fun i => ?_, h0⟩
  rcases (hx.1 i).lt_or_eq with h | h
  · exact h
  · have := hlo x hx i h.symm
    rw [h0] at this
    exact absurd this (lt_irrefl 0)

end CausalPhys
