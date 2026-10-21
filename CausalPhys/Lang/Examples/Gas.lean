/-
  Physics: the ideal gas law pV = nRT, written once.

  Two lab setups:
    * locked piston (V, n, T held fixed)  → Lean computes: the law determines p;
    * weighted piston (p, n, T held fixed) → Lean computes: the law determines V.

  The general theorems of the core then give, with no extra work:
    * both setups allow exactly the same states (`same_data`),
    * every intervention has exactly one outcome,
  and a short calculation gives the physics:
    * heating with a locked piston raises the pressure, the volume stays;
    * heating with a weighted piston raises the volume, the pressure stays;
    * so the same do(T := 2) from the same starting point gives different volumes.
-/
import CausalPhys.Lang.Core
import CausalPhys.Physics

namespace CausalPhys.Lang.Gas

inductive V | p | vol | n | T
deriving DecidableEq, Repr

instance : Inhabited V := ⟨.p⟩

noncomputable section

/-- The model: one law, solvable for p or for V. -/
def model : Model Unit V ℝ where
  eqList := [()]
  varList := [.p, .vol, .n, .T]
  law _ s := s .p * s .vol = s .n * R * s .T
  dom s := 0 < s .p ∧ 0 < s .vol
  solvers _ :=
    [(.p, mech [.n, .T, .vol] fun s => s .n * R * s .T / s .vol),
     (.vol, mech [.n, .T, .p] fun s => s .n * R * s .T / s .p)]
  sound := by
    intro _ v m h s hD
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · show _ ↔ s .p = s .n * R * s .T / s .vol
      rw [eq_div_iff hD.2.ne']
    · show _ ↔ s .vol = s .n * R * s .T / s .p
      rw [eq_div_iff hD.1.ne', mul_comm (s .vol)]

/-- Locked piston in a heat bath, closed vessel. -/
def locked : Setup model := { exo := [.vol, .n, .T] }

/-- Weighted piston in a heat bath, closed vessel. -/
def weighted : Setup model := { exo := [.p, .n, .T] }

end

/-! ## Computed by Lean -/

theorem locked_determines : locked.determines () = .p := by decide
theorem weighted_determines : weighted.determines () = .vol := by decide
theorem locked_acyclic : locked.Acyclic := by decide
theorem weighted_acyclic : weighted.Acyclic := by decide

/-! ## From the general theorems -/

/-- Data cannot distinguish the setups. -/
theorem same_data (s : V → ℝ) (hD : model.dom s) :
    (∃ u, locked.scm.Solves u s) ↔ (∃ u, weighted.scm.Solves u s) :=
  Setup.obs_equiv locked weighted s hD

/-- Every intervention has exactly one outcome, in both setups. -/
theorem locked_do (x : V) (c : ℝ) (u : V → ℝ) : ∃! s, (locked.scm.doI x c).Solves u s :=
  locked.do_existsUnique locked_acyclic x c u

theorem weighted_do (x : V) (c : ℝ) (u : V → ℝ) : ∃! s, (weighted.scm.doI x c).Solves u s :=
  weighted.do_existsUnique weighted_acyclic x c u

/-! ## The physics -/

/-- Heating with a locked piston: the volume stays, the pressure follows. -/
theorem locked_heat (c : ℝ) (u s : V → ℝ) (h : (locked.scm.doI .T c).Solves u s) :
    s .vol = u .vol ∧ s .p = u .n * R * c / u .vol := by
  rw [locked.do_exo_iff (by decide)] at h
  have hv := locked.exo_eq h (v := .vol) (by decide)
  have hn := locked.exo_eq h (v := .n) (by decide)
  have hT := locked.exo_eq h (v := .T) (by decide)
  have hp := locked.mech_eq h ()
  rw [locked_determines] at hp
  simp only [Function.update_apply, reduceCtorEq, ↓reduceIte] at hv hn hT
  simp [Model.mechOf, Model.find, model, mech] at hp
  rw [hp, hv, hn, hT]
  exact ⟨rfl, rfl⟩

/-- Heating with a weighted piston: the pressure stays, the volume follows. -/
theorem weighted_heat (c : ℝ) (u s : V → ℝ) (h : (weighted.scm.doI .T c).Solves u s) :
    s .p = u .p ∧ s .vol = u .n * R * c / u .p := by
  rw [weighted.do_exo_iff (by decide)] at h
  have hp := weighted.exo_eq h (v := .p) (by decide)
  have hn := weighted.exo_eq h (v := .n) (by decide)
  have hT := weighted.exo_eq h (v := .T) (by decide)
  have hv := weighted.mech_eq h ()
  rw [weighted_determines] at hv
  simp only [Function.update_apply, reduceCtorEq, ↓reduceIte] at hp hn hT
  simp [Model.mechOf, Model.find, model, mech] at hv
  rw [hv, hp, hn, hT]
  exact ⟨rfl, rfl⟩

/-- Same starting point, same intervention do(T := 2), different answers:
    the volume stays 1 with a locked piston and becomes 2 with a weighted one. -/
theorem different_answers (s s' : V → ℝ)
    (hs : (locked.scm.doI .T 2).Solves (fun | .p => R | _ => 1) s)
    (hs' : (weighted.scm.doI .T 2).Solves (fun | .p => R | _ => 1) s') :
    s .vol = 1 ∧ s' .vol = 2 := by
  have hR := R_pos.ne'
  refine ⟨(locked_heat 2 _ s hs).1, ?_⟩
  rw [(weighted_heat 2 _ s' hs').2]
  field_simp

end CausalPhys.Lang.Gas
