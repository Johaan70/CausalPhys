/-
  Physics: the ideal gas law pV = nRT, written once, with two lab setups.

  Lean computes that the law determines p with a locked piston and V with a
  weighted piston. The general theorems give that data cannot tell the setups
  apart and that every intervention has exactly one outcome; reading off the
  solution gives the physics: heating raises p in one setup and V in the other.
-/
import CausalPhys.Lang.Syntax
import CausalPhys.Physics

open CausalPhys CausalPhys.Lang

namespace CausalPhys.Examples

causal_model Gas where
  variables p vol n T
  units p : Pa, vol : m^3, n : mol, T : K, R : J/(mol*K)
  domain 0 < p ∧ 0 < vol ∧ 0 < n ∧ 0 < T
  facts R_pos
  law gas : p * vol = n * R * T
  witness p := 1, vol := 1, n := 1, T := 1 / R
  setup locked fixes vol n T      -- locked piston, heat bath, closed vessel
  setup weighted fixes p n T      -- weighted piston, heat bath, closed vessel

/-- info: gas can be solved for [p, vol, n, T] -/
#guard_msgs in
#causal_solvable Gas.model

/--
info: gas determines p, reading [n, T, vol]
acyclic: every intervention has exactly one outcome of the causal model
-/
#guard_msgs in
#causal_order Gas.locked
/--
info: gas determines vol, reading [n, T, p]
acyclic: every intervention has exactly one outcome of the causal model
-/
#guard_msgs in
#causal_order Gas.weighted

namespace Gas

/-! ## Computed by Lean -/

theorem locked_determines : locked.determines .gas = .p := by struct_decide
theorem weighted_determines : weighted.determines .gas = .vol := by struct_decide
theorem locked_acyclic : locked.Acyclic := by struct_decide
theorem weighted_acyclic : weighted.Acyclic := by struct_decide

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

/-- For the gas law itself: with positive amount, temperature and volume, the
    law has exactly one solution in the domain (the pressure nRT/V). -/
theorem locked_laws (u : V → ℝ) (hn : 0 < u .n) (hT : 0 < u .T) (hv : 0 < u .vol) :
    ∃! s, model.dom s ∧ model.Sat s ∧ ∀ v, v ∈ locked.exo → s v = u v := by
  have := R_pos
  laws_unique

/-! ## The physics -/

/-- Heating with a locked piston: the volume stays, the pressure follows. -/
theorem locked_heat (c : ℝ) (u s : V → ℝ) (h : (locked.scm.doI .T c).Solves u s) :
    s .vol = u .vol ∧ s .p = u .n * R * c / u .vol := by
  read_solution h
  rw [h_p, h_vol, h_n, h_T]
  exact ⟨rfl, rfl⟩

/-- Heating with a weighted piston: the pressure stays, the volume follows. -/
theorem weighted_heat (c : ℝ) (u s : V → ℝ) (h : (weighted.scm.doI .T c).Solves u s) :
    s .p = u .p ∧ s .vol = u .n * R * c / u .p := by
  read_solution h
  rw [h_vol, h_p, h_n, h_T]
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

end Gas

end CausalPhys.Examples
