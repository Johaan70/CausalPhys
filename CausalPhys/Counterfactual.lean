import CausalPhys.Core

set_option linter.unusedSectionVars false

namespace CausalPhys
open SCM

variable {V : Type} {α : Type u} [DecidableEq V]

structure TwinSCM (M : SCM V α) (x : V) (c : α) where
  u           : V → α
  s_act       : V → α
  s_cf        : V → α
  h_actual    : M.Solves u s_act
  h_counter   : (M.doI x c).Solves u s_cf

namespace TwinSCM

variable {M : SCM V α} {x : V} {c : α}

theorem abduce_exogenous (twin : TwinSCM M x c) (v : V) :
    match M.mech v with
    | none   => twin.s_act v = twin.u v
    | some m => twin.s_act v = m.f twin.s_act := twin.h_actual v

theorem counterfactual_unaffected (twin : TwinSCM M x c) {v : V} (hv : v ≠ x) (hm : M.mech v = none) :
    twin.s_cf v = twin.s_act v := by
  have h_cf := doI_exo M c twin.u twin.s_cf hv hm twin.h_counter
  have h_act := twin.h_actual v
  rw [hm] at h_act
  rw [h_cf, h_act]

theorem counterfactual_unique {rank : V → Nat} (hr : M.Recursive rank)
    (twin₁ twin₂ : TwinSCM M x c) (hu : twin₁.u = twin₂.u) :
    twin₁.s_cf = twin₂.s_cf := by
  have h_eq : (M.doI x c).Solves twin₂.u twin₁.s_cf := by
    rw [← hu]
    exact twin₁.h_counter
  exact (hr.doI x c).unique h_eq twin₂.h_counter

/-- det som faktisk er observert (s_act) bestemmer kontrafaktumet. -/
theorem cf_determined_by_actual {rank : V → Nat} (hr : M.Recursive rank)
    (t₁ t₂ : TwinSCM M x c) (h : t₁.s_act = t₂.s_act) : t₁.s_cf = t₂.s_cf := by
  have hsol : (M.doI x c).Solves t₂.u t₁.s_cf := by
    intro v
    have h1 := t₁.h_counter v
    by_cases hv : v = x
    · subst hv
      simpa [SCM.doI] using h1
    · rw [doI_mech_ne M c hv] at h1 ⊢
      cases hm : M.mech v with
      | none =>
        rw [hm] at h1
        have h1' : t₁.s_cf v = t₁.u v := h1
        show t₁.s_cf v = t₂.u v
        have a1 := t₁.h_actual v
        have a2 := t₂.h_actual v
        rw [hm] at a1 a2
        rw [h1', ← a1, h, a2]
      | some m =>
        rw [hm] at h1
        exact h1
  exact (hr.doI x c).unique hsol t₂.h_counter

end TwinSCM

/-! Additiv støy: nivå 3 gir et annet svar enn nivå 2. -/
inductive AN | X | UY | Y
deriving DecidableEq

/-- Y := 2·X + U_Y, der U_Y er uobservert støy. -/
def anModel : SCM AN Int :=
  ⟨fun
    | .Y => some ⟨[.X, .UY], fun s => 2 * s .X + s .UY, by
        intro s t h
        show _ = _
        rw [h .X (by simp), h .UY (by simp)]⟩
    | _ => none⟩

/-- Vi så X = 1 og Y = 5. Hadde X vært 4, ville Y vært 11 — uansett hva u er. -/
theorem an_counterfactual (t : TwinSCM anModel .X 4)
    (hx : t.s_act .X = 1) (hy : t.s_act .Y = 5) : t.s_cf .Y = 11 := by
  have ay : t.s_act .Y = 2 * t.s_act .X + t.s_act .UY := t.h_actual .Y
  have cy : t.s_cf .Y = 2 * t.s_cf .X + t.s_cf .UY :=
    doI_other anModel (v := .Y) 4 t.u t.s_cf _ (by decide) rfl t.h_counter
  have cx : t.s_cf .X = 4 := doI_self anModel .X 4 t.u t.s_cf t.h_counter
  have cu : t.s_cf .UY = t.s_act .UY :=
    TwinSCM.counterfactual_unaffected t (by decide) rfl
  omega

end CausalPhys
