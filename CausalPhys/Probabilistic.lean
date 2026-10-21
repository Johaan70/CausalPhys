/-
  CausalPhys.Probabilistic — fra ligningssystem til betingede uavhengigheter.

  Bro mellom CausalPhys og PearlDoCalculus (v3.0):

    ligninger + labbens valg av eksogene variabler
      → (CausalOrder) beregnet Simon-lesning, bevist rekursiv
      → (her) kausal graf som en `PearlDoCalculus.DAG`
      → (her) en `CausalModel` der de eksogene variablene er uavhengige
         tilfeldige variabler og de endogene er gitt av ligningene
      → (PearlDoCalculus.SetSound) d-separasjon i grafen ⇒ betinget uavhengighet.

  Bevist her:
    • `toDAG`, `toCausalModel`: konstruksjonen.
    • `fullJoint_eq`: fellesfordelingen er produktet av de eksogene fordelingene
      ganger indikatoren for at ligningene holder.
    • `solves_of_fullJoint_ne_zero`: all sannsynlighetsmasse ligger på løsninger
      av ligningssystemet.
    • `condIndep_of_dsep`: d-separasjon i den kausale ordningsgrafen gir
      betinget uavhengighet.
    • `dsep_roots`, `exo_indep`: to disjunkte mengder eksogene variabler er
      uavhengige.
    • Gassloven på log-skala (verdier i Fin 5): oppsett A gir T ⊥ V, oppsett B
      gir T ⊥ p. Labbens valg avgjør hvilke uavhengigheter som holder.

  Verdier må ha endelig type (PearlDoCalculus arbeider med diskrete fordelinger).
-/
import CausalPhys.CausalOrder
import CausalPhys.CausalOrderExamples
import PearlDoCalculus.SetSound

set_option linter.unusedSectionVars false

open PearlDoCalculus PearlDoCalculus.DAG PearlDoCalculus.DAG.CausalModel

namespace CausalPhys
namespace Prob

variable {V : Type} [DecidableEq V] [Fintype V]
variable {β : Type} [Fintype β] [DecidableEq β] [Inhabited β]

/-! ## Konstruksjonen -/

/-- Kant u → v: u er en forelder i mekanismen til v. -/
def edgeOf (M : SCM V β) (u v : V) : Prop := u ∈ (M.mech v).elim [] Mech.parents

instance (M : SCM V β) : DecidableRel (edgeOf M) := fun u v => by
  unfold edgeOf; infer_instance

/-- Den kausale ordningsgrafen til en rekursiv modell. -/
def toDAG (M : SCM V β) (rank : V → ℕ) (hr : M.Recursive rank) : DAG V where
  edge := edgeOf M
  decEdge := inferInstance
  rank := rank
  rank_strict_mono u v h := by
    unfold edgeOf at h
    cases hm : M.mech v with
    | none => rw [hm] at h; simp at h
    | some m => rw [hm] at h; exact hr v m hm u h

theorem edge_iff (M : SCM V β) (rank : V → ℕ) (hr : M.Recursive rank) (u v : V) :
    (toDAG M rank hr).edge u v ↔ ∃ m, M.mech v = some m ∧ u ∈ m.parents := by
  show edgeOf M u v ↔ _
  unfold edgeOf
  cases hm : M.mech v <;> simp

/-- Eksogene variabler er røtter i grafen. -/
theorem no_parents_of_exo (M : SCM V β) (rank : V → ℕ) (hr : M.Recursive rank) {v : V}
    (hv : M.mech v = none) (u : V) : ¬ (toDAG M rank hr).edge u v := by
  rw [edge_iff]
  rintro ⟨m, hm, _⟩
  rw [hv] at hm
  cases hm

/-- Fyll inn foreldreverdier til en hel tilstand (standardverdi ellers). -/
def fill (G : DAG V) (v : V) (pa : ∀ _u : {u // u ∈ G.parents v}, β) : V → β :=
  fun w => if h : w ∈ G.parents v then pa ⟨w, h⟩ else default

/-- Sannsynlighetsmodellen: eksogene variabler trekkes uavhengig fra `P v`,
    endogene bestemmes deterministisk av ligningene. -/
noncomputable def toCausalModel (M : SCM V β) (rank : V → ℕ) (hr : M.Recursive rank)
    (P : V → PMF β) : (toDAG M rank hr).CausalModel (fun _ => β) where
  fin _ := inferInstance
  deq _ := inferInstance
  kernel v pa :=
    match M.mech v with
    | none => P v
    | some m => PMF.pure (m.f (fill (toDAG M rank hr) v pa))

/-! ## Semantikk: fordelingen er «løs ligningene med tilfeldige eksogene verdier» -/

/-- En tilordning på alle noder lest som en tilstand. -/
def stateOf (u : Assignment (α := fun _ : V => β) (Finset.univ : Finset V)) : V → β :=
  fun w => u ⟨w, Finset.mem_univ w⟩

/-- Faktoren til node `v`: eksogen ⇒ P_v(s_v); endogen ⇒ [s_v = f_v(s)]. -/
noncomputable def factor (M : SCM V β) (P : V → PMF β) (s : V → β) (v : V) : ENNReal :=
  match M.mech v with
  | none => P v (s v)
  | some m => if s v = m.f s then 1 else 0

theorem fullJoint_eq (M : SCM V β) (rank : V → ℕ) (hr : M.Recursive rank) (P : V → PMF β)
    (u : Assignment (α := fun _ : V => β) (Finset.univ : Finset V)) :
    (toCausalModel M rank hr P).fullJoint u = ∏ v, factor M P (stateOf u) v := by
  rw [PearlDoCalculus.fullJoint_apply_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  unfold PearlDoCalculus.kfac
  rw [dite_eq_left ⟨Finset.mem_univ v, Finset.subset_univ _⟩]
  unfold factor
  cases hm : M.mech v with
  | none =>
    simp only [toCausalModel, hm]
    rfl
  | some m =>
    simp only [toCausalModel, hm, PMF.pure_apply]
    have hloc : m.f (fill (toDAG M rank hr) v (Assignment.restrict (Finset.subset_univ _) u))
        = m.f (stateOf u) := by
      apply m.local_
      intro p hp
      have hpar : p ∈ (toDAG M rank hr).parents v := by
        simp only [DAG.parents, Finset.mem_filter, Finset.mem_univ, true_and]
        exact (edge_iff M rank hr p v).2 ⟨m, hm, hp⟩
      simp only [fill, dite_eq_left hpar]
      rfl
    rw [hloc]
    congr 1

/-- All sannsynlighetsmasse ligger på tilstander der hver ligning holder. -/
theorem solves_of_fullJoint_ne_zero (M : SCM V β) (rank : V → ℕ) (hr : M.Recursive rank)
    (P : V → PMF β) (u : Assignment (α := fun _ : V => β) (Finset.univ : Finset V))
    (h : (toCausalModel M rank hr P).fullJoint u ≠ 0) :
    ∀ v m, M.mech v = some m → stateOf u v = m.f (stateOf u) := by
  intro v m hm
  rw [fullJoint_eq, Finset.prod_ne_zero_iff] at h
  have hv := h v (Finset.mem_univ v)
  unfold factor at hv
  rw [hm] at hv
  by_contra hne
  simp [hne] at hv

/-! ## Hovedbroen: d-separasjon ⇒ betinget uavhengighet -/

theorem condIndep_of_dsep (M : SCM V β) (rank : V → ℕ) (hr : M.Recursive rank) (P : V → PMF β)
    (X Y Z : Finset V) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (h : SetSound.DSeparatedSet (toDAG M rank hr) Z X Y) :
    (toCausalModel M rank hr P).CondIndep X Y Z :=
  SetSound.dsep_sound_set _ X Y Z hXZ hYZ h

/-! ## Et generelt grafteorem: røtter er d-separert av ∅ -/

theorem blocked_fwd_of_root {G : DAG V} :
    ∀ {a y : V} (p : Walk G a y), (∀ u, ¬ G.edge u y) → (∃ u, G.edge u a) →
      Walk.blockedAux ∅ .fwd p := by
  intro a y p
  induction p with
  | nil a =>
    rintro hy ⟨u, hu⟩
    exact absurd hu (hy u)
  | fwd e rest ih =>
    intro hy _
    simp only [Walk.blockedAux]
    exact Or.inr (ih hy ⟨_, e⟩)
  | bwd e rest ih =>
    intro _ _
    simp only [Walk.blockedAux]
    exact Or.inl (by simp)

/-- To ulike røtter er d-separert av den tomme mengden. -/
theorem dsep_roots {G : DAG V} {x y : V} (hx : ∀ u, ¬ G.edge u x) (hy : ∀ u, ¬ G.edge u y)
    (hxy : x ≠ y) : G.DSeparated ∅ x y := by
  intro p
  cases p with
  | nil => exact absurd rfl hxy
  | fwd e rest =>
    show Walk.blockedAux ∅ .start (Walk.fwd e rest)
    simp only [Walk.blockedAux]
    exact blocked_fwd_of_root rest hy ⟨_, e⟩
  | bwd e rest => exact absurd e (hx _)

/-- To disjunkte mengder eksogene variabler er uavhengige. -/
theorem exo_indep (M : SCM V β) (rank : V → ℕ) (hr : M.Recursive rank) (P : V → PMF β)
    (X Y : Finset V) (hX : ∀ x ∈ X, M.mech x = none) (hY : ∀ y ∈ Y, M.mech y = none)
    (hXY : Disjoint X Y) :
    (toCausalModel M rank hr P).CondIndep X Y ∅ := by
  apply condIndep_of_dsep _ _ _ _ _ _ _ (Finset.disjoint_empty_right _) (Finset.disjoint_empty_right _)
  intro x hx y hy p _
  have hne : x ≠ y := fun h => Finset.disjoint_left.1 hXY hx (h ▸ hy)
  exact dsep_roots (no_parents_of_exo M rank hr (hX x hx)) (no_parents_of_exo M rank hr (hY y hy)) hne p

/-! ## Eksempel: gassloven på log-skala, beregnet orden, utledet uavhengighet -/

instance : Fintype Gas := ⟨{.p, .Vol, .T, .n}, by intro x; cases x <;> simp⟩

/-- log p + log V = log n + log T (R absorbert), med verdier på et endelig gitter. -/
def gasLogEqs : Unit → Equation Gas (Fin 5) := fun _ =>
  ⟨[.p, .Vol, .n, .T], fun s => s .p + s .Vol = s .n + s .T, by
    intro s t h
    rw [h .p (by simp), h .Vol (by simp), h .n (by simp), h .T (by simp)]⟩

def mechLogP : Mech Gas (Fin 5) :=
  ⟨[.n, .T, .Vol], fun s => s .n + s .T - s .Vol, by
    intro s t h; show _ = _; rw [h .n (by simp), h .T (by simp), h .Vol (by simp)]⟩

def mechLogV : Mech Gas (Fin 5) :=
  ⟨[.n, .T, .p], fun s => s .n + s .T - s .p, by
    intro s t h; show _ = _; rw [h .n (by simp), h .T (by simp), h .p (by simp)]⟩

def gasLogSolvers (ex : List Gas) : Order.Solvers (Order.gasS ex) gasLogEqs (fun _ => True) where
  mech := fun _ v => match v with
    | .Vol => mechLogV
    | _ => mechLogP
  parents := by
    intro e v hv
    simp [Order.gasS] at hv
    rcases hv with rfl | rfl <;> rfl
  sound := by
    intro e v hv s _
    simp [Order.gasS] at hv
    rcases hv with rfl | rfl
    · show s .p + s .Vol = s .n + s .T ↔ s .p = s .n + s .T - s .Vol
      rw [eq_sub_iff_add_eq]
    · show s .p + s .Vol = s .n + s .T ↔ s .Vol = s .n + s .T - s .p
      rw [eq_sub_iff_add_eq, add_comm (s .Vol)]

/-- Oppsett A, BEREGNET fra labbens valg, som sannsynlighetsmodell. -/
def readLogA : Reading gasLogEqs (fun _ => True) :=
  Order.toReading Order.gasA _ Order.gasA_valid (gasLogSolvers _)
def readLogB : Reading gasLogEqs (fun _ => True) :=
  Order.toReading Order.gasB _ Order.gasB_valid (gasLogSolvers _)

theorem readLogA_rec : readLogA.toSCM.Recursive (Order.rankV (Order.compute Order.gasA)) :=
  Order.toReading_recursive _ _ _ _ Order.gasA_acyclic
theorem readLogB_rec : readLogB.toSCM.Recursive (Order.rankV (Order.compute Order.gasB)) :=
  Order.toReading_recursive _ _ _ _ Order.gasB_acyclic

theorem exo_mech {R : Reading gasLogEqs (fun _ => True)} {v : Gas} (h : R.read v = none) :
    R.toSCM.mech v = none := by
  simp [Reading.toSCM, h]

/-- Låst stempel: temperatur og volum er uavhengige, uansett fordelinger. -/
theorem setupA_T_indep_V (P : Gas → PMF (Fin 5)) :
    (toCausalModel readLogA.toSCM _ readLogA_rec P).CondIndep {.T} {.Vol} ∅ := by
  apply exo_indep
  · intro x hx; simp at hx; subst hx
    exact exo_mech ((Order.toReading_exo_iff _ _ _ _ _).2 (by decide))
  · intro y hy; simp at hy; subst hy
    exact exo_mech ((Order.toReading_exo_iff _ _ _ _ _).2 (by decide))
  · decide

/-- Lodd på stempelet: temperatur og trykk er uavhengige. -/
theorem setupB_T_indep_p (P : Gas → PMF (Fin 5)) :
    (toCausalModel readLogB.toSCM _ readLogB_rec P).CondIndep {.T} {.p} ∅ := by
  apply exo_indep
  · intro x hx; simp at hx; subst hx
    exact exo_mech ((Order.toReading_exo_iff _ _ _ _ _).2 (by decide))
  · intro y hy; simp at hy; subst hy
    exact exo_mech ((Order.toReading_exo_iff _ _ _ _ _).2 (by decide))
  · decide

end Prob
end CausalPhys
