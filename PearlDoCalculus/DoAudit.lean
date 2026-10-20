import PearlDoCalculus.Audit
import PearlDoCalculus.DoCalculus

/-!
# Audit av do-kalkulusen: regel 2 krever betingelsen

Skjult konfunder `Z ← U → Y` med `U` uniform og `Z`, `Y` kopier av `U`.
Her er `Y` og `Z` ikke d-separert i `G_{Z̲}`, og konklusjonen i regel 2 feiler:
`P(y=1, z=0) · P_{z=0}(∅) = 0`, men `P_{z=0}(y=1) · P(z=0) ≠ 0`.
Observasjon og intervensjon på `Z` er altså forskjellige, slik de skal være.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Classical

namespace DoAudit

/-- Kjernefaktoren på `univ` er kjernen evaluert i tilordningen. -/
lemma kfac_univ {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}
    (M : G.CausalModel α) (u : Assignment (α := α) (Finset.univ : Finset V)) (v : V) :
    kfac M Finset.univ u v =
      M.kernel v (u.restrict (Finset.subset_univ _)) (u ⟨v, Finset.mem_univ v⟩) := by
  have hc : v ∈ (Finset.univ : Finset V) ∧ G.parents v ⊆ Finset.univ :=
    ⟨Finset.mem_univ v, Finset.subset_univ _⟩
  unfold kfac
  rw [dif_pos hc]

/-- Konfundergrafen: `U = 0`, `Z = 1`, `Y = 2`, med `0 → 1` og `0 → 2`. -/
def confG : DAG (Fin 3) where
  edge u v := u = 0 ∧ (v = 1 ∨ v = 2)
  decEdge := fun u v => inferInstanceAs (Decidable (u = 0 ∧ (v = 1 ∨ v = 2)))
  rank v := v.val
  rank_strict_mono := by
    intro u v h
    rcases h with ⟨rfl, rfl | rfl⟩ <;> decide

lemma zero_mem_parents {v : Fin 3} (hv : v ≠ 0) : (0 : Fin 3) ∈ confG.parents v := by
  fin_cases v <;> simp_all [DAG.parents, confG]

/-- `U` uniform; `Z` og `Y` er kopier av `U`. -/
noncomputable def confModel : confG.CausalModel (fun _ => Fin 2) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if hv : v = 0 then PMF.uniformOfFinset Finset.univ ⟨0, by simp⟩
    else PMF.pure (pa ⟨0, zero_mem_parents hv⟩)

abbrev A2 (S : Finset (Fin 3)) := Assignment (α := fun _ : Fin 3 => Fin 2) S

/-- Intervensjonsverdien `z₀ = 0`. -/
def z₀ : A2 {1} := fun _ => 0

/-- Testtilordningen `y = 1, z = 0` på `Y ∪ Z ∪ W = {2} ∪ {1} ∪ ∅`. -/
def tT : A2 ({2} ∪ {1} ∪ ∅) := fun v => if v.1 = 2 then 1 else 0

/-- Vitne for `P(z=0) > 0`: alt er 0. -/
def uAll0 : A2 Finset.univ := fun _ => 0

/-- Vitne for `P_{z=0}(y=1) > 0`: `U = 1`, `Z = 0` (satt), `Y = 1`. -/
def uW : A2 Finset.univ := fun v => if v.1 = 1 then 0 else 1

/-- **Audit: regel 2 krever d-separasjonsbetingelsen.** I konfundermodellen
feiler produktidentiteten fra `rule2_core`. -/
theorem rule2_fails_with_confounder :
    confModel.marginal ({2} ∪ {1} ∪ ∅) tT *
      (doModel confModel {1} z₀).marginal ∅ (tT.restrict (by
        intro v hv; simp at hv)) ≠
    (doModel confModel {1} z₀).marginal ({2} ∪ ∅) (tT.restrict (by
        intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
      confModel.marginal ({1} ∪ ∅) (tT.restrict (by
        intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := by
  -- Venstresiden: Z og Y er alltid like, så P(y=1, z=0) = 0.
  have hL : confModel.marginal ({2} ∪ {1} ∪ ∅) tT = 0 := by
    refine Audit.marginal_eq_zero_of confModel _ tT (fun u hu => ?_)
    have h1 : u ⟨1, Finset.mem_univ 1⟩ = 0 := by
      have := congrFun hu ⟨1, by simp⟩
      simpa [Assignment.restrict, tT] using this
    have h2 : u ⟨2, Finset.mem_univ 2⟩ = 1 := by
      have := congrFun hu ⟨2, by simp⟩
      simpa [Assignment.restrict, tT] using this
    by_cases h0 : u ⟨0, Finset.mem_univ 0⟩ = 0
    · refine ⟨2, ?_⟩
      rw [kfac_univ]
      simp [confModel, Assignment.restrict, h0, h2, PMF.pure_apply]
    · have h0' : (0 : Fin 2) ≠ u ⟨0, Finset.mem_univ 0⟩ := Ne.symm h0
      refine ⟨1, ?_⟩
      rw [kfac_univ]
      simp [confModel, Assignment.restrict, h1, h0', PMF.pure_apply]
  -- Høyresiden: begge faktorene er positive.
  have hR1 : (doModel confModel {1} z₀).marginal ({2} ∪ ∅) (tT.restrict (by
        intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) ≠ 0 := by
    refine Audit.marginal_ne_zero_of _ _ _ uW ?_ (fun v => ?_)
    · funext ⟨v, hv⟩
      have : v = 2 := by simpa using hv
      subst this
      simp [Assignment.restrict, tT, uW]
    · rw [kfac_doModel]
      fin_cases v <;> simp [z₀, uW, kfac_univ, confModel, Assignment.restrict,
        PMF.pure_apply, PMF.uniformOfFinset_apply]
  have hR2 : confModel.marginal ({1} ∪ ∅) (tT.restrict (by
        intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) ≠ 0 := by
    refine Audit.marginal_ne_zero_of _ _ _ uAll0 ?_ (fun v => ?_)
    · funext ⟨v, hv⟩
      have : v = 1 := by simpa using hv
      subst this
      simp [Assignment.restrict, tT, uAll0]
    · rw [kfac_univ]
      fin_cases v <;> simp [uAll0, confModel, Assignment.restrict,
        PMF.pure_apply, PMF.uniformOfFinset_apply]
  intro heq
  rw [hL, zero_mul] at heq
  exact mul_ne_zero hR1 hR2 heq.symm

/-! ## Regel 2 gjelder, og er ikke-triviell

`Z → Y` på `Fin 2` (`Z = 0`, `Y = 1`) med `Z` uniform og `Y` en kopi av `Z`.
I `G_{Z̲}` er den eneste kanten fjernet, så betingelsen holder. Identiteten fra
`rule2_core` har venstreside `P(y=1, z=1) · P_{z=1}(∅) = ½ ≠ 0`: teoremet er
ikke sant bare fordi begge sider er 0. -/

abbrev B2 (S : Finset (Fin 2)) := Assignment (α := fun _ : Fin 2 => Fin 2) S

/-- `Z` uniform; `Y` er en kopi av `Z`. -/
noncomputable def copyModel : Audit.edgeG.CausalModel (fun _ => Fin 2) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if hv : v = 1 then PMF.pure (pa ⟨0, by subst hv; exact Audit.mem_parents_one⟩)
    else PMF.uniformOfFinset Finset.univ ⟨0, by simp⟩

/-- I `G_{Z̲}` med `Z = {0}` finnes ingen kanter, så ingen vandring mellom
forskjellige noder. -/
lemma no_walk_cutOut : ∀ {a b : Fin 2} (p : Walk (cutOut Audit.edgeG {0}) a b),
    a ≠ b → False := by
  intro a b p hab
  cases p with
  | nil => exact hab rfl
  | fwd e _ => exact e.2 (Finset.mem_singleton.mpr e.1.1)
  | bwd e _ => exact e.2 (Finset.mem_singleton.mpr e.1.1)

def zP : B2 {0} := fun _ => 1
def tP : B2 ({1} ∪ {0} ∪ ∅) := fun _ => 1
def u11 : B2 Finset.univ := fun _ => 1

/-- **Audit: regel 2 gjelder og er ikke-triviell.** Betingelsen holder, og
identiteten fra `rule2_core` har venstreside ≠ 0. -/
theorem rule2_holds_nontrivially :
    copyModel.marginal ({1} ∪ {0} ∪ ∅) tP *
        (doModel copyModel {0} zP).marginal ∅ (tP.restrict (by intro v hv; simp at hv)) ≠ 0 ∧
    copyModel.marginal ({1} ∪ {0} ∪ ∅) tP *
        (doModel copyModel {0} zP).marginal ∅ (tP.restrict (by intro v hv; simp at hv)) =
      (doModel copyModel {0} zP).marginal ({1} ∪ ∅) (tP.restrict (by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
        copyModel.marginal ({0} ∪ ∅) (tP.restrict (by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := by
  have h : SetSound.DSeparatedSet (cutOut Audit.edgeG {0}) ∅ {1} {0} := by
    intro y hy z hz p _
    exfalso
    refine no_walk_cutOut p ?_
    simp only [Finset.mem_singleton] at hy hz
    subst hy
    subst hz
    decide
  refine ⟨mul_ne_zero ?_ ?_, rule2_core copyModel {1} {0} ∅ zP (by simp) (by simp) (by simp)
    h tP (by funext ⟨v, hv⟩; rfl)⟩
  · refine Audit.marginal_ne_zero_of _ _ _ u11 (by funext ⟨v, hv⟩; rfl) (fun v => ?_)
    rw [kfac_univ]
    fin_cases v <;> simp [copyModel, u11, Assignment.restrict, PMF.pure_apply,
      PMF.uniformOfFinset_apply]
  · refine Audit.marginal_ne_zero_of _ _ _ u11 (by funext ⟨v, hv⟩; simp at hv) (fun v => ?_)
    rw [kfac_doModel]
    fin_cases v <;> simp [copyModel, u11, zP, kfac_univ, Assignment.restrict, PMF.pure_apply,
      PMF.uniformOfFinset_apply]

end DoAudit

#print axioms DoAudit.rule2_fails_with_confounder
#print axioms DoAudit.rule2_holds_nontrivially
