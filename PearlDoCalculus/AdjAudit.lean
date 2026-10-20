import PearlDoCalculus.Adjustment
import PearlDoCalculus.DoAudit

/-!
# Audit av justeringsformlene: back-door i en konfundert graf

`Z → X`, `Z → Y`, `X → Y` (`Z = 0`, `X = 1`, `Y = 2`): `Z` er en observert
konfunder. Hypotesene i back-door holder, og identiteten fra `backdoor_stratum`
har venstreside ≠ 0.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Classical

namespace AdjAudit

/-- Konfundergrafen med observert `Z`: `0 → 1`, `0 → 2`, `1 → 2`. -/
def bdG : DAG (Fin 3) where
  edge u v := (u = 0 ∧ (v = 1 ∨ v = 2)) ∨ (u = 1 ∧ v = 2)
  decEdge := fun u v =>
    inferInstanceAs (Decidable ((u = 0 ∧ (v = 1 ∨ v = 2)) ∨ (u = 1 ∧ v = 2)))
  rank v := v.val
  rank_strict_mono := by
    intro u v h
    rcases h with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ <;> decide

lemma par_X : (0 : Fin 3) ∈ bdG.parents 1 := by simp [DAG.parents, bdG]
lemma par_Y : (1 : Fin 3) ∈ bdG.parents 2 := by simp [DAG.parents, bdG]

/-- `Z` uniform, `X` kopi av `Z`, `Y` kopi av `X`. -/
noncomputable def bdModel : bdG.CausalModel (fun _ => Fin 2) where
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  kernel := fun v pa =>
    if h1 : v = 1 then PMF.pure (pa ⟨0, by subst h1; exact par_X⟩)
    else if h2 : v = 2 then PMF.pure (pa ⟨1, by subst h2; exact par_Y⟩)
    else PMF.uniformOfFinset Finset.univ ⟨0, by simp⟩

/-- I `G_{X̲}` er hver vandring fra `Y = 2` til `X = 1` blokkert av `{Z} = {0}`:
første steg må gå bakover til `0`, og der er `0` en gaffel. -/
lemma bd_blocked : ∀ {a b : Fin 3} (p : Walk (cutOut bdG {1}) a b),
    a = 2 → b = 1 → Walk.blockedAux {0} .start p := by
  intro a b p ha hb
  cases p with
  | nil v =>
    subst ha
    exact absurd hb (by decide)
  | fwd e p =>
    subst ha
    exfalso
    simp [cutOut, bdG] at e
  | @bwd _ a1 _ e p =>
    subst ha
    fin_cases a1
    · simp only [Walk.blockedAux]
      cases p with
      | nil v => exact absurd hb (by decide)
      | fwd e' p' =>
        simp only [Walk.blockedAux]
        exact Or.inl (by simp)
      | bwd e' p' =>
        exfalso
        simp [cutOut, bdG] at e'
    · exfalso
      simp [cutOut, bdG] at e
    · exfalso
      simp [cutOut, bdG] at e

abbrev C2 (S : Finset (Fin 3)) := Assignment (α := fun _ : Fin 3 => Fin 2) S

def tB : C2 ({2} ∪ {1} ∪ {0}) := fun _ => 0
def u0 : C2 Finset.univ := fun _ => 0

/-- **Audit: back-door i en konfundert graf.** Hypotesene holder, og identiteten
fra `backdoor_stratum` har venstreside ≠ 0. -/
theorem backdoor_holds_nontrivially :
    bdModel.marginal ({2} ∪ {1} ∪ {0}) tB *
        bdModel.marginal {0} (tB.restrict (by
          intro v hv; simp only [Finset.mem_union]; tauto)) ≠ 0 ∧
    bdModel.marginal ({2} ∪ {1} ∪ {0}) tB *
        bdModel.marginal {0} (tB.restrict (by
          intro v hv; simp only [Finset.mem_union]; tauto)) =
      (doModel bdModel {1} (tB.restrict (by
          intro v hv; simp only [Finset.mem_union]; tauto))).marginal ({2} ∪ {0})
          (tB.restrict (by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
        bdModel.marginal ({1} ∪ {0})
          (tB.restrict (by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := by
  have hdesc : ∀ x ∈ ({1} : Finset (Fin 3)), ∀ z ∈ ({0} : Finset (Fin 3)),
      ¬ bdG.Reaches x z := by
    intro x hx z hz hr
    rw [Finset.mem_singleton] at hx hz
    subst hx
    subst hz
    have := bdG.rank_le_of_reaches hr
    simp [bdG] at this
  have h : SetSound.DSeparatedSet (cutOut bdG {1}) {0} {2} {1} :=
    fun y hy x hx => DAG.dsepPath_of_dsep (fun p =>
      bd_blocked p (Finset.mem_singleton.mp hy) (Finset.mem_singleton.mp hx))
  refine ⟨mul_ne_zero ?_ ?_,
    Adjustment.backdoor_stratum bdModel {1} {2} {0} (by simp) (by simp) (by simp) hdesc h tB⟩
  · refine Audit.marginal_ne_zero_of _ _ _ u0 (by funext v; rfl) (fun v => ?_)
    rw [DoAudit.kfac_univ]
    fin_cases v <;> simp [bdModel, u0, Assignment.restrict, PMF.pure_apply,
      PMF.uniformOfFinset_apply]
  · refine Audit.marginal_ne_zero_of _ _ _ u0 (by funext v; rfl) (fun v => ?_)
    rw [DoAudit.kfac_univ]
    fin_cases v <;> simp [bdModel, u0, Assignment.restrict, PMF.pure_apply,
      PMF.uniformOfFinset_apply]

end AdjAudit

#print axioms AdjAudit.backdoor_holds_nontrivially
