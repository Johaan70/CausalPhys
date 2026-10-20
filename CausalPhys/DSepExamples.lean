/-
  CausalPhys.DSepExamples — betingede uavhengigheter avgjort av `decide`.

  Hele kjeden er automatisk: labbens valg → beregnet kausal orden (CausalOrder)
  → graf → d-separasjon avgjort av Bayes-ball (DSepDecide) → betinget
  uavhengighet i fordelingen ligningene genererer (PearlDoCalculus).

  Verdier ligger på et endelig gitter (Fin 5) og lovene er skrevet additivt,
  som på log-skala. Uavhengighetene avhenger bare av grafen, ikke av tallene.
-/
import CausalPhys.DSepDecide

set_option linter.unusedSectionVars false
set_option linter.ambiguousOpen false
set_option maxRecDepth 200000

open PearlDoCalculus PearlDoCalculus.DAG

namespace CausalPhys
namespace DSep

/-! ## Gass -/

abbrev gasA_G := Prob.toDAG Prob.readLogA.toSCM _ Prob.readLogA_rec
def gasVs : List Gas := [.p, .Vol, .T, .n]

/-- Låst stempel: T og V er d-separert … -/
theorem gasA_T_V : Check gasA_G gasVs ∅ {.T} {.Vol} := by decide
/-- … men ikke gitt trykket: p er en kollider, og å betinge på den åpner stien. -/
theorem gasA_T_V_given_p_fails : ¬ Check gasA_G gasVs {.p} {.T} {.Vol} := by decide

theorem gasA_T_indep_V (P : Gas → PMF (Fin 5)) :
    (Prob.toCausalModel Prob.readLogA.toSCM _ Prob.readLogA_rec P).CondIndep {.T} {.Vol} ∅ :=
  condIndep_of_check _ _ _ P gasVs _ _ _ (by decide) (by decide) gasA_T_V

/-! ## Elektrisk krets: spenningskilde og strømkilde -/

instance : Fintype Order.Circ :=
  ⟨{.U, .Rr, .I, .P, .T, .Ta, .k}, by intro x; cases x <;> simp⟩

open Order in
/-- Joule P = U + I, Ohm U = R + I, avkjøling T = Tₐ + k + P (additiv form). -/
def circLogEqs : CEq → Equation Circ (Fin 5)
  | .joule => ⟨[.P, .U, .I], fun s => s .P = s .U + s .I, by
      intro s t h; rw [h .P (by simp), h .U (by simp), h .I (by simp)]⟩
  | .ohm => ⟨[.U, .Rr, .I], fun s => s .U = s .Rr + s .I, by
      intro s t h; rw [h .U (by simp), h .Rr (by simp), h .I (by simp)]⟩
  | .newton => ⟨[.T, .Ta, .k, .P], fun s => s .T = s .Ta + s .k + s .P, by
      intro s t h; rw [h .T (by simp), h .Ta (by simp), h .k (by simp), h .P (by simp)]⟩

open Order in
def circLogMech : CEq → Circ → Mech Circ (Fin 5)
  | .joule, .I => ⟨[.P, .U], fun s => s .P - s .U, by
      intro s t h; show _ = _; rw [h .P (by simp), h .U (by simp)]⟩
  | .joule, .P => ⟨[.U, .I], fun s => s .U + s .I, by
      intro s t h; show _ = _; rw [h .U (by simp), h .I (by simp)]⟩
  | .ohm, .I => ⟨[.U, .Rr], fun s => s .U - s .Rr, by
      intro s t h; show _ = _; rw [h .U (by simp), h .Rr (by simp)]⟩
  | .ohm, .U => ⟨[.Rr, .I], fun s => s .Rr + s .I, by
      intro s t h; show _ = _; rw [h .Rr (by simp), h .I (by simp)]⟩
  | .newton, .T => ⟨[.Ta, .k, .P], fun s => s .Ta + s .k + s .P, by
      intro s t h; show _ = _; rw [h .Ta (by simp), h .k (by simp), h .P (by simp)]⟩
  | _, _ => SCM.Mech.const 0

open Order in
def circLogSolvers (ex : List Circ) : Solvers (circS ex) circLogEqs (fun _ => True) where
  mech := circLogMech
  parents := by
    intro e v hv
    cases e <;> simp [circS] at hv <;> rcases hv with rfl | rfl <;> rfl
  sound := by
    intro e v hv s _
    cases e <;> simp [circS] at hv
    · rcases hv with rfl | rfl
      · show s .P = s .U + s .I ↔ s .I = s .P - s .U
        rw [eq_sub_iff_add_eq, add_comm (s .I), eq_comm]
      · exact Iff.rfl
    · rcases hv with rfl | rfl
      · show s .U = s .Rr + s .I ↔ s .I = s .U - s .Rr
        rw [eq_sub_iff_add_eq, add_comm (s .I), eq_comm]
      · exact Iff.rfl
    · subst hv
      exact Iff.rfl

def readV : Reading circLogEqs (fun _ => True) :=
  Order.toReading Order.voltageSource _ Order.voltage_valid (circLogSolvers _)
def readI : Reading circLogEqs (fun _ => True) :=
  Order.toReading Order.currentSource _ Order.current_valid (circLogSolvers _)
theorem readV_rec : readV.toSCM.Recursive (Order.rankV (Order.compute Order.voltageSource)) :=
  Order.toReading_recursive _ _ _ _ Order.voltage_acyclic
theorem readI_rec : readI.toSCM.Recursive (Order.rankV (Order.compute Order.currentSource)) :=
  Order.toReading_recursive _ _ _ _ Order.current_acyclic

abbrev GV := Prob.toDAG readV.toSCM _ readV_rec
abbrev GI := Prob.toDAG readI.toSCM _ readI_rec
def circVs : List Order.Circ := [.U, .Rr, .I, .P, .T, .Ta, .k]

/-- Spenningskilde: gitt effekten P sier spenningen ingenting mer om temperaturen. -/
theorem V_U_T_given_P : Check GV circVs {.P} {.U} {.T} := by decide
/-- … heller ikke motstanden. -/
theorem V_R_T_given_P : Check GV circVs {.P} {.Rr} {.T} := by decide
/-- Motstand og spenning er uavhengige … -/
theorem V_R_U : Check GV circVs ∅ {.Rr} {.U} := by decide
/-- … men ikke gitt strømmen (I er en kollider: «bortforklaring»). -/
theorem V_R_U_given_I_fails : ¬ Check GV circVs {.I} {.Rr} {.U} := by decide

/-- Strømkilde: gitt P er motstanden uten betydning for temperaturen. -/
theorem I_R_T_given_P : Check GI circVs {.P} {.Rr} {.T} := by decide
/-- Motstand og strøm er uavhengige, men ikke gitt spenningen. -/
theorem I_R_I : Check GI circVs ∅ {.Rr} {.I} := by decide
theorem I_R_I_given_U_fails : ¬ Check GI circVs {.U} {.Rr} {.I} := by decide

/-- Som sannsynlighetsutsagn: med spenningskilde er U ⊥ T | P for ALLE
    fordelinger av de eksogene størrelsene. -/
theorem V_U_indep_T_given_P (Pr : Order.Circ → PMF (Fin 5)) :
    (Prob.toCausalModel readV.toSCM _ readV_rec Pr).CondIndep {.U} {.T} {.P} :=
  condIndep_of_check _ _ _ Pr circVs _ _ _ (by decide) (by decide) V_U_T_given_P

theorem I_R_indep_T_given_P (Pr : Order.Circ → PMF (Fin 5)) :
    (Prob.toCausalModel readI.toSCM _ readI_rec Pr).CondIndep {.Rr} {.T} {.P} :=
  condIndep_of_check _ _ _ Pr circVs _ _ _ (by decide) (by decide) I_R_T_given_P

end DSep
end CausalPhys
