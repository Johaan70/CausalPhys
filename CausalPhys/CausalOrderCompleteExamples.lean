/-
  CausalPhys.CausalOrderCompleteExamples — den komplette algoritmen på eksemplene.
-/
import CausalPhys.CausalOrderComplete
import CausalPhys.CausalOrderExamples

set_option maxRecDepth 100000

set_option linter.unusedSectionVars false

namespace CausalPhys
namespace Order

theorem gasA_complete : Valid gasA (computeC gasA) ∧ OrderedLT gasA (computeC gasA) := by decide
theorem gasB_complete : Valid gasB (computeC gasB) ∧ OrderedLT gasB (computeC gasB) := by decide
theorem voltage_complete :
    Valid voltageSource (computeC voltageSource) ∧ OrderedLT voltageSource (computeC voltageSource) := by
  decide
theorem current_complete :
    Valid currentSource (computeC currentSource) ∧ OrderedLT currentSource (computeC currentSource) := by
  decide
theorem market_complete : Valid marketS (computeC marketS) := by decide
theorem cyc_complete : Valid cycS (computeC cycS) := by decide

/-- Lengste-vei-rangen alene gir streng orden i kretsen. -/
theorem voltage_lp_ordered :
    OrderedLT voltageSource ⟨(computeC voltageSource).σ, (computeC voltageSource).inv,
      lpRank voltageSource (computeC voltageSource)⟩ := by decide

/-- Den uttømmende reserven alene finner en gyldig matching i kretsen. -/
theorem voltage_brute_ok :
    (brute voltageSource).map (fun c => decide (Valid voltageSource c)) = some true := by decide

end Order
end CausalPhys
