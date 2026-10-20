/-
  CausalPhys.CausalOrderExamples — Lean beregner kausal retning fra labbens valg.

  1. Gass: labben velger hva som holdes fast; Lean beregner at p (A) eller V (B)
     er effekten, og den beregnede modellen ER oppsettet fra Physics.lean.
  2. Elektrisk krets (Ohm, Joule, Newtons avkjølingslov): samme tre lover,
     men spenningskilde og strømkilde gir ulik kausal orden. Her må algoritmen
     bruke en utvidende sti. Begge modellene er bevist rekursive.
  3. Marked: Lean finner likevektsblokken {P, Q}, og den beregnede modellen er
     markedet fra Blocks.lean, som allerede er bevist entydig løsbart.
  4. Syklus: Lean finner at x, y og z danner én blokk.
-/
import CausalPhys.CausalOrder
import CausalPhys.Blocks

set_option linter.unusedSectionVars false

namespace CausalPhys
namespace Order

/-! ## 1. Gass -/

instance : Inhabited Gas := ⟨.p⟩

/-- Gassloven: kan løses for p eller V. Labben velger hva som er eksogent. -/
def gasS (ex : List Gas) : Struct Unit Gas where
  eqList := [()]
  varList := [.p, .Vol, .T, .n]
  eq_complete := by intro e; simp
  var_complete := by intro v; cases v <;> simp
  canSolve := fun _ => [.p, .Vol]
  deps := fun _ v => match v with
    | .p => [.n, .T, .Vol]
    | .Vol => [.n, .T, .p]
    | _ => []
  exo := ex

/-- Oppsett A: varmebad, låst stempel, lukket beholder. -/
def gasA : Struct Unit Gas := gasS [.Vol, .T, .n]
/-- Oppsett B: varmebad, lodd på stempelet, lukket beholder. -/
def gasB : Struct Unit Gas := gasS [.p, .T, .n]

theorem gasA_valid : Valid gasA (compute gasA) := by decide
theorem gasB_valid : Valid gasB (compute gasB) := by decide
theorem gasA_acyclic : OrderedLT gasA (compute gasA) := by decide
theorem gasB_acyclic : OrderedLT gasB (compute gasB) := by decide

/-- Lean beregner: i oppsett A er trykket effekten … -/
theorem gasA_effect : (compute gasA).σ () = .p := by decide
/-- … og i oppsett B volumet. -/
theorem gasB_effect : (compute gasB).σ () = .Vol := by decide

noncomputable def gasSolvers (ex : List Gas) : Solvers (gasS ex) gasEqs gasDom where
  mech := fun _ v => match v with
    | .Vol => mechV
    | _ => mechP
  parents := by
    intro e v hv
    simp [gasS] at hv
    rcases hv with rfl | rfl <;> rfl
  sound := by
    intro e v hv s hD
    simp [gasS] at hv
    rcases hv with rfl | rfl
    · show s .p * s .Vol = s .n * R * s .T ↔ s .p = s .n * R * s .T / s .Vol
      rw [eq_div_iff hD.1]
    · show s .p * s .Vol = s .n * R * s .T ↔ s .Vol = s .n * R * s .T / s .p
      rw [eq_div_iff hD.2, mul_comm (s .Vol)]

/-- Den BEREGNEDE modellen for oppsett A er nøyaktig `setupA`. -/
theorem gasA_computed_eq :
    (toReading gasA (compute gasA) gasA_valid (gasSolvers _)).toSCM = setupA := by
  have h1 : (compute gasA).inv .p = some () := by decide
  have h2 : (compute gasA).inv .Vol = none := by decide
  have h3 : (compute gasA).inv .T = none := by decide
  have h4 : (compute gasA).inv .n = none := by decide
  simp only [Reading.toSCM, toReading, setupA, SCM.mk.injEq]
  funext v
  cases v <;> simp [h1, h2, h3, h4, gasSolvers]

theorem gasB_computed_eq :
    (toReading gasB (compute gasB) gasB_valid (gasSolvers _)).toSCM = setupB := by
  have h1 : (compute gasB).inv .p = none := by decide
  have h2 : (compute gasB).inv .Vol = some () := by decide
  have h3 : (compute gasB).inv .T = none := by decide
  have h4 : (compute gasB).inv .n = none := by decide
  simp only [Reading.toSCM, toReading, setupB, SCM.mk.injEq]
  funext v
  cases v <;> simp [h1, h2, h3, h4, gasSolvers]

/-! ## 2. Elektrisk krets: spenningskilde mot strømkilde -/

/-- Spenning, resistans, strøm, effekt, temperatur, omgivelsestemperatur, varmeoverføringskoeffisient. -/
inductive Circ | U | Rr | I | P | T | Ta | k
deriving DecidableEq, Repr

instance : Inhabited Circ := ⟨.U⟩

/-- Joules lov (P = U·I), Ohms lov (U = R·I), Newtons avkjølingslov (T = Tₐ + k·P). -/
inductive CEq | joule | ohm | newton
deriving DecidableEq, Repr

def circS (ex : List Circ) : Struct CEq Circ where
  eqList := [.joule, .ohm, .newton]   -- Joule først, så algoritmen må bruke en utvidende sti
  varList := [.U, .Rr, .I, .P, .T, .Ta, .k]
  eq_complete := by intro e; cases e <;> simp
  var_complete := by intro v; cases v <;> simp
  canSolve
    | .joule => [.I, .P]
    | .ohm => [.I, .U]
    | .newton => [.T]
  deps
    | .joule, .I => [.P, .U]
    | .joule, .P => [.U, .I]
    | .ohm, .I => [.U, .Rr]
    | .ohm, .U => [.Rr, .I]
    | .newton, .T => [.Ta, .k, .P]
    | _, _ => []
  exo := ex

/-- Spenningskilde: U, R, Tₐ og k holdes fast. -/
def voltageSource : Struct CEq Circ := circS [.U, .Rr, .Ta, .k]
/-- Strømkilde: I, R, Tₐ og k holdes fast. -/
def currentSource : Struct CEq Circ := circS [.I, .Rr, .Ta, .k]

theorem voltage_valid : Valid voltageSource (compute voltageSource) := by decide
theorem current_valid : Valid currentSource (compute currentSource) := by decide
theorem voltage_acyclic : OrderedLT voltageSource (compute voltageSource) := by decide
theorem current_acyclic : OrderedLT currentSource (compute currentSource) := by decide

/-- Spenningskilde: Ohm bestemmer strømmen, Joule effekten (etter utvidende sti). -/
theorem voltage_order :
    (compute voltageSource).σ .ohm = .I ∧ (compute voltageSource).σ .joule = .P ∧
    (compute voltageSource).σ .newton = .T := by decide

/-- Strømkilde: Ohm bestemmer spenningen. -/
theorem current_order :
    (compute currentSource).σ .ohm = .U ∧ (compute currentSource).σ .joule = .P := by decide

/-- Kausal rekkefølge med spenningskilde: Ohm < Joule < Newton. -/
theorem voltage_ranks :
    (compute voltageSource).rank .ohm < (compute voltageSource).rank .joule ∧
    (compute voltageSource).rank .joule < (compute voltageSource).rank .newton := by decide

def circEqs : CEq → Equation Circ ℝ
  | .joule => ⟨[.P, .U, .I], fun s => s .P = s .U * s .I, by
      intro s t h; rw [h .P (by simp), h .U (by simp), h .I (by simp)]⟩
  | .ohm => ⟨[.U, .Rr, .I], fun s => s .U = s .Rr * s .I, by
      intro s t h; rw [h .U (by simp), h .Rr (by simp), h .I (by simp)]⟩
  | .newton => ⟨[.T, .Ta, .k, .P], fun s => s .T = s .Ta + s .k * s .P, by
      intro s t h; rw [h .T (by simp), h .Ta (by simp), h .k (by simp), h .P (by simp)]⟩

/-- Domenet: resistans og spenning er ikke null. -/
def circDom (s : Circ → ℝ) : Prop := s .Rr ≠ 0 ∧ s .U ≠ 0

noncomputable def circMech : CEq → Circ → Mech Circ ℝ
  | .joule, .I => ⟨[.P, .U], fun s => s .P / s .U, by
      intro s t h; show _ = _; rw [h .P (by simp), h .U (by simp)]⟩
  | .joule, .P => ⟨[.U, .I], fun s => s .U * s .I, by
      intro s t h; show _ = _; rw [h .U (by simp), h .I (by simp)]⟩
  | .ohm, .I => ⟨[.U, .Rr], fun s => s .U / s .Rr, by
      intro s t h; show _ = _; rw [h .U (by simp), h .Rr (by simp)]⟩
  | .ohm, .U => ⟨[.Rr, .I], fun s => s .Rr * s .I, by
      intro s t h; show _ = _; rw [h .Rr (by simp), h .I (by simp)]⟩
  | .newton, .T => ⟨[.Ta, .k, .P], fun s => s .Ta + s .k * s .P, by
      intro s t h; show _ = _; rw [h .Ta (by simp), h .k (by simp), h .P (by simp)]⟩
  | _, _ => SCM.Mech.const 0

noncomputable def circSolvers (ex : List Circ) : Solvers (circS ex) circEqs circDom where
  mech := circMech
  parents := by
    intro e v hv
    cases e <;> simp [circS] at hv <;> rcases hv with rfl | rfl <;> rfl
  sound := by
    intro e v hv s hD
    cases e <;> simp [circS] at hv
    · rcases hv with rfl | rfl
      · show s .P = s .U * s .I ↔ s .I = s .P / s .U
        rw [eq_div_iff hD.2, mul_comm (s .I)]
        exact eq_comm
      · exact Iff.rfl
    · rcases hv with rfl | rfl
      · show s .U = s .Rr * s .I ↔ s .I = s .U / s .Rr
        rw [eq_div_iff hD.1, mul_comm (s .I)]
        exact eq_comm
      · exact Iff.rfl
    · subst hv
      exact Iff.rfl

/-- Den beregnede kretsmodellen med spenningskilde er rekursiv … -/
theorem voltage_recursive :
    (toReading voltageSource _ voltage_valid (circSolvers _)).toSCM.Recursive
      (rankV (compute voltageSource)) :=
  toReading_recursive _ _ _ _ voltage_acyclic

/-- … så ethvert inngrep, for eksempel do(R := c), har ett entydig utfall. -/
theorem voltage_doR_unique (c : ℝ) {u s t : Circ → ℝ}
    (hs : ((toReading voltageSource _ voltage_valid (circSolvers _)).toSCM.doI .Rr c).Solves u s)
    (ht : ((toReading voltageSource _ voltage_valid (circSolvers _)).toSCM.doI .Rr c).Solves u t) :
    s = t :=
  voltage_recursive.doI_unique .Rr c hs ht

theorem current_recursive :
    (toReading currentSource _ current_valid (circSolvers _)).toSCM.Recursive
      (rankV (compute currentSource)) :=
  toReading_recursive _ _ _ _ current_acyclic

/-! ## 3. Markedet: Lean finner likevektsblokken -/

instance : Inhabited MV := ⟨.t⟩

inductive MEq | demand | supply
deriving DecidableEq, Repr

def marketS : Struct MEq MV where
  eqList := [.demand, .supply]
  varList := [.t, .y, .w, .P, .Q]
  eq_complete := by intro e; cases e <;> simp
  var_complete := by intro v; cases v <;> simp
  canSolve
    | .demand => [.Q]
    | .supply => [.P]
  deps
    | .demand, .Q => [.P, .y]
    | .supply, .P => [.Q, .t, .w]
    | _, _ => []
  exo := [.t, .y, .w]

theorem market_valid : Valid marketS (compute marketS) := by decide
theorem market_blocks : OrderedLE marketS (compute marketS) := by decide
/-- Ikke rekursiv: det finnes en syklus. -/
theorem market_cyclic : ¬ OrderedLT marketS (compute marketS) := by decide
/-- Lean finner blokken {etterspørsel, tilbud}, altså {Q, P}. -/
theorem market_block : blockOf marketS .demand = [.demand, .supply] := by decide

def marketEqs (m : Market) : MEq → Equation MV ℝ
  | .demand => ⟨[.Q, .P, .y], fun s => s .Q = m.a - m.b * s .P + m.c * s .y, by
      intro s t h; rw [h .Q (by simp), h .P (by simp), h .y (by simp)]⟩
  | .supply => ⟨[.Q, .P, .t, .w], fun s => s .Q = m.d + m.e * (s .P - s .t) + m.f * s .w, by
      intro s t h; rw [h .Q (by simp), h .P (by simp), h .t (by simp), h .w (by simp)]⟩

noncomputable def marketSolvers (m : Market) : Solvers marketS (marketEqs m) (fun _ => True) where
  mech
    | .demand, _ => m.demandMech
    | .supply, _ => m.supplyMech
  parents := by
    intro e v hv
    cases e <;> simp [marketS] at hv <;> subst hv <;> rfl
  sound := by
    intro e v hv s _
    have he := m.he.ne'
    cases e <;> simp [marketS] at hv <;> subst hv
    · exact Iff.rfl
    · show s .Q = m.d + m.e * (s .P - s .t) + m.f * s .w ↔
        s .P = (s .Q - m.d - m.f * s .w) / m.e + s .t
      constructor
      · intro h; rw [h]; field_simp; ring
      · intro h; rw [h]; field_simp; ring

/-- Den beregnede modellen er markedet fra Blocks.lean … -/
theorem market_computed_eq (m : Market) :
    (toReading marketS _ market_valid (marketSolvers m)).toSCM = m.scm := by
  have h1 : (compute marketS).inv .t = none := by decide
  have h2 : (compute marketS).inv .y = none := by decide
  have h3 : (compute marketS).inv .w = none := by decide
  have h4 : (compute marketS).inv .P = some .supply := by decide
  have h5 : (compute marketS).inv .Q = some .demand := by decide
  simp only [Reading.toSCM, toReading, Market.scm, SCM.mk.injEq]
  funext v
  cases v <;> simp [h1, h2, h3, h4, h5, marketSolvers]

/-- … så blokken Lean fant, er bevist entydig løsbar. -/
theorem market_computed_unique (m : Market) {u s t : MV → ℝ}
    (hs : (toReading marketS _ market_valid (marketSolvers m)).toSCM.Solves u s)
    (ht : (toReading marketS _ market_valid (marketSolvers m)).toSCM.Solves u t) : s = t := by
  rw [market_computed_eq] at hs ht
  exact m.scm_unique hs ht

/-! ## 4. Syklusen x := y, y := x + z, z := x − 1 -/

instance : Inhabited XYZ := ⟨.x⟩

inductive CycEq | ex | ey | ez
deriving DecidableEq, Repr

def cycS : Struct CycEq XYZ where
  eqList := [.ex, .ey, .ez]
  varList := [.x, .y, .z]
  eq_complete := by intro e; cases e <;> simp
  var_complete := by intro v; cases v <;> simp
  canSolve
    | .ex => [.x]
    | .ey => [.y]
    | .ez => [.z]
  deps
    | .ex, .x => [.y]
    | .ey, .y => [.x, .z]
    | .ez, .z => [.x]
    | _, _ => []
  exo := []

theorem cyc_valid : Valid cycS (compute cycS) := by decide
theorem cyc_one_block : blockOf cycS .ex = [.ex, .ey, .ez] := by decide
theorem cyc_not_acyclic : ¬ OrderedLT cycS (compute cycS) := by decide

end Order
end CausalPhys
