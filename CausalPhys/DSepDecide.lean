/-
  CausalPhys.DSepDecide — en avgjørbar d-separasjonstest (Bayes-ball), bevist sunn.

  Metode: sertifisert beregning, som i CausalOrder.lean.
    • En kjørbar Bayes-ball-beregning lager et sertifikat: en mengde `anc` som
      skal inneholde alle forfedre av Z, og en mengde `reach` av tilstander
      (node, kom inn langs pila?) som ballen kan nå fra x.
    • `Valid` sjekker at sertifikatet er lukket under Bayes-ball-reglene og at
      y ikke er nådd. Det er et avgjørbart utsagn, så `decide` kan avgjøre det.
    • `Valid.dsep`: et gyldig sertifikat medfører d-separasjon i
      PearlDoCalculus' vandringsbaserte forstand. Beviset går ved induksjon
      over vandringer: en åpen vandring kan aldri forlate `reach`.
    • `condIndep_of_check`: sammen med Probabilistic.lean gir testen betinget
      uavhengighet i fordelingen et ligningssystem genererer.

  Testen er sunn: sier den ja, holder d-separasjonen. Den er ikke bevist
  fullstendig: sier den nei, er det ikke bevist at det finnes en åpen sti.
-/
import CausalPhys.Probabilistic

set_option linter.unusedSectionVars false

open PearlDoCalculus PearlDoCalculus.DAG

namespace CausalPhys
namespace DSep

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Sertifikat og sjekk -/

/-- Sertifikat: forfedre av Z (overmengde holder) og Bayes-ball-tilstander.
    `(m, true)`: ballen kom til m langs en pil inn i m (fra en forelder);
    `(m, false)`: ballen kom til m mot en pil (fra et barn). -/
structure Cert (V : Type) where
  anc   : List V
  reach : List (V × Bool)

/-- Bayes-ball-reglene som lukkethetsbetingelser. -/
def Valid (G : DAG V) (Z : Finset V) (x y : V) (c : Cert V) : Prop :=
  x ≠ y ∧
  (∀ z ∈ Z, z ∈ c.anc) ∧
  (∀ u v, G.edge u v → v ∈ c.anc → u ∈ c.anc) ∧
  (∀ b, G.edge x b → (b, true) ∈ c.reach) ∧
  (∀ b, G.edge b x → (b, false) ∈ c.reach) ∧
  (∀ m d b, (m, d) ∈ c.reach → m ∉ Z → G.edge m b → (b, true) ∈ c.reach) ∧
  (∀ m b, (m, true) ∈ c.reach → m ∈ c.anc → G.edge b m → (b, false) ∈ c.reach) ∧
  (∀ m b, (m, false) ∈ c.reach → m ∉ Z → G.edge b m → (b, false) ∈ c.reach) ∧
  (∀ d, (y, d) ∉ c.reach)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 200000 in
instance (G : DAG V) (Z : Finset V) (x y : V) (c : Cert V) : Decidable (Valid G Z x y c) := by
  unfold Valid; infer_instance

/-! ## Sunnhet -/

theorem anc_of_reaches {G : DAG V} {Z : Finset V} {x y : V} {c : Cert V}
    (h : Valid G Z x y c) {m z : V} (hz : z ∈ Z) (hr : G.Reaches m z) : m ∈ c.anc := by
  have hZ := h.2.1
  have hpred := h.2.2.1
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => exact hZ z hz
  | head e _ ih => exact hpred _ _ e ih

def incOf : Bool → Incoming
  | true => .fwd
  | false => .bwd

/-- En åpen vandring som starter i en tilstand i `reach`, ender i en tilstand i `reach`. -/
theorem open_stays {G : DAG V} {Z : Finset V} {x y : V} {c : Cert V} (h : Valid G Z x y c) :
    ∀ {m t : V} (q : Walk G m t) (d : Bool), (m, d) ∈ c.reach →
      ¬ Walk.blockedAux Z (incOf d) q → ∃ d', (t, d') ∈ c.reach := by
  have hF := h.2.2.2.2.2.1
  have hC := h.2.2.2.2.2.2.1
  have hB := h.2.2.2.2.2.2.2.1
  intro m t q
  induction q with
  | nil a =>
    intro d hd _
    exact ⟨d, hd⟩
  | @fwd a b _ e rest ih =>
    intro d hd hopen
    have hrest : ¬ Walk.blockedAux Z .fwd rest ∧ a ∉ Z := by
      cases d <;> simp only [incOf, Walk.blockedAux, not_or] at hopen <;> exact ⟨hopen.2, hopen.1⟩
    exact ih true (hF a d b hd hrest.2 e) hrest.1
  | @bwd a b _ e rest ih =>
    intro d hd hopen
    cases d with
    | true =>
      simp only [incOf, Walk.blockedAux, not_or] at hopen
      obtain ⟨hcol, hrest⟩ := hopen
      push Not at hcol
      obtain ⟨z, hz, hr⟩ := hcol
      have ha : a ∈ c.anc := anc_of_reaches h hz hr
      exact ih false (hC a b hd ha e) hrest
    | false =>
      simp only [incOf, Walk.blockedAux, not_or] at hopen
      exact ih false (hB a b hd hopen.1 e) hopen.2

/-- Hovedteoremet: et gyldig sertifikat gir d-separasjon. -/
theorem Valid.dsep {G : DAG V} {Z : Finset V} {x y : V} {c : Cert V} (h : Valid G Z x y c) :
    G.DSeparated Z x y := by
  intro p
  by_contra hopen
  have hxy := h.1
  have hx1 := h.2.2.2.1
  have hx2 := h.2.2.2.2.1
  have hy := h.2.2.2.2.2.2.2.2
  cases p with
  | nil => exact hxy rfl
  | fwd e rest =>
    have : ¬ Walk.blockedAux Z .fwd rest := by
      simpa [Walk.Blocked, Walk.blockedAux] using hopen
    obtain ⟨d', hd'⟩ := open_stays h rest true (hx1 _ e) this
    exact hy d' hd'
  | bwd e rest =>
    have : ¬ Walk.blockedAux Z .bwd rest := by
      simpa [Walk.Blocked, Walk.blockedAux] using hopen
    obtain ⟨d', hd'⟩ := open_stays h rest false (hx2 _ e) this
    exact hy d' hd'

/-! ## Algoritmen (kjørbar; utdataene sjekkes av `Valid`) -/

/-- Forfedre av Z, ved iterasjon over en liste av alle noder. -/
def ancIter (G : DAG V) (vs : List V) : Nat → List V → List V
  | 0, A => A
  | k + 1, A => ancIter G vs k (A ++ vs.filter fun u => u ∉ A ∧ ∃ v ∈ A, G.edge u v)

def ancOf (G : DAG V) (vs : List V) (Z : Finset V) : List V :=
  ancIter G vs vs.length (vs.filter fun z => z ∈ Z)

/-- Ett Bayes-ball-steg fra en mengde tilstander. -/
def ballStep (G : DAG V) (vs : List V) (Z : Finset V) (A : List V) (R : List (V × Bool)) :
    List (V × Bool) :=
  R ++ ((R.flatMap fun md =>
    let m := md.1
    (if m ∉ Z then (vs.filter fun b => G.edge m b).map (·, true) else []) ++
    (if (md.2 && decide (m ∈ A)) || (!md.2 && decide (m ∉ Z))
      then (vs.filter fun b => G.edge b m).map (·, false) else [])).filter fun s => s ∉ R).eraseDups

def ballIter (G : DAG V) (vs : List V) (Z : Finset V) (A : List V) :
    Nat → List (V × Bool) → List (V × Bool)
  | 0, R => R
  | k + 1, R => ballIter G vs Z A k (ballStep G vs Z A R)

def computeCert (G : DAG V) (vs : List V) (Z : Finset V) (x : V) : Cert V :=
  let A := ancOf G vs Z
  let R0 := (vs.filter fun b => G.edge x b).map (·, true) ++ (vs.filter fun b => G.edge b x).map (·, false)
  ⟨A, ballIter G vs Z A (2 * vs.length + 2) R0⟩

/-- Avgjørbar mengdetest: hvert par (x, y) har et gyldig sertifikat. -/
def Check (G : DAG V) (vs : List V) (Z X Y : Finset V) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, Valid G Z x y (computeCert G vs Z x)

instance (G : DAG V) (vs : List V) (Z X Y : Finset V) : Decidable (Check G vs Z X Y) := by
  unfold Check; infer_instance

theorem Check.dsepSet {G : DAG V} {vs : List V} {Z X Y : Finset V} (h : Check G vs Z X Y) :
    SetSound.DSeparatedSet G Z X Y :=
  fun x hx y hy => fun p _ => (h x hx y hy).dsep p

/-! ## Fra ligningssystem til betinget uavhengighet, avgjort av `decide` -/

variable {β : Type} [Fintype β] [DecidableEq β] [Inhabited β]

theorem condIndep_of_check (M : SCM V β) (rank : V → ℕ) (hr : M.Recursive rank)
    (P : V → PMF β) (vs : List V) (X Y Z : Finset V) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (h : Check (Prob.toDAG M rank hr) vs Z X Y) :
    (Prob.toCausalModel M rank hr P).CondIndep X Y Z :=
  Prob.condIndep_of_dsep M rank hr P X Y Z hXZ hYZ h.dsepSet

end DSep
end CausalPhys
