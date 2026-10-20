/-
  CausalPhys.CausalOrder — Lean beregner Simon-ordenen selv.

  Inndata er bare STRUKTUREN i et ligningssystem: hvilke variabler hver ligning
  kan løses for, hvilke variabler løsningen da leser, og hvilke variabler labben
  holder fast (eksogene). Ut kommer:

    • en perfekt matching ligning → endogen variabel (Kuhns algoritme med
      utvidende stier),
    • blokkene (sterkt sammenhengende komponenter i avhengighetsgrafen), og
    • en rang som ordner blokkene.

  Dette er den fine Dulmage–Mendelsohn-dekomposisjonen for et velbestemt system
  (like mange ligninger som endogene variabler, perfekt matching finnes).

  Metode: sertifisert beregning. Algoritmen er ikke bevist å alltid lykkes, men
  utdataene er et SERTIFIKAT som sjekkes av avgjørbare utsagn (`Valid`,
  `OrderedLT`, `OrderedLE`). Kjernen avgjør dem med `decide`, og teoremene under
  garanterer at et sjekket sertifikat sammen med semantiske løsere gir
  • en gyldig Simon-lesning (`toReading`),
  • de eksogene variablene er nøyaktig de labben valgte (`toReading_exo_iff`),
  • en rekursiv kausal modell når ordenen er streng (`toReading_recursive`), og
  • blokkstruktur (`toReading_parents_le`) når den er svak.
-/
import CausalPhys.Core
import CausalPhys.SimonOrder

set_option linter.unusedSectionVars false

namespace CausalPhys
namespace Order

/-! ## Struktur og sertifikat -/

/-- Strukturen til et ligningssystem, uten selve ligningene. -/
structure Struct (E V : Type) where
  eqList       : List E
  varList      : List V
  eq_complete  : ∀ e, e ∈ eqList
  var_complete : ∀ v, v ∈ varList
  /-- Variablene ligning `e` kan løses for. -/
  canSolve     : E → List V
  /-- Foreldrene når `e` løses for `v`. -/
  deps         : E → V → List V
  /-- Variablene labben holder fast. -/
  exo          : List V

/-- Et sertifikat: matching, invers matching og rang på ligningene. -/
structure Cert (E V : Type) where
  σ    : E → V
  inv  : V → Option E
  rank : E → Nat

variable {E V : Type} [DecidableEq E] [DecidableEq V]

/-! ## Algoritmen (kjørbar, strukturelt rekursiv slik at kjernen kan evaluere den) -/

def upd (f : V → Option E) (a : V) (b : Option E) : V → Option E :=
  fun x => if x = a then b else f x

/-- Utvidende sti fra ligning `e` (Kuhn). `fuel` synker i hvert kall. -/
def aug (S : Struct E V) : Nat → E → List V → List V → (V → Option E) → Option (V → Option E)
  | 0, _, _, _, _ => none
  | _ + 1, _, [], _, _ => none
  | f + 1, e, v :: vs, vis, mV =>
    if v ∈ vis ∨ v ∈ S.exo then aug S f e vs vis mV
    else
      match mV v with
      | none => some (upd mV v (some e))
      | some e' =>
        match aug S f e' (S.canSolve e') (v :: vis) mV with
        | some m' => some (upd m' v (some e))
        | none => aug S f e vs (v :: vis) mV

/-- Match alle ligningene etter tur. -/
def matchAll (S : Struct E V) (fuel : Nat) : List E → (V → Option E) → Option (V → Option E)
  | [], mV => some mV
  | e :: es, mV =>
    match aug S fuel e (S.canSolve e) [] mV with
    | some m' => matchAll S fuel es m'
    | none => none

def fuelOf (S : Struct E V) : Nat := 4 * (S.eqList.length + 1) * (S.varList.length + 1) + 16

/-- Variabel → ligningen som bestemmer den. -/
def invOf (S : Struct E V) : V → Option E :=
  (matchAll S (fuelOf S) S.eqList (fun _ => none)).getD (fun _ => none)

/-- Ligning → variabelen den bestemmer. -/
def sigmaOf [Inhabited V] (S : Struct E V) (e : E) : V :=
  (S.varList.find? (fun v => decide (invOf S v = some e))).getD default

/-- Kant c → b: ligning b leser variabelen ligning c bestemmer. -/
def edge [Inhabited V] (S : Struct E V) (c b : E) : Bool :=
  decide (sigmaOf S c ∈ S.deps b (sigmaOf S b))

def reachStep [Inhabited V] (S : Struct E V) (R : List (E × E)) : List (E × E) :=
  (R ++ (R.flatMap fun ac => (S.eqList.filter fun b => edge S ac.2 b).map fun b => (ac.1, b))).eraseDups

def reachIter [Inhabited V] (S : Struct E V) : Nat → List (E × E) → List (E × E)
  | 0, R => R
  | k + 1, R => reachIter S k (reachStep S R)

/-- Nåbarhet i avhengighetsgrafen (refleksiv og transitiv). -/
def reachList [Inhabited V] (S : Struct E V) : List (E × E) :=
  reachIter S S.eqList.length (S.eqList.map fun a => (a, a))

def reach [Inhabited V] (S : Struct E V) (a b : E) : Bool := decide ((a, b) ∈ reachList S)

/-- Rang = antall ligninger strengt under i blokkordenen. -/
def rankOf [Inhabited V] (S : Struct E V) (e : E) : Nat :=
  (S.eqList.filter fun x => reach S x e && !reach S e x).length

/-- Hele beregningen. -/
def compute [Inhabited V] (S : Struct E V) : Cert E V :=
  ⟨sigmaOf S, invOf S, rankOf S⟩

/-- Ligningene i samme blokk som `e`. -/
def blockOf [Inhabited V] (S : Struct E V) (e : E) : List E :=
  S.eqList.filter fun x => reach S x e && reach S e x

/-! ## Sjekkeren: avgjørbare utsagn -/

/-- Sertifikatet er en perfekt matching av ligninger på de endogene variablene. -/
def Valid (S : Struct E V) (c : Cert E V) : Prop :=
  (∀ e ∈ S.eqList, c.σ e ∈ S.canSolve e) ∧
  (∀ v ∈ S.varList, ∀ e ∈ S.eqList, c.inv v = some e ↔ c.σ e = v) ∧
  (∀ v ∈ S.varList, c.inv v = none ↔ v ∈ S.exo)

/-- Blokkorden: en ligning leser bare variabler fra samme eller lavere blokk. -/
def OrderedLE (S : Struct E V) (c : Cert E V) : Prop :=
  ∀ e ∈ S.eqList, ∀ p ∈ S.deps e (c.σ e), ∀ e' ∈ S.eqList, c.inv p = some e' → c.rank e' ≤ c.rank e

/-- Streng orden: ingen sykler, alle blokker er enkeltligninger. -/
def OrderedLT (S : Struct E V) (c : Cert E V) : Prop :=
  ∀ e ∈ S.eqList, ∀ p ∈ S.deps e (c.σ e), ∀ e' ∈ S.eqList, c.inv p = some e' → c.rank e' < c.rank e

instance (S : Struct E V) (c : Cert E V) : Decidable (Valid S c) := by
  unfold Valid; infer_instance
instance (S : Struct E V) (c : Cert E V) : Decidable (OrderedLE S c) := by
  unfold OrderedLE; infer_instance
instance (S : Struct E V) (c : Cert E V) : Decidable (OrderedLT S c) := by
  unfold OrderedLT; infer_instance

/-! ## Fra sertifikat til gyldig lesning -/

theorem Valid.mem {S : Struct E V} {c : Cert E V} (h : Valid S c) (e : E) :
    c.σ e ∈ S.canSolve e := h.1 e (S.eq_complete e)

theorem Valid.inv_iff {S : Struct E V} {c : Cert E V} (h : Valid S c) (v : V) (e : E) :
    c.inv v = some e ↔ c.σ e = v := h.2.1 v (S.var_complete v) e (S.eq_complete e)

theorem Valid.inv_none {S : Struct E V} {c : Cert E V} (h : Valid S c) (v : V) :
    c.inv v = none ↔ v ∈ S.exo := h.2.2 v (S.var_complete v)

universe u
variable {α : Type u}

/-- Semantiske løsere: for hver tillatt (ligning, variabel) en mekanisme som
    løser ligningen for variabelen på domenet `D`, med foreldrene strukturen oppgir. -/
structure Solvers (S : Struct E V) (eqs : E → Equation V α) (D : (V → α) → Prop) where
  mech    : E → V → Mech V α
  parents : ∀ e v, v ∈ S.canSolve e → (mech e v).parents = S.deps e v
  sound   : ∀ e v, v ∈ S.canSolve e → ∀ s, D s → ((eqs e).holds s ↔ s v = (mech e v).f s)

variable {eqs : E → Equation V α} {D : (V → α) → Prop}

/-- Hovedteoremet: et gyldig sertifikat gir en gyldig Simon-lesning. -/
def toReading (S : Struct E V) (c : Cert E V) (hv : Valid S c) (sol : Solvers S eqs D) :
    Reading eqs D where
  read v := (c.inv v).map fun e => (e, sol.mech e v)
  sound := by
    intro v e m h s hD
    cases hi : c.inv v with
    | none => simp [hi] at h
    | some e' =>
      simp only [hi, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hσ : c.σ e' = v := (hv.inv_iff v e').1 hi
      have hmem : v ∈ S.canSolve e' := hσ ▸ hv.mem e'
      exact sol.sound e' v hmem s hD
  cover := by
    intro e
    refine ⟨c.σ e, sol.mech e (c.σ e), ?_⟩
    simp [(hv.inv_iff (c.σ e) e).2 rfl]
  inj := by
    intro v w e m m' h1 h2
    cases hi : c.inv v with
    | none => simp [hi] at h1
    | some e1 =>
      cases hj : c.inv w with
      | none => simp [hj] at h2
      | some e2 =>
        simp only [hi, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
        simp only [hj, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
        have a := (hv.inv_iff v e1).1 hi
        have b := (hv.inv_iff w e2).1 hj
        rw [← a, ← b, h1.1, h2.1]

/-- De eksogene variablene i lesningen er nøyaktig dem labben valgte. -/
theorem toReading_exo_iff (S : Struct E V) (c : Cert E V) (hv : Valid S c)
    (sol : Solvers S eqs D) (v : V) :
    (toReading S c hv sol).read v = none ↔ v ∈ S.exo := by
  rw [← hv.inv_none v]
  show (c.inv v).map _ = none ↔ _
  cases c.inv v <;> simp

/-- Rang på variabler: eksogene får 0, en endogen får rangen til sin ligning + 1. -/
def rankV (c : Cert E V) (v : V) : Nat :=
  match c.inv v with
  | none => 0
  | some e => c.rank e + 1

/-- Mekanismen til en endogen variabel i den beregnede modellen. -/
theorem toReading_mech {S : Struct E V} {c : Cert E V} {hv : Valid S c} {sol : Solvers S eqs D}
    {v : V} {m : Mech V α} (hm : (toReading S c hv sol).toSCM.mech v = some m) :
    ∃ e, c.inv v = some e ∧ c.σ e = v ∧ m = sol.mech e v := by
  cases hi : c.inv v with
  | none =>
    simp [Reading.toSCM, toReading, hi] at hm
  | some e =>
    simp [Reading.toSCM, toReading, hi] at hm
    exact ⟨e, rfl, (hv.inv_iff v e).1 hi, hm.symm⟩

/-- Streng orden ⇒ den beregnede kausale modellen er rekursiv. Da gir kjernen
    entydige løsninger og entydige utfall av alle inngrep. -/
theorem toReading_recursive (S : Struct E V) (c : Cert E V) (hv : Valid S c)
    (sol : Solvers S eqs D) (hlt : OrderedLT S c) :
    (toReading S c hv sol).toSCM.Recursive (rankV c) := by
  intro v m hm p hp
  obtain ⟨e, hi, hσ, rfl⟩ := toReading_mech hm
  have hmem : v ∈ S.canSolve e := hσ ▸ hv.mem e
  rw [sol.parents e v hmem, ← hσ] at hp
  have hrv : rankV c v = c.rank e + 1 := by simp [rankV, hi]
  rw [hrv]
  cases hp' : c.inv p with
  | none => simp [rankV, hp']
  | some e' =>
    have := hlt e (S.eq_complete e) p hp e' (S.eq_complete e') hp'
    simp [rankV, hp']
    omega

/-- Svak orden ⇒ foreldre ligger i samme eller lavere blokk. -/
theorem toReading_parents_le (S : Struct E V) (c : Cert E V) (hv : Valid S c)
    (sol : Solvers S eqs D) (hle : OrderedLE S c) :
    ∀ v m, (toReading S c hv sol).toSCM.mech v = some m →
      ∀ p, p ∈ m.parents → rankV c p ≤ rankV c v := by
  intro v m hm p hp
  obtain ⟨e, hi, hσ, rfl⟩ := toReading_mech hm
  have hmem : v ∈ S.canSolve e := hσ ▸ hv.mem e
  rw [sol.parents e v hmem, ← hσ] at hp
  have hrv : rankV c v = c.rank e + 1 := by simp [rankV, hi]
  rw [hrv]
  cases hp' : c.inv p with
  | none => simp [rankV, hp']
  | some e' =>
    have := hle e (S.eq_complete e) p hp e' (S.eq_complete e') hp'
    simp [rankV, hp']
    omega

end Order
end CausalPhys
