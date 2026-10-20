/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import PearlDoCalculus.Reachability

/-!
# d-separasjonsfundamentet, steg 2: stier som induktiv struktur

Andre steg i 4b. Steg 1 ga rettet reachability. d-separasjon handler derimot
om udireket stier: man følger kanter uten å bry seg om retningen, men man
husker retningen til hver enkelt kant — for det er nettopp retningsmønsteret
ved hver node som avgjør om noden er en collider.

`Walk G a b` er en sti fra `a` til `b` bygd av orienterte steg. To
cons-konstruktører holder orienteringen:

* `fwd` legger til en kant som peker framover langs stien (`a → b` i DAG-en),
* `bwd` legger til en kant som peker bakover (`b → a` i DAG-en).

Det er dette skillet steg 3 trenger: en collider er en node der steget inn er
`fwd` og steget ut er `bwd` — to piler som møtes.

Merk: `Walk` tillater gjentatte noder, så dette er strengt tatt en vandring,
ikke en sti i grafteoriens forstand. Soundness-teoremet for d-separasjon
holder på vandringsnivå, så vi pålegger ikke distinkthet nå; en
distinkthetsrefinement kan legges på som eget predikat hvis det trengs.
-/

namespace PearlDoCalculus

namespace DAG

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]

/--
`Walk G a b`: en udireket vandring fra `a` til `b` i DAG-en `G`, bygd av
orienterte steg. Hver kant huskes med sin retning:

* `nil v` — den tomme vandringen i `v`,
* `fwd e rest` — et steg langs en framoverkant, så `rest`,
* `bwd e rest` — et steg langs en bakoverkant, så `rest`.
-/
inductive Walk (G : DAG V) : V → V → Type u
  | nil (v : V) : Walk G v v
  | fwd {a b c : V} : G.edge a b → Walk G b c → Walk G a c
  | bwd {a b c : V} : G.edge b a → Walk G b c → Walk G a c

namespace Walk

/-- Antall kanter i vandringen. -/
def length {G : DAG V} : {a b : V} → Walk G a b → ℕ
  | _, _, .nil _ => 0
  | _, _, .fwd _ rest => length rest + 1
  | _, _, .bwd _ rest => length rest + 1

/-- Nodene vandringen besøker, i rekkefølge fra `a` til `b`. -/
def support {G : DAG V} : {a b : V} → Walk G a b → List V
  | a, _, .nil _ => [a]
  | a, _, .fwd _ rest => a :: support rest
  | a, _, .bwd _ rest => a :: support rest

/-- En vandring besøker nøyaktig én node mer enn den har kanter. -/
theorem length_support {G : DAG V} {a b : V} (p : Walk G a b) :
    p.support.length = p.length + 1 := by
  induction p with
  | nil v => simp [support, length]
  | fwd e q ih => simp [support, length, ih]
  | bwd e q ih => simp [support, length, ih]

end Walk

end DAG

end PearlDoCalculus
