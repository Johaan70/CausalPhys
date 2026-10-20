/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import PearlDoCalculus.DAG

/-!
# d-separasjonsfundamentet, steg 1: rettet reachability

Dette er første steg i 4b — fundamentet under det generelle back-door-teoremet.
4b bygges trinnvis: hver bit kompilert og committet før neste, ikke som én blind
bolk.

Dette steget etablerer rettet reachability i en endelig DAG: relasjonen
`G.Reaches u v` — `v` nås fra `u` langs rettede kanter. Den trengs to steder
nedstrøms:

* Back-door-kriteriet krever at justeringssettet `Z` ikke inneholder
  etterkommere av behandlingen `X`.
* Collider-regelen i d-separasjon refererer til etterkommere av collideren.

Kjerneegenskapen er `rank_le_of_reaches`: reachability respekterer
rangfunksjonen. Det er den endelige DAG-ens acyklisitet uttrykt på en form vi
kan regne med. `not_reaches_of_edge` er acyklisitet på kantnivå.

Neste steg: stier som induktiv struktur, deretter collider-blokkering.
-/

namespace PearlDoCalculus

namespace DAG

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- `G.Reaches u v`: `v` nås fra `u` via en muligens tom rettet sti — altså
`v` er etterkommer av `u`, der `u` selv regnes som etterkommer av seg selv. -/
def Reaches (G : DAG V) : V → V → Prop :=
  Relation.ReflTransGen G.edge

/-- Reachability er refleksiv. -/
theorem Reaches.refl (G : DAG V) (u : V) : G.Reaches u u :=
  Relation.ReflTransGen.refl

/-- En enkelt kant gir reachability. -/
theorem Reaches.of_edge (G : DAG V) {u v : V} (h : G.edge u v) :
    G.Reaches u v :=
  Relation.ReflTransGen.single h

/-- Reachability er transitiv. -/
theorem Reaches.trans (G : DAG V) {u v w : V}
    (h₁ : G.Reaches u v) (h₂ : G.Reaches v w) : G.Reaches u w :=
  Relation.ReflTransGen.trans h₁ h₂

/--
**Reachability respekterer rang.**

En etterkommer har minst like høy rang som forfaren. Dette er den endelige
DAG-ens acyklisitet uttrykt på regnbar form: rangfunksjonen er en monoton
invariant langs enhver rettet sti.
-/
theorem rank_le_of_reaches (G : DAG V) {u v : V} (h : G.Reaches u v) :
    G.rank u ≤ G.rank v := by
  induction h with
  | refl => exact le_rfl
  | tail _ hbc ih => exact le_trans ih (le_of_lt (G.rank_strict_mono _ _ hbc))

/--
Acyklisitet på kantnivå: følger man en kant `u → v`, finnes ingen rettet sti
tilbake fra `v` til `u`.
-/
theorem not_reaches_of_edge (G : DAG V) {u v : V} (h : G.edge u v) :
    ¬ G.Reaches v u := by
  intro hvu
  exact absurd (G.rank_strict_mono u v h)
    (not_lt.mpr (G.rank_le_of_reaches hvu))

end DAG

end PearlDoCalculus
