/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Endelige rettede asykliske grafer (skjelett)

Skjelettstruktur for endelige DAG-er som vi skal trenge for milepæl 2 og
fremover (generelt back-door-kriterium, d-separasjon, do-kalkylens tre regler).

Acyklicitet kodes via en *rangfunksjon* `V → ℕ` som er strengt voksende
langs kanter. For endelige grafer er dette ekvivalent med fravær av sykluser
(eksistens av topologisk sortering), og det er det letteste å arbeide med
formelt.

## Roadmap

* `DAG.parents`, `DAG.ancestors`, `DAG.descendants` — settet av foreldre, forfedre, etterkommere.
* `DAG.path` — induktiv definisjon av sti.
* `DAG.dSeparated` — d-separasjon (chain/fork/collider-blokkering).
* `DAG.backdoorCriterion` — Pearls back-door-kriterium.
* `truncatedFactorization` — generell intervensjon.
* `doCalculus_rule1/2/3` — de tre reglene.
* `shpitserPearlCompleteness` — fullstendighetsteoremet (langt løp).
-/

namespace PearlDoCalculus

/--
En endelig rettet asyklisk graf på en vertekstype `V`. Acyklicitet kodes via
en rangfunksjon: kanter går strengt fra lavere til høyere rang.

For endelige grafer er dette ekvivalent med en topologisk sortering, og er den
mest håndterlige formuleringen formelt.
-/
structure DAG (V : Type*) [DecidableEq V] [Fintype V] where
  /-- Kantrelasjon `u → v`. -/
  edge : V → V → Prop
  /-- Avgjørbar kantrelasjon (slik at vi kan beregne over endelige settet). -/
  decEdge : DecidableRel edge
  /-- Topologisk rang: kanter går strengt fra lavere til høyere rang. -/
  rank : V → ℕ
  /-- Acyklicitet: rangen er strengt voksende langs kanter. -/
  rank_strict_mono : ∀ u v, edge u v → rank u < rank v

namespace DAG

variable {V : Type*} [DecidableEq V] [Fintype V]

attribute [instance] DAG.decEdge

/-- Settet av direkte foreldre til `v` i `G`. -/
def parents (G : DAG V) (v : V) : Finset V :=
  (Finset.univ : Finset V).filter (fun u => G.edge u v)

/-- Acyklicitet (avledet): ingen vertex er sin egen forelder. -/
theorem not_self_edge (G : DAG V) (v : V) : ¬ G.edge v v := by
  intro h
  exact (lt_irrefl _) (G.rank_strict_mono v v h)

end DAG

end PearlDoCalculus
