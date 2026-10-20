/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import PearlDoCalculus.Blocking

/-!
# d-separasjonsfundamentet, steg 4: d-separasjonsrelasjonen

Fjerde steg i 4b. Steg 1–3 ga reachability, vandringer, og blokkering. Her
samles de til selve relasjonen:

`x` og `y` er d-separert av `Z` når *enhver* vandring mellom dem er blokkert.

Det er en kvantifisering over `Walk G x y`-typen fra steg 2. Negasjonen er
ren: `x` og `y` er ikke d-separert nettopp når det finnes minst én åpen
vandring — en aktiv informasjonskanal i Pearls forstand.

`not_dSeparated_of_edge` er den første konkrete konsekvensen: nabonoder kan
aldri d-separeres, for den direkte kanten er selv en kort, alltid åpen
vandring.

Det som ennå mangler er to ting. Symmetri (`DSeparated G Z x y →
DSeparated G Z y x`) krever vandringsreversering og utsettes til et eget
steg. Og framfor alt: soundness (steg 5) — teoremet om at d-separasjon
faktisk medfører betinget uavhengighet. Steg 1–4 er definisjoner og deres
umiddelbare egenskaper; steg 5 er der fundamentet bærer vekt.
-/

namespace PearlDoCalculus

namespace DAG

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]

/--
`DSeparated G Z x y`: `x` og `y` er d-separert av `Z` — enhver vandring
mellom dem er blokkert.
-/
def DSeparated (G : DAG V) (Z : Finset V) (x y : V) : Prop :=
  ∀ p : Walk G x y, Walk.Blocked Z p

/--
`x` og `y` er *ikke* d-separert nettopp når det finnes en åpen vandring
mellom dem.
-/
theorem not_dSeparated_iff (G : DAG V) (Z : Finset V) (x y : V) :
    ¬ DSeparated G Z x y ↔ ∃ p : Walk G x y, Walk.Open Z p := by
  simp only [DSeparated, Walk.Open, not_forall]

/--
Nabonoder kan aldri d-separeres: den direkte kanten `x → y` er en vandring
av lengde 1, og en vandring uten indre noder er aldri blokkert.
-/
theorem not_dSeparated_of_edge (G : DAG V) (Z : Finset V) {x y : V}
    (h : G.edge x y) : ¬ DSeparated G Z x y := by
  intro hsep
  have hb : Walk.Blocked Z (Walk.fwd h (Walk.nil (G := G) y)) :=
    hsep (Walk.fwd h (Walk.nil (G := G) y))
  simp [Walk.Blocked, Walk.blockedAux] at hb

end DAG

end PearlDoCalculus
