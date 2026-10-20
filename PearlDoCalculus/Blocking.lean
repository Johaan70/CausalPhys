/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import PearlDoCalculus.Walks

/-!
# d-separasjonsfundamentet, steg 3: collider og blokkering

Tredje steg i 4b — det begrepsmessig vanskeligste stykket før selve
soundness-teoremet.

En indre node på en vandring er enten en collider eller en ikke-collider,
avgjort av retningsmønsteret til de to kantene som møtes der:

* `→ m ←` (steg inn `fwd`, steg ut `bwd`): collider.
* `→ m →`, `← m →`, `← m ←`: ikke-collider.

Pearls blokkeringskriterium: en vandring er blokkert av et sett `Z` hvis den
inneholder enten en ikke-collider i `Z`, eller en collider der verken noden
selv eller noen etterkommer ligger i `Z`. Her kobles steg 3 tilbake til steg
1 — «etterkommer» er `Reaches`.

`blockedAux` rekurserer over `Walk` og bærer med seg orienteringen til steget
som førte inn til delvandringens startnode (`Incoming`). Det er det som lar
hver indre node klassifiseres: steget inn er kjent fra rekursjonens
parameter, steget ut fra neste konstruktør.

Neste steg: d-separasjonsrelasjonen (steg 4), deretter soundness (steg 5).
-/

namespace PearlDoCalculus

namespace DAG

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]

/--
Orienteringen til steget som førte inn til en node, sett i en større
vandring. `start` betyr at noden er vandringens startpunkt — da er den ikke
en indre node og kan ikke blokkere. `fwd`/`bwd` er retningen på kanten inn.
-/
inductive Incoming
  | start
  | fwd
  | bwd

namespace Walk

/--
`blockedAux Z inc p`: delvandringen `p` inneholder en blokkerende node, gitt
at `p`-ens startnode ble nådd av et steg med orientering `inc`.

Startnoden `m` til en ikke-tom `p` er en indre node når `inc ≠ start`. Den er
en collider når steget inn er `fwd` og steget ut er `bwd`, og blokkerer da
hvis `∀ z ∈ Z, ¬ Reaches m z` (ingen etterkommer, `m` selv inkludert, i `Z`).
Ellers er den en ikke-collider og blokkerer hvis `m ∈ Z`.
-/
def blockedAux {G : DAG V} (Z : Finset V) :
    Incoming → {m t : V} → Walk G m t → Prop
  | _,      _, _, .nil _      => False
  | .start, _, _, .fwd _ rest => blockedAux Z .fwd rest
  | .start, _, _, .bwd _ rest => blockedAux Z .bwd rest
  | .fwd,   m, _, .fwd _ rest => m ∈ Z ∨ blockedAux Z .fwd rest
  | .bwd,   m, _, .fwd _ rest => m ∈ Z ∨ blockedAux Z .fwd rest
  | .fwd,   m, _, .bwd _ rest => (∀ z ∈ Z, ¬ G.Reaches m z) ∨ blockedAux Z .bwd rest
  | .bwd,   m, _, .bwd _ rest => m ∈ Z ∨ blockedAux Z .bwd rest

/--
`Blocked Z p`: vandringen `p` er blokkert av `Z` etter Pearls kriterium.
Startnoden behandles ikke som indre — derfor `Incoming.start`.
-/
def Blocked {G : DAG V} (Z : Finset V) {s t : V} (p : Walk G s t) : Prop :=
  blockedAux Z .start p

/--
`Open Z p`: vandringen er åpen (aktiv) gitt `Z` — ikke blokkert. Det er de
åpne vandringene d-separasjon må utelukke.
-/
def Open {G : DAG V} (Z : Finset V) {s t : V} (p : Walk G s t) : Prop :=
  ¬ Blocked Z p

/-- Den tomme vandringen har ingen indre noder og er aldri blokkert. -/
theorem not_blocked_nil {G : DAG V} (Z : Finset V) (v : V) :
    ¬ Blocked Z (Walk.nil (G := G) v) := by
  simp [Blocked, blockedAux]

end Walk

end DAG

end PearlDoCalculus
