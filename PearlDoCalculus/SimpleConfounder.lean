/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Pearls do-kalkyle: Minimal konfundermodell

Denne filen etablerer det minste ikke-trivielle kausalmodell-tilfellet der
do-operatoren skiller seg fra betinging: tre variabler `Z`, `X`, `Y` med
DAG-strukturen `Z → X`, `Z → Y`, `X → Y`. Her er `Z` en konfunder for den
kausale effekten av `X` på `Y`.

Hovedresultatet `backdoor_adjustment` sier at den intervensjonelle
fordelingen `P(Y | do(X = x*))` er lik back-door-justert formel
`Σ_z P(Y | X = x*, Z = z) · P(Z = z)`.

## Kolmogorov-minimale antakelser

Vi forutsetter kun:
* Tre typer `Ωz Ωx Ωy` (verdimengder for `Z`, `X`, `Y`); for `backdoor_adjustment`
  også at `Ωz` er endelig (`Fintype Ωz`).
* En marginal `P(Z)` på `Z` (felt `pZ`).
* Betingede kjerner `P(X | Z)` og `P(Y | X, Z)` (felt `pX_given_Z`, `pY_given_XZ`).

Ingenting annet trengs for dette tilfellet. DAG-strukturen kodes implisitt
i *signaturen* til kjernene.

## Begrepsmessig kjerne

I denne minimalmodellen er beviset i hovedsak en utregning: vi *konstruerer*
fellesfordelingen fra faktoriseringen, så den betingede `P(Y | X, Z)` er per
definisjon lik kjernen `pY_given_XZ`. Det matematiske innholdet ligger i å
skille presist mellom de to fordelingene — observasjonell og intervensjonell —
og gjøre relasjonen mellom dem eksplisitt:

* `joint` bygger den observasjonelle fellesfordelingen.
* `doX` bygger den intervensjonelle marginalen via *trunkert faktorisering*:
  faktoren `P(X | Z)` erstattes av punktmasse på `x*`.
* `backdoor_adjustment` viser at intervensjonelle størrelser kan uttrykkes
  som vektet sum av observasjonelle størrelser når `Z` "blokkerer" alle
  back-door-stier fra `X` til `Y`. I trekanten her er den eneste back-door-stien
  `X ← Z → Y`, og den blokkeres av `{Z}`.
-/

namespace PearlDoCalculus

open scoped BigOperators ENNReal

/--
En minimal strukturell kausalmodell på tre variabler `Z, X, Y` med
DAG-strukturen `Z → X`, `Z → Y`, `X → Y`.

Signaturene koder DAG-en: `pX_given_Z` avhenger kun av `Z`, og
`pY_given_XZ` av `(X, Z)`. Det er ingen kjerne for `Z` selv — bare
marginalen `pZ` — siden `Z` ikke har foreldre.
-/
structure SimpleConfounderModel (Ωz Ωx Ωy : Type*) where
  /-- Marginal fordeling for konfunderen `Z`. -/
  pZ          : PMF Ωz
  /-- Betinget fordeling for `X` gitt `Z`. -/
  pX_given_Z  : Ωz → PMF Ωx
  /-- Betinget fordeling for `Y` gitt `(X, Z)`. -/
  pY_given_XZ : Ωx → Ωz → PMF Ωy

namespace SimpleConfounderModel

variable {Ωz Ωx Ωy : Type*}

/--
Observasjonell fellesfordeling `P(Z, X, Y)` bygget fra DAG-faktoriseringen:
`P(Z, X, Y) = P(Z) · P(X | Z) · P(Y | X, Z)`.
-/
noncomputable def joint (M : SimpleConfounderModel Ωz Ωx Ωy) :
    PMF (Ωz × Ωx × Ωy) :=
  M.pZ.bind fun z =>
    (M.pX_given_Z z).bind fun x =>
      (M.pY_given_XZ x z).map fun y => (z, x, y)

/--
Intervensjonell marginal `P(Y | do(X = x*))` via Pearls trunkerte faktorisering.

I uttrykket `P(Z) · P(X | Z) · P(Y | X, Z)` erstatter intervensjonen `do(X = x*)`
faktoren `P(X | Z)` med punktmasse på `x*`. Etter marginalisering over `Z` står
vi igjen med

  `P(Y = y | do(X = x*)) = Σ_z P(Z = z) · P(Y = y | X = x*, Z = z)`.

Dette er forskjellig fra den observasjonelle betingede `P(Y = y | X = x*)`, som
ville hatt `P(Z = z | X = x*)` (ikke `P(Z = z)`) i summen — og det er nettopp
konfunder-skjevheten.
-/
noncomputable def doX (M : SimpleConfounderModel Ωz Ωx Ωy) (x_star : Ωx) :
    PMF Ωy :=
  M.pZ.bind fun z => M.pY_given_XZ x_star z

/--
**Back-door-justering (minimaltilfellet).**

For DAG-en `Z → X`, `Z → Y`, `X → Y` er den intervensjonelle fordelingen
`P(Y | do(X = x*))` identifiserbar fra den observasjonelle fordelingen som

  `Σ_z P(Y | X = x*, Z = z) · P(Z = z)`.

Begrepsmessig: høyresiden er beregnbar fra observasjonsdata alene
(ingen intervensjon nødvendig), og teoremet sier at den gir samme svar som
faktisk å intervenere på `X`. Den strukturelle premissen som gjør dette
mulig, er at `{Z}` blokkerer den eneste back-door-stien `X ← Z → Y`.

I denne minimalmodellen er beviset en utregning som reduserer
`PMF.bind`-strukturen i `doX` til justeringssummen via `PMF.bind_apply`
og endelig-type-identiteten `tsum = Finset.sum`.
-/
theorem backdoor_adjustment [Fintype Ωz]
    (M : SimpleConfounderModel Ωz Ωx Ωy) (x_star : Ωx) (y : Ωy) :
    (M.doX x_star) y = ∑ z, M.pY_given_XZ x_star z y * M.pZ z := by
  unfold doX
  rw [PMF.bind_apply, tsum_fintype]
  exact Finset.sum_congr rfl fun z _ => mul_comm _ _

/--
Variant med argumentene i naturlig "observasjonell" rekkefølge:
`P(Z) · P(Y | X, Z)`. Algebraisk identisk med `backdoor_adjustment`,
men noen ganger lettere å bruke i avledninger.
-/
theorem backdoor_adjustment' [Fintype Ωz]
    (M : SimpleConfounderModel Ωz Ωx Ωy) (x_star : Ωx) (y : Ωy) :
    (M.doX x_star) y = ∑ z, M.pZ z * M.pY_given_XZ x_star z y := by
  unfold doX
  rw [PMF.bind_apply, tsum_fintype]

end SimpleConfounderModel

end PearlDoCalculus
