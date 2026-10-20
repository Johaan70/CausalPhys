/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Pearls do-kalkyle: Front-door-strukturen (strukturell form + kanselleringslemma)

Denne filen formaliserer front-door-kausalmodellen og beviser to teoremer:

1. `frontdoor_structural` — strukturell form av front-door-justering.
2. `frontdoor_X_cancellation` — den algebraiske kjernen som lar oss eliminere
   referansen til den uobserverte konfunderen `U`.

DAG-strukturen er `U → X`, `U → Y`, `X → Z`, `Z → Y`, der `U` typisk er en
uobservert konfunder og `Z` er en observert mediator (klassisk:
X = røyking, Z = tjære, Y = kreft, U = disposisjon).

## Hva er bevist

`frontdoor_structural` viser at intervensjonen kan skrives som
`Σ_z P(Z=z | X=x*) · Σ_u P(U=u) · P(Y=y | Z=z, U=u)`. Dette er en strukturell
omforming som fortsatt refererer til `U`.

`frontdoor_X_cancellation` er kanselleringslemmaet: når vi summerer over `x'`
med vekter `pX_given_U(u, x')`, summerer disse til 1 (siden `pX_given_U u` er
en PMF), og resultatet kollapser til en ren `pU`-vektet sum.

Disse to teoremene utgjør den algebraiske bunnsteinen for den fulle
observerbare front-door-formelen. Det som gjenstår for milepæl 2b er:

* Definere observerbar fellesfordeling `PMF (ΩX × ΩZ × ΩY)` ved å
  marginalisere ut `U`.
* Definere betingede sannsynligheter `P(X)`, `P(Z|X)`, `P(Y|X,Z)` via
  ENNReal-divisjon med 0/0 = 0-konvensjon.
* Bevise at den observerbare formelen reduserer til `frontdoor_structural`
  via `frontdoor_X_cancellation`, under egnede positivitetsantakelser.

Kanselleringslemmaet er det matematisk substansielle steget; resten er
"plumbing" rundt betinget sannsynlighet i Mathlib.
-/

namespace PearlDoCalculus

open scoped BigOperators ENNReal

/--
Front-door-modell på fire variabler `U, X, Z, Y` med DAG-strukturen
`U → X`, `U → Y`, `X → Z`, `Z → Y`.

Signaturene koder DAG-en:
* `pX_given_U` avhenger kun av `U` (Z er ikke forelder av X).
* `pZ_given_X` avhenger kun av `X` (U er ikke forelder av Z direkte).
* `pY_given_ZU` avhenger av `(Z, U)` (X er ikke direkte forelder av Y).
-/
structure FrontDoorModel (ΩU ΩX ΩZ ΩY : Type*) where
  /-- Marginal fordeling for den uobserverte konfunderen `U`. -/
  pU          : PMF ΩU
  /-- Betinget fordeling for `X` gitt `U`. -/
  pX_given_U  : ΩU → PMF ΩX
  /-- Betinget fordeling for `Z` gitt `X` (mediatoren). -/
  pZ_given_X  : ΩX → PMF ΩZ
  /-- Betinget fordeling for `Y` gitt `(Z, U)`. -/
  pY_given_ZU : ΩZ → ΩU → PMF ΩY

namespace FrontDoorModel

variable {ΩU ΩX ΩZ ΩY : Type*}

/-- Full observasjonell fellesfordeling `P(U, X, Z, Y)`. -/
noncomputable def joint (M : FrontDoorModel ΩU ΩX ΩZ ΩY) :
    PMF (ΩU × ΩX × ΩZ × ΩY) :=
  M.pU.bind fun u =>
    (M.pX_given_U u).bind fun x =>
      (M.pZ_given_X x).bind fun z =>
        (M.pY_given_ZU z u).map fun y => (u, x, z, y)

/--
Intervensjonell marginal `P(Y | do(X = x*))` via trunkert faktorisering.
`pX_given_U` erstattes av punktmasse på `x*`; resultatet marginaliseres
over `(U, Z)`.
-/
noncomputable def doX (M : FrontDoorModel ΩU ΩX ΩZ ΩY) (x_star : ΩX) : PMF ΩY :=
  M.pU.bind fun u =>
    (M.pZ_given_X x_star).bind fun z =>
      M.pY_given_ZU z u

/--
**Front-door-justering, strukturell form.**

For DAG-en `U → X`, `U → Y`, `X → Z`, `Z → Y`:

  `P(Y = y | do(X = x*)) = Σ_z P(Z=z | X=x*) · Σ_u P(U=u) · P(Y=y | Z=z, U=u)`.

Intervensjonen propageres gjennom mediatoren `Z` (ytre sum), mens
`U`-bidraget faktoriserer som en indre sum vektet av marginalen `pU`.
-/
theorem frontdoor_structural [Fintype ΩU] [Fintype ΩZ]
    (M : FrontDoorModel ΩU ΩX ΩZ ΩY) (x_star : ΩX) (y : ΩY) :
    (M.doX x_star) y =
      ∑ z, (M.pZ_given_X x_star) z * ∑ u, M.pU u * (M.pY_given_ZU z u) y := by
  unfold doX
  rw [PMF.bind_apply, tsum_fintype]
  have inner_unfold : ∀ u,
      ((M.pZ_given_X x_star).bind (fun z => M.pY_given_ZU z u)) y =
        ∑ z, M.pZ_given_X x_star z * (M.pY_given_ZU z u) y := by
    intro u
    rw [PMF.bind_apply, tsum_fintype]
  simp_rw [inner_unfold]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun u _ => ?_
  ring

/--
**Front-door, kanselleringslemma.**

Den algebraiske kjernen i front-door-identifikasjonen:

  `Σ_x' Σ_u pU(u) · pX_given_U(u, x') · pY_given_ZU(z, u, y)`
   ` = Σ_u pU(u) · pY_given_ZU(z, u, y)`

Tolkning: summen over `x'` med vekter `pX_given_U(u, x')` kollapser fordi
`pX_given_U u` er en PMF (summerer til 1). Det er nettopp dette som lar oss
eliminere referansen til `U` i den observerbare formen — `x'`-summen i
front-door-formelen "absorberer" `pX_given_U`-faktoren, og det som står
igjen er ren `pU`-vektet sum.

Bevisstrategi:
1. Bytt summasjonsrekkefølge (`Finset.sum_comm`).
2. For hver `u`, faktoriser ut den `x'`-uavhengige termen.
3. Trekk faktoren ut av summen (`Finset.mul_sum`).
4. Den indre summen `Σ_x' pX_given_U(u, x') = 1` siden `pX_given_U u` er PMF.
5. `mul_one` avslutter.
-/
theorem frontdoor_X_cancellation [Fintype ΩX] [Fintype ΩU]
    (M : FrontDoorModel ΩU ΩX ΩZ ΩY) (z : ΩZ) (y : ΩY) :
    ∑ x' : ΩX, ∑ u : ΩU, M.pU u * (M.pX_given_U u) x' * (M.pY_given_ZU z u) y =
      ∑ u : ΩU, M.pU u * (M.pY_given_ZU z u) y := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  have h_factor : ∀ x' : ΩX,
      M.pU u * (M.pX_given_U u) x' * (M.pY_given_ZU z u) y =
      (M.pU u * (M.pY_given_ZU z u) y) * (M.pX_given_U u) x' := by
    intro x'; ring
  simp_rw [h_factor]
  rw [← Finset.mul_sum]
  have h_sum_one : ∑ x' : ΩX, (M.pX_given_U u) x' = 1 := by
    simpa using (M.pX_given_U u).tsum_coe
  rw [h_sum_one, mul_one]

end FrontDoorModel

end PearlDoCalculus
