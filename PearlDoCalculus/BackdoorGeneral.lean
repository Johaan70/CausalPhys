/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import PearlDoCalculus.SimpleConfounderObservable

/-!
# Pearls do-kalkyle: Generell back-door, justeringsformelen (trinn 4a)

Pearls generelle back-door-teorem deler seg i to. Gitt en vilkårlig endelig
DAG, en behandling `X`, et utfall `Y` og et justeringssett `Z`:

* (4a) Hvis `Z` oppfyller back-door-kriteriets *fordelingsmessige* konsekvens —
  at den observasjonelle betingede `P(Y | X=x*, Z=z)` er lik den
  intervensjonelle kjernen `P(Y | do(X=x*), Z=z)` der `Z` har masse — så holder
  justeringsformelen `P(Y | do(X=x*)) = Σ_z P(Y|X=x*,Z=z) · P(Z=z)`.
* (4b) Det grafiske back-door-kriteriet *medfører* den konsekvensen.

Denne filen formaliserer 4a: `backdoor_general`. Det er kjernen som ikke
trenger d-separasjon. Beviset er den totale sannsynlighetsloven for den
intervensjonelle fordelingen, pluss substitusjonen kriteriet tillater.

4b — å utlede hypotesen fra grafen — krever d-separasjon med korrekthetsbevis,
og er et eget fundament som bygges trinnvis, ikke her.

## Generaliteten

`backdoor_general` er bevisst abstrakt: konfunderrommet `Ωz`, marginalen `pZ`,
den intervensjonelle kjernen `qY` og den observasjonelle betingede `condY` er
vilkårlige. Enhver konkret back-door-modell er et tilfelle. De to `example`-ene
nederst viser at trinn 0 (minimaltilfellet) og trinn 2 (observerbar form)
faktoriserer gjennom `backdoor_general`: det første med en triviell
back-door-identitet (`condY` lik kjernen per definisjon), det andre med den
ekte, der identiteten er `condY_eq_kernel` under overlapp.
-/

namespace PearlDoCalculus

open scoped BigOperators ENNReal

/--
**Generell back-door-justering — justeringsformel-kjernen.**

La `Z` ha marginal `pZ`. La `qY z` være den intervensjonelle fordelingen til
`Y` gitt `Z = z` under `do(X = x*)`, slik at `P(Y | do(X=x*))` er `pZ.bind qY`.
La `condY z y` være den observasjonelle betingede `P(Y=y | X=x*, Z=z)`.

Hypotesen `hbd` er back-door-kriteriets fordelingskonsekvens: der `Z` har
masse, faller den observasjonelle betingede sammen med den intervensjonelle
kjernen. Da gjelder justeringsformelen

  `P(Y=y | do(X=x*)) = Σ_z condY z y · pZ z`.

Beviset: den totale sannsynlighetsloven for `pZ.bind qY` gir
`Σ_z (qY z) y · pZ z`; der `pZ z = 0` er leddet null på begge sider, og ellers
bytter `hbd` kjernen mot `condY`.
-/
theorem backdoor_general {Ωz Ωy : Type*} [Fintype Ωz]
    (pZ : PMF Ωz) (qY : Ωz → PMF Ωy) (condY : Ωz → Ωy → ENNReal) (y : Ωy)
    (hbd : ∀ z, pZ z ≠ 0 → condY z y = (qY z) y) :
    (pZ.bind qY) y = ∑ z, condY z y * pZ z := by
  rw [PMF.bind_apply, tsum_fintype]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hz : pZ z = 0
  · simp [hz]
  · rw [hbd z hz]
    exact mul_comm _ _

/-
## Forankring: de konkrete tilfellene faktoriserer gjennom `backdoor_general`.
-/

/-- Trinn 0 (minimaltilfellet) som et tilfelle av `backdoor_general`.
Her er back-door-identiteten triviell: `condY` er kjernen per definisjon. -/
example {Ωz Ωx Ωy : Type*} [Fintype Ωz]
    (M : SimpleConfounderModel Ωz Ωx Ωy) (x_star : Ωx) (y : Ωy) :
    (M.doX x_star) y = ∑ z, (M.pY_given_XZ x_star z) y * M.pZ z :=
  backdoor_general M.pZ (fun z => M.pY_given_XZ x_star z)
    (fun z y => (M.pY_given_XZ x_star z) y) y (fun _ _ => rfl)

/-- Trinn 2 (observerbar form) som et tilfelle av `backdoor_general`. Her er
back-door-identiteten den ekte: `condY_eq_kernel`, gyldig under overlapp. -/
example {Ωz Ωx Ωy : Type*} [Fintype Ωz] [Fintype Ωy]
    (M : SimpleConfounderModel Ωz Ωx Ωy) (x_star : Ωx) (y : Ωy)
    (hpos : ∀ z, (M.pX_given_Z z) x_star ≠ 0) :
    (M.doX x_star) y = ∑ z, M.condY y x_star z * M.pZ z :=
  backdoor_general M.pZ (fun z => M.pY_given_XZ x_star z)
    (fun z y => M.condY y x_star z) y
    (fun z hz => M.condY_eq_kernel y x_star z (mul_ne_zero hz (hpos z)))

end PearlDoCalculus
