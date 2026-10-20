/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Pearls do-kalkyle: Back-door med mediator (trinn 3)

Trinn 3 i back-door-stigen. Modellen har en mediator på den kausale stien:
DAG-en `Z → X`, `Z → Y`, `X → M`, `M → Y`. Her er `Z` fortsatt konfunder, men
effekten av `X` på `Y` går nå gjennom mediatoren `M`.

Det subtile poenget: justeringssettet er konfunderen `{Z}`, ikke mediatoren
`M`. `M` er en etterkommer av `X` og ligger på den kausale stien; å justere for
den ville blokkert nettopp effekten vi vil måle. Back-door-kriteriet sier
presist dette — justeringssettet kan ikke inneholde etterkommere av `X`.

## Resultatene

* `backdoor_mediator` — strukturell form: `P(Y | do(X=x*))` uttrykt som
  `Σ_z (Σ_m P(M=m|X=x*) · P(Y=y|M=m,Z=z)) · P(Z=z)`. Den indre `Σ_m` er den
  observasjonelle betingede `P(Y|X,Z)` skrevet ut via mediatoren.
* `backdoor_mediator_observable` — samme, med `P(Y|X,Z)` som den ekte
  observasjonelle betingede `condY`, definert ved divisjon fra
  fellesfordelingen, under overlapp-antakelsen `P(X=x*|Z=z) ≠ 0`.

## Betinget uavhengighet

Identiteten hviler på to uavhengigheter som DAG-en koder i kjerne-signaturene:
`M` avhenger kun av `X` (så `M` er uavhengig av `Z` gitt `X`), og `Y` avhenger
kun av `(M, Z)` (så `Y` er uavhengig av `X` gitt `M, Z`). Begge er innebygd i
typene til `pM_given_X` og `pY_given_MZ`.

Som i trinn 2 er `jointMass` den faktoriserte fellesloven; broen til den
`bind`-konstruerte `joint` er et rutinemessig `tsum`-kollaps, ikke tatt med.
-/

namespace PearlDoCalculus

open scoped BigOperators ENNReal

/--
Strukturell kausalmodell med mediator, på fire variabler `Z, X, M, Y` med
DAG-strukturen `Z → X`, `Z → Y`, `X → M`, `M → Y`.

`Z` er konfunder; `M` er mediator på den kausale stien `X → M → Y`.
Signaturene koder DAG-en: `pM_given_X` avhenger kun av `X`, `pY_given_MZ`
av `(M, Z)`.
-/
structure MediatorModel (Ωz Ωx Ωm Ωy : Type*) where
  /-- Marginal fordeling for konfunderen `Z`. -/
  pZ          : PMF Ωz
  /-- Betinget fordeling for `X` gitt `Z`. -/
  pX_given_Z  : Ωz → PMF Ωx
  /-- Betinget fordeling for mediatoren `M` gitt `X`. -/
  pM_given_X  : Ωx → PMF Ωm
  /-- Betinget fordeling for `Y` gitt `(M, Z)`. -/
  pY_given_MZ : Ωm → Ωz → PMF Ωy

namespace MediatorModel

variable {Ωz Ωx Ωm Ωy : Type*} (M : MediatorModel Ωz Ωx Ωm Ωy)

/-- Observasjonell fellesfordeling `P(Z, X, M, Y)` fra DAG-faktoriseringen. -/
noncomputable def joint : PMF (Ωz × Ωx × Ωm × Ωy) :=
  M.pZ.bind fun z =>
    (M.pX_given_Z z).bind fun x =>
      (M.pM_given_X x).bind fun m =>
        (M.pY_given_MZ m z).map fun y => (z, x, m, y)

/--
Intervensjonell marginal `P(Y | do(X = x*))` via trunkert faktorisering:
faktoren `P(X | Z)` erstattes av punktmasse på `x*`. `M` følger fortsatt
`P(M | X = x*)`, og `Y` følger `P(Y | M, Z)`.
-/
noncomputable def doX (x_star : Ωx) : PMF Ωy :=
  M.pZ.bind fun z =>
    (M.pM_given_X x_star).bind fun m =>
      M.pY_given_MZ m z

/-- Fellesfordelingens punktmasse `P(Z=z, X=x, M=m, Y=y)`, ved faktoriseringen. -/
noncomputable def jointMass (z : Ωz) (x : Ωx) (m : Ωm) (y : Ωy) : ENNReal :=
  M.pZ z * (M.pX_given_Z z) x * (M.pM_given_X x) m * (M.pY_given_MZ m z) y

/-- Marginal `P(Z=z, X=x)`, ved å summere ut `M` og `Y`. -/
noncomputable def pZX [Fintype Ωm] [Fintype Ωy] (z : Ωz) (x : Ωx) : ENNReal :=
  ∑ m, ∑ y, M.jointMass z x m y

/-- Marginal `P(Z=z, X=x, Y=y)`, ved å summere ut `M`. -/
noncomputable def pZXY [Fintype Ωm] (z : Ωz) (x : Ωx) (y : Ωy) : ENNReal :=
  ∑ m, M.jointMass z x m y

/-- Observasjonell betinget `P(Y=y | X=x, Z=z) = P(Z,X,Y) / P(Z,X)`. -/
noncomputable def condY [Fintype Ωm] [Fintype Ωy] (y : Ωy) (x : Ωx) (z : Ωz) :
    ENNReal :=
  M.pZXY z x y / M.pZX z x

/--
**Back-door med mediator, strukturell form.**

For DAG-en `Z → X`, `Z → Y`, `X → M`, `M → Y`:

  `P(Y=y | do(X=x*)) = Σ_z (Σ_m P(M=m|X=x*)·P(Y=y|M=m,Z=z)) · P(Z=z)`.

Den indre `Σ_m` er den observasjonelle betingede `P(Y|X=x*,Z=z)` skrevet ut
via mediatoren. Beviset reduserer `doX`-ens nestede `bind` til dobbeltsummen.
-/
theorem backdoor_mediator [Fintype Ωz] [Fintype Ωm]
    (x_star : Ωx) (y : Ωy) :
    (M.doX x_star) y
      = ∑ z, (∑ m, (M.pM_given_X x_star) m * (M.pY_given_MZ m z) y) * M.pZ z := by
  unfold doX
  rw [PMF.bind_apply, tsum_fintype]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [PMF.bind_apply, tsum_fintype]
  exact mul_comm _ _

/--
**Marginaliseringslemma: `P(Z, X) = P(Z) · P(X | Z)`.**

Summer ut `M` og `Y`; `pM_given_X` og `pY_given_MZ` summerer hver til 1.
-/
theorem pZX_eq [Fintype Ωm] [Fintype Ωy] (z : Ωz) (x : Ωx) :
    M.pZX z x = M.pZ z * (M.pX_given_Z z) x := by
  unfold pZX jointMass
  have hinner : ∀ m,
      ∑ y, M.pZ z * (M.pX_given_Z z) x * (M.pM_given_X x) m * (M.pY_given_MZ m z) y
        = M.pZ z * (M.pX_given_Z z) x * (M.pM_given_X x) m := by
    intro m
    rw [← Finset.mul_sum]
    have h1 : ∑ y, (M.pY_given_MZ m z) y = 1 := by
      simpa using (M.pY_given_MZ m z).tsum_coe
    rw [h1, mul_one]
  simp only [hinner]
  rw [← Finset.mul_sum]
  have hM : ∑ m, (M.pM_given_X x) m = 1 := by
    simpa using (M.pM_given_X x).tsum_coe
  rw [hM, mul_one]

/--
**Faktorisering av `P(Z, X, Y)`.**

`P(Z,X,Y) = P(Z)·P(X|Z) · Σ_m P(M=m|X)·P(Y|M,Z)` — den indre summen er
mediator-marginaliseringen.
-/
theorem pZXY_eq [Fintype Ωm] (z : Ωz) (x : Ωx) (y : Ωy) :
    M.pZXY z x y
      = (M.pZ z * (M.pX_given_Z z) x)
          * ∑ m, (M.pM_given_X x) m * (M.pY_given_MZ m z) y := by
  unfold pZXY jointMass
  simp_rw [mul_assoc (M.pZ z * (M.pX_given_Z z) x)]
  rw [← Finset.mul_sum]

/--
**Den observasjonelle betingede er lik mediator-summen, under positivitet.**

Når `P(Z=z, X=x) ≠ 0` faller `condY = P(Y|X,Z)` sammen med
`Σ_m P(M=m|X)·P(Y|M,Z)`. Beviset er kansellering: `(c · S) / c = S`.
-/
theorem condY_eq_mediatorsum [Fintype Ωm] [Fintype Ωy]
    (y : Ωy) (x : Ωx) (z : Ωz)
    (hpos : M.pZ z * (M.pX_given_Z z) x ≠ 0) :
    M.condY y x z = ∑ m, (M.pM_given_X x) m * (M.pY_given_MZ m z) y := by
  have hctop : M.pZ z * (M.pX_given_Z z) x ≠ ⊤ :=
    ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)
  unfold condY
  rw [M.pZXY_eq z x y, M.pZX_eq z x,
      mul_comm (M.pZ z * (M.pX_given_Z z) x) _, mul_div_assoc,
      ENNReal.div_self hpos hctop, mul_one]

/--
**Back-door med mediator, observerbar form.**

Under overlapp-antakelsen `∀ z, P(X=x* | Z=z) ≠ 0`:

  `P(Y=y | do(X=x*)) = Σ_z P(Y=y | X=x*, Z=z) · P(Z=z)`,

der `P(Y|X,Z)` er den ekte observasjonelle betingede `condY`. Justeringssettet
er konfunderen `Z` alene — mediatoren `M` er marginalisert bort inne i `condY`,
ikke betinget på.
-/
theorem backdoor_mediator_observable [Fintype Ωz] [Fintype Ωm] [Fintype Ωy]
    (x_star : Ωx) (y : Ωy) (hpos : ∀ z, (M.pX_given_Z z) x_star ≠ 0) :
    (M.doX x_star) y = ∑ z, M.condY y x_star z * M.pZ z := by
  rw [M.backdoor_mediator x_star y]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hz : M.pZ z = 0
  · simp [hz]
  · rw [M.condY_eq_mediatorsum y x_star z (mul_ne_zero hz (hpos z))]

end MediatorModel

end PearlDoCalculus
