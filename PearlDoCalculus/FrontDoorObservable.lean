/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import PearlDoCalculus.FrontDoor

/-!
# Pearls do-kalkyle: Front-door observerbar form (fundament)

Denne filen bygger fundamentet for den observerbare front-door-formelen:
de observerbare marginalene og betingede sannsynlighetene som lar oss
uttrykke `P(Y | do(X))` uten referanse til den uobserverte konfunderen `U`.

## Argument-konvensjon

Kjernene i `FrontDoorModel` er curriet som `betingelse → PMF utfall`:
`pX_given_U u x`, `pZ_given_X x z`, `pY_given_ZU z u y`. De observerbare
betingede defineres med utfall først: `pU_given_X u x` ("P(U=u | X=x)"),
`pY_given_XZ y x z`. Marginalene: `pX x`, `pXZ x z`, `pXZY x z y`.

## Innhold

* `pX`, `pXZ`, `pXZY` — observerbare marginaler, med `U` marginalisert ut.
* `pU_given_X`, `pY_given_XZ` — observerbare betingede via ENNReal-divisjon.
* `pXZ_eq_pX_mul_pZ_given_X` — strukturlemma: `P(X,Z) = P(X) * P(Z|X)`.
* `sum_pU_given_X_times_pY` — capstone: `Σ_u P(U|X) * P(Y|Z,U) = P(Y|X,Z)`,
  den betingede uavhengigheten som baerer front-door-identifikasjonen.

## Merknad om hypotesen

Capstone-lemmaet trenger kun `P(Z=z | X=x') ≠ 0`, ikke full positivitet av
`P(X)`. Grunnen: kanselleringen `(A*c)/(b*c) = A/b` i ENNReal holder for
enhver `b` saa lenge `c ≠ 0` og `c ≠ ⊤` — ogsaa naar `b = 0` (begge sider
blir da `⊤` eller `0` konsistent).
-/

namespace PearlDoCalculus

open scoped BigOperators ENNReal

namespace FrontDoorModel

variable {ΩU ΩX ΩZ ΩY : Type*} [Fintype ΩU] (M : FrontDoorModel ΩU ΩX ΩZ ΩY)

/-- Observerbar marginal `P(X = x)`, med `U` marginalisert ut. -/
noncomputable def pX (x : ΩX) : ENNReal :=
  ∑ u, M.pU u * (M.pX_given_U u) x

/-- Observerbar marginal `P(X = x, Z = z)`, med `U` marginalisert ut. -/
noncomputable def pXZ (x : ΩX) (z : ΩZ) : ENNReal :=
  ∑ u, M.pU u * (M.pX_given_U u) x * (M.pZ_given_X x) z

/-- Observerbar marginal `P(X = x, Z = z, Y = y)`, med `U` marginalisert ut. -/
noncomputable def pXZY (x : ΩX) (z : ΩZ) (y : ΩY) : ENNReal :=
  ∑ u, M.pU u * (M.pX_given_U u) x * (M.pZ_given_X x) z * (M.pY_given_ZU z u) y

/-- Observerbar betinget `P(U = u | X = x) = P(U, X) / P(X)`. -/
noncomputable def pU_given_X (u : ΩU) (x : ΩX) : ENNReal :=
  (M.pU u * (M.pX_given_U u) x) / M.pX x

/-- Observerbar betinget `P(Y = y | X = x, Z = z) = P(X, Z, Y) / P(X, Z)`. -/
noncomputable def pY_given_XZ (y : ΩY) (x : ΩX) (z : ΩZ) : ENNReal :=
  M.pXZY x z y / M.pXZ x z

/-- Unfolding-lemma for `pU_given_X` (definisjonelt). -/
theorem pU_given_X_eq (u : ΩU) (x : ΩX) :
    M.pU_given_X u x = (M.pU u * (M.pX_given_U u) x) / M.pX x := rfl

/-- Unfolding-lemma for `pY_given_XZ` (definisjonelt). -/
theorem pY_given_XZ_eq (y : ΩY) (x : ΩX) (z : ΩZ) :
    M.pY_given_XZ y x z = M.pXZY x z y / M.pXZ x z := rfl

/-- Enhver PMF-verdi er endelig, saa `P(Z | X) ≠ ⊤`. -/
theorem pZ_given_X_ne_top (x : ΩX) (z : ΩZ) : (M.pZ_given_X x) z ≠ ⊤ :=
  PMF.apply_ne_top _ _

/--
**Strukturlemma: `P(X, Z) = P(X) * P(Z | X)`.**

Faktoren `P(Z | X)` er konstant i `U`-summen og trekkes ut via `Finset.sum_mul`.
Gjelder ubetinget (ogsaa naar `P(X) = 0`) — en ren algebraisk identitet.
-/
theorem pXZ_eq_pX_mul_pZ_given_X (x : ΩX) (z : ΩZ) :
    M.pXZ x z = M.pX x * (M.pZ_given_X x) z := by
  unfold pXZ pX
  rw [Finset.sum_mul]

/--
**Front-door capstone: betinget uavhengighet via marginalisering over `U`.**

  `Σ_u P(U=u | X=x') * P(Y=y | Z=z, U=u) = P(Y=y | X=x', Z=z)`

Dette er det betingede-uavhengighets-steget som lar oss eliminere referansen
til den uobserverte `U` i front-door-formelen. Eneste hypotese:
`P(Z=z | X=x') ≠ 0`.

Bevisstrategi:
1. `hLHS`: venstresiden er `(Σ_u P(U,X)*P(Y|Z,U)) / P(X)` — trekk divisjonen
   ut av summen via `div_eq_mul_inv` + `Finset.sum_mul`.
2. `hNum`: telleren `P(X,Z,Y)` faktoriserer som `(Σ_u ...) * P(Z|X)`.
3. `pXZ_eq_pX_mul_pZ_given_X` gir nevneren som `P(X) * P(Z|X)`.
4. `h_cancel`: kanseller `P(Z|X)` i teller og nevner.
-/
theorem sum_pU_given_X_times_pY (x' : ΩX) (z : ΩZ) (y : ΩY)
    (h_pZ_ne : (M.pZ_given_X x') z ≠ 0) :
    ∑ u, M.pU_given_X u x' * (M.pY_given_ZU z u) y = M.pY_given_XZ y x' z := by
  have h_pZ_top : (M.pZ_given_X x') z ≠ ⊤ := PMF.apply_ne_top _ _
  -- (1) Venstresiden: trekk 1 / P(X) ut av summen.
  have hLHS : (∑ u, M.pU_given_X u x' * (M.pY_given_ZU z u) y)
      = (∑ u, M.pU u * (M.pX_given_U u) x' * (M.pY_given_ZU z u) y) / M.pX x' := by
    rw [div_eq_mul_inv, Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    unfold pU_given_X
    rw [div_eq_mul_inv, mul_right_comm]
  -- (2) Telleren P(X,Z,Y) faktoriserer ut P(Z|X).
  have hNum : M.pXZY x' z y
      = (∑ u, M.pU u * (M.pX_given_U u) x' * (M.pY_given_ZU z u) y)
          * (M.pZ_given_X x') z := by
    unfold pXZY
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    ring
  -- (3) Kanselleringssteget, isolert. Eneste bruk av ENNReal-divisjonslemma.
  have h_cancel : ∀ A : ENNReal,
      A * (M.pZ_given_X x') z / (M.pX x' * (M.pZ_given_X x') z) = A / M.pX x' := by
    intro A
    exact ENNReal.mul_div_mul_right A (M.pX x') h_pZ_ne h_pZ_top
  -- Sett sammen.
  rw [hLHS, pY_given_XZ_eq, hNum, pXZ_eq_pX_mul_pZ_given_X, h_cancel]
/--
**Front-door-justering, fullt observerbar form.**

Under DAG-en `U → X`, `U → Y`, `X → Z`, `Z → Y`, og positivitetsantakelsen
`∀ x' z, P(Z=z | X=x') ≠ 0`:

  `P(Y=y | do(X=x*)) = Σ_z P(Z=z|X=x*) · Σ_x' P(X=x') · P(Y=y|X=x',Z=z)`.

Dette er selve front-door-formelen (Pearl 1995) i sin fullt estimerbare form
— ingen referanse til den uobserverte `U` gjenstår. Beviset kobler
`frontdoor_structural` (strukturell form med U), `frontdoor_X_cancellation`
(algebraisk kansellering av U-summen via x'-summering), og
`sum_pU_given_X_times_pY` (capstone: U-summen blir en observerbar betinget).
-/
theorem frontdoor_adjustment_observable [Fintype ΩU] [Fintype ΩX] [Fintype ΩZ]
    (M : FrontDoorModel ΩU ΩX ΩZ ΩY) (x_star : ΩX) (y : ΩY)
    (hpos : ∀ x' z, (M.pZ_given_X x') z ≠ 0) :
    (M.doX x_star) y =
      ∑ z, (M.pZ_given_X x_star) z * ∑ x', M.pX x' * M.pY_given_XZ y x' z := by
  rw [M.frontdoor_structural x_star y]
  refine Finset.sum_congr rfl fun z _ => ?_
  congr 1
  rw [← M.frontdoor_X_cancellation z y]
  refine Finset.sum_congr rfl fun x' _ => ?_
  have hxtop : M.pX x' ≠ ⊤ := by
    have hbind : M.pX x' = (M.pU.bind M.pX_given_U) x' := by
      unfold FrontDoorModel.pX
      rw [PMF.bind_apply, tsum_fintype]
    rw [hbind]
    exact PMF.apply_ne_top _ _
  by_cases hx : M.pX x' = 0
  · have hz : ∀ u, M.pU u * (M.pX_given_U u) x' = 0 := by
      have hsum0 : ∑ u, M.pU u * (M.pX_given_U u) x' = 0 := hx
      exact fun u => (Finset.sum_eq_zero_iff.mp hsum0) u (Finset.mem_univ u)
    simp only [hz, zero_mul, Finset.sum_const_zero]
    rw [hx, zero_mul]
  · have hSumDiv : (∑ u, M.pU_given_X u x' * (M.pY_given_ZU z u) y)
        = (∑ u, M.pU u * (M.pX_given_U u) x' * (M.pY_given_ZU z u) y) / M.pX x' := by
      rw [div_eq_mul_inv, Finset.sum_mul]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [M.pU_given_X_eq, div_eq_mul_inv, mul_right_comm]
    have hEq := M.sum_pU_given_X_times_pY x' z y (hpos x' z)
    rw [hSumDiv] at hEq
    have hcancel : (∑ u, M.pU u * (M.pX_given_U u) x' * (M.pY_given_ZU z u) y)
          / M.pX x' * M.pX x'
        = ∑ u, M.pU u * (M.pX_given_U u) x' * (M.pY_given_ZU z u) y :=
      ENNReal.div_mul_cancel hx hxtop
    rw [hEq] at hcancel
    rw [mul_comm] at hcancel
    exact hcancel.symm

end FrontDoorModel

end PearlDoCalculus
