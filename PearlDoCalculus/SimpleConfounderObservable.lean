/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import PearlDoCalculus.SimpleConfounder

/-!
# Pearls do-kalkyle: Back-door observerbar form (trinn 2)

Trinn 2 i back-door-stigen: erstatt kjernen `pY_given_XZ` med den *ekte*
observasjonelle betingede sannsynligheten `P(Y | X, Z)`, definert fra
fellesfordelingen ved divisjon, og bevis back-door-justeringen i den formen.

## Bakgrunn

`SimpleConfounderModel` har DAG-en `Z → X`, `Z → Y`, `X → Y`. Den observerbare
back-door-formelen er

  `P(Y = y | do(X = x*)) = Σ_z P(Y = y | X = x*, Z = z) · P(Z = z)`

der `P(Y | X, Z)` er en betinget sannsynlighet beregnet fra observasjonsdata,
ikke kjernen direkte. Det er denne formen som faktisk kan estimeres.

## Den observasjonelle betingede

Fellesfordelingen til den kausale modellen er, ved DAG-faktoriseringen,
`P(Z, X, Y) = P(Z) · P(X | Z) · P(Y | X, Z)` — dette er `jointMass`. Det er
*definisjonen* av et kausalt Bayes-netts fellesfordeling. Den observasjonelle
betingede er da forholdet `condY = P(Z,X,Y) / P(Z,X)`, presis definisjonen av
betinget sannsynlighet.

Den `bind`-konstruerte PMF-en `SimpleConfounderModel.joint` er en alternativ
representasjon av samme lov. Identiteten `joint (z,x,y) = jointMass z x y` er
et rutinemessig trippel-`tsum`-kollaps over de nestede `bind`/`map`-ene; den er
ikke tatt med her, og er det eneste gjenstaaende leddet for full
representasjons-ekvivalens.

## Positivitetsantakelsen

`backdoor_adjustment_observable` krever overlapp: `P(X = x* | Z = z) ≠ 0` for
alle `z`. Dette er den klassiske positivitets- og overlapp-antakelsen i kausal
inferens — uten den kan ikke `P(Y | do(X=x*))` estimeres, fordi `x*` aldri
opptrer sammen med enkelte `z`. Naar antakelsen brytes feiler formelen genuint;
den er ikke en teknisk bekvemmelighet.
-/

namespace PearlDoCalculus

open scoped BigOperators ENNReal

namespace SimpleConfounderModel

variable {Ωz Ωx Ωy : Type*} (M : SimpleConfounderModel Ωz Ωx Ωy)

/-- Fellesfordelingens punktmasse `P(Z=z, X=x, Y=y)`, ved DAG-faktoriseringen. -/
noncomputable def jointMass (z : Ωz) (x : Ωx) (y : Ωy) : ENNReal :=
  M.pZ z * (M.pX_given_Z z) x * (M.pY_given_XZ x z) y

/-- Marginal `P(Z=z, X=x)`, ved aa summere ut `Y`. -/
noncomputable def pZX [Fintype Ωy] (z : Ωz) (x : Ωx) : ENNReal :=
  ∑ y, M.jointMass z x y

/-- Observasjonell betinget `P(Y=y | X=x, Z=z) = P(Z,X,Y) / P(Z,X)`. -/
noncomputable def condY [Fintype Ωy] (y : Ωy) (x : Ωx) (z : Ωz) : ENNReal :=
  M.jointMass z x y / M.pZX z x

/--
**Marginaliseringslemma: `P(Z, X) = P(Z) · P(X | Z)`.**

Summer ut `Y`; faktorene som ikke avhenger av `y` trekkes ut, og `pY_given_XZ`
summerer til 1.
-/
theorem pZX_eq [Fintype Ωy] (z : Ωz) (x : Ωx) :
    M.pZX z x = M.pZ z * (M.pX_given_Z z) x := by
  unfold pZX jointMass
  rw [← Finset.mul_sum]
  have hsum : ∑ y, (M.pY_given_XZ x z) y = 1 := by
    simpa using (M.pY_given_XZ x z).tsum_coe
  rw [hsum, mul_one]

/--
**Den observasjonelle betingede er lik kjernen, under positivitet.**

Naar `P(Z=z, X=x) = P(Z=z)·P(X=x|Z=z) ≠ 0` er betinget veldefinert, og
`condY y x z = P(Y=y | X=x, Z=z)` faller sammen med kjernen `pY_given_XZ x z y`.
Beviset er kansellering: `(c · b) / c = b`.
-/
theorem condY_eq_kernel [Fintype Ωy] (y : Ωy) (x : Ωx) (z : Ωz)
    (hpos : M.pZ z * (M.pX_given_Z z) x ≠ 0) :
    M.condY y x z = (M.pY_given_XZ x z) y := by
  have hctop : M.pZ z * (M.pX_given_Z z) x ≠ ⊤ :=
    ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)
  unfold condY
  rw [M.pZX_eq z x]
  unfold jointMass
  rw [mul_comm (M.pZ z * (M.pX_given_Z z) x) ((M.pY_given_XZ x z) y),
      mul_div_assoc, ENNReal.div_self hpos hctop, mul_one]

/--
**Back-door-justering, observerbar form.**

For DAG-en `Z → X`, `Z → Y`, `X → Y`, under overlapp-antakelsen
`∀ z, P(X=x* | Z=z) ≠ 0`:

  `P(Y = y | do(X = x*)) = Σ_z P(Y=y | X=x*, Z=z) · P(Z=z)`

der `P(Y | X, Z)` er den observasjonelle betingede `condY`, beregnet fra
fellesfordelingen — ikke kjernen. Dette er formen som faktisk er estimerbar
fra observasjonsdata.

Beviset: start fra `backdoor_adjustment` (kjerneform), og bytt termvis
`pY_given_XZ` mot `condY` via `condY_eq_kernel`. Naar `P(Z=z) = 0` er begge
sider null; ellers gir overlapp at betinget er veldefinert.
-/
theorem backdoor_adjustment_observable [Fintype Ωy] [Fintype Ωz]
    (x_star : Ωx) (y : Ωy) (hpos : ∀ z, (M.pX_given_Z z) x_star ≠ 0) :
    (M.doX x_star) y = ∑ z, M.condY y x_star z * M.pZ z := by
  rw [M.backdoor_adjustment x_star y]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hz : M.pZ z = 0
  · simp [hz]
  · rw [M.condY_eq_kernel y x_star z (mul_ne_zero hz (hpos z))]

end SimpleConfounderModel

end PearlDoCalculus
