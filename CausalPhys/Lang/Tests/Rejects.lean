/-
  Test suite, negative tests: mistakes the language must reject, with the
  message it must give. Each error is pinned with `#guard_msgs`.

  Lean still adds the failed declarations (with `sorry`), so this file is not
  imported by `CausalPhys.lean`; CI checks it on its own.
-/
import CausalPhys.Lang.Syntax
import CausalPhys.Lang.Examples.Gas
import CausalPhys.Lang.Examples.Complexation

open CausalPhys CausalPhys.Lang

namespace CausalPhys.Tests.Rejects

/-! A formula that does not solve its law (Ohm's law solved wrongly). -/
/--
error: law_solve: could not show that this formula solves the law on the domain. Check the formula, add what is needed to the domain, or give a proof after `by`.
e✝ : Law
s✝ : V → ℝ
hD✝ : 0 < s✝ V.R
⊢ s✝ V.U = s✝ V.R * s✝ V.I ↔ s✝ V.I = s✝ V.R / s✝ V.U
---
warning: declaration uses `sorry`
-/
#guard_msgs in
causal_model WrongFormula where
  variables U R I
  domain 0 < R
  law ohm : U = R * I
    solve I := R / U
  witness R := 1
  setup s fixes U R

/-! A solver for a variable the model does not have. -/
/--
error: P is not a variable of the model
-/
#guard_msgs in
causal_model UnknownVariable where
  variables U R I
  law ohm : U = R * I
    solve P := R * I
  witness U := 0
  setup s fixes R I

/-! A formula for x that mentions x itself. -/
/--
error: the formula for x must not mention x
-/
#guard_msgs in
causal_model SelfReference where
  variables x y
  law l : x = 2 * y
    solve x := x / 2 + y
  witness x := 0
  setup s fixes y

/-! A setup that fixes too much: the law has nothing left to determine. -/
/--
error: could not synthesize default value for field 'valid' of 'CausalPhys.Lang.Setup' using tactics
---
error: this setup has no valid causal reading: the laws cannot be matched one-to-one with the variables that are not fixed (fix fewer or other variables)
⊢ Order.Valid (model.struct [V.U, V.R, V.I]) (model.order [V.U, V.R, V.I])
-/
#guard_msgs in
causal_model OverFixed where
  variables U R I
  law ohm : U = R * I
    solve U := R * I
  witness U := 0
  setup s fixes U R I

/-! A false claim about the causal order. -/
causal_model Ohm where
  variables U R I
  law ohm : U = R * I
    solve U := R * I
  witness U := 0
  setup voltage fixes R I

/--
error: kernel_decide: the statement is false (the kernel evaluates it to `false`)
-/
#guard_msgs in
theorem false_order : Ohm.voltage.determines .ohm = .I := by struct_decide

/-! Two laws that say the same thing: the linear criterion reports a singular
    block instead of claiming a unique outcome. -/
causal_model Singular where
  variables x y a
  law l1 : x = y + a
    solve x := y + a
  law l2 : y = x - a
    solve y := x - a
  witness x := 0
  setup s fixes a

/--
info: cyclic, linear in each block, singular: det(I − C) = 0 for a block, so the linear criterion fails (for an affine block this means no outcome or infinitely many)
-/
#guard_msgs in
#causal_check Singular.s

/-! A nonlinear cyclic block is not mistaken for a linear one. -/
causal_model Nonlinear where
  variables x y a
  law l1 : x = y * y + a
    solve x := y * y + a
  law l2 : y = x - a
    solve y := x - a
  witness x := 0
  setup s fixes a

/--
info: cyclic: neither criterion applies (the block is not linear, and no reading of its laws gives multi-affine residuals with a P-matrix secant on the domain); uniqueness needs a domain-specific argument (monotonicity, Gale–Nikaido, Minty–Browder), plugged in with Setup.unique_of_laws
-/
#guard_msgs in
#causal_check Nonlinear.s

/-! A domain that contradicts the law: no witness can exist, so the model is
    rejected (in phase 2 such a domain made the formula check empty). -/
/--
error: witness: could not show that the witness satisfies this law
case refine_2.l
⊢ 0 = 1
-/
#guard_msgs in
causal_model Contradictory where
  variables x a
  domain x = 0
  law l : x = 1
    solve x := 2
  witness x := 0
  setup s fixes a

/-! A model without a witness. -/
/--
error: causal_model: give a `witness`, a state that lies in the domain and satisfies every law, e.g. `witness x := 1, y := 2`; variables not listed are 0. This shows that the domain and the laws are consistent.
-/
#guard_msgs in
causal_model NoWitness where
  variables x a
  law l : x = a
    solve x := a
  setup s fixes a

/-! An intervention on a variable the lab already holds fixed leaves a law
    with nothing to determine: the intervened setup is rejected. -/
causal_model Supply where
  variables P Q t
  law supply : Q = 2 * P - t
    solve Q := 2 * P - t
    solve P := (Q + t) / 2
  law demand : Q = 10 - P
    solve Q := 10 - P
    solve P := 10 - Q
  witness P := 4, Q := 6, t := 2
  setup market fixes t

/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: this setup has no valid causal reading: the laws cannot be matched one-to-one with the variables that are not fixed (fix fewer or other variables)
⊢ Order.Valid ((Supply.model.remove Supply.Law.supply).struct (Supply.V.t :: Supply.market.exo))
    ((Supply.model.remove Supply.Law.supply).order (Supply.V.t :: Supply.market.exo))
-/
#guard_msgs in
noncomputable def badIntervention := Supply.market.intervene .supply .t

/-! Parameters must be explicit, and must not share a name with a variable. -/
/--
error: causal_model: parameters must be explicit binders `(name : Type)`
-/
#guard_msgs in
causal_model ImplicitParam {k : ℝ} where
  variables x y
  law l : x = k * y
    solve x := k * y
  witness x := 0
  setup s fixes y

/--
error: causal_model: the parameter x has the same name as a variable
-/
#guard_msgs in
causal_model ClashingParam (x : ℝ) where
  variables x y
  law l : y = 2 * x
    solve y := 2 * x
  witness y := 0
  setup s fixes x

/-! Units. The gas law without the gas constant: the two sides do not match. -/
/--
error: units: the two sides of this law have different units: kg·m²·s⁻² (J) vs K·mol
-/
#guard_msgs in
causal_model GasWithoutR where
  variables p vol n T
  units p : Pa, vol : m^3, n : mol, T : K
  law gas : p * vol = n * T
    solve p := n * T / vol
  witness T := 0
  setup locked fixes vol n T

/-! Units. A solving formula with the wrong unit. -/
/--
error: units: this formula for p has unit kg·m⁵·s⁻², but p has unit kg·m⁻¹·s⁻² (Pa)
-/
#guard_msgs in
causal_model GasWrongFormula where
  variables p vol n T
  units p : Pa, vol : m^3, n : mol, T : K, R : J/(mol*K)
  law gas : p * vol = n * R * T
    solve p := n * R * T * vol
  witness T := 0
  setup locked fixes vol n T

/-! Units. The exponent in the Arrhenius law must be dimensionless (here R is missing). -/
/--
error: units: the argument of Real.exp must be dimensionless, but it has unit kg·m²·s⁻²·K⁻¹·mol⁻¹
-/
#guard_msgs in
causal_model ArrheniusWithoutR where
  variables k A Ea T
  units k : 1/s, A : 1/s, Ea : J/mol, T : K
  law arrhenius : k = A * Real.exp (-(Ea / T))
    solve k := A * Real.exp (-(Ea / T))
  witness T := 1
  setup lab fixes A Ea T

/-! Units. A constant without a declared unit. -/
/--
error: units: no unit declared for R; add it to `units`
-/
#guard_msgs in
causal_model UndeclaredConstant where
  variables p vol n T
  units p : Pa, vol : m^3, n : mol, T : K
  law gas : p * vol = n * R * T
    solve p := n * R * T / vol
  witness T := 0
  setup locked fixes vol n T

/-! Units. A variable without a unit. -/
/--
error: units: no unit declared for the variable I
-/
#guard_msgs in
causal_model MissingUnit where
  variables U R I
  units U : V, R : ohm
  law ohm : U = R * I
    solve U := R * I
  witness U := 0
  setup s fixes R I

/-! A formula is derived only where the domain makes it valid. Without `0 < Vel`
    in the domain, MV = PY cannot be solved for M (that divides by V), so a
    setup that needs the law to determine M is rejected. -/
/--
error: could not synthesize default value for field 'valid' of 'CausalPhys.Lang.Setup' using tactics
---
error: this setup has no valid causal reading: the laws cannot be matched one-to-one with the variables that are not fixed (fix fewer or other variables)
⊢ Order.Valid (model.struct [V.Vel, V.P, V.Y]) (model.order [V.Vel, V.P, V.Y])
-/
#guard_msgs in
causal_model MoneyWithoutVelocity where
  variables M Vel P Y
  units M : NOK, Vel : 1/yr, P : NOK/item, Y : item/yr
  domain 0 < P ∧ 0 < Y
  law fisher : M * Vel = P * Y
  witness M := 1, Vel := 1, P := 1, Y := 1
  setup target fixes Vel P Y

/-! Numbers only for the variables the lab holds fixed: with a locked piston the
    pressure is an effect, not an input. -/
/--
error: #causal_eval: the lab does not hold p fixed in this setup; only the fixed variables get values (vol, n, T)
-/
#guard_msgs in
#causal_eval CausalPhys.Examples.Gas.locked with vol := 1/40, n := 1, p := 100000 using R

/-! A nonlinear block is reported, not computed: the closed flask's equilibrium
    is the root of a polynomial, not a rational number in general. -/
/--
error: #causal_eval: the block [k1, k2, metal, ligand] is not linear in its own variables, so its values cannot be computed this way
-/
#guard_msgs in
#causal_eval CausalPhys.Examples.Complexation.closed ⟨1000, 100, by norm_num, by norm_num⟩ with
  m0 := 1/1000, l0 := 1/500

end CausalPhys.Tests.Rejects
