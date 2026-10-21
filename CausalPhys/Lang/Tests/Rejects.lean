/-
  Test suite, negative tests: mistakes the language must reject, with the
  message it must give. Each error is pinned with `#guard_msgs`.

  Lean still adds the failed declarations (with `sorry`), so this file is not
  imported by `CausalPhys.lean`; CI checks it on its own.
-/
import CausalPhys.Lang.Syntax

open CausalPhys CausalPhys.Lang

namespace CausalPhys.Tests.Rejects

/-! A formula that does not solve its law (Ohm's law solved wrongly). -/
/--
error: law_solve: could not show that this formula solves the law on the domain. Check the formula, add what is needed to the domain, or give a proof after `by`.
e✝ : Law
s✝ : V → ℝ
hD✝ : 0 < s✝ V.R
⊢ s✝ V.U = s✝ V.R * s✝ V.I ↔ s✝ V.I = s✝ V.R / s✝ V.U
-/
#guard_msgs in
causal_model WrongFormula where
  variables U R I
  domain 0 < R
  law ohm : U = R * I
    solve I := R / U
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
  setup s fixes U R I

/-! A false claim about the causal order. -/
causal_model Ohm where
  variables U R I
  law ohm : U = R * I
    solve U := R * I
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
  setup s fixes a

/--
info: cyclic, linear, singular: det(I − C) = 0, so the linear criterion fails (for an affine block this means no outcome or infinitely many)
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
  setup s fixes a

/--
info: cyclic, nonlinear: the linear criterion does not apply; uniqueness needs a domain-specific argument (monotonicity, Gale–Nikaido, Minty–Browder), plugged in with Setup.unique_of_laws
-/
#guard_msgs in
#causal_check Nonlinear.s

end CausalPhys.Tests.Rejects
