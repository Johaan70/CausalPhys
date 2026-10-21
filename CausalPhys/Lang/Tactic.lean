/-
  CausalPhys.Lang.Tactic — automation for the language (phase 3).

    `law_solve`        proves that a solving formula really solves its law on the
                       domain (the algebra a student would do by hand: multiply
                       out, move terms over). Positivity conditions from the
                       domain are made available to `field_simp`.
    `read_solution h`  for `h : S.scm.Solves u s` or `h : (S.scm.doI x c).Solves u s`
                       adds one hypothesis per variable, `h_x : s x = …`, giving
                       the value the causal model assigns to it. The causal
                       order is computed by the kernel, the formulas are then
                       unfolded by `simp`.
    `#causal_order S`  prints which law determines which variable, what it
                       reads, the blocks, and whether the setup is acyclic.
-/
import CausalPhys.Lang.Core
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.CasesM

namespace CausalPhys.Lang

open Lean Meta Elab Tactic Command

/-! ## Proving that a formula solves its law -/

/-- Proves `∀ s, dom s → (law s ↔ s v = formula s)` for the usual algebraic
    rearrangements: definitional, linear, or after clearing denominators that
    the domain makes nonzero. -/
macro "law_solve" : tactic => `(tactic| (
  intro s hD
  try simp only [CausalPhys.Lang.mech] at hD ⊢
  all_goals try casesm* _ ∧ _
  all_goals first
  | exact Iff.rfl
  | exact eq_comm
  | (constructor <;> intro h <;> (try field_simp at h) <;> (try field_simp) <;>
      first
      | linear_combination h
      | linear_combination -h
      | linarith
      | nlinarith [h])
  | fail "law_solve: could not show that this formula solves the law on the domain. \
      Check the formula, add what is needed to the domain, or give a proof after `by`."))

/-! ## Evaluation by the kernel -/

/-- Weak head normal form computed by the kernel (fast for the matching algorithm). -/
def kernelWhnf (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  match Kernel.whnf (← getEnv) (← getLCtx) e with
  | .ok r => pure r
  | .error _ => throwError "kernel could not evaluate {e}"

/-- Normal form of a value built from constructors (lists, options, enumerations). -/
partial def kernelNorm (e : Expr) : MetaM Expr := do
  let r ← kernelWhnf e
  let fn := r.getAppFn
  match fn.constName? with
  | some n =>
    if (← getEnv).isConstructor n then
      let args ← r.getAppArgs.mapM fun a => do
        if (← isType a) || (← isProof a) then pure a else kernelNorm a
      pure (mkAppN fn args)
    else pure r
  | none => pure r

/-- A proof of the decidable proposition `p`, checked by the kernel only. -/
def kernelDecideProof (p : Expr) : MetaM Expr := do
  let inst ← synthInstance (mkApp (mkConst ``Decidable) p)
  let rflTrue := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
  pure (mkApp3 (mkConst ``of_decide_eq_true) p inst rflTrue)

/-- The constructors of an enumeration type. -/
def ctorsOf (V : Expr) : MetaM (List Name) := do
  let some n := V.getAppFn.constName? | throwError "not an inductive type: {V}"
  let info ← getConstInfoInduct n
  pure info.ctors

/-! ## Reading off a solution -/

/-- `read_solution h` adds `h_x : s x = …` for every variable `x`. -/
elab "read_solution " h:ident : tactic => withMainContext do
  let hdecl ← getLocalDeclFromUserName h.getId
  let ty ← instantiateMVars hdecl.type
  let (``CausalPhys.SCM.Solves, #[V, _, model, _, _]) := ty.getAppFnArgs
    | throwError "read_solution: expected a hypothesis `… .Solves u s`"
  -- `model` is `S.scm` or `(S.scm).doI x c`
  let (S, isDo) ← match model.getAppFnArgs with
    | (``CausalPhys.Lang.Setup.scm, args) => pure (args[7]!, false)
    | (``CausalPhys.SCM.doI, args) =>
      match args[3]!.getAppFnArgs with
      | (``CausalPhys.Lang.Setup.scm, args') => pure (args'[7]!, true)
      | _ => throwError "read_solution: unsupported model {model}"
    | _ => throwError "read_solution: unsupported model {model}"
  let SType ← inferType S
  let M := SType.getAppArgs.back!
  let some modelName := M.getAppFn.constName?
    | throwError "read_solution: the model must be a named definition"
  let modelId := mkCIdent modelName
  let u := ty.getAppArgs[3]!
  let s := ty.getAppArgs[4]!
  let hTerm := mkFVar hdecl.fvarId
  for ctor in ← ctorsOf V do
    let v := mkConst ctor
    let base ← mkAppM (if isDo then ``Setup.do_value_eq else ``Setup.value_eq) #[S, hTerm, v]
    let inv ← mkAppM ``Order.Cert.inv #[← mkAppM ``Setup.cert #[S], v]
    let val ← kernelNorm inv
    let hi ← kernelDecideProof (← mkEq inv val)
    let rhsEq ← if val.isAppOfArity ``Option.none 1 then
        mkAppOptM ``Setup.rhs_none #[none, none, none, none, none, none, none, S,
          u, s, v, hi]
      else
        mkAppOptM ``Setup.rhs_some #[none, none, none, none, none, none, none, S,
          u, s, v, none, hi]
    let name := h.getId.appendAfter ("_" ++ ctor.getString!)
    let g ← getMainGoal
    let (_, g) ← (← g.assert `rhs_aux (← inferType rhsEq) rhsEq).intro1P
    let (_, g) ← (← g.assert name (← inferType base) base).intro1P
    replaceMainGoal [g]
    withMainContext do
      let nm := mkIdent name
      let ra := mkIdent `rhs_aux
      evalTactic (← `(tactic| rw [$ra:ident] at $nm:ident))
      evalTactic (← `(tactic| clear $ra:ident))
      evalTactic (← `(tactic|
        try simp only [Model.mechOf, Model.find, Model.ofSolvers, CausalPhys.Lang.mech,
          $modelId:ident, List.map_cons, List.map_nil, List.find?_cons, List.find?_nil,
          Option.map_some, Option.getD_some, Function.update_apply,
          reduceCtorEq, decide_true, decide_false, ↓reduceIte] at $nm:ident))

/-! ## Printing the causal order -/

/-- Short display of a constructor value or a list of them. -/
partial def shortName (e : Expr) : String :=
  match e.listLit? with
  | some (_, xs) => "[" ++ ", ".intercalate (xs.map shortName) ++ "]"
  | none =>
    match e.getAppFn.constName? with
    | some n => n.getString!
    | none => toString e

/-- `#causal_order S` prints the causal order a setup gets. -/
elab "#causal_order " t:term : command => runTermElabM fun _ => do
  let S ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  let S ← instantiateMVars S
  let SType ← whnfR (← inferType S)
  let #[E, V, _, _, _, _, M] := SType.getAppArgs
    | throwError "#causal_order: expected a setup"
  let _ := V
  let mut lines : Array MessageData := #[]
  for ctor in ← ctorsOf E do
    let e := mkConst ctor
    let v ← kernelNorm (← mkAppM ``Setup.determines #[S, e])
    let deps ← kernelNorm (← mkAppM ``Model.deps #[M, e, v])
    lines := lines.push m!"{shortName e} determines {shortName v}, reading {shortName deps}"
  let acyclic ← kernelNorm (← mkDecide (← mkAppM ``Setup.Acyclic #[S]))
  if acyclic.isAppOf ``Bool.true then
    lines := lines.push m!"acyclic: every intervention has exactly one outcome"
  else
    let mut seen : Array Expr := #[]
    for ctor in ← ctorsOf E do
      let e := mkConst ctor
      if seen.any (·.isConstOf ctor) then continue
      let b ← kernelNorm (← mkAppM ``Setup.block #[S, e])
      let elems := (b.listLit?.map (·.2)).getD []
      seen := seen ++ elems.toArray
      if elems.length > 1 then
        lines := lines.push m!"cyclic block: {shortName b}"
  logInfo (MessageData.joinSep lines.toList "\n")

end CausalPhys.Lang
