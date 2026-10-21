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
import CausalPhys.Lang.Linear
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

/-! ## The linear criterion, automatically -/

/-- Unfolding lemmas for the linear criterion. -/
macro "linear_unfold" : tactic => `(tactic|
  simp only [Setup.formula, Setup.const, Setup.coef, Setup.base, Setup.linMatrix,
    Model.mechOf, Model.find, Model.ofSolvers, CausalPhys.Lang.mech,
    List.map_cons, List.map_nil, List.find?_cons, List.find?_nil,
    Option.map_some, Option.getD_some, Function.update_apply, List.mem_cons, List.not_mem_nil,
    reduceCtorEq, decide_true, decide_false, ↓reduceIte, or_false, or_true, false_or, true_or,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_succ, Fin.isValue, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.of_apply, Matrix.sub_apply, Matrix.one_apply_eq, Matrix.one_apply_ne,
    ne_eq, Fin.reduceEq, not_false_eq_true, Fin.succ_zero_eq_one, Fin.succ_one_eq_two])

/-- `linear_block` proves `∃! s, S.scm.Solves u s` with the linear criterion:
    it enumerates the computed matching, proves that every formula is affine,
    and computes det(I − C). If it cannot show det(I − C) ≠ 0 by itself, that
    goal is left, simplified, for the user (it is the domain-specific part). -/
elab "linear_block" : tactic => withMainContext do
  let goal ← instantiateMVars (← getMainTarget)
  let (``ExistsUnique, #[_, p]) := goal.getAppFnArgs
    | throwError "linear_block: expected a goal `∃! s, S.scm.Solves u s`"
  let (S, u) ← lambdaTelescope p fun _ body => do
    let (``CausalPhys.SCM.Solves, #[_, _, model, u, _]) := body.getAppFnArgs
      | throwError "linear_block: expected a goal `∃! s, S.scm.Solves u s`"
    let (``CausalPhys.Lang.Setup.scm, args) := model.getAppFnArgs
      | throwError "linear_block: expected a goal `∃! s, S.scm.Solves u s`"
    pure (args[7]!, u)
  let SType ← inferType S
  let M := SType.getAppArgs.back!
  let some modelName := M.getAppFn.constName?
    | throwError "linear_block: the model must be a named definition"
  let some setupName := S.getAppFn.constName?
    | throwError "linear_block: the setup must be a named definition"
  let eqs ← kernelNorm (← mkAppM ``Model.eqList #[M])
  let some (_, laws) := eqs.listLit? | throwError "linear_block: could not list the laws"
  let mut vars : Array Expr := #[]
  for e in laws do
    vars := vars.push (← kernelNorm (← mkAppM ``Order.Cert.σ #[← mkAppM ``Setup.cert #[S], e]))
  let lawsStx ← laws.toArray.mapM fun e => Term.exprToSyntax e
  let varsStx ← vars.mapM fun e => Term.exprToSyntax e
  let SStx ← Term.exprToSyntax S
  let uStx ← Term.exprToSyntax u
  let modelId := mkCIdent modelName
  let setupId := mkCIdent setupName
  evalTactic (← `(tactic|
    refine Setup.linear_existsUnique (S := $SStx) (laws := ![$lawsStx,*]) (vars := ![$varsStx,*])
      (by kernel_decide) ?aff $uStx ?det))
  -- affinity: unfold every formula and compare with `ring`
  evalTactic (← `(tactic| case aff =>
    unfold Setup.IsAffine
    simp only [Fin.forall_fin_succ, IsEmpty.forall_iff, and_true]
    repeat' apply And.intro
    all_goals
      intro s
      try linear_unfold
      simp only [$modelId:ident, $setupId:ident]
      try linear_unfold
      first
      | ring1
      | fail "linear_block: a formula of this setup is not affine in its endogenous \
          variables; the linear criterion does not apply (try a monotonicity or fixed \
          point argument via `unique_of_laws`)"))
  -- the determinant: compute it, then try the usual ways to see it is nonzero
  evalTactic (← `(tactic| (
    first
    | simp only [Matrix.det_fin_one, Matrix.det_fin_two, Matrix.det_fin_three]
    | simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, Matrix.one_apply]
    try linear_unfold
    simp only [$modelId:ident, $setupId:ident]
    try linear_unfold
    try ring_nf
    try (first
      | positivity
      | (field_simp; positivity)
      | norm_num))))

/-! ## Which criterion applies? -/

/-- `#causal_check S` says how the question "exactly one outcome?" is settled
    for a setup: by structure (acyclic), by the linear criterion (and what is
    left to show), or that a domain-specific argument is needed. -/
elab "#causal_check " t:term : command => runTermElabM fun _ => do
  let S ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  let S ← instantiateMVars S
  let acyclic ← kernelNorm (← mkDecide (← mkAppM ``Setup.Acyclic #[S]))
  if acyclic.isAppOf ``Bool.true then
    logInfo m!"acyclic: every intervention has exactly one outcome (Setup.do_existsUnique)"
    return
  let SType ← inferType S
  let V := SType.getAppArgs[1]!
  let realTy := SType.getAppArgs[2]!
  let uTy ← mkArrow V realTy
  let goalTy ← withLocalDeclD `u uTy fun u => do
    let body ← withLocalDeclD `s uTy fun s => do
      let scm ← mkAppM ``Setup.scm #[S]
      let sol ← mkAppM ``CausalPhys.SCM.Solves #[scm, u, s]
      mkLambdaFVars #[s] sol
    mkForallFVars #[u] (← mkAppM ``ExistsUnique #[body])
  let saved ← saveState
  let result ← try
      Core.resetMessageLog
      let g ← mkFreshExprMVar goalTy
      let gs ← Term.withoutErrToSorry <| Tactic.run g.mvarId! <| Tactic.withoutRecover (do
        evalTactic (← `(tactic| intro u))
        evalTactic (← `(tactic| linear_block)))
      if (← MonadLog.hasErrors) then
        throwError "failed"
      let pf ← instantiateMVars g
      if pf.hasSorry then throwError "failed"
      let singular ← gs.anyM fun g => do
        return (← instantiateMVars (← g.getType)).isConstOf ``False
      let rest ← gs.mapM fun g => g.withContext do
        return toMessageData (← ppExpr (← instantiateMVars (← g.getType)))
      pure (some (if singular then [m!"__singular__"] else rest))
    catch _ => pure none
  saved.restore
  match result with
  | some [m] =>
    if (← m.toString) == "__singular__" then
      logInfo m!"cyclic, linear, singular: det(I − C) = 0, so the linear criterion \
        fails (for an affine block this means no outcome or infinitely many)"
    else
      logInfo m!"cyclic, linear: exactly one outcome provided that\n  {m}\n\
        (finish `linear_block` with a proof of this)"
  | some [] => logInfo m!"cyclic, linear: exactly one outcome for every choice of the \
      exogenous values (proved by linear_block)"
  | some rest => logInfo m!"cyclic, linear: exactly one outcome provided that\n  \
      {MessageData.joinSep rest "\n  "}\n\
      (finish `linear_block` with a proof of this)"
  | none => logInfo m!"cyclic, nonlinear: the linear criterion does not apply; uniqueness \
      needs a domain-specific argument (monotonicity, Gale–Nikaido, Minty–Browder), \
      plugged in with Setup.unique_of_laws"

end CausalPhys.Lang
