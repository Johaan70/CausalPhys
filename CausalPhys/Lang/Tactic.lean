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
import CausalPhys.Lang.Blockwise
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

/-- Simp lemmas that unfold a model or setup expression: every constant in it
    whose type is a `Model …` or a `Setup …` (the user's model and setups, and
    `Model.replace` / `Setup.intervene` after an intervention). -/
def unfoldLemmas (es : Array Expr) : MetaM (Array (TSyntax `Lean.Parser.Tactic.simpLemma)) := do
  let mut names : Array Name := #[]
  for e in es do
    for n in e.getUsedConstants do
      if names.contains n then continue
      let ci ← getConstInfo n
      let ok ← forallTelescopeReducing ci.type fun _ b =>
        pure (b.isAppOf ``Model || b.isAppOf ``Setup)
      if ok then names := names.push n
  names.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkCIdent n):ident)

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
  let extra ← unfoldLemmas #[M, S]
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
        try simp only [Model.mechOf, Model.find, Model.ofSolvers, CausalPhys.Lang.mech, CausalPhys.SCM.Mech.const,
          $extra,*, List.map_cons, List.map_nil, List.find?_cons, List.find?_nil,
          Option.map_some, Option.getD_some, Function.update_apply,
          reduceCtorEq, decide_true, decide_false, ↓reduceIte] at $nm:ident))

/-! ## Printing the causal order -/

/-- Short display of a constructor value or a list of them. -/
partial def shortName (e : Expr) : String :=
  match e.listLit? with
  | some (_, xs) => "[" ++ ", ".intercalate (xs.map shortName) ++ "]"
  | none =>
    if e.isAppOfArity ``Subtype.mk 4 then shortName e.getAppArgs[2]! else
    match e.getAppFn.constName? with
    | some n => n.getString!
    | none => toString e

/-- `#causal_order S` prints the causal order a setup gets. -/
elab "#causal_order " t:term : command => runTermElabM fun _ => do
  let S ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  let S ← instantiateMVars S
  let SType ← whnfR (← inferType S)
  let #[_, _, _, _, _, _, M] := SType.getAppArgs
    | throwError "#causal_order: expected a setup"
  let eqs ← kernelNorm (← mkAppM ``Model.eqList #[M])
  let some (_, laws) := eqs.listLit? | throwError "#causal_order: could not list the laws"
  let mut lines : Array MessageData := #[]
  for e in laws do
    let v ← kernelNorm (← mkAppM ``Setup.determines #[S, e])
    let deps ← kernelNorm (← mkAppM ``Model.deps #[M, e, v])
    lines := lines.push m!"{shortName e} determines {shortName v}, reading {shortName deps}"
  let acyclic ← kernelNorm (← mkDecide (← mkAppM ``Setup.Acyclic #[S]))
  if acyclic.isAppOf ``Bool.true then
    lines := lines.push m!"acyclic: every intervention has exactly one outcome of the causal model"
  else
    let mut seen : Array String := #[]
    for e in laws do
      if seen.contains (shortName e) then continue
      let b ← kernelNorm (← mkAppM ``Setup.block #[S, e])
      let elems := (b.listLit?.map (·.2)).getD []
      seen := seen ++ (elems.map shortName).toArray
      if elems.length > 1 then
        lines := lines.push m!"cyclic block: {shortName b}"
  logInfo (MessageData.joinSep lines.toList "\n")

/-! ## The linear criterion, automatically -/

/-- Unfolding lemmas for the linear criterion. -/
macro "linear_unfold" : tactic => `(tactic|
  simp only [Setup.formula, Setup.const, Setup.coef, Setup.base, Setup.linMatrix,
    Model.mechOf, Model.find, Model.ofSolvers, CausalPhys.Lang.mech, CausalPhys.SCM.Mech.const,
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
  let extra ← unfoldLemmas #[M, S]
  let eqs ← kernelNorm (← mkAppM ``Model.eqList #[M])
  let some (_, laws) := eqs.listLit? | throwError "linear_block: could not list the laws"
  let mut vars : Array Expr := #[]
  for e in laws do
    vars := vars.push (← kernelNorm (← mkAppM ``Order.Cert.σ #[← mkAppM ``Setup.cert #[S], e]))
  let lawsStx ← laws.toArray.mapM fun e => Term.exprToSyntax e
  let varsStx ← vars.mapM fun e => Term.exprToSyntax e
  let SStx ← Term.exprToSyntax S
  let uStx ← Term.exprToSyntax u
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
      simp only [$extra,*]
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
    simp only [$extra,*]
    try linear_unfold
    try ring_nf
    try (first
      | positivity
      | (field_simp; positivity)
      | norm_num))))

/-! ## The linear criterion, block by block -/

/-- Unfolding lemmas for the blockwise criterion. -/
syntax "block_unfold" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| block_unfold $[$loc]?) => `(tactic|
  simp only [Setup.formula, Setup.bconst, Setup.bcoef, Setup.bbase, Setup.bmat, Setup.bvec,
    Model.mechOf, Model.find, Model.ofSolvers, CausalPhys.Lang.mech, CausalPhys.SCM.Mech.const,
    List.map_cons, List.map_nil, List.find?_cons, List.find?_nil,
    Option.map_some, Option.getD_some, Function.update_apply, List.mem_cons, List.not_mem_nil,
    reduceCtorEq, decide_true, decide_false, ↓reduceIte, or_false, or_true, false_or, true_or,
    and_true, true_and, and_false, false_and,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_succ, Matrix.cons_val, Fin.isValue,
    Fin.sum_univ_succ, Fin.sum_univ_zero, ne_eq, Fin.reduceEq, not_false_eq_true, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two] $[$loc]?)

/-- `block_linear` proves `∃! s, S.scm.Solves u s` with the blockwise linear
    criterion: Lean computes the blocks in causal order, proves that every
    formula is affine in the variables of its own block (coefficients may depend
    on lower blocks), and computes det(I − C) for every block. Determinant
    conditions it cannot discharge are left as goals, one per block. -/
elab "block_linear" : tactic => withMainContext do
  let goal ← instantiateMVars (← getMainTarget)
  let (``ExistsUnique, #[_, p]) := goal.getAppFnArgs
    | throwError "block_linear: expected a goal `∃! s, S.scm.Solves u s`"
  let (S, u) ← lambdaTelescope p fun _ body => do
    let (``CausalPhys.SCM.Solves, #[_, _, model, u, _]) := body.getAppFnArgs
      | throwError "block_linear: expected a goal `∃! s, S.scm.Solves u s`"
    let (``CausalPhys.Lang.Setup.scm, args) := model.getAppFnArgs
      | throwError "block_linear: expected a goal `∃! s, S.scm.Solves u s`"
    pure (args[7]!, u)
  let SType ← inferType S
  let M := SType.getAppArgs.back!
  let extra ← unfoldLemmas #[M, S]
  let eqs ← kernelNorm (← mkAppM ``Model.eqList #[M])
  let some (_, laws) := eqs.listLit? | throwError "block_linear: could not list the laws"
  let laws := laws.toArray
  let mut vars : Array Expr := #[]
  for e in laws do
    vars := vars.push (← kernelNorm (← mkAppM ``Order.Cert.σ #[← mkAppM ``Setup.cert #[S], e]))
  -- the rank of a law: how many laws lie strictly upstream of it (equal inside a block)
  let exo ← mkAppM ``Setup.exo #[S]
  let st ← mkAppM ``Model.struct #[M, exo]
  let mut ranks : Array Nat := #[]
  for e in laws do
    let r ← kernelNorm (← mkAppOptM ``Order.rankOf #[none, none, none, none, none, st, e])
    let some k := r.rawNatLit? <|> (do let n ← r.nat?; pure n)
      | throwError "block_linear: could not compute the rank of {e}"
    ranks := ranks.push k
  let levels := (ranks.toList.eraseDups.toArray.qsort (· < ·))
  let m := levels.size
  let blkIdx : Array Nat := ranks.map fun r => levels.idxOf r
  let lawsStx ← laws.mapM fun e => Term.exprToSyntax e
  let varsStx ← vars.mapM fun e => Term.exprToSyntax e
  let mT := Syntax.mkNumLit (toString m)
  let blkStx : Array Term ← blkIdx.mapM fun k => `(($(Syntax.mkNumLit (toString k)) : Fin $mT))
  let mut bvStx : Array Term := #[]
  for b in [0:m] do
    let mut vs : Array Term := #[]
    for i in [0:laws.size] do
      if blkIdx[i]! == b then vs := vs.push varsStx[i]!
    bvStx := bvStx.push (← `([$vs,*]))
  let SStx ← Term.exprToSyntax S
  let uStx ← Term.exprToSyntax u
  evalTactic (← `(tactic|
    refine Setup.block_existsUnique (S := $SStx) (laws := ![$lawsStx,*]) (vars := ![$varsStx,*])
      (blk := ![$blkStx,*]) (bv := ![$bvStx,*]) (by kernel_decide) ?aff $uStx ?det))
  evalTactic (← `(tactic| case aff =>
    unfold Setup.BlockAffine
    simp only [Fin.forall_fin_succ, IsEmpty.forall_iff, and_true]
    repeat' apply And.intro
    all_goals
      intro s
      try block_unfold
      simp only [$extra,*]
      try block_unfold
      first
      | ring1
      | fail "block_linear: a formula is not affine in the variables of its own block; \
          the blockwise linear criterion does not apply (try a monotonicity or fixed \
          point argument via `unique_of_laws`)"))
  let hsI := mkIdent `hs
  let hlowI := mkIdent `hlow
  let sI := mkIdent `s
  let bI := mkIdent `b
  let nT := Syntax.mkNumLit (toString laws.size)
  evalTactic (← `(tactic| (intro $bI:ident; fin_cases $bI:ident)))
  let detGoals ← getGoals
  let mut rest : List MVarId := []
  for (g, b) in detGoals.zip (List.range m) do
    setGoals [g]
    evalTactic (← `(tactic| intro $sI:ident $hsI:ident $hlowI:ident))
    evalTactic (← `(tactic|
      try simp only [$extra,*, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, IsEmpty.forall_iff, implies_true, and_true] at $hsI:ident))
    -- laws of lower blocks of size one: their equations can be substituted
    let mut lowIds : Array Ident := #[]
    for k in [0:laws.size] do
      let bk := blkIdx[k]!
      if bk < b && (blkIdx.filter (· == bk)).size == 1 then
        let hk := mkIdent (Name.mkSimple s!"hlow_{k}")
        let kT := Syntax.mkNumLit (toString k)
        evalTactic (← `(tactic|
          have $hk:ident := $hlowI:ident ($kT : Fin $nT) (by decide)))
        evalTactic (← `(tactic| try block_unfold at $hk:ident))
        evalTactic (← `(tactic| try simp only [$extra,*] at $hk:ident))
        evalTactic (← `(tactic| try block_unfold at $hk:ident))
        lowIds := lowIds.push hk
    let lowLemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
      lowIds.mapM fun h => `(Lean.Parser.Tactic.simpLemma| $h:ident)
    -- reduce to the determinant of block b alone
    let mut idxs : Array Term := #[]
    for k in [0:laws.size] do
      if blkIdx[k]! == b then idxs := idxs.push (← `(($(Syntax.mkNumLit (toString k)) : Fin $nT)))
    evalTactic (← `(tactic|
      rw [Setup.det_bmat (idx := ![$idxs,*]) (by kernel_decide) (by kernel_decide) $sI:ident]))
    evalTactic (← `(tactic| (
      try simp only [Fin.isValue, Fin.mk_zero, Fin.zero_eta, Fin.mk_one]
      try (first
        | simp only [Matrix.det_fin_one, Matrix.det_fin_two, Matrix.det_fin_three]
        | simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, Matrix.one_apply])
      try simp only [Matrix.submatrix_apply]
      try simp (config := { decide := true }) only [Matrix.cons_val, Setup.bmat, ↓reduceIte,
        ite_true, ite_false, and_self, and_true, true_and, and_false, false_and]
      try block_unfold
      try simp only [$extra,*]
      try block_unfold)))
    if !lowLemmas.isEmpty then
      evalTactic (← `(tactic| try simp only [$lowLemmas,*]))
    evalTactic (← `(tactic| (
      try simp only [$hsI:ident]
      try simp (config := { decide := true }) only [Matrix.cons_val, ↓reduceIte, ite_true,
        ite_false, and_self, and_true, true_and, and_false, false_and, mul_one, one_mul,
        mul_zero, zero_mul, sub_zero, zero_sub, add_zero, zero_add]
      try ring_nf
      try (first
        | (norm_num; done)
        | positivity
        | (field_simp; positivity))
      try simp only [not_true_eq_false, ne_eq, not_false_eq_true])))
    rest := rest ++ (← getGoals)
  setGoals rest

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
    logInfo m!"acyclic: every intervention has exactly one outcome of the causal model \
      (Setup.do_existsUnique; it satisfies the laws when it lies in the domain)"
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
        evalTactic (← `(tactic| intro $(mkIdent `u):ident))
        evalTactic (← `(tactic| block_linear)))
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
      logInfo m!"cyclic, linear in each block, singular: det(I − C) = 0 for a block, so \
        the linear criterion fails (for an affine block this means no outcome or infinitely \
        many)"
    else
      logInfo m!"cyclic, linear in each block: exactly one outcome of the causal model \
        provided that\n  {m}\n(finish `block_linear` with a proof of this)"
  | some [] => logInfo m!"cyclic, linear in each block: exactly one outcome of the causal \
      model for every choice of the exogenous values (proved by block_linear)"
  | some rest => logInfo m!"cyclic, linear in each block: exactly one outcome of the causal \
      model provided that\n  \
      {MessageData.joinSep rest "\n  "}\n\
      (finish `block_linear` with a proof of this)"
  | none => logInfo m!"cyclic: the linear criterion does not apply (some formula is not \
      affine in the variables of its own block); uniqueness needs another argument \
      (monotonicity, Gale–Nikaido, Minty–Browder), plugged in with Setup.unique_of_laws"

/-! ## The domain: consistency and outcomes inside it -/

/-- Unfolding lemmas for the model in a goal `Model.dom M x` / `Model.Sat M x`. -/
def modelLemmasIn (e : Expr) : MetaM (Array (TSyntax `Lean.Parser.Tactic.simpLemma)) := do
  let some m := e.find? fun x => x.isAppOf ``Model.dom || x.isAppOf ``Model.Sat
    | throwError "expected a goal about `Model.dom` or `Model.Sat`"
  unfoldLemmas #[m.getAppArgs[3]!]

/-- Proves `M.dom w ∧ M.Sat w` for a concrete state `w` (the witness of a
    model): unfold, then the usual arithmetic closers. -/
elab "witness_check" : tactic => withMainContext do
  let extra ← modelLemmasIn (← instantiateMVars (← getMainTarget))
  evalTactic (← `(tactic| (
    refine ⟨?_, ?_⟩
    · try simp only [$extra,*, CausalPhys.Lang.Model.ofSolvers]
      all_goals try (repeat' constructor)
      all_goals first
        | positivity
        | (norm_num; done)
        | linarith
        | fail "witness: could not show that the witness lies in the domain"
    · unfold CausalPhys.Lang.Model.Sat
      intro e
      cases e <;> (try simp only [$extra,*, CausalPhys.Lang.Model.ofSolvers]) <;>
        first
        | rfl
        | (norm_num; done)
        | ring1
        | (field_simp; done)
        | (field_simp; ring1)
        | linarith
        | fail "witness: could not show that the witness satisfies this law")))

/-- Proves `∀ s, S.scm.Solves u s → M.dom s` for acyclic setups: read the
    solution off, substitute, and show each condition with `positivity` (using
    hypotheses about the exogenous values in the context). -/
elab "in_domain" : tactic => withMainContext do
  let goal ← instantiateMVars (← getMainTarget)
  let extra ← modelLemmasIn goal
  let sId := mkIdent `s
  let hsId := mkIdent `hs
  evalTactic (← `(tactic| intro $sId:ident $hsId:ident))
  evalTactic (← `(tactic| read_solution $hsId:ident))
  let names ← withMainContext do
    let lctx ← getLCtx
    pure <| lctx.foldl (init := #[]) fun acc d =>
      if d.userName.toString.startsWith "hs_" then acc.push (mkIdent d.userName) else acc
  let lemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
    names.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $n:ident)
  evalTactic (← `(tactic| (
    try simp only [$extra,*, CausalPhys.Lang.Model.ofSolvers]
    try simp only [$lemmas,*]
    all_goals try (repeat' constructor)
    all_goals first
      | positivity
      | fail "in_domain: could not show that the outcome lies in the domain")))

/-- Proves `∃! s, M.dom s ∧ M.Sat s ∧ (exogenous values)`: exactly one solution
    of the laws themselves inside the domain. Uses the structure (acyclic) or
    the linear criterion for the causal model, then `in_domain`. -/
macro "laws_unique" : tactic => `(tactic| (
  refine CausalPhys.Lang.Setup.laws_existsUnique _ ?_ ?_
  · first
    | exact CausalPhys.Lang.Setup.existsUnique _ (by struct_decide) _
    | linear_block
    | block_linear
  · in_domain))


end CausalPhys.Lang
