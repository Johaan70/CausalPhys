/-
  CausalPhys.Lang.Eval — numbers: `#causal_eval`.

      #causal_eval Gas.locked with vol := 1/40, n := 1, T := 300 using R

  computes the outcome of the lab setup for the given values of the variables
  the lab holds fixed, exactly (as rational numbers), and proves it:

    * the state lies in the domain and satisfies every law,
    * it is a solution of the causal model of the setup with these fixed values,
    * and the only one.

  How the numbers are found does not need to be trusted: the blocks are solved
  in causal order, a block of one law by evaluating its formula, a cyclic block
  by probing its formulas (affine in the block's own variables) and solving the
  linear system over ℚ. The proof then checks the numbers against the laws with
  `norm_num`, and uniqueness comes from `Setup.unique` (acyclic setups) or from
  `block_linear` (linear blocks, with the determinant evaluated at the given
  values).

  `using R, …` names constants to unfold (such as the gas constant). Values that
  are not rational (an exponential, a square root) or a block that is not
  linear are reported, not computed.
-/
import CausalPhys.Lang.Tactic
import Mathlib.Tactic.NormNum

namespace CausalPhys.Lang

open Lean Meta Elab Command Tactic Qq

/-- Names of the definitions to unfold in a model or setup expression (as in
    `unfoldLemmas`). -/
def unfoldNames (es : Array Expr) : MetaM (Array Name) := do
  let mut names : Array Name := #[]
  for e in es do
    for n in e.getUsedConstants do
      if names.contains n then continue
      let ci ← getConstInfo n
      let ok ← forallTelescopeReducing ci.type fun _ b =>
        pure (b.isAppOf ``Model || b.isAppOf ``Setup)
      if ok then names := names.push n
  return names

/-- Evaluate a real expression to a rational number with `simp` (unfolding
    `names`) and `norm_num`; `none` if it does not become a rational literal. -/
def evalRat (names : Array Name) (e : Expr) : MetaM (Option Rat) := do
  let mut thms ← getSimpTheorems
  for n in names ++ #[``Model.mechOf, ``Model.find, ``Model.ofSolvers, ``mech] do
    thms ← thms.addDeclToUnfold n
  let ctx ← Simp.mkContext {} #[thms] (← getSimpCongrTheorems)
  let e' ← try pure (← Mathlib.Meta.NormNum.deriveSimp ctx #[← Simp.getSimprocs] true e).expr
    catch _ => pure e
  try
    let r ← Mathlib.Meta.NormNum.derive (u := Level.zero) (α := q(ℝ)) e'
    return r.toRat
  catch _ => return none

/-- The real number `q` as an expression. -/
def ratExpr (q : Rat) : TermElabM Expr := do
  let n := Syntax.mkNumLit (toString q.num.natAbs)
  let d := Syntax.mkNumLit (toString q.den)
  let stx ← if q.den == 1 then `(($n : ℝ)) else `((($n : ℝ) / $d))
  let stx ← if q.num < 0 then `(-$stx) else pure stx
  Term.elabTerm stx (some (mkConst ``Real))

/-- A state: `Function.update` of the zero state at the given variables. -/
def stateExpr (V : Expr) (vals : Array (Expr × Expr)) : MetaM Expr := do
  let zero ← mkAppOptM ``OfNat.ofNat #[mkConst ``Real, mkRawNatLit 0, none]
  let mut f ← withLocalDeclD `v V fun v => mkLambdaFVars #[v] zero
  for (v, q) in vals do
    f ← mkAppM ``Function.update #[f, v, q]
  return f

/-- Display of a rational number. -/
def ratStr (q : Rat) : String :=
  if q.den == 1 then toString q.num else s!"{q.num}/{q.den}"

/-- Solve `A x = b` over ℚ by Gaussian elimination; `none` if singular. -/
def solveRat (A : Array (Array Rat)) (b : Array Rat) : Option (Array Rat) := Id.run do
  let n := b.size
  let at2 (M : Array (Array Rat)) (i j : Nat) : Rat := (M.getD i #[]).getD j 0
  let mut M : Array (Array Rat) := (List.range n).toArray.map fun i => (A.getD i #[]).push (b.getD i 0)
  for c in [0:n] do
    let some p := (List.range n).find? (fun r => r ≥ c && at2 M r c != 0) | return none
    let rc := M.getD c #[]
    let rp := M.getD p #[]
    M := (M.set! c rp).set! p rc
    let piv := at2 M c c
    M := M.set! c ((M.getD c #[]).map (· / piv))
    for r in [0:n] do
      if r != c then
        let f := at2 M r c
        if f != 0 then
          M := M.set! r ((List.range (n + 1)).toArray.map fun k => at2 M r k - f * at2 M c k)
  return some ((List.range n).toArray.map fun i => at2 M i n)

syntax evalItem := ident " := " term
syntax (name := causalEval) "#causal_eval " term " with " evalItem,+
  (" using " ident,+)? : command

@[command_elab causalEval] def elabCausalEval : CommandElab := fun stx => runTermElabM fun _ => do
  let S ← Term.elabTerm stx[1] none
  Term.synthesizeSyntheticMVarsNoPostponing
  let S ← nameSetup (← instantiateMVars S)
  let SType ← whnfR (← inferType S)
  let V := SType.getAppArgs[1]!
  let M := SType.getAppArgs.back!
  let usingNames : Array Name ← if stx[4].getNumArgs > 0 then
      stx[4][1].getSepArgs.mapM fun i => realizeGlobalConstNoOverloadWithInfo i
    else pure #[]
  let names := (← unfoldNames #[M, S]) ++ usingNames
  let ctors ← ctorsOf V
  -- the fixed values
  let exo ← kernelNorm (← mkAppM ``Setup.exo #[S])
  let some (_, exoVars) := exo.listLit? | throwError "#causal_eval: could not list the fixed variables"
  let exoNames := exoVars.map fun e => e.constName!
  let mut vals : Array (Name × Rat) := #[]
  for it in stx[3].getSepArgs do
    let x := it[0].getId
    let some c := ctors.find? (·.getString! == x.toString)
      | throwErrorAt it[0] "#causal_eval: {x} is not a variable of the model"
    unless exoNames.contains c do
      throwErrorAt it[0] "#causal_eval: the lab does not hold {x} fixed in this setup; \
        only the fixed variables get values ({", ".intercalate (exoNames.map (·.getString!))})"
    let e ← Term.elabTermEnsuringType it[2] (some (mkConst ``Real))
    Term.synthesizeSyntheticMVarsNoPostponing
    let some q ← evalRat usingNames (← instantiateMVars e)
      | throwErrorAt it[2] "#causal_eval: {x} must be a rational number"
    vals := vals.push (c, q)
  for c in exoNames do
    unless vals.any (·.1 == c) do
      throwError "#causal_eval: give a value for {c.getString!}, which the lab holds fixed"
  -- solve block by block, in causal order
  let laws ← listOf' (← mkAppM ``Model.eqList #[M])
  let cert ← mkAppM ``Model.order #[M, exo]
  let st ← mkAppM ``Model.struct #[M, exo]
  let mut rows : Array (Expr × Name × List Name × List Expr) := #[]
  for e in laws do
    let v ← kernelNorm (← mkAppM ``Order.Cert.σ #[cert, e])
    let deps ← listOf' (← mkAppM ``Model.deps #[M, e, v])
    let blk ← listOf' (← mkAppM ``Order.blockOf #[st, e])
    rows := rows.push (e, v.constName!, deps.map (·.constName!), blk)
  let mut known := vals
  let mut done : Array Name := #[]
  let mut cyclic := false
  -- blocks in causal order: a block is next when everything it reads from
  -- outside itself is known
  while done.size < rows.size do
    let next? := rows.find? fun (_, v, _, blk) =>
      !done.contains v &&
      (rows.filter fun r => blk.any (· == r.1)).all fun (_, _, deps, _) =>
        deps.all fun d => known.any (·.1 == d) ||
          (rows.any fun r => blk.any (· == r.1) && r.2.1 == d)
    let some (_, _, _, blk) := next? | throwError "#causal_eval: could not order the blocks"
    let members := rows.filter fun r => blk.any (· == r.1)
    if members.size > 1 then cyclic := true
    -- f_i at the current state with the block's variables at `z`
    let evalAt (z : Array Rat) (i : Nat) : TermElabM Rat := do
      let mut st := known
      for j in [0:members.size] do
        st := st.push (members[j]!.2.1, z[j]!)
      let w ← stateExpr V (← st.mapM fun (c, q) => do pure (mkConst c, ← ratExpr q))
      let (ei, vi, _, _) := members[i]!
      let f ← mkAppM ``Mech.f #[← mkAppM ``Model.mechOf #[M, ei, mkConst vi]]
      let some q ← evalRat names (mkApp f w)
        | throwError "#causal_eval: the formula of {shortName ei} for {vi.getString!} does not \
            give a rational number here (a function such as exp or sqrt, or a constant to \
            unfold: add it after `using`)"
      return q
    let k := members.size
    let zero := Array.replicate k (0 : Rat)
    if k == 1 then
      known := known.push (members[0]!.2.1, ← evalAt zero 0)
    else
      let mut A : Array (Array Rat) := #[]
      let mut b : Array Rat := #[]
      for i in [0:k] do
        let c ← evalAt zero i
        let mut row : Array Rat := #[]
        for j in [0:k] do
          let cij := (← evalAt (zero.set! j 1) i) - c
          row := row.push ((if i == j then 1 else 0) - cij)
        A := A.push row
        b := b.push c
      let some x := solveRat A b
        | throwError "#causal_eval: the linear block [{", ".intercalate (members.map (shortName ·.1)).toList}] is singular \
            at these values"
      -- the probing assumed the formulas are affine in the block; check it
      for i in [0:k] do
        if (← evalAt x i) != x[i]! then
          throwError "#causal_eval: the block [{", ".intercalate (members.map (shortName ·.1)).toList}] is not linear in \
            its own variables, so its values cannot be computed this way"
      for j in [0:k] do
        known := known.push (members[j]!.2.1, x[j]!)
    for m in members do done := done.push m.2.1
  -- the claim and its proof
  let u ← stateExpr V (← vals.mapM fun (c, q) => do pure (mkConst c, ← ratExpr q))
  let w ← stateExpr V (← known.mapM fun (c, q) => do pure (mkConst c, ← ratExpr q))
  let scm ← mkAppM ``Setup.scm #[S]
  let claim ← withLocalDeclD `s (← mkArrow V (mkConst ``Real)) fun s => do
    let body ← mkArrow (← mkAppM ``CausalPhys.SCM.Solves #[scm, u, s]) (← mkEq s w)
    let uniq ← mkForallFVars #[s] body
    mkAppM ``And #[← mkAppM ``Model.dom #[M, w], ← mkAppM ``And #[← mkAppM ``Model.Sat #[M, w],
      ← mkAppM ``And #[← mkAppM ``CausalPhys.SCM.Solves #[scm, u, w], uniq]]]
  let lemmas ← names.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkCIdent n):ident)
  let SStx ← Term.exprToSyntax S
  let MStx ← Term.exprToSyntax M
  let uStx ← Term.exprToSyntax u
  let wStx ← Term.exprToSyntax w
  let g ← mkFreshExprMVar claim
  let uniqTac ← if cyclic then
      `(tactic| exact (show ∃! s, ($SStx).scm.Solves $uStx s by
          block_linear <;> norm_num [Function.update_apply, $lemmas,*]).unique h hs)
    else
      `(tactic| exact Setup.unique $SStx (by struct_decide) h hs)
  let gs ← Term.withoutErrToSorry <| Tactic.run g.mvarId! do
    evalTactic (← `(tactic| (
      have hw : CausalPhys.Lang.Model.dom $MStx $wStx ∧ CausalPhys.Lang.Model.Sat $MStx $wStx := by
        refine ⟨?_, ?_⟩
        · simp only [$lemmas,*, CausalPhys.Lang.Model.ofSolvers, Function.update_apply,
            reduceCtorEq, ↓reduceIte]
          all_goals norm_num [$lemmas,*]
        · intro e
          cases e <;> simp only [$lemmas,*, CausalPhys.Lang.Model.ofSolvers,
            Function.update_apply, reduceCtorEq, ↓reduceIte] <;> (try norm_num [$lemmas,*])
      have hs : ($SStx).scm.Solves $uStx $wStx := by
        refine (Setup.solves_iff $SStx $uStx $wStx hw.1).2 ⟨hw.2, ?_⟩
        intro v hv
        revert hv
        cases v <;> (try simp [$lemmas,*, Function.update_apply])
      refine ⟨hw.1, hw.2, hs, fun s h => ?_⟩
      $uniqTac:tactic)))
  unless gs.isEmpty do throwError "#causal_eval: the proof left goals"
  let pf ← instantiateMVars g
  if pf.hasSorry then throwError "#causal_eval: the proof failed"
  -- report, in the order of the variables
  let mut lines : Array String := #[]
  for c in ctors do
    let some (_, q) := known.find? (·.1 == c) | continue
    let tag := if exoNames.contains c then "fixed" else "computed"
    lines := lines.push s!"{c.getString!} = {ratStr q}  ({tag})"
  lines := lines.push "proved: in the domain, satisfies every law, and is the only outcome of \
    the setup with these fixed values"
  logInfo (String.intercalate "\n" lines.toList)
where
  listOf' (e : Expr) : MetaM (List Expr) := do
    let some (_, xs) := (← kernelNorm e).listLit? | throwError "#causal_eval: not a list: {e}"
    pure xs

end CausalPhys.Lang
