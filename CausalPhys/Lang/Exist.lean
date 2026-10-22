/-
  CausalPhys.Lang.Exist — existence of an outcome in a nonlinear cyclic block.

  The secant criterion (`secant_unique`) shows that a nonlinear block has at
  most one solution in the domain. `block_exists` shows that it has one:

      ∃ s, S.scm.Solves u s ∧ M.dom s

  The method, for each way of matching the laws to the endogenous variables
  (the setup's own matching first) and each small set of "core" variables that
  breaks every cycle:

    1. The other variables are computed from the core by their formulas, in
       causal order: given core values x, the state is st x.
    2. For each core variable xⱼ, Fⱼ(x) = xⱼ − (its formula at st x). A zero of
       F gives a state where every formula holds.
    3. The box is 0 ≤ xⱼ ≤ bⱼ, with bⱼ the formula's value when the whole core
       is 0 (for a mass balance: the total). Poincaré–Miranda
       (`poincare_miranda_strict`) gives a zero when Fⱼ < 0 on the face xⱼ = 0
       and Fⱼ ≥ 0 on the face xⱼ = bⱼ; the strict lower faces put the zero
       strictly inside, so the core values are positive.
    4. The state lies in the domain, every law holds (`Model.mechOf_sound`),
       and it agrees with the fixed values, so it solves the causal model
       (`Setup.solves_iff`).

  The inequalities are proved by `positivity_hyps` (positivity, using the
  hypotheses `0 < t`, `0 ≤ t` in the context), `nlinarith` or `field_simp` and
  `nlinarith`. Conditions on the fixed values (such as 0 < m₀) are taken from
  the context. A formula that divides by a core variable is not continuous on
  the box; such candidates are skipped.
-/
import CausalPhys.Lang.Eval
import CausalPhys.PoincareMiranda

namespace CausalPhys.Lang

open Lean Meta Elab Tactic

/-! ## Symbolic evaluation -/

/-- Simplify `e`, unfolding the model and setup definitions `names`. -/
def simpNorm (names : Array Name) (e : Expr) : MetaM Expr := do
  let mut thms ← getSimpTheorems
  for n in names ++ #[``Model.mechOf, ``Model.find, ``Model.ofSolvers, ``Model.restrict, ``mech] do
    thms ← thms.addDeclToUnfold n
  thms ← thms.addConst ``Function.update_apply
  thms ← thms.addConst ``List.filter_cons
  thms ← thms.addConst ``List.filter_nil
  let ctx ← Simp.mkContext {} #[thms] (← getSimpCongrTheorems)
  let (r, _) ← simp e ctx #[← Simp.getSimprocs]
  return r.expr

/-- Does `e` divide by something that mentions `x`? -/
def dividesBy (x : Expr) (e : Expr) : Bool :=
  (e.find? fun t =>
    (t.isAppOfArity ``HDiv.hDiv 6 && t.appArg!.containsFVar x.fvarId!) ||
    (t.isAppOfArity ``Inv.inv 3 && t.appArg!.containsFVar x.fvarId!)).isSome

/-- All perfect matchings of laws to endogenous variables, from the solvable
    lists, with `first` (if it is one) first. -/
partial def matchings (laws : Array Name) (cans : Array (List Name)) (endo : List Name)
    (first : Array Name) : Array (Array Name) := Id.run do
  let rec go (i : Nat) (used : List Name) (acc : Array Name) : Array (Array Name) :=
    if i == laws.size then #[acc] else
    (cans[i]!.filter fun v => endo.contains v && !used.contains v).foldl
      (fun out v => out ++ go (i + 1) (v :: used) (acc.push v)) #[]
  let all := go 0 [] #[]
  if all.contains first then
    return #[first] ++ all.filter (· != first)
  return all

/-- Subsets of `xs` with `k` elements. -/
def subsetsOf {α : Type} : List α → Nat → List (List α)
  | _, 0 => [[]]
  | [], _ + 1 => []
  | x :: xs, k + 1 => (subsetsOf xs k).map (x :: ·) ++ subsetsOf xs (k + 1)

/-- A causal order of the variables `rest`, each read only from `known` or
    earlier ones; `none` if there is a cycle. -/
partial def topo (deps : Name → List Name) (known : List Name) (rest : List Name) :
    Option (List Name) :=
  if rest.isEmpty then some [] else
  match rest.find? (fun v => (deps v).all fun d => known.contains d || !rest.contains d) with
  | none => none
  | some v => (topo deps (v :: known) (rest.erase v)).map (v :: ·)

/-! ## The tactic -/

def mkFinLit (k j : Nat) : MetaM Expr := do
  mkAppOptM ``OfNat.ofNat #[mkApp (mkConst ``Fin) (mkRawNatLit k), mkRawNatLit j, none]
def mkVec (α : Expr) (xs : Array Expr) : MetaM Expr := do
  let mut v ← mkAppOptM ``Matrix.vecEmpty #[α]
  for x in xs.reverse do
    v ← mkAppM ``Matrix.vecCons #[x, v]
  return v

/-- The conjuncts of a conjunction. -/
partial def conjuncts (e : Expr) : List Expr :=
  match e.app2? ``And with
  | some (a, b) => conjuncts a ++ conjuncts b
  | none => [e]

/-- `conj_prove t` proves a conjunction part by part with `t`, in rounds: a part
    proved in one round is a hypothesis in the next (a concentration that is a
    product of others is positive once they are). -/
elab "conj_prove " t:tactic : tactic => withMainContext do
  let goal ← instantiateMVars (← getMainTarget)
  let mut todo := conjuncts goal
  let mut round := 0
  while !todo.isEmpty && round < 4 do
    round := round + 1
    let mut left : List Expr := []
    for p in todo do
      let saved ← saveState
      let ok ← try
          let pStx ← Term.exprToSyntax p
          evalTactic (← `(tactic| have : $pStx := by $t:tactic))
          pure true
        catch _ => pure false
      unless ok do
        saved.restore
        left := left ++ [p]
    if left.length == todo.length then break
    todo := left
  evalTactic (← `(tactic| (repeat' constructor) <;> assumption))

def tryCandidate (M u : Expr) (names : Array Name)
    (lemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma))
    (SStx MStx uStx : Term) (realT : Expr) (core order : List Name)
    (lawOf : Name → Name) : TacticM (Option String) := do
  let k := core.length
  let finT := mkApp (mkConst ``Fin) (mkRawNatLit k)
  let xT ← mkArrow finT realT
  -- symbolic state and core formulas, over a variable x : Fin k → ℝ
  let built ← withLocalDeclD `x xT fun x => do
    let mut st := u
    let mut vals : Array (Name × Expr) := #[]
    for j in [0:k] do
      let xj := mkApp x (← mkFinLit k j)
      st ← mkAppM ``Function.update #[st, mkConst core[j]!, xj]
    for v in order do
      let f ← mkAppM ``Mech.f #[← mkAppM ``Model.mechOf #[M, mkConst (lawOf v), mkConst v]]
      let ev ← simpNorm names (mkApp f st)
      if dividesBy x ev then throwError "division"
      vals := vals.push (v, ev)
      st ← mkAppM ``Function.update #[st, mkConst v, ev]
    let mut gs : Array Expr := #[]
    for j in [0:k] do
      let f ← mkAppM ``Mech.f #[← mkAppM ``Model.mechOf #[M, mkConst (lawOf core[j]!),
        mkConst core[j]!]]
      let g ← simpNorm names (mkApp f st)
      if dividesBy x g then throwError "division"
      gs := gs.push g
    -- F x = (x j − g j)_j, and the box tops b j = g j at x = 0
    let mut comps : Array Expr := #[]
    for j in [0:k] do
      comps := comps.push (← mkAppM ``HSub.hSub #[mkApp x (← mkFinLit k j), gs[j]!])
    let F ← mkLambdaFVars #[x] (← mkVec realT comps)
    let zeroX ← withLocalDeclD `i finT fun i => do
      mkLambdaFVars #[i] (← mkAppOptM ``OfNat.ofNat #[realT, mkRawNatLit 0, none])
    let mut bs : Array Expr := #[]
    for j in [0:k] do
      bs := bs.push (← simpNorm names (gs[j]!.replaceFVar x zeroX))
    let b ← mkVec realT bs
    let stL ← mkLambdaFVars #[x] st
    return (F, b, stL)
  let (F, b, stL) := built
  let FStx ← Term.exprToSyntax F
  let bStx ← Term.exprToSyntax b
  let stStx ← Term.exprToSyntax stL
  -- facts about the box point, for each coordinate
  let idx : Array Term := (List.range k).toArray.map fun j => Syntax.mkNumLit (toString j)
  let closer ← `(tactic| first
    | positivity_hyps
    | (apply sub_pos.1; ring_nf; positivity_hyps)
    | (apply sub_nonneg.1; ring_nf; positivity_hyps)
    | nlinarith
    | (field_simp; nlinarith)
    | (field_simp at *; nlinarith)
    | (apply sub_pos.1; field_simp; nlinarith)
    | (apply sub_nonneg.1; field_simp; nlinarith))
  -- one case per law: the law holds because its variable equals its formula
  let lawsE := ((← kernelNorm (← mkAppM ``Model.eqList #[M])).listLit?.map (·.2)).getD []
  let mut cases : Array (TSyntax `tactic) := #[]
  for e in lawsE do
    let en := e.constName!
    let v := (core ++ order).find? (lawOf · == en) |>.getD en
    cases := cases.push (← `(tactic|
      case $(mkIdent (Name.mkSimple en.getString!)):ident =>
        refine (CausalPhys.Lang.Model.mechOf_sound (M := $MStx) (e := $(mkCIdent en))
          (v := $(mkCIdent v)) (by struct_decide) _ hD).2 ?_
        simp only [$lemmas,*, Model.mechOf, Model.find, Model.ofSolvers, Model.restrict,
            List.filter_cons, List.filter_nil, CausalPhys.Lang.mech,
          List.map_cons, List.map_nil, List.find?_cons, List.find?_nil, Option.map_some,
          Option.getD_some, Function.update_apply, reduceCtorEq, decide_true, decide_false,
          ↓reduceIte]
        all_goals first | rfl | ring1 | linarith | (field_simp; linarith) | (field_simp; ring1)))
  let saved ← saveState
  let g ← getMainGoal
  try
    let gs ← Term.withoutErrToSorry <| Tactic.run g (do
      evalTactic (← `(tactic| (
        obtain ⟨x, hx, hpos, hF⟩ := CausalPhys.poincare_miranda_strict (a := 0) (b := $bStx)
          (by intro i; fin_cases i <;> simp <;> $closer:tactic) $FStx
          (by apply Continuous.continuousOn; refine continuous_pi fun i => ?_
              fin_cases i <;> simp <;> fun_prop)
          (by
            intro y hy i hi
            $[have := hy.1 $idx]*
            simp only [Pi.zero_apply] at *
            fin_cases i <;> simp at hi <;> simp [hi] <;> $closer:tactic)
          (by
            intro y hy i hi
            $[have := hy.1 $idx]*
            simp only [Pi.zero_apply] at *
            fin_cases i <;> simp at hi <;> simp [hi] <;> $closer:tactic)
        $[have := congrFun hF $idx]*
        $[have := hpos $idx]*
        $[have := hx.2 $idx]*
        simp only [Pi.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
          Pi.sub_apply] at *
        have hD : CausalPhys.Lang.Model.dom $MStx ($stStx x) := by
          simp only [$lemmas,*, CausalPhys.Lang.Model.ofSolvers, Function.update_apply,
            reduceCtorEq, ↓reduceIte]
          conj_prove $closer:tactic
        have hSat : CausalPhys.Lang.Model.Sat $MStx ($stStx x) := by
          intro e
          cases e
          $[$cases]*
        refine ⟨$stStx x, (Setup.solves_iff $SStx $uStx ($stStx x) hD).2 ⟨hSat, ?_⟩, hD⟩
        intro v hv
        revert hv
        cases v <;> simp [$lemmas,*, Function.update_apply]))))
    if !gs.isEmpty || (← instantiateMVars (mkMVar g)).hasSorry then
      let left ← gs.mapM fun g => do (m!"{← g.getType}").toString
      let errs ← (← Core.getMessageLog).toList.filter (·.severity == .error) |>.mapM
        fun m => m.data.toString
      saved.restore
      return some s!"goals left {left}; errors {errs}"
    replaceMainGoal []
    return none
  catch ex =>
    let msg ← ex.toMessageData.toString
    saved.restore
    return some msg

/-- See the module documentation. -/
elab "block_exists" : tactic => withMainContext do
  addParamFacts
  withMainContext do
  let goal ← instantiateMVars (← getMainTarget)
  let some (_, body) := goal.consumeMData.app2? ``Exists
    | throwError "block_exists: expected `∃ s, S.scm.Solves u s ∧ M.dom s`"
  let some (sol, _) ← lambdaTelescope body fun xs b => do
      let some (l, r) := b.app2? ``And | return none
      return some (l.abstract xs, r.abstract xs)
    | throwError "block_exists: expected `∃ s, S.scm.Solves u s ∧ M.dom s`"
  let (``CausalPhys.SCM.Solves, #[_, _, scm, u, _]) := sol.getAppFnArgs
    | throwError "block_exists: expected `∃ s, S.scm.Solves u s ∧ M.dom s`"
  let S := scm.getAppArgs[7]!
  let SType ← whnfR (← inferType S)
  let V := SType.getAppArgs[1]!
  let M := SType.getAppArgs.back!
  let names ← unfoldNames #[M, S]
  let ctors ← ctorsOf V
  let exo := ((← kernelNorm (← mkAppM ``Setup.exo #[S])).listLit?.map (·.2)).getD []
  let exoN := exo.map (·.constName!)
  let endo := ctors.filter fun c => !exoN.contains c
  let lawsE := ((← kernelNorm (← mkAppM ``Model.eqList #[M])).listLit?.map (·.2)).getD []
  unless lawsE.all (·.isConst) do
    throwError "block_exists: the laws are not named constructors (a model with a law switched \
      off is not supported)"
  let laws := lawsE.toArray.map (·.constName!)
  let mut cans : Array (List Name) := #[]
  for e in lawsE do
    let l ← kernelNorm (← mkAppM ``Model.canSolve #[M, e])
    cans := cans.push (((l.listLit?.map (·.2)).getD []).map (·.constName!))
  let cert ← mkAppM ``Setup.cert #[S]
  let mut own : Array Name := #[]
  for e in lawsE do
    own := own.push (← kernelNorm (← mkAppM ``Order.Cert.σ #[cert, e])).constName!
  let lemmas ← names.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkCIdent n):ident)
  let SStx ← Term.exprToSyntax S
  let MStx ← Term.exprToSyntax M
  let uStx ← Term.exprToSyntax u
  let realT := mkConst ``Real
  for pick in matchings laws cans endo own do
    let lawOf (v : Name) : Name := laws[(pick.toList.idxOf? v).getD 0]!
    let mut depsMap : Array (Name × List Name) := #[]
    for (e, v) in laws.zip pick do
      let d ← kernelNorm (← mkAppM ``Model.deps #[M, mkConst e, mkConst v])
      depsMap := depsMap.push (v, ((d.listLit?.map (·.2)).getD []).map (·.constName!))
    let deps (v : Name) : List Name := ((depsMap.find? (·.1 == v)).map (·.2)).getD []
    trace[debug] "pick {pick}, deps {depsMap}"
    for k in [1:min 4 (endo.length + 1)] do
      for core in subsetsOf endo k do
        let some order := topo deps (exoN ++ core) (endo.filter fun v => !core.contains v)
          | trace[debug] "no topo for {core}"; continue
        trace[debug] "trying {core} {order}"
        let res ← try
            tryCandidate M u names lemmas SStx MStx uStx realT core order lawOf
          catch ex => pure (some (← ex.toMessageData.toString))
        match res with
        | none => return
        | some msg => trace[debug] "pick {pick}, core {core}: {msg}"
  throwError "block_exists: no matching and core gave a box where Poincaré–Miranda applies \
    (the conditions on the fixed values may be missing from the context)"

/-! ## Uniqueness through another matching -/

/-- The setup's laws, its endogenous variables, what each law can be solved
    for, and its own matching. -/
def setupInfo (S M : Expr) : MetaM (Array Name × List Name × Array (List Name) × Array Name ×
    List Name × Array Expr) := do
  let SType ← whnfR (← inferType S)
  let V := SType.getAppArgs[1]!
  let ctors ← ctorsOf V
  let exo := ((← kernelNorm (← mkAppM ``Setup.exo #[S])).listLit?.map (·.2)).getD []
  let exoN := exo.map (·.constName!)
  let endo := ctors.filter fun c => !exoN.contains c
  let lawsE := ((← kernelNorm (← mkAppM ``Model.eqList #[M])).listLit?.map (·.2)).getD []
  let laws := lawsE.toArray.map fun e => e.constName?.getD (Name.mkSimple (shortName e))
  let mut cans : Array (List Name) := #[]
  for e in lawsE do
    let l ← kernelNorm (← mkAppM ``Model.canSolve #[M, e])
    cans := cans.push (((l.listLit?.map (·.2)).getD []).map (·.constName!))
  let cert ← mkAppM ``Setup.cert #[S]
  let mut own : Array Name := #[]
  for e in lawsE do
    own := own.push (← kernelNorm (← mkAppM ``Order.Cert.σ #[cert, e])).constName!
  return (laws, endo, cans, own, exoN, lawsE.toArray)

/-- `secant_unique_any` proves
      `∀ u x y, S.scm.Solves u x → S.scm.Solves u y → M.dom x → M.dom y → x = y`
    with `secant_unique`, first for the setup's own matching, then for the other
    matchings of laws to variables: inside the domain the solutions do not
    depend on which formula each law is read with (`Setup.solves_iff_restrict`),
    so the criterion may use the matching whose formulas are multi-affine. -/
elab "secant_unique_any" : tactic => withMainContext do
  let saved ← saveState
  let ok ← try
      evalTactic (← `(tactic| secant_unique))
      pure (← getGoals).isEmpty
    catch _ => pure false
  if ok then return
  saved.restore
  let goal ← instantiateMVars (← getMainTarget)
  let S ← forallTelescopeReducing goal.consumeMData fun xs _ => do
    for x in xs do
      if let some h := (← inferType x).find? fun e => e.isAppOf ``Setup.scm then
        return h.getAppArgs[7]!
    throwError "secant_unique_any: expected a goal about `S.scm.Solves`"
  let M := (← whnfR (← inferType S)).getAppArgs.back!
  let (laws, endo, cans, own, _, lawsE) ← setupInfo S M
  unless lawsE.all (·.isConst) do
    throwError "secant_unique_any: the laws are not named constructors"
  let SStx ← Term.exprToSyntax S
  let MStx ← Term.exprToSyntax M
  for pick in matchings laws cans endo own do
    if pick == own then continue
    let alts ← (laws.zip pick).mapM fun (e, v) =>
      `(Lean.Parser.Term.matchAltExpr| | $(mkCIdent e):ident => $(mkCIdent v):ident)
    let s1 ← saveState
    let res ← try
        let pickStx ← `(fun e => match e with $alts:matchAlt*)
        let S' ← Term.elabTerm (← `(({ exo := ($SStx).exo } : Setup (($MStx).restrict $pickStx))))
          none
        Term.synthesizeSyntheticMVarsNoPostponing
        let S' ← nameSetup (← instantiateMVars S')
        let S'Stx ← Term.exprToSyntax S'
        let errs0 := (← Core.getMessageLog).toList.filter (·.severity == .error) |>.length
        evalTactic (← `(tactic| (
          have key : ∀ u x y, ($S'Stx).scm.Solves u x → ($S'Stx).scm.Solves u y →
              (($MStx).restrict $pickStx).dom x → (($MStx).restrict $pickStx).dom y → x = y := by
            secant_unique
          intro u x y hx hy hDx hDy
          exact key u x y ((Setup.solves_iff_restrict $SStx $pickStx $S'Stx rfl u x hDx).1 hx)
            ((Setup.solves_iff_restrict $SStx $pickStx $S'Stx rfl u y hDy).1 hy) hDx hDy)))
        let errs := (← Core.getMessageLog).toList.filter (·.severity == .error) |>.length
        pure ((← getGoals).isEmpty && errs == errs0)
      catch _ => pure false
    if res then return
    s1.restore
  throwError "secant_unique_any: no matching of laws to variables makes the secant criterion apply"

/-! ## Uniqueness from the laws themselves -/

/-- Unfold the model and setup definitions only (no other simplification). -/
def unfoldOnly (names : Array Name) (e : Expr) : MetaM Expr := do
  let mut thms : SimpTheorems := {}
  for n in names ++ #[``Model.ofSolvers, ``Model.restrict] do
    thms ← thms.addDeclToUnfold n
  let ctx ← Simp.mkContext {} #[thms] (← getSimpCongrTheorems)
  let (r, _) ← simp e ctx #[]
  return r.expr

/-- The arguments `a` of applications `s a` in `e`. -/
partial def collectApps (s e : Expr) : List Expr :=
  match e with
  | .app f a => (if f == s then [a] else []) ++ collectApps s f ++ collectApps s a
  | .lam _ t b _ => collectApps s t ++ collectApps s b
  | .forallE _ t b _ => collectApps s t ++ collectApps s b
  | .letE _ t v b _ => collectApps s t ++ collectApps s v ++ collectApps s b
  | .mdata _ b => collectApps s b
  | .proj _ _ b => collectApps s b
  | _ => []

/-- The constructors `c` such that `s c` occurs in `e`. -/
def mentioned (s : Expr) (e : Expr) : List Name := Id.run do
  let mut out : List Name := []
  for t in collectApps s e do
    if let some c := t.constName? then
      if !out.contains c then out := out ++ [c]
  return out

def realOne : MetaM Expr := mkAppOptM ``OfNat.ofNat #[mkConst ``Real, mkRawNatLit 1, none]
def realZero : MetaM Expr := mkAppOptM ``OfNat.ofNat #[mkConst ``Real, mkRawNatLit 0, none]

/-- Can we show `∀ z, M.dom z → 0 < f z` (or `0 < -f z`)? -/
def provesOnDomain (M f : Expr) (neg : Bool)
    (extra : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) : TacticM Bool := do
  let sT := (← whnf (← inferType f)).bindingDomain!
  let ty ← withLocalDeclD `z sT fun z => do
    let fz := (mkApp f z).headBeta
    let body ← mkAppM ``LT.lt #[← realZero, ← if neg then mkAppM ``Neg.neg #[fz] else pure fz]
    mkForallFVars #[z] (← mkArrow (← mkAppM ``Model.dom #[M, z]) body)
  let saved ← saveState
  let ok ← try
      let g ← mkFreshExprMVar ty
      let gs ← Term.withoutErrToSorry <| Tactic.run g.mvarId! do
        evalTactic (← `(tactic| (
          intro z hz
          simp only [$extra,*, CausalPhys.Lang.Model.ofSolvers] at hz
          try casesm* _ ∧ _
          add_param_facts
          first
          | positivity
          | positivity_hyps
          | (ring_nf; positivity_hyps)
          | (norm_num; done))))
      pure (gs.isEmpty && !(← instantiateMVars g).hasSorry)
    catch _ => pure false
  saved.restore
  return ok

/-- `law_secant_unique` proves
      `∀ u x y, S.scm.Solves u x → S.scm.Solves u y → M.dom x → M.dom y → x = y`
    from the laws, not from the formulas: each law gives a residual ±(lhs − rhs),
    paired with a variable it mentions so that the diagonal of the secant
    matrix is positive on the domain, and `Setup.laws_secant_unique` applies if
    the residuals are multi-affine and the principal minors are positive. -/
elab "law_secant_unique" : tactic => withTheReader Core.Context
    (fun ctx => { ctx with maxHeartbeats := ctx.maxHeartbeats * 20 }) <| withMainContext do
  addParamFacts
  withMainContext do
  let goal ← instantiateMVars (← getMainTarget)
  let S ← forallTelescopeReducing goal.consumeMData fun xs _ => do
    for x in xs do
      if let some h := (← inferType x).find? fun e => e.isAppOf ``Setup.scm then
        return h.getAppArgs[7]!
    throwError "law_secant_unique: expected a goal about `S.scm.Solves`"
  let SType ← whnfR (← inferType S)
  let V := SType.getAppArgs[1]!
  let M := SType.getAppArgs.back!
  let names ← unfoldNames #[M, S]
  let extra ← names.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkCIdent n):ident)
  let (laws, endo, _, own, _, lawsE) ← setupInfo S M
  let realT := mkConst ``Real
  let sT ← mkArrow V realT
  -- residual of each law, and the endogenous variables it mentions
  let (resids, mentions) ← withLocalDeclD `s sT fun s => do
    let mut rs : Array Expr := #[]
    let mut ms : Array (List Name) := #[]
    for e in lawsE do
      let p ← unfoldOnly names (← mkAppM ``Model.law #[M, e, s])
      let some (_, a, b) := p.eq? | throwError "law_secant_unique: law {e} is not an equation"
      rs := rs.push (← mkLambdaFVars #[s] (← mkAppM ``HSub.hSub #[a, b]))
      ms := ms.push ((mentioned s p).filter endo.contains)
    return (rs, ms)
  let n := laws.size
  let SStx ← Term.exprToSyntax S
  for pick in matchings laws mentions endo own do
    -- the sign of each residual: the diagonal slope must be positive on the domain
    let mut signs : Array Bool := #[]
    let mut ok := true
    for i in [0:n] do
      let r := resids[i]!
      let v := mkConst pick[i]!
      let slope ← withLocalDeclD `z sT fun z => do
        let d ← mkAppM ``HSub.hSub #[mkApp r (← mkAppM ``Function.update #[z, v, ← realOne]),
          mkApp r (← mkAppM ``Function.update #[z, v, ← realZero])]
        mkLambdaFVars #[z] (← simpNorm names d)
      let pos ← provesOnDomain M slope false extra
      if pos then signs := signs.push true
      else if ← provesOnDomain M slope true extra then signs := signs.push false
      else ok := false; break
    unless ok do
      trace[debug] "pick {pick}: no sign for a diagonal (signs so far {signs})"
      continue
    let resStx ← (List.range n).toArray.mapM fun i => do
      let r ← Term.exprToSyntax resids[i]!
      if signs[i]! then `(fun s => $r s) else `(fun s => -($r s))
    let varsStx := pick.map fun v => (⟨(mkCIdent v).raw⟩ : Term)
    let lawCtors ← lawsE.mapM fun e => Term.exprToSyntax e
    let nT := Syntax.mkNumLit (toString n)
    let saved ← saveState
    let res ← try
        let errs0 := (← Core.getMessageLog).toList.filter (·.severity == .error) |>.length
        evalTactic (← `(tactic| (
          intro u x y hx hy hDx hDy
          refine Setup.laws_secant_unique $SStx (vars := ![$varsStx,*]) (by decide)
            (by intro v hv; cases v <;> first
                | (exfalso; apply hv; simp [$extra,*]; done)
                | decide)
            (![$resStx,*] : Fin $nT → _ → ℝ) ?hres ?hma ?hP hx hy hDx hDy
          case hres =>
            intro s _ hSat i
            $[have := hSat $lawCtors]*
            simp only [$extra,*, CausalPhys.Lang.Model.ofSolvers] at *
            fin_cases i <;> simp <;> linarith
          case hma =>
            intro i j z t
            fin_cases i <;> fin_cases j <;> (simp [Function.update_apply]; try ring1))))
        -- the P-matrix condition
        evalTactic (← `(tactic| intro $(mkIdent `x) $(mkIdent `y) $(mkIdent `hDx) $(mkIdent `hDy)
          $(mkIdent `hexo)))
        proveMinors n extra (mkIdent `hexo) (mkIdent `hDx) (mkIdent `hDy)
        let errL := (← Core.getMessageLog).toList.filter (·.severity == .error)
        let left ← (← getGoals).mapM fun g => g.withContext do (m!"{← ppExpr (← g.getType)}").toString
        let em ← errL.mapM fun m => m.data.toString
        pure (if left.isEmpty && errL.length == errs0 then none else some s!"left {left} errors {em}")
      catch ex => pure (some (← ex.toMessageData.toString))
    match res with
    | none => return
    | some msg =>
      saved.restore
      trace[debug] "pick {pick} signs {signs}: {msg}"
  throwError "law_secant_unique: no pairing of laws with variables gives a P-matrix"

/-! ## Which criterion applies? -/

open Command in
/-- `#causal_check S` says how the question "exactly one outcome?" is settled
    for a setup: by structure (acyclic), by the linear criterion (and what is
    left to show), or that a domain-specific argument is needed. -/
elab "#causal_check " t:term : command => runTermElabM fun _ => do
  let S ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  let S ← nameSetup (← instantiateMVars S)
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
  let timedOut ← IO.mkRef false
  let saved ← saveState
  let result ← withBudget 200000 <| tryCatchRuntimeEx (do
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
      pure (some (if singular then [m!"__singular__"] else rest)))
    (fun e => do if e.isRuntime then timedOut.set true
                 pure none)
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
  | none =>
    -- second criterion: multi-affine formulas and a secant P-matrix (uniqueness only)
    let M := SType.getAppArgs.back!
    let uniqTy ← withLocalDeclD `u uTy fun u => withLocalDeclD `x uTy fun x =>
      withLocalDeclD `y uTy fun y => do
        let scm ← mkAppM ``Setup.scm #[S]
        let hx ← mkAppM ``CausalPhys.SCM.Solves #[scm, u, x]
        let hy ← mkAppM ``CausalPhys.SCM.Solves #[scm, u, y]
        let dx ← mkAppM ``Model.dom #[M, x]
        let dy ← mkAppM ``Model.dom #[M, y]
        let body ← mkArrow hx (← mkArrow hy (← mkArrow dx (← mkArrow dy (← mkEq x y))))
        mkForallFVars #[u, x, y] body
    let saved ← saveState
    -- `secant_unique` multiplies this budget by 20
    let res2 ← withBudget 50000 <| tryCatchRuntimeEx (do
        Core.resetMessageLog
        let g ← mkFreshExprMVar uniqTy
        let gs ← Term.withoutErrToSorry <| Tactic.run g.mvarId! <| Tactic.withoutRecover (do
          evalTactic (← `(tactic| secant_unique)))
        if (← MonadLog.hasErrors) then throwError "failed"
        if (← instantiateMVars g).hasSorry then throwError "failed"
        let rest ← gs.mapM fun g => g.withContext do
          return toMessageData (← ppExpr (← instantiateMVars (← g.getType)))
        pure (some rest))
      (fun e => do if e.isRuntime then timedOut.set true
                   pure none)
    saved.restore
    -- the secant criterion on the laws themselves, then through another matching
    let mut other := 0
    let mut res2 := res2
    for (k, tac) in [(1, ← `(tactic| law_secant_unique)), (2, ← `(tactic| secant_unique_any))] do
      if res2.isSome || (← timedOut.get) then break
      let saved ← saveState
      let r ← withBudget 50000 <| tryCatchRuntimeEx (do
          Core.resetMessageLog
          let g ← mkFreshExprMVar uniqTy
          let gs ← Term.withoutErrToSorry <| Tactic.run g.mvarId! <| Tactic.withoutRecover (do
            evalTactic tac)
          if (← MonadLog.hasErrors) || !gs.isEmpty then throwError "failed"
          if (← instantiateMVars g).hasSorry then throwError "failed"
          pure (some ([] : List MessageData)))
        (fun e => do if e.isRuntime then timedOut.set true
                     pure none)
      saved.restore
      if r.isSome then other := k; res2 := r
    let how := if other == 1 then "secant P-matrix criterion on the laws, proved by \
      law_secant_unique" else if other == 2 then "secant P-matrix criterion, read with another \
      matching of laws to variables, proved by secant_unique_any" else "secant P-matrix \
      criterion, proved by secant_unique"
    -- existence, when every fixed value is positive
    let mut exists_ := false
    if (match res2 with | some [] => true | _ => false) then
      let exo : List Expr := ((← kernelNorm (← mkAppM ``Setup.exo #[S])).listLit?.map (·.2)).getD []
      let exTy ← withLocalDeclD `u uTy fun u => do
        let mut hyps : Array Expr := #[]
        for v in exo do
          hyps := hyps.push (← mkAppM ``LT.lt #[← mkAppOptM ``OfNat.ofNat
            #[realTy, mkRawNatLit 0, none], mkApp u v])
        let body ← withLocalDeclD `s uTy fun s => do
          let scm ← mkAppM ``Setup.scm #[S]
          mkLambdaFVars #[s] (← mkAppM ``And #[← mkAppM ``CausalPhys.SCM.Solves #[scm, u, s],
            ← mkAppM ``Model.dom #[M, s]])
        let mut t ← mkAppM ``Exists #[body]
        for h in hyps.reverse do t ← mkArrow h t
        mkForallFVars #[u] t
      let saved ← saveState
      let r ← withBudget 400000 <| tryCatchRuntimeEx (do
          Core.resetMessageLog
          let g ← mkFreshExprMVar exTy
          let gs ← Term.withoutErrToSorry <| Tactic.run g.mvarId! <| Tactic.withoutRecover (do
            evalTactic (← `(tactic| intros))
            evalTactic (← `(tactic| block_exists)))
          if (← MonadLog.hasErrors) || !gs.isEmpty then throwError "failed"
          if (← instantiateMVars g).hasSorry then throwError "failed"
          pure true)
        (fun _ => pure false)
      saved.restore
      exists_ := r
    match res2 with
    | some [] =>
      if exists_ then
        logInfo m!"cyclic, not linear in its own block, but multi-affine: exactly one outcome \
          in the domain whenever every fixed value is positive (at most one: {how}; at least \
          one: Poincaré–Miranda, proved by block_exists)"
      else
        logInfo m!"cyclic, not linear in its own block, but multi-affine: at most \
          one outcome in the domain ({how})"
    | some rest => logInfo m!"cyclic, not linear in its own block, but multi-affine: at most \
        one outcome in the domain provided that these principal minors are positive:\n  \
        {MessageData.joinSep rest "\n  "}\n(finish `secant_unique` with proofs of these)"
    | none =>
      if ← timedOut.get then
        logInfo m!"cyclic: no criterion succeeded within its time limit (block_linear: \
          200000 heartbeats, secant_unique: 1000000); uniqueness is not decided here. Try \
          the tactics directly with a larger `maxHeartbeats`, or give a domain-specific \
          argument with Setup.unique_of_laws"
      else logInfo m!"cyclic: neither criterion applies (the block is not linear, and no \
          reading of its laws gives multi-affine residuals with a P-matrix secant on the \
          domain); uniqueness needs a domain-specific argument (monotonicity, Gale–Nikaido, \
          Minty–Browder), plugged in with Setup.unique_of_laws"


end CausalPhys.Lang
