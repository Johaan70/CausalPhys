/-
  CausalPhys.Lang.Syntax — the surface language (phase 3).

  A model is written the way it is written on a blackboard:

      causal_model Gas where
        variables p vol n T
        domain 0 < p ∧ 0 < vol
        law gas : p * vol = n * R * T
          solve p := n * R * T / vol
          solve vol := n * R * T / p
        witness p := 1, vol := 1, n := 1, T := 1 / R
        setup locked fixes vol n T
        setup weighted fixes p n T

  and becomes, inside `namespace Gas`:
    * `V` (the variables) and `Law` (the laws) as enumeration types,
    * `model : Model Law V ℝ`, built with `Model.ofSolvers`; what each formula
      reads is collected from the formula itself, and that each formula solves
      its law on the domain is proved by `law_solve` (or by the tactic given
      after `by`),
    * `consistent : ∃ s, model.dom s ∧ model.Sat s`, proved from the `witness`
      (a concrete state; variables not listed are 0). Every model must have one,
      so a domain that contradicts the laws is rejected,
    * one `Setup model` per `setup` line.

  Parameters (equilibrium constants, elasticities …) are binders after the
  name: `causal_model Market (m : Params) where …`; then `model` and every
  setup take the same parameters.

  Optional `units x : m/s, …` declares the unit of every variable and of the
  constants the formulas use; then every law, domain condition and solving
  formula is checked dimensionally (`CausalPhys.Lang.Units`).

  Formulas may use any Lean term; a bare identifier that names a variable is
  read as that variable. This also applies to identifiers bound inside a
  formula (`fun y => …`), so bound names must differ from the variable names.
-/
import CausalPhys.Lang.Tactic
import CausalPhys.Lang.Units

namespace CausalPhys.Lang

open Lean Elab Command

syntax solveClause := "solve " ident " := " term (" by " tacticSeq)?
syntax lawClause := "law " ident " : " term (ppLine solveClause)*
syntax setupClause := "setup " ident " fixes " ident+
syntax witnessItem := ident " := " term
syntax unitItem := ident " : " term
syntax unitsClause := "units " sepBy1(unitItem, ", ")
syntax witnessClause := "witness " sepBy1(witnessItem, ", ") (" by " tacticSeq)?

syntax (name := causalModel) "causal_model " ident (ppSpace bracketedBinder)* " where"
  ppLine "variables " ident+
  (ppLine unitsClause)?
  (ppLine "domain " term)?
  (ppLine lawClause)+
  (ppLine witnessClause)?
  (ppLine setupClause)* : command

/-- Replace every identifier naming a variable by `s V.x`. -/
partial def substVars (vars : Array Name) (s : Term) : Syntax → MacroM Syntax
  | stx@(Syntax.ident _ _ n _) =>
    if vars.contains n.eraseMacroScopes then
      `(($s $(mkIdent (`V ++ n.eraseMacroScopes))))
    else pure stx
  | Syntax.node info k args => do
    return Syntax.node info k (← args.mapM (substVars vars s))
  | stx => pure stx

/-- The variables a formula mentions, in order of first appearance. -/
partial def collectVars (vars : Array Name) (acc : Array Name) : Syntax → Array Name
  | Syntax.ident _ _ n _ =>
    let n := n.eraseMacroScopes
    if vars.contains n && !acc.contains n then acc.push n else acc
  | Syntax.node _ _ args => args.foldl (collectVars vars) acc
  | _ => acc

/-- The names bound by explicit binders `(a b : T)`, used as arguments. -/
def binderArgs (bs : Array Syntax) : Array Term := Id.run do
  let mut out := #[]
  for b in bs do
    if b.getKind == ``Lean.Parser.Term.explicitBinder then
      for x in b[1].getArgs do
        out := out.push ⟨x⟩
  return out

def vIdent (n : Name) : Ident := mkIdent (`V ++ n)
def lawIdent (n : Name) : Ident := mkIdent (`Law ++ n)

macro_rules
  | `(causal_model $name:ident $bs:bracketedBinder* where
        variables $vs:ident*
        $[$uc?:unitsClause]?
        $[domain $dom?]?
        $laws:lawClause*
        $[$wc?:witnessClause]?
        $setups:setupClause*) => do
    let binders : Array Syntax := bs.map (·.raw)
    for b in binders do
      unless b.getKind == ``Lean.Parser.Term.explicitBinder do
        Macro.throwErrorAt b "causal_model: parameters must be explicit binders `(name : Type)`"
    let args := binderArgs binders
    let vars := vs.map (·.getId.eraseMacroScopes)
    for a in args do
      if vars.contains a.raw.getId.eraseMacroScopes then
        Macro.throwErrorAt a s!"causal_model: the parameter {a.raw.getId} has the same name as a variable"
    let s ← `(s)
    -- units: dimensional analysis of laws, domain and solving formulas
    let mut uenv : Units.Env := []
    if let some uc := uc? then
      let `(unitsClause| units $items:unitItem,*) := uc | Macro.throwUnsupported
      for it in items.getElems do
        let `(unitItem| $x:ident : $u:term) := it | Macro.throwUnsupported
        uenv := (x.getId.eraseMacroScopes, ← Units.ofUnitSyntax u) :: uenv
      for v in vs do
        unless uenv.any (·.1 == v.getId.eraseMacroScopes) do
          Macro.throwErrorAt v s!"units: no unit declared for the variable {v.getId}"
      if let some d := dom? then Units.checkProp uenv d
      for l in laws do
        let `(lawClause| law $_:ident : $rel:term $sols:solveClause*) := l
          | Macro.throwUnsupported
        Units.checkProp uenv rel
        for sol in sols do
          match sol with
          | `(solveClause| solve $x:ident := $f:term $[by $_]?) =>
            Units.checkSolve uenv x.getId.eraseMacroScopes f
          | _ => pure ()
    -- the law names and their contents
    let mut lawNames : Array Name := #[]
    let mut lawAlts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
    let mut solverAlts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
    for l in laws do
      let `(lawClause| law $ln:ident : $rel:term $sols:solveClause*) := l
        | Macro.throwUnsupported
      let lname := ln.getId.eraseMacroScopes
      lawNames := lawNames.push lname
      let rel' : Term := ⟨← substVars vars s rel⟩
      lawAlts := lawAlts.push (← `(Lean.Parser.Term.matchAltExpr| | $(lawIdent lname):ident => $rel'))
      let mut entries : Array Term := #[]
      for sol in sols do
        let (x, f, tac?) ← match sol with
          | `(solveClause| solve $x:ident := $f:term by $tac:tacticSeq) => pure (x, f, some tac)
          | `(solveClause| solve $x:ident := $f:term) => pure (x, f, none)
          | _ => Macro.throwUnsupported
        let xn := x.getId.eraseMacroScopes
        unless vars.contains xn do
          Macro.throwErrorAt x s!"{xn} is not a variable of the model"
        let ps := collectVars vars #[] f
        if ps.contains xn then
          Macro.throwErrorAt f s!"the formula for {xn} must not mention {xn}"
        let psT : Array Term := ps.map fun p => ⟨(vIdent p).raw⟩
        let f' : Term := ⟨← substVars vars s f⟩
        let proof ← withRef sol <| match tac? with
          | some tac => `(by $tac)
          | none => `(by law_solve)
        entries := entries.push (← `(⟨$(vIdent xn), CausalPhys.Lang.mech [$psT,*] (fun $s => $f'),
            $proof⟩))
      solverAlts := solverAlts.push
        (← `(Lean.Parser.Term.matchAltExpr| | $(lawIdent lname):ident => [$entries,*]))
    let domBody : Term ← match dom? with
      | some d => pure ⟨← substVars vars s d⟩
      | none => `(True)
    let vCtors := vars.map mkIdent
    let lCtors := lawNames.map mkIdent
    let vList : Array Term := vars.map fun v => ⟨(vIdent v).raw⟩
    let lList : Array Term := lawNames.map fun l => ⟨(lawIdent l).raw⟩
    let firstV := vIdent vars[0]!
    let vT := mkIdent `V
    let lawT := mkIdent `Law
    let modelT := mkIdent `model
    let modelApp : Term ← `($modelT $args*)
    let mut cmds : Array (TSyntax `command) := #[]
    cmds := cmds.push (← `(namespace $name))
    cmds := cmds.push (← `(inductive $vT:ident where $[| $vCtors:ident]* deriving DecidableEq, Repr))
    cmds := cmds.push (← `(instance : Inhabited $vT := ⟨$firstV⟩))
    cmds := cmds.push (← `(inductive $lawT:ident where $[| $lCtors:ident]* deriving DecidableEq, Repr))
    cmds := cmds.push (← `(
      set_option linter.unusedTactic false in
      set_option linter.unnecessarySeqFocus false in
      set_option linter.unusedVariables false in
      noncomputable def $modelT $bs:bracketedBinder* : CausalPhys.Lang.Model $lawT $vT ℝ :=
        CausalPhys.Lang.Model.ofSolvers [$lList,*] [$vList,*]
          (by intro e; cases e <;> simp) (by intro v; cases v <;> simp)
          (fun e $s => match e with $lawAlts:matchAlt*)
          (fun $s => $domBody)
          (fun e => match e with $solverAlts:matchAlt*)))
    -- the witness: a state in the domain that satisfies every law
    let some wc := wc? | Macro.throwErrorAt name "causal_model: give a `witness`, a state \
      that lies in the domain and satisfies every law, e.g. `witness x := 1, y := 2`; \
      variables not listed are 0. This shows that the domain and the laws are consistent."
    let (items, wtac?) ← match wc with
      | `(witnessClause| witness $its:witnessItem,* by $t:tacticSeq) => pure (its.getElems, some t)
      | `(witnessClause| witness $its:witnessItem,*) => pure (its.getElems, none)
      | _ => Macro.throwUnsupported
    let mut wvals : Array (Name × Term) := #[]
    for it in items do
      let `(witnessItem| $x:ident := $e:term) := it | Macro.throwUnsupported
      let xn := x.getId.eraseMacroScopes
      unless vars.contains xn do
        Macro.throwErrorAt x s!"{xn} is not a variable of the model"
      wvals := wvals.push (xn, e)
    let mut walts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
    for v in vars do
      let val : Term ← match wvals.find? (·.1 == v) with
        | some (_, e) => pure e
        | none => `((0 : ℝ))
      walts := walts.push (← `(Lean.Parser.Term.matchAltExpr| | $(vIdent v):ident => $val))
    let wproof ← withRef wc <| match wtac? with
      | some t => `(by $t)
      | none => `(by witness_check)
    let consT := mkIdent `consistent
    cmds := cmds.push (← `(
      /-- The domain and the laws are consistent: the witness satisfies both. -/
      theorem $consT $bs:bracketedBinder* :
          ∃ s, ($modelApp).dom s ∧ ($modelApp).Sat s :=
        ⟨fun v => (match v with $walts:matchAlt*), $wproof⟩))
    for st in setups do
      let `(setupClause| setup $sn:ident fixes $xs:ident*) := st | Macro.throwUnsupported
      for x in xs do
        unless vars.contains x.getId.eraseMacroScopes do
          Macro.throwErrorAt x s!"{x.getId} is not a variable of the model"
      let xsT : Array Term := xs.map fun x => ⟨(vIdent x.getId.eraseMacroScopes).raw⟩
      cmds := cmds.push (← withRef st `(
        noncomputable def $sn $bs:bracketedBinder* : CausalPhys.Lang.Setup $modelApp :=
          { exo := [$xsT,*] }))
    cmds := cmds.push (← `(end $name))
    return mkNullNode cmds

end CausalPhys.Lang
