/-
  CausalPhys.Lang.Syntax — the surface language (phase 3).

  A model is written the way it is written on a blackboard:

      causal_model Gas where
        variables p vol n T
        domain 0 < p ∧ 0 < vol ∧ 0 < n ∧ 0 < T
        facts R_pos
        law gas : p * vol = n * R * T
        witness p := 1, vol := 1, n := 1, T := 1 / R
        setup locked fixes vol n T
        setup weighted fixes p n T

  and becomes, inside `namespace Gas`:
    * `V` (the variables) and `Law` (the laws) as enumeration types,
    * `model : Model Law V ℝ`, built with `Model.ofSolvers`. For every variable
      a law is affine in, the formula is derived from the law (`deriveFormula`)
      and kept if `law_solve` proves that it solves the law on the domain; a
      formula that needs more (a denominator the domain does not keep away from
      0) is left out. `#causal_solvable` shows the result. A formula can also
      be written by hand, `solve x := …` (with a proof after `by` if needed),
      which is the way for laws that are not affine in `x`; a formula written
      by hand must be proved, and comes before the derived ones. What each
      formula reads is collected from the formula itself,
    * `consistent : ∃ s, model.dom s ∧ model.Sat s`, proved from the `witness`
      (a concrete state; variables not listed are 0). Every model must have one,
      so a domain that contradicts the laws is rejected,
    * one `Setup model` per `setup` line.

  `facts h₁, h₂` makes facts about constants (such as `R_pos : 0 < R`)
  available to every formula proof and to the witness.

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
import CausalPhys.Lang.Exist
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
  (ppLine "facts " term,+)?
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

/-! ## Deriving a formula from a law that is linear in a variable

  A law `lhs = rhs` that is affine in `x` is `a·x + b = 0` with `a`, `b` free of
  `x`. The derivation works on the syntax: every side is split into the part
  proportional to `x` and the rest, as signed sums of terms, and then
  `x = (lB − rB) / (rA − lA)` is written with the obvious simplifications
  (no `0 +`, no `1 ·`, no `/ 1`). Whether the formula solves the law on the
  domain (where `rA − lA ≠ 0` is needed) is decided when the model is
  elaborated; a derived formula that cannot be proved is left out. -/

/-- A signed sum of terms; `true` means the term is added. -/
abbrev SSum := Array (Bool × Term)

def isOne (t : Term) : Bool := match t.raw.isNatLit? with | some 1 => true | _ => false

def one : MacroM Term := `(1)

/-- Multiply every term of a sum by `t` (on the left). -/
def SSum.mulL (t : Term) (xs : SSum) : MacroM SSum :=
  xs.mapM fun (sg, x) => do
    if isOne x then return (sg, t) else return (sg, ← `($t * $x))

/-- Multiply every term of a sum by `t` (on the right). -/
def SSum.mulR (xs : SSum) (t : Term) : MacroM SSum :=
  xs.mapM fun (sg, x) => do
    if isOne x then return (sg, t) else return (sg, ← `($x * $t))

def SSum.div (xs : SSum) (t : Term) : MacroM SSum :=
  xs.mapM fun (sg, x) => do return (sg, ← `($x / $t))

def SSum.neg (xs : SSum) : SSum := xs.map fun (sg, x) => (!sg, x)

/-- The sum as a term. -/
def SSum.toTerm (xs : SSum) : MacroM Term := do
  if xs.isEmpty then return ← `(0)
  let (sg0, x0) := xs[0]!
  let mut acc : Term ← if sg0 then pure x0 else `(-$x0)
  for (sg, x) in xs.toList.drop 1 do
    acc ← if sg then `($acc + $x) else `($acc - $x)
  return acc

/-- Does the syntax mention the identifier `x`? -/
partial def mentions (x : Name) : Syntax → Bool
  | Syntax.ident _ _ n _ => n.eraseMacroScopes == x
  | Syntax.node _ _ args => args.any (mentions x)
  | _ => false

/-- Split `e` into `a·x + b`; `none` if `e` is not affine in `x`. -/
partial def splitLin (x : Name) (e : Term) : MacroM (Option (SSum × SSum)) := do
  if !mentions x e then return some (#[], #[(true, e)])
  match e with
  | `($i:ident) => if i.getId.eraseMacroScopes == x then return some (#[(true, ← one)], #[])
                   else return some (#[], #[(true, e)])
  | `(($a)) => splitLin x a
  | `($a + $b) => do
    let some (a1, b1) ← splitLin x a | return none
    let some (a2, b2) ← splitLin x b | return none
    return some (a1 ++ a2, b1 ++ b2)
  | `($a - $b) => do
    let some (a1, b1) ← splitLin x a | return none
    let some (a2, b2) ← splitLin x b | return none
    return some (a1 ++ a2.neg, b1 ++ b2.neg)
  | `(-$a) => do
    let some (a1, b1) ← splitLin x a | return none
    return some (a1.neg, b1.neg)
  | `($a * $b) => do
    if !mentions x a then
      let some (a2, b2) ← splitLin x b | return none
      return some (← a2.mulL a, ← b2.mulL a)
    if !mentions x b then
      let some (a1, b1) ← splitLin x a | return none
      return some (← a1.mulR b, ← b1.mulR b)
    return none
  | `($a / $b) => do
    if mentions x b then return none
    let some (a1, b1) ← splitLin x a | return none
    return some (← a1.div b, ← b1.div b)
  | _ => return none

/-- The formula for `x` from the law `lhs = rhs`, if the law is affine in `x`. -/
def deriveFormula (x : Name) (rel : Term) : MacroM (Option Term) := do
  let `($l = $r) := rel | return none
  let some (lA, lB) ← splitLin x l | return none
  let some (rA, rB) ← splitLin x r | return none
  -- x = (lB − rB) / (rA − lA), or the same with both signs flipped
  let num := lB ++ rB.neg
  let den := rA ++ lA.neg
  if den.isEmpty then return none
  let (num, den) := if den.all (fun p => !p.1) then (num.neg, den.neg) else (num, den)
  let numT ← num.toTerm
  if den.size == 1 && isOne den[0]!.2 && den[0]!.1 then return some numT
  let denT ← den.toTerm
  if den.size == 1 then return some (← `($numT / $denT))
  return some (← `($numT / ($denT)))

/-! ## Optional solvers

  `solvers% [req% a, opt% b, …]` elaborates to the list of those entries that
  elaborate without error: a required entry (written by the user) must, an
  optional one (derived) is dropped if its proof fails. -/

syntax solverEntry := ("req% " <|> "opt% ") term
syntax (name := solversList) "solvers%" "[" solverEntry,* "]" : term

open Lean.Elab.Term Meta in
@[term_elab solversList] def elabSolvers : TermElab := fun stx expectedType? => do
  let some expTy := expectedType? | throwError "solvers%: the expected type is not known"
  let expTy ← whnfR (← instantiateMVars expTy)
  unless expTy.isAppOfArity ``List 1 do
    throwError "solvers%: expected a list type, got {expTy}"
  let elemTy := expTy.appArg!
  let ents := stx[2].getSepArgs
  let isReq (ent : Syntax) :=
    let tok := if ent[0].isAtom then ent[0] else ent[0][0]
    tok.getAtomVal.startsWith "req%"
  -- required entries first, with their proofs, so that a failing optional
  -- entry cannot take them down with it
  let mut out : Array Expr := #[]
  for ent in ents do
    if isReq ent then out := out.push (← elabTermEnsuringType ent[1] elemTy)
  synthesizeSyntheticMVarsNoPostponing
  for ent in ents do
    if isReq ent then continue
    let saved ← saveState
    let errs0 := (← Core.getMessageLog).toList.filter (·.severity == .error) |>.length
    let ok ← try
        let e ← withoutErrToSorry do
          let e ← elabTermEnsuringType ent[1] elemTy
          synthesizeSyntheticMVarsNoPostponing
          instantiateMVars e
        let errs := (← Core.getMessageLog).toList.filter (·.severity == .error) |>.length
        if e.hasSorry || errs > errs0 then pure none else pure (some e)
      catch _ => pure none
    match ok with
    | some e => out := out.push e
    | none => saved.restore
  mkListLit elemTy out.toList

def vIdent (n : Name) : Ident := mkIdent (`V ++ n)
def lawIdent (n : Name) : Ident := mkIdent (`Law ++ n)

macro_rules
  | `(causal_model $name:ident $bs:bracketedBinder* where
        variables $vs:ident*
        $[$uc?:unitsClause]?
        $[domain $dom?]?
        $[facts $facts?,*]?
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
    -- facts about constants (such as `R_pos : 0 < R`) available to every formula proof
    let factTerms : Array Term := match facts? with
      | some fs => fs.getElems
      | none => #[]
    let withFacts (t : TSyntax `tactic) : MacroM (TSyntax `tactic) := do
      let mut tac := t
      for f in factTerms.reverse do
        tac ← `(tactic| (have := $f; $tac))
      pure tac
    let solveTac : TSyntax ``Lean.Parser.Tactic.tacticSeq ←
      `(tacticSeq| $(← withFacts (← `(tactic| law_solve))):tactic)
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
          | none => `(by $solveTac)
        entries := entries.push (← `(⟨$(vIdent xn), CausalPhys.Lang.mech [$psT,*] (fun $s => $f'),
            $proof⟩))
      -- formulas derived for the other variables the law is affine in
      let given := sols.filterMap fun sol => match sol with
        | `(solveClause| solve $x:ident := $_:term $[by $_]?) => some x.getId.eraseMacroScopes
        | _ => none
      let mut opts : Array Term := #[]
      for xn in collectVars vars #[] rel do
        if given.contains xn then continue
        let some f ← deriveFormula xn rel | continue
        let ps := collectVars vars #[] f
        if ps.contains xn then continue
        let psT : Array Term := ps.map fun p => ⟨(vIdent p).raw⟩
        let f' : Term := ⟨← substVars vars s f⟩
        opts := opts.push (← `(⟨$(vIdent xn), CausalPhys.Lang.mech [$psT,*] (fun $s => $f'),
            by $solveTac⟩))
      let reqE ← entries.mapM fun e => `(solverEntry| req% $e)
      let optE ← opts.mapM fun e => `(solverEntry| opt% $e)
      solverAlts := solverAlts.push
        (← `(Lean.Parser.Term.matchAltExpr| | $(lawIdent lname):ident =>
              solvers% [$(reqE ++ optE),*]))
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
      | none => do
        let t ← withFacts (← `(tactic| witness_check))
        `(by $t:tactic)
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
