/-
  CausalPhys.Lang.Units — dimensional analysis for `causal_model` (point 4).

  A model may declare units:

      units p : Pa, vol : m^3, n : mol, T : K, R : J/(mol*K)

  for its variables and for every constant or parameter its formulas use
  (`R`, `c.K1`, …). Lean then computes the dimension of every subterm of every
  law, domain condition and solving formula, and refuses the model where they
  do not match, pointing at the offending subterm:

    * both sides of `=`, `<`, `≤` must have the same dimension, and so must the
      terms of a sum;
    * a solving formula must have the dimension of the variable it solves for;
    * `Real.exp`, `Real.log`, `Real.sin`, `Real.cos` need a dimensionless
      argument; `Real.sqrt` halves the dimension;
    * numerals are dimensionless, except `0`, which fits any dimension.

  Units are SI base units (m, kg, s, A, K, mol, cd), common derived units
  (N, Pa, J, W, C, V, ohm, Hz, L for litre, M for mol/L), and any other name,
  which becomes a base unit of its own: `NOK`, `item`, `yr` for economics.
  Only dimensions are checked, not scale factors (a litre and a cubic metre
  are both length³).
-/
import Lean

namespace CausalPhys.Lang.Units

open Lean

/-- A dimension: exponents of named base units, sorted, without zeros. -/
abbrev Dim := List (String × Int)

/-- SI order first, then other base units alphabetically. -/
def rank (n : String) : Nat :=
  match ["kg", "m", "s", "A", "K", "mol", "cd"].idxOf? n with
  | some i => i
  | none => 100

def norm (d : Dim) : Dim :=
  let names := (d.map (·.1)).eraseDups
  let summed := names.map fun n => (n, (d.filter (·.1 == n)).foldl (fun a p => a + p.2) 0)
  (summed.filter (·.2 != 0)).mergeSort fun a b =>
    rank a.1 < rank b.1 || (rank a.1 == rank b.1 && a.1 ≤ b.1)

def mul (a b : Dim) : Dim := norm (a ++ b)
def inv (a : Dim) : Dim := a.map fun (n, e) => (n, -e)
def pow (a : Dim) (k : Int) : Dim := norm (a.map fun (n, e) => (n, e * k))
def one : Dim := []

def superscript (k : Int) : String :=
  let digits := toString k.natAbs
  let sup := digits.toList.map fun c => match c with
    | '0' => '⁰' | '1' => '¹' | '2' => '²' | '3' => '³' | '4' => '⁴'
    | '5' => '⁵' | '6' => '⁶' | '7' => '⁷' | '8' => '⁸' | _ => '⁹'
  (if k < 0 then "⁻" else "") ++ String.ofList sup

def fmtBase (d : Dim) : String :=
  if d.isEmpty then "1 (dimensionless)"
  else "·".intercalate (d.map fun (n, e) => if e == 1 then n else n ++ superscript e)

/-- The built-in units, in SI base dimensions. -/
def builtin : List (String × Dim) :=
  let m : Dim := [("m", 1)]; let kg : Dim := [("kg", 1)]; let s : Dim := [("s", 1)]
  let A : Dim := [("A", 1)]
  let N := norm (kg ++ m ++ pow s (-2))
  let J := mul N m
  let W := mul J (inv s)
  let C := mul A s
  let Vt := mul W (inv A)
  [("m", m), ("kg", kg), ("s", s), ("A", A), ("K", [("K", 1)]), ("mol", [("mol", 1)]),
   ("cd", [("cd", 1)]), ("N", N), ("Pa", mul N (pow m (-2))), ("J", J), ("W", W),
   ("C", C), ("V", Vt), ("ohm", mul Vt (inv A)), ("Hz", inv s), ("L", pow m 3),
   ("M", mul [("mol", 1)] (pow m (-3)))]

/-- A dimension in base units, with the name of a derived unit when there is one. -/
def fmt (d : Dim) : String :=
  let base := fmtBase d
  match builtin.find? (fun (n, x) => norm x == norm d && d.length > 1 && n != "M") with
  | some (n, _) => base ++ s!" ({n})"
  | none => base

/-- The dimension of a unit expression such as `J/(mol*K)` or `m^3`. -/
partial def ofUnitSyntax (stx : Term) : MacroM Dim := do
  match stx with
  | `($a * $b) => return mul (← ofUnitSyntax a) (← ofUnitSyntax b)
  | `($a / $b) => return mul (← ofUnitSyntax a) (inv (← ofUnitSyntax b))
  | `($a ^ $k:num) => return pow (← ofUnitSyntax a) k.getNat
  | `($a ^ (-$k:num)) => return pow (← ofUnitSyntax a) (-(k.getNat : Int))
  | `(($a)) => ofUnitSyntax a
  | `(1) => return one
  | `($x:ident) =>
    let n := x.getId.eraseMacroScopes.toString
    match builtin.find? (·.1 == n) with
    | some (_, d) => return d
    | none => return [(n, 1)]
  | _ => Macro.throwErrorAt stx "units: not a unit expression (use names, *, /, ^ and 1)"

/-- A dimension, or "fits any dimension" (the numeral 0). -/
inductive DV
  | any
  | d (x : Dim)
  deriving Inhabited

def DV.fmt : DV → String
  | .any => "any"
  | .d x => Units.fmt x

/-- The environment: dimensions of variables and declared constants. -/
abbrev Env := List (Name × Dim)

def unify (ref : Syntax) (what : String) (a b : DV) : MacroM DV :=
  match a, b with
  | .any, x => pure x
  | x, .any => pure x
  | .d x, .d y =>
    if norm x == norm y then pure (.d x)
    else Macro.throwErrorAt ref s!"units: {what}: {Units.fmt x} vs {Units.fmt y}"

def dimensionless : List Name :=
  [`Real.exp, `Real.log, `Real.sin, `Real.cos, `Real.tanh, `Real.sinh, `Real.cosh, `exp, `log]

/-- The dimension of a formula. -/
partial def infer (env : Env) (stx : Term) : MacroM DV := do
  match stx with
  | `($a + $b) => unify stx "the terms of this sum have different units" (← infer env a) (← infer env b)
  | `($a - $b) => unify stx "the terms of this difference have different units" (← infer env a) (← infer env b)
  | `($a * $b) =>
    match (← infer env a), (← infer env b) with
    | .d x, .d y => return .d (mul x y)
    | _, _ => return .any
  | `($a / $b) =>
    match (← infer env a), (← infer env b) with
    | .d x, .d y => return .d (mul x (inv y))
    | _, _ => return .any
  | `($a ^ $k:num) =>
    match (← infer env a) with
    | .d x => return .d (pow x k.getNat)
    | .any => return .any
  | `(-$a) => infer env a
  | `(($a)) => infer env a
  | `($n:num) => return (if n.getNat == 0 then .any else .d one)
  | `($_:scientific) => return .d one
  | `($f:ident $args*) =>
    let fn := f.getId.eraseMacroScopes
    if dimensionless.contains fn then
      for a in args do
        match (← infer env a) with
        | .d x =>
          unless x.isEmpty do
            Macro.throwErrorAt a s!"units: the argument of {fn} must be dimensionless, \
              but it has unit {Units.fmt x}"
        | .any => pure ()
      return .d one
    else if fn == `Real.sqrt && args.size == 1 then
      match (← infer env args[0]!) with
      | .d x =>
        unless x.all (·.2 % 2 == 0) do
          Macro.throwErrorAt stx s!"units: the square root of {Units.fmt x} is not a unit"
        return .d (x.map fun (n, e) => (n, e / 2))
      | .any => return .any
    else
      Macro.throwErrorAt f s!"units: do not know the unit of the function {fn}"
  | `($x:ident) =>
    let n := x.getId.eraseMacroScopes
    match env.find? (·.1 == n) with
    | some (_, d) => return .d d
    | none => Macro.throwErrorAt x s!"units: no unit declared for {n}; add it to `units`"
  | _ => Macro.throwErrorAt stx "units: cannot work out the unit of this expression"

/-- Check a proposition: a law or a domain condition. -/
partial def checkProp (env : Env) (stx : Term) : MacroM Unit := do
  match stx with
  | `($a ∧ $b) => checkProp env a; checkProp env b
  | `($a ∨ $b) => checkProp env a; checkProp env b
  | `(($a)) => checkProp env a
  | `($a = $b) => discard <| unify stx "the two sides of this law have different units" (← infer env a) (← infer env b)
  | `($a < $b) => discard <| unify stx "the two sides of this comparison have different units" (← infer env a) (← infer env b)
  | `($a ≤ $b) => discard <| unify stx "the two sides of this comparison have different units" (← infer env a) (← infer env b)
  | `($a ≠ $b) => discard <| unify stx "the two sides of this comparison have different units" (← infer env a) (← infer env b)
  | _ => Macro.throwErrorAt stx "units: cannot check this condition (use =, <, ≤, ≠, ∧, ∨)"

/-- Check that a solving formula has the unit of the variable it solves for. -/
def checkSolve (env : Env) (x : Name) (f : Term) : MacroM Unit := do
  let some (_, dx) := env.find? (·.1 == x) | return
  match (← infer env f) with
  | .any => pure ()
  | .d df =>
    unless norm df == norm dx do
      Macro.throwErrorAt f s!"units: this formula for {x} has unit {Units.fmt df}, \
        but {x} has unit {Units.fmt dx}"

end CausalPhys.Lang.Units
