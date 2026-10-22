/-
  Exports what Lean computes for the teaching page `docs/kausal-lab.html`.

  For every model on the page and every choice of fixed variables (every lab
  setup with as many fixed variables as the model has variables minus laws),
  Lean evaluates the same functions `#causal_order` uses: whether the setup is
  valid (a perfect matching exists), which law determines which variable, what
  it reads, the blocks and whether the setup is acyclic. The same is done for
  every model with one law switched off (`Model.remove`), which is what an
  intervention gives. Units are the dimensions `causal_model` computes.

  Run by `scripts/build_lab.py`, which writes the JSON into the page. CI runs
  it again and fails if the page differs: the page cannot drift from Lean.
-/
import CausalPhys

open Lean Meta Elab Command CausalPhys CausalPhys.Lang CausalPhys.Examples

namespace CausalPhys.Lang.Export

def jstr (s : String) : String := "\"" ++ s ++ "\""
def jarr (xs : List String) : String := "[" ++ ",".intercalate xs ++ "]"
def jnames (xs : List Expr) : String := jarr (xs.map (jstr ∘ shortName))

def listOf (e : Expr) : MetaM (List Expr) := do
  let some (_, xs) := (← kernelNorm e).listLit? | throwError "export: not a list: {e}"
  pure xs

def isTrue (p : Expr) : MetaM Bool := do
  pure ((← kernelNorm (← mkDecide p)).isAppOf ``Bool.true)

/-- All sublists of `xs` with `k` elements, in order. -/
def choose {α : Type} : List α → Nat → List (List α)
  | _, 0 => [[]]
  | [], _ + 1 => []
  | x :: xs, k + 1 => (choose xs k).map (x :: ·) ++ choose xs (k + 1)

/-- One JSON object per lab setup of model `M`. -/
def setups (M : Expr) : MetaM String := do
  let Mty ← whnfR (← inferType M)
  let #[_, Vty, _] := Mty.getAppArgs | throwError "export: expected a model"
  let vars ← listOf (← mkAppM ``Model.varList #[M])
  let laws ← listOf (← mkAppM ``Model.eqList #[M])
  let mut out : Array String := #[]
  for exo in choose vars (vars.length - laws.length) do
    let exoE ← mkListLit Vty exo
    let st ← mkAppM ``Model.struct #[M, exoE]
    let cert ← mkAppM ``Model.order #[M, exoE]
    let fixed := "\"fixed\":" ++ jnames exo
    unless ← isTrue (← mkAppM ``Order.Valid #[st, cert]) do
      out := out.push ("{" ++ fixed ++ ",\"valid\":false}")
      continue
    let mut rows : Array String := #[]
    for e in laws do
      let v ← kernelNorm (← mkAppM ``Order.Cert.σ #[cert, e])
      let deps ← listOf (← mkAppM ``Model.deps #[M, e, v])
      let blk ← listOf (← mkAppM ``Order.blockOf #[st, e])
      rows := rows.push ("{\"law\":" ++ jstr (shortName e) ++ ",\"var\":" ++ jstr (shortName v) ++
        ",\"reads\":" ++ jnames deps ++
        ",\"block\":" ++ jnames blk ++ "}")
    let acyc ← isTrue (← mkAppM ``Order.OrderedLT #[st, cert])
    out := out.push ("{" ++ fixed ++ ",\"valid\":true,\"acyclic\":" ++ toString acyc ++
      ",\"order\":" ++ jarr rows.toList ++ "}")
  pure (jarr out.toList)

/-- Which variables each law can be solved for. -/
def solvable (M : Expr) : MetaM String := do
  let laws ← listOf (← mkAppM ``Model.eqList #[M])
  let rows ← laws.mapM fun e => do
    let vs ← listOf (← mkAppM ``Model.canSolve #[M, e])
    pure (jstr (shortName e) ++ ":" ++ jnames vs)
  pure ("{" ++ ",".intercalate rows ++ "}")

/-- The dimension of every declared name, as `causal_model` computes it. -/
def unitsJson (s : String) : CommandElabM String := do
  let env ← getEnv
  let mut rows : Array String := #[]
  for part in s.splitOn "," do
    let some (name, u) := (match part.splitOn ":" with
      | [n, u] => some (n.replace " " "", u.replace " " "") | _ => none) | throwError "export: units {part}"
    let some ustx := (Parser.runParserCategory env `term u).toOption
      | throwError "export: cannot parse unit {u}"
    let d ← liftMacroM (Units.ofUnitSyntax ⟨ustx⟩)
    rows := rows.push (jstr name ++ ":" ++ jstr (Units.fmt d))
  pure (",".intercalate rows.toList)


/-- `#export_model "gas" "p : Pa, …" Gas.model` prints one JSON line. -/
elab "#export_model " key:str us:str M:term : command => do
  let json ← runTermElabM fun _ => do
    let M ← Term.elabTerm M none
    Term.synthesizeSyntheticMVarsNoPostponing
    let M ← instantiateMVars M
    let vars ← listOf (← mkAppM ``Model.varList #[M])
    let laws ← listOf (← mkAppM ``Model.eqList #[M])
    let main ← setups M
    let mut removed : Array String := #[]
    for e in laws do
      removed := removed.push (jstr (shortName e) ++ ":" ++ (← setups (← mkAppM ``Model.remove #[M, e])))
    pure ("{\"key\":" ++ jstr key.getString ++ ",\"vars\":" ++ jnames vars ++
      ",\"laws\":" ++ jnames laws ++ ",\"solvable\":" ++ (← solvable M) ++
      ",\"setups\":" ++ main ++ ",\"without\":{" ++ ",".intercalate removed.toList ++ "}")
  logInfo ("EXPORT " ++ json ++ ",\"units\":{" ++ (← unitsJson us.getString) ++ "}}")

end CausalPhys.Lang.Export

