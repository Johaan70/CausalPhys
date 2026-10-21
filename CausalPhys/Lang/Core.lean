/-
  CausalPhys.Lang.Core — the clean core of the language (phase 2).

  A model is written ONCE, as domain content:
    * the variables and the equations (laws) of the system,
    * the domain where the laws make sense (e.g. positive concentrations),
    * for each equation, the ways it can be solved for a variable.

  Everything else is derived, once and for all, by the field-independent
  machinery:
    * the structure (which equation can determine which variable, and what it
      reads) is read off the solvers, so it can never disagree with them;
    * a lab setup is just a list of exogenous variables; Lean computes the
      Simon matching and the blocks (`Setup.valid` is checked by `decide`);
    * the causal model, and general theorems that hold for every model:

        `solves_iff`       inside the domain: solutions of the causal model =
                           solutions of the laws
        `obs_equiv`        two setups allow the same states (data cannot tell them apart)
        `do_iff`           do(x := c) = delete the equation that determines x, add x = c
        `do_exo_iff`       intervening on an exogenous variable = new exogenous value
        `unique`           acyclic setup ⇒ at most one outcome
        `exists_solution`  acyclic setup ⇒ at least one outcome
        `do_existsUnique`  acyclic setup ⇒ every intervention has exactly one outcome
        `laws_existsUnique` if that outcome lies in the domain, the laws have
                           exactly one solution in the domain
        `blocks_independent` for a uniform structure (checked by `decide`), the
                           blocks do not depend on the matching found

  "Outcome" always means a solution of the causal model, i.e. of the solved
  formulas. Outside the domain those need not satisfy the laws (Lean's
  x / 0 = 0, for instance), so statements about the laws themselves go through
  `solves_iff` or `laws_existsUnique`, which ask for the domain. The language
  does not check that the domain is consistent with the laws: that is part of
  the domain content the user writes.

  Nothing here mentions physics, chemistry or economics. The examples in
  `CausalPhys/Lang/Examples` are special cases.
-/
import CausalPhys.CausalOrderComplete
import CausalPhys.DulmageMendelsohn
import CausalPhys.Blocks

set_option linter.unusedSectionVars false

namespace CausalPhys

universe u

/-! ## Existence for acyclic causal models (general SCM fact) -/

namespace SCM

variable {V : Type} {α : Type u}

/-- Insert the mechanisms `k` times, starting from the exogenous values. -/
def iter (M : SCM V α) (u : V → α) : Nat → V → α
  | 0 => u
  | k + 1 => fun v =>
    match M.mech v with
    | none => u v
    | some m => m.f (M.iter u k)

/-- After `rank v + 1` rounds the value of `v` no longer changes. -/
theorem Recursive.iter_stable {M : SCM V α} {rank : V → Nat} (hr : M.Recursive rank)
    (u : V → α) : ∀ r, ∀ v, rank v = r → ∀ j, r < j → M.iter u j v = M.iter u (r + 1) v := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro v hv j hj
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    simp only [iter]
    cases hm : M.mech v with
    | none => rfl
    | some m =>
      apply m.local_
      intro p hp
      have hpr : rank p < r := hv ▸ hr v m hm p hp
      exact (ih (rank p) hpr p rfl j (by omega)).trans (ih (rank p) hpr p rfl r hpr).symm

/-- An acyclic causal model has a solution for every choice of exogenous values. -/
theorem Recursive.exists {M : SCM V α} {rank : V → Nat} (hr : M.Recursive rank)
    (u : V → α) : ∃ s, M.Solves u s := by
  refine ⟨fun v => M.iter u (rank v + 1) v, fun v => ?_⟩
  cases hm : M.mech v with
  | none =>
    show M.iter u (rank v + 1) v = u v
    simp [iter, hm]
  | some m =>
    show M.iter u (rank v + 1) v = m.f _
    have h1 : M.iter u (rank v + 1) v = m.f (M.iter u (rank v)) := by simp only [iter, hm]
    rw [h1]
    apply m.local_
    intro p hp
    show M.iter u (rank v) p = M.iter u (rank p + 1) p
    exact hr.iter_stable u _ p rfl _ (hr v m hm p hp)

end SCM

namespace Lang

open CausalPhys.Order

/-- Proves that a mechanism reads only its parents. -/
macro "mech_local" : tactic =>
  `(tactic| (intro s t h; simp (disch := simp) only [h]))

/-- A mechanism: the parents it reads and the formula. Locality is proved
    automatically for formulas written directly in terms of `s x`. -/
def mech {V : Type} {α : Type u} (ps : List V) (f : (V → α) → α)
    (h : ∀ s t : V → α, (∀ v, v ∈ ps → s v = t v) → f s = f t := by mech_local) :
    Mech V α :=
  ⟨ps, f, h⟩

/-- A model: the domain content, written once. -/
structure Model (E V : Type) (α : Type u) where
  eqList       : List E
  varList      : List V
  eq_complete  : ∀ e, e ∈ eqList := by intro e; cases e <;> simp
  var_complete : ∀ v, v ∈ varList := by intro v; cases v <;> simp
  /-- The laws, as relations between the variables. -/
  law          : E → (V → α) → Prop
  /-- Where the laws make sense (e.g. positive concentrations). -/
  dom          : (V → α) → Prop := fun _ => True
  /-- The ways each law can be solved: (variable, formula). -/
  solvers      : E → List (V × Mech V α)
  /-- Each formula really solves its law on the domain. -/
  sound        : ∀ e v m, (v, m) ∈ solvers e → ∀ s, dom s → (law e s ↔ s v = m.f s)

namespace Model

variable {E V : Type} {α : Type u} [DecidableEq E] [DecidableEq V] (M : Model E V α)

/-- All laws hold. -/
def Sat (s : V → α) : Prop := ∀ e, M.law e s

/-- The variables law `e` can be solved for. -/
def canSolve (e : E) : List V := (M.solvers e).map Prod.fst

/-- The formula for `e` solved for `v`, if there is one. -/
def find (e : E) (v : V) : Option (Mech V α) :=
  ((M.solvers e).find? fun p => decide (p.1 = v)).map Prod.snd

/-- What `e` reads when solved for `v`. -/
def deps (e : E) (v : V) : List V := ((M.find e v).map Mech.parents).getD []

/-- The variables of law `e`, read off its first solver. -/
def eqVars (e : E) : List V :=
  match M.solvers e with
  | [] => []
  | (v, m) :: _ => v :: m.parents

/-- The structure seen by the matching algorithm, for a given lab setup. -/
def struct (exo : List V) : Struct E V where
  eqList := M.eqList
  varList := M.varList
  eq_complete := M.eq_complete
  var_complete := M.var_complete
  canSolve := M.canSolve
  deps := M.deps
  exo := exo

/-- The computed Simon order (matching and ranks). -/
def order [Inhabited V] (exo : List V) : Cert E V := computeC (M.struct exo)

/-- The law as an `Equation` (it may read every variable). -/
def equation (e : E) : Equation V α where
  vars := M.varList
  holds := M.law e
  local_ := by
    intro s t h
    have : s = t := funext fun v => h v (M.var_complete v)
    rw [this]

/-- Fallback formula, never used for a solvable pair. -/
def idMech (v : V) : Mech V α := ⟨[v], fun s => s v, fun _ _ h => h v (by simp)⟩

/-- The formula used when `e` is solved for `v`. -/
def mechOf (e : E) (v : V) : Mech V α := (M.find e v).getD (idMech v)

theorem find_spec {e : E} {v : V} (h : v ∈ M.canSolve e) :
    ∃ m, M.find e v = some m ∧ (v, m) ∈ M.solvers e := by
  unfold canSolve at h
  obtain ⟨⟨v', m'⟩, hm, rfl⟩ := List.mem_map.1 h
  cases hf : (M.solvers e).find? (fun p => decide (p.1 = v')) with
  | none =>
    have := List.find?_eq_none.1 hf _ hm
    simp at this
  | some p =>
    have h1 := List.find?_some hf
    have h2 := List.mem_of_find?_eq_some hf
    obtain ⟨pv, pm⟩ := p
    simp only [decide_eq_true_eq] at h1
    subst h1
    exact ⟨pm, by simp [find, hf], h2⟩

/-- The solvers, packaged for the matching algorithm. -/
def solversOf (exo : List V) : Solvers (M.struct exo) M.equation M.dom where
  mech := M.mechOf
  parents := by
    intro e v hv
    obtain ⟨m, hf, -⟩ := M.find_spec hv
    simp [mechOf, deps, hf, struct]
  sound := by
    intro e v hv s hD
    obtain ⟨m, hf, hm⟩ := M.find_spec hv
    simp only [mechOf, hf, Option.getD_some]
    exact M.sound e v m hm s hD

end Model

/-- One way to solve a law: the variable it determines, the formula, and the
    proof that the formula solves the law on the domain. Keeping the proof next
    to the formula is what lets a surface syntax check each formula separately. -/
structure Solver (V : Type) (α : Type u) (law : (V → α) → Prop) (dom : (V → α) → Prop) where
  target : V
  mech   : Mech V α
  sound  : ∀ s, dom s → (law s ↔ s target = mech.f s)

/-- Build a model from laws and solvers that carry their own proofs. -/
def Model.ofSolvers {E V : Type} {α : Type u} (eqList : List E) (varList : List V)
    (eq_complete : ∀ e, e ∈ eqList) (var_complete : ∀ v, v ∈ varList)
    (law : E → (V → α) → Prop) (dom : (V → α) → Prop)
    (solvers : (e : E) → List (Solver V α (law e) dom)) : Model E V α where
  eqList := eqList
  varList := varList
  eq_complete := eq_complete
  var_complete := var_complete
  law := law
  dom := dom
  solvers e := (solvers e).map fun x => (x.target, x.mech)
  sound := by
    intro e v m h s hD
    obtain ⟨x, hx, hxe⟩ := List.mem_map.1 h
    simp only [Prod.mk.injEq] at hxe
    obtain ⟨rfl, rfl⟩ := hxe
    exact x.sound s hD

open Lean Meta Elab Tactic in
/-- Closes a decidable goal by evaluation in the kernel only. Unlike `decide`, it
    accepts goals that mention symbolic parameters (rate constants, elasticities …):
    structural facts never look at them, so the evaluation goes through. The
    kernel evaluates the statement first and a false or unevaluable goal is
    refused at once; the kernel checks the proof again when the declaration is
    added. -/
elab "kernel_decide" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let inst ← synthInstance (mkApp (mkConst ``Decidable) t)
  let b ← g.withContext do
    match Kernel.whnf (← getEnv) (← getLCtx) (mkApp2 (mkConst ``Decidable.decide) t inst) with
    | .ok r => pure r
    | .error _ => throwError "kernel_decide: the kernel could not evaluate the statement"
  if b.isConstOf ``Bool.false then
    throwError "kernel_decide: the statement is false (the kernel evaluates it to `false`)"
  unless b.isConstOf ``Bool.true do
    throwError "kernel_decide: the kernel could not evaluate the statement to `true`"
  let rflTrue := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
  g.assign (mkApp3 (mkConst ``of_decide_eq_true) t inst rflTrue)
  replaceMainGoal []

/-- Decides a structural fact about a model (matching, blocks, acyclicity). -/
macro "struct_decide" : tactic => `(tactic| first | decide | kernel_decide)

/-- Checks that a lab setup gives a valid causal reading. -/
macro "setup_check" : tactic => `(tactic| first | decide | kernel_decide |
  fail "this setup has no valid causal reading: the laws cannot be matched one-to-one \
    with the variables that are not fixed (fix fewer or other variables)")

/-- A lab setup: which variables the lab holds fixed. `valid` says that the
    computed matching is a perfect matching; it is checked by evaluation. -/
structure Setup {E V : Type} {α : Type u} [DecidableEq E] [DecidableEq V] [Inhabited V]
    (M : Model E V α) where
  exo   : List V
  valid : Valid (M.struct exo) (M.order exo) := by setup_check

namespace Setup

variable {E V : Type} {α : Type u} [DecidableEq E] [DecidableEq V] [Inhabited V]
  {M : Model E V α} (S : Setup M)

/-- The computed order. -/
def cert : Cert E V := M.order S.exo

/-- The variable law `e` determines in this setup. -/
def determines (e : E) : V := S.cert.σ e

/-- The causal reading of the laws. -/
def reading : Reading M.equation M.dom := toReading _ _ S.valid (M.solversOf S.exo)

/-- The causal model of this setup. -/
def scm : SCM V α := S.reading.toSCM

/-- No cycles: every block is a single equation. -/
def Acyclic : Prop := OrderedLT (M.struct S.exo) S.cert

instance : Decidable S.Acyclic := by unfold Acyclic; infer_instance

/-- The laws in the same block as `e`. -/
def block (e : E) : List E := blockOf (M.struct S.exo) e

/-! ### Reading values off a solution -/

theorem exo_iff (v : V) : S.scm.mech v = none ↔ v ∈ S.exo := by
  have h := toReading_exo_iff (M.struct S.exo) S.cert S.valid (M.solversOf S.exo) v
  show (S.reading.read v).map Prod.snd = none ↔ v ∈ (M.struct S.exo).exo
  rw [← h]
  show _ ↔ S.reading.read v = none
  cases S.reading.read v <;> simp

/-- An exogenous variable keeps the value the lab gave it. -/
theorem exo_eq {u s : V → α} (h : S.scm.Solves u s) {v : V} (hv : v ∈ S.exo) :
    s v = u v := by
  have hs := h v
  rw [(S.exo_iff v).2 hv] at hs
  exact hs

theorem mech_determines (e : E) :
    S.scm.mech (S.determines e) = some (M.mechOf e (S.determines e)) := by
  have hi : (M.order S.exo).inv (S.determines e) = some e := (S.valid.inv_iff _ e).2 rfl
  simp [scm, Reading.toSCM, reading, toReading, hi, Model.solversOf]

/-- The variable a law determines is given by that law's formula. -/
theorem mech_eq {u s : V → α} (h : S.scm.Solves u s) (e : E) :
    s (S.determines e) = (M.mechOf e (S.determines e)).f s := by
  have hs := h (S.determines e)
  rw [S.mech_determines e] at hs
  exact hs

/-! ### Causal model versus laws -/

/-- 1. On the domain, the solutions of the causal model are exactly the states
    that satisfy every law and have the exogenous values. -/
theorem solves_iff (u s : V → α) (hD : M.dom s) :
    S.scm.Solves u s ↔ M.Sat s ∧ ∀ v, v ∈ S.exo → s v = u v := by
  rw [scm, S.reading.solves_iff u s hD]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun v hv => h2 v ((toReading_exo_iff _ _ S.valid _ v).2 hv)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun v hv => h2 v ((toReading_exo_iff _ _ S.valid _ v).1 hv)⟩

/-- 2. Observational equivalence: any two setups of the same model allow the
    same states. The causal order is not visible in the data. -/
theorem obs_equiv (S₁ S₂ : Setup M) (s : V → α) (hD : M.dom s) :
    (∃ u, S₁.scm.Solves u s) ↔ (∃ u, S₂.scm.Solves u s) := by
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨s, (S₂.solves_iff s s hD).2 ⟨((S₁.solves_iff u s hD).1 hu).1, fun _ _ => rfl⟩⟩
  · rintro ⟨u, hu⟩
    exact ⟨s, (S₁.solves_iff s s hD).2 ⟨((S₂.solves_iff u s hD).1 hu).1, fun _ _ => rfl⟩⟩

/-! ### Interventions -/

theorem read_ne_iff (x : V) (e : E) :
    (∀ m, S.reading.read x ≠ some (e, m)) ↔ S.determines e ≠ x := by
  show (∀ m, (S.cert.inv x).map (fun e => (e, M.mechOf e x)) ≠ some (e, m)) ↔ S.cert.σ e ≠ x
  constructor
  · intro h hx
    have hi : S.cert.inv x = some e := (S.valid.inv_iff x e).2 hx
    exact h (M.mechOf e x) (by simp [hi])
  · intro h m hm
    cases hi : S.cert.inv x with
    | none => simp [hi] at hm
    | some e' =>
      simp only [hi, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨rfl, -⟩ := hm
      exact h ((S.valid.inv_iff x e').1 hi)

/-- 3. Graph surgery = equation surgery: after do(x := c), x = c, every law that
    does not determine x still holds, and the other exogenous variables keep
    their values. -/
theorem do_iff (x : V) (c : α) (u s : V → α) (hD : M.dom s) :
    (S.scm.doI x c).Solves u s ↔
      s x = c ∧ (∀ e, S.determines e ≠ x → M.law e s) ∧
      (∀ v, v ≠ x → v ∈ S.exo → s v = u v) := by
  rw [scm, S.reading.doI_iff x c u s hD]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun e he => h2 e ((S.read_ne_iff x e).2 he), fun v hvx hv => ?_⟩
    exact h3 v hvx ((toReading_exo_iff _ _ S.valid _ v).2 hv)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun e he => h2 e ((S.read_ne_iff x e).1 he), fun v hvx hv => ?_⟩
    exact h3 v hvx ((toReading_exo_iff _ _ S.valid _ v).1 hv)

/-- 4. Intervening on an exogenous variable is just a new exogenous value. -/
theorem do_exo_iff {x : V} (hx : x ∈ S.exo) (c : α) (u s : V → α) :
    (S.scm.doI x c).Solves u s ↔ S.scm.Solves (Function.update u x c) s :=
  SCM.doI_exo_iff _ c u s ((S.exo_iff x).2 hx)

/-! ### Acyclic setups: exactly one outcome -/

theorem recursive (hA : S.Acyclic) : S.scm.Recursive (rankV S.cert) :=
  toReading_recursive _ _ S.valid _ hA

/-- 5. Uniqueness. -/
theorem unique (hA : S.Acyclic) {u s t : V → α} (hs : S.scm.Solves u s)
    (ht : S.scm.Solves u t) : s = t :=
  (S.recursive hA).unique hs ht

/-- 6. Existence. -/
theorem exists_solution (hA : S.Acyclic) (u : V → α) : ∃ s, S.scm.Solves u s :=
  (S.recursive hA).exists u

/-- 7. Every intervention has exactly one outcome. -/
theorem do_existsUnique (hA : S.Acyclic) (x : V) (c : α) (u : V → α) :
    ∃! s, (S.scm.doI x c).Solves u s := by
  have hr := (S.recursive hA).doI x c
  obtain ⟨s, hs⟩ := hr.exists u
  exact ⟨s, hs, fun t ht => hr.unique ht hs⟩

/-- 7b. Exactly one outcome, for the setup itself. -/
theorem existsUnique (hA : S.Acyclic) (u : V → α) : ∃! s, S.scm.Solves u s := by
  obtain ⟨s, hs⟩ := S.exists_solution hA u
  exact ⟨s, hs, fun t ht => S.unique hA ht hs⟩

/-! ### Cyclic setups -/

/-- 8. If the laws, with the exogenous values fixed, have at most one solution
    on the domain, so does the causal model. For a cyclic block this is the
    domain-specific part (a determinant, monotonicity, a fixed point theorem …). -/
theorem unique_of_laws
    (huniq : ∀ s t, M.dom s → M.dom t → M.Sat s → M.Sat t →
      (∀ v, v ∈ S.exo → s v = t v) → s = t)
    {u s t : V → α} (hDs : M.dom s) (hDt : M.dom t)
    (hs : S.scm.Solves u s) (ht : S.scm.Solves u t) : s = t := by
  obtain ⟨hs1, hs2⟩ := (S.solves_iff u s hDs).1 hs
  obtain ⟨ht1, ht2⟩ := (S.solves_iff u t hDt).1 ht
  exact huniq s t hDs hDt hs1 ht1 fun v hv => (hs2 v hv).trans (ht2 v hv).symm

/-- 8b. A solution of the causal model that lies in the domain satisfies the laws. -/
theorem sat_of_solves {u s : V → α} (hs : S.scm.Solves u s) (hD : M.dom s) : M.Sat s :=
  ((S.solves_iff u s hD).1 hs).1

/-- 8c. From the causal model back to the laws: if the causal model has exactly
    one outcome and that outcome lies in the domain, then the laws, with the
    exogenous values fixed, have exactly one solution in the domain. -/
theorem laws_existsUnique {u : V → α} (h : ∃! s, S.scm.Solves u s)
    (hD : ∀ s, S.scm.Solves u s → M.dom s) :
    ∃! s, M.dom s ∧ M.Sat s ∧ ∀ v, v ∈ S.exo → s v = u v := by
  obtain ⟨s, hs, huniq⟩ := h
  refine ⟨s, ⟨hD s hs, (S.solves_iff u s (hD s hs)).1 hs⟩, ?_⟩
  rintro t ⟨htD, htS, htE⟩
  exact huniq t ((S.solves_iff u t htD).2 ⟨htS, htE⟩)

/-- 9. Dulmage–Mendelsohn: if the structure is uniform (each law is solved for
    one of its variables and then reads the others, checked by `decide`), the
    dependency between laws is the same for every valid matching. -/
theorem blocks_independent (hu : DM.Uniform (M.struct S.exo) M.eqVars)
    (c : Cert E V) (hc : Valid (M.struct S.exo) c) (x e : E) :
    DM.Reach (fun e v => v ∈ M.eqVars e) S.cert.σ x e ↔
      DM.Reach (fun e v => v ∈ M.eqVars e) c.σ x e :=
  DM.blocks_independent hu S.valid hc x e

/-! ### Reading a solution off, variable by variable -/

/-- What the causal model says variable `v` equals: its exogenous value, or the
    formula of the law that determines it. -/
def rhs (u s : V → α) (v : V) : α :=
  match S.cert.inv v with
  | none => u v
  | some e => (M.mechOf e v).f s

theorem scm_mech (v : V) : S.scm.mech v = (S.cert.inv v).map fun e => M.mechOf e v := by
  simp only [scm, Reading.toSCM, reading, toReading, Model.solversOf, cert, Option.map_map]
  rfl

theorem value_eq {u s : V → α} (h : S.scm.Solves u s) (v : V) : s v = S.rhs u s v := by
  have hv := h v
  rw [S.scm_mech v] at hv
  unfold rhs
  cases hi : S.cert.inv v with
  | none => rw [hi] at hv; exact hv
  | some e => rw [hi] at hv; exact hv

/-- Conversely, a state that takes the value the model assigns to every variable
    is a solution. -/
theorem solves_of_values {u s : V → α} (h : ∀ v, s v = S.rhs u s v) : S.scm.Solves u s := by
  intro v
  have hv := h v
  rw [S.scm_mech v]
  unfold rhs at hv
  cases hi : S.cert.inv v with
  | none => rw [hi] at hv; exact hv
  | some e => rw [hi] at hv; exact hv

theorem do_value_eq {x : V} {c : α} {u s : V → α} (h : (S.scm.doI x c).Solves u s) (v : V) :
    s v = if v = x then c else S.rhs u s v := by
  by_cases hvx : v = x
  · subst hvx
    simp only [ite_true]
    exact SCM.doI_self _ v c u s h
  · simp only [hvx, ite_false]
    have hv := h v
    rw [SCM.doI_mech_ne _ c hvx, S.scm_mech v] at hv
    unfold rhs
    cases hi : S.cert.inv v with
    | none => rw [hi] at hv; exact hv
    | some e => rw [hi] at hv; exact hv

theorem rhs_none {u s : V → α} {v : V} (h : S.cert.inv v = none) : S.rhs u s v = u v := by
  simp [rhs, h]

theorem rhs_some {u s : V → α} {v : V} {e : E} (h : S.cert.inv v = some e) :
    S.rhs u s v = (M.mechOf e v).f s := by
  simp [rhs, h]

end Setup

/- From here on the causal model of a setup is used only through the theorems
   above. Making it irreducible stops Lean from re-running the matching
   algorithm symbolically whenever it inspects a solution. -/
attribute [irreducible] Setup.scm

end Lang
end CausalPhys
