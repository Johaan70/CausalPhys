/-
# Soundness of d-separation (Verma–Pearl) — proof skeleton

## For the assistant filling this in

This file is a **decomposition**, not a proof. Every `sorry` is a separate
task. Work bottom-up: Layer 0 → Layer 1 → Layer 2 → Layer 3 → final.
Do not attempt `dsep_sound` directly; it is a short composition once the
layers below are closed.

Existing `PearlDoCalculus` definitions this file builds on, with their
verified signatures:

    DAG.lean
      structure DAG (V) [DecidableEq V] [Fintype V]
      DAG.edge : V → V → Prop          -- lowercase
      DAG.rank : V → ℕ
      DAG.parents (G) (v) : Finset V

    Reachability.lean
      DAG.Reaches (G) : V → V → Prop
      Reaches.refl, Reaches.of_edge, Reaches.trans
      rank_le_of_reaches, not_reaches_of_edge

    Walks.lean
      inductive DAG.Walk (G) : V → V → Type u
        | nil (v) : Walk G v v
        | fwd {a b c} : G.edge a b → Walk G b c → Walk G a c
        | bwd {a b c} : G.edge b a → Walk G b c → Walk G a c
      Walk.length, Walk.support : Walk G a b → List V

    Blocking.lean
      Walk.blockedAux, Walk.Blocked, Walk.Open

    DSeparation.lean
      DAG.DSeparated (G) (Z : Finset V) (x y : V) : Prop

    CausalModel.lean
      structure CausalModel (G : DAG V) (α : V → Type v)
      Assignment (S : Finset V) : Type (max u v) := ∀ v : {v // v ∈ S}, α v.1
      Assignment.restrict {S T} (h : T ⊆ S) : Assignment S → Assignment T
      Assignment.extend
      marginal (M) (S : Finset V) : PMF (Assignment (α := α) S)
      jointUpTo, fullJoint
      CondIndep (M) (X Y Z : Finset V) : Prop

**`marginal` returns a `PMF`, not a value.** Write `(M.marginal S) a`, with
the assignment applied to the PMF. `M.marginal S a` also elaborates but is
easy to misread; keep the parentheses.

**Namespaces.** Everything above lives under `PearlDoCalculus.DAG` or
`PearlDoCalculus`. Do *not* `open DAG` here — it shadows `CausalModel` and
`CondIndep` and turns them into field projections on `G`, which produces a
cascade of "invalid field" errors. `set_option autoImplicit false` is on so
a typo is an error rather than a silently invented variable.

Three properties of the existing code shape everything below.

1. `DAG.Walk` is an inductive *Type*, not a list. All induction in Layer 2
   goes over `nil`/`fwd`/`bwd`. `fwd` steps with the arrow along travel,
   `bwd` against it. A collider at `m` is: arrived by `fwd`, departs by
   `bwd`.

2. `blockedAux` threads an `Incoming` state through the walk. Its collider
   case reads

       | .fwd, m, _, .bwd _ rest => (∀ z ∈ Z, ¬ G.Reaches m z) ∨ ...

   so "this collider is open" unfolds to `∃ z ∈ Z, G.Reaches m z`.
   Layer 2's central lemma is exactly that existential.

3. `CondIndep` is stated multiplicatively:

       P(X∪Y∪Z) · P(Z) = P(X∪Z) · P(Y∪Z)

   No division, no positivity hypotheses. A deliberate choice that avoids
   `ENNReal` division entirely, so Layer 3 lands directly in the target
   form. Do not reformulate it as a quotient.

## Proof strategy: moralisation, not walk induction

The `CausalModel.lean` docstring proposes structural induction directly
over blocked/active walks. That is how Pearl presents the result and it is
the harder path to formalise: because `blockedAux` carries state, being
blocked is not local to a single step, and the naive induction hypothesis
does not close.

This skeleton takes the Lauritzen route instead:

    d-separation in G
      ⟹ (restrict to ancestral subgraph)
    d-separation in G.induce (ancestors G ({x,y} ∪ Z))
      ⟹ (moralise)
    vertex separation in moralGraph
      ⟹ (factorisation splits along a separator)
    conditional independence

Graph content sits in Layer 2, probabilistic content in Layers 1 and 3.
They are independent and can be worked in parallel.

## Difficulty map

    Layer 0   routine       induce, ancestral sets, moral graph, cliques
    Layer 1   HARD          marginalisation onto an ancestral set
    Layer 2   HARDEST       d-separation ↔ moral separation
    Layer 3   medium        product form ⟹ CondIndep
    Final     short         composition

If Layer 2 resists, the induction is stated wrong. Change the statement
before fighting the tactic.

## Arithmetic warning

`jointUpTo` and `marginal` land in `ENNReal`, not `ℝ≥0`. Lemmas proved for
`ℝ≥0` do not apply and fail in confusing ways — `div_lt_one`, `norm_num` on
fractions, and `decide` on numerals all behave differently. When a goal
looks like it should close but does not, run `set_option pp.all true` and
read the type before reaching for another tactic. `ENNReal.div_lt_iff` and
`tsub_eq_zero_iff_le` are the workhorses; truncated subtraction is a trap.

## Placeholder convention

Hypotheses whose exact form is not yet known are written `True` rather than
`sorry`. A `sorry` in hypothesis position makes the whole declaration a
non-proposition and Lean rejects it outright. Replace each `True` with the
real statement as it becomes clear, working from the layer below.
-/

import PearlDoCalculus.CausalModel
import PearlDoCalculus.DSeparation
import PearlDoCalculus.Blocking
import PearlDoCalculus.Walks
import PearlDoCalculus.Reachability
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Combinatorics.SimpleGraph.Clique
set_option pp.proofs true
set_option autoImplicit false

namespace PearlDoCalculus

universe u v

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : V → Type v}
variable {G : DAG V}

open Classical
open DAG DAG.CausalModel
/-! ## Layer 0 — induced subgraphs, ancestral sets, moral graph

Nothing here is deep, but `DAG.induce` does not exist yet and everything
downstream needs it. Start here: if Layer 0 does not typecheck, the rest
of the file is built on sand.
-/

/--
Induced subgraph on `A`: keep only edges with both endpoints in `A`.

`DAG` carries `rank` plus whatever acyclicity condition `DAG.lean` imposes
(see lines 39–56). Reuse `G.rank` unchanged — the induced edge relation is
a subrelation, so any rank condition holding for `G` still holds.
-/
def DAG.induce (G : DAG V) (A : Finset V) : DAG V where
  edge u v := u ∈ A ∧ v ∈ A ∧ G.edge u v
  decEdge := by infer_instance
  rank := G.rank
  rank_strict_mono := by
    intro u v h
    exact G.rank_strict_mono u v h.2.2

/-- Edges of the induced subgraph are edges of `G`. -/
lemma DAG.induce_edge {A : Finset V} {u w : V}
    (h : (DAG.induce G A).edge u w) : G.edge u w := by
  exact h.2.2

/-- Reachability in the induced subgraph implies reachability in `G`. -/
lemma DAG.induce_reaches {A : Finset V} {u w : V}
    (h : (DAG.induce G A).Reaches u w) : G.Reaches u w := by
  exact Relation.ReflTransGen.mono (fun _ _ e => DAG.induce_edge e) _ _ h

/--
Ancestors of `S`: every vertex reaching some element of `S`. Contains `S`
by `Reaches.refl`. Decidability of the filter comes from `open Classical`.
-/
noncomputable def ancestors (G : DAG V) (S : Finset V) : Finset V :=
  Finset.univ.filter (fun v => ∃ s ∈ S, G.Reaches v s)

lemma mem_ancestors_iff {S : Finset V} {v : V} :
    v ∈ ancestors G S ↔ ∃ s ∈ S, G.Reaches v s := by
  simp [ancestors]
/-- `S ⊆ ancestors G S`, by `Reaches.refl`. -/
lemma subset_ancestors (S : Finset V) : S ⊆ ancestors G S := by
  intro s hs
  simp [ancestors]
  exact ⟨s, hs, DAG.Reaches.refl G s⟩

/-- Closure under parents, via `Reaches.of_edge` and `Reaches.trans`.
Short, but it does need proving — it does not come for free. -/
lemma ancestors_parent_closed {S : Finset V} {v w : V}
    (hv : v ∈ ancestors G S) (hw : G.edge w v) : w ∈ ancestors G S := by
  simp [ancestors] at hv ⊢
  obtain ⟨s, hs, hvs⟩ := hv
  exact ⟨s, hs, DAG.Reaches.trans G (DAG.Reaches.of_edge G hw) hvs⟩

/-- Idempotence, via `Reaches.trans`. -/
lemma ancestors_ancestors (S : Finset V) :
    ancestors G (ancestors G S) = ancestors G S := by
  apply Finset.Subset.antisymm
  · intro v hv
    simp [ancestors] at hv ⊢
    obtain ⟨t, ⟨s, hs, hts⟩, hvt⟩ := hv
    exact ⟨s, hs, DAG.Reaches.trans G hvt hts⟩
  · exact subset_ancestors _

/--
Moral graph on `A`: `G`'s edges with direction forgotten, plus a marriage
edge between any two parents of a common child in `A`.

Marriage edges are exactly the colliders. That correspondence is the whole
point of the construction and drives Layer 2.
-/
noncomputable def moralGraph (G : DAG V) (A : Finset V) : SimpleGraph V :=
  SimpleGraph.fromRel (fun u w =>
    u ∈ A ∧ w ∈ A ∧
      (G.edge u w ∨ ∃ c ∈ A, G.edge u c ∧ G.edge w c))

/-- Vertex separation: every walk from `x` to `y` meets `Z`.
Defined free-standing — one cannot extend `SimpleGraph`'s namespace with
dot notation from here. -/
def Separates (H : SimpleGraph V) (Z : Finset V) (x y : V) : Prop :=
  ∀ p : H.Walk x y, ∃ z ∈ Z, z ∈ p.support

/-- The family `{v} ∪ parents v` is a clique in the moral graph.
`IsClique` wants a `Set V`, hence the coercion. -/
lemma moral_family_clique (A : Finset V) (v : V) (hv : v ∈ A)
    (hpa : ∀ w ∈ G.parents v, w ∈ A) :
    (moralGraph G A).IsClique (↑(insert v (G.parents v)) : Set V) := by
  intro a ha b hb hab
  simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe,
    DAG.parents, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  simp only [moralGraph, SimpleGraph.fromRel_adj]
  refine ⟨hab, ?_⟩
  rcases ha with rfl | ha
  · rcases hb with rfl | hb
    · exact absurd rfl hab
    · exact Or.inr ⟨hpa b (by simp [DAG.parents, hb]), hv, Or.inl hb⟩
  · rcases hb with rfl | hb
    · exact Or.inl ⟨hpa a (by simp [DAG.parents, ha]), hv, Or.inl ha⟩
    · exact Or.inl ⟨hpa a (by simp [DAG.parents, ha]),
        hpa b (by simp [DAG.parents, hb]), Or.inr ⟨v, hv, ha, hb⟩⟩
/-! ## Layer 1 — ancestral reduction

Marginalising the joint onto an ancestrally closed set yields the joint of
the induced model.

**Use `G.rank`.** `rank_le_of_reaches` gives strong induction on the
maximum rank among non-ancestors without constructing a topological order.

Sketch: let `v` be a non-ancestor of maximal rank. No vertex of `A` has
`v` as a parent — otherwise `v` would be an ancestor. So `v` occurs in
exactly one factor, `P(v | parents v)`, which sums to 1 over `α v`. Sum it
out and recurse. `PMF.bind`, `Finset.sum_comm` and `tsum_eq_sum` do the
work.
-/
/-- For noder i en ancestralt lukket mengde er foreldrene uendret av `induce`. -/
lemma DAG.induce_parents_eq (A : Finset V)
    (hA : ∀ v ∈ A, ∀ w, G.edge w v → w ∈ A) (v : V) (hv : v ∈ A) :
    (DAG.induce G A).parents v = G.parents v := by
  ext u
  rw [DAG.parents, DAG.parents, Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  show (u ∈ A ∧ v ∈ A ∧ G.edge u v) ↔ G.edge u v
  constructor
  · exact fun h => h.2.2
  · exact fun he => ⟨hA v hv u he, hv, he⟩
/-- Indikatoren `b = extend asg x` bestemmer både `asg` og `x` entydig.
Nøkkelen til å kollapse dobbeltsummen i `extendOverList`. -/
lemma extend_eq_iff (S : Finset V) (v : V) (hvS : v ∉ S)
    (b : Assignment (α := α) (insert v S))
    (asg : Assignment (α := α) S) (x : α v) :
    (Assignment.extend asg x = b) ↔
      (asg = b.restrict (Finset.subset_insert v S) ∧
       x = b ⟨v, Finset.mem_insert_self v S⟩) := by
  constructor
  · intro hb
    subst hb
    constructor
    · funext u
      simp [Assignment.extend, Assignment.restrict]
      intro hu
      exact absurd (hu ▸ u.2) hvS
    · simp [Assignment.extend]
  · rintro ⟨h1, h2⟩
    subst h1
    subst h2
    funext u
    by_cases hv : u.1 = v
    · have : u = ⟨v, Finset.mem_insert_self v S⟩ := Subtype.ext hv
      subst this
      simp [Assignment.extend]
    · have huS : u.1 ∈ S := by
        rcases Finset.mem_insert.mp u.2 with h | h
        · exact absurd h hv
        · exact h
      simp [Assignment.extend, Assignment.restrict, hv, huS]

/-- `extendOverList` på tom liste er punktmassen på `base`.

Merk teknikken for `cast`: `rw! (castMode := .all)` flytter mengden, og
`simp [eqRec_eq_cast, cast_cast]` opphever transportene. Den kombinasjonen
er nøkkelen til alt arbeid med `extendOverList` og `jointUpTo`. -/
lemma extendOverList_nil (M : CausalModel G α) (B : Finset V)
    (base : Assignment (α := α) B)
    (hpar : ∀ v ∈ ([] : List V), G.parents v ⊆ B)
    (a : Assignment (α := α) (B ∪ ([] : List V).toFinset)) :
    (extendOverList M B base [] hpar) a = if a = cast (by simp) base then 1 else 0 := by
  have hB : B ∪ ([] : List V).toFinset = B := by simp
  have key : ∀ (S : Finset V) (h : S = B) (a : Assignment (α := α) S),
      (cast (congrArg (fun S => PMF (Assignment (α := α) S)) h.symm) (PMF.pure base)) a
        = if a = cast (congrArg (fun S => Assignment (α := α) S) h.symm) base then 1 else 0 := by
    intro S h a
    subst h
    simp [PMF.pure_apply]
  exact key _ hB a
/-- Flytter en `cast` fra den ene siden av en likhet til den andre. -/
lemma cast_eq_iff_eq_cast_symm {A B : Sort _} (h : A = B) (b : A) (a : B) :
    (cast h b = a) ↔ (b = cast h.symm a) := by
  subst h
  simp

/-- `extendOverList` på en ikke-tom liste faktoriserer: halens fordeling
ganger kjernen for hodet. Kjeden av `cast`-omskrivinger er den samme som i
`extendOverList_nil`, med `extend_eq_iff` for kollapsen. -/
lemma extendOverList_cons (M : CausalModel G α) (B : Finset V)
    (base : Assignment (α := α) B) (v : V) (vs : List V)
    (hpar : ∀ w ∈ (v :: vs), G.parents w ⊆ B)
    (hv : v ∉ B ∪ vs.toFinset)
    (htype : Assignment (α := α) (insert v (B ∪ vs.toFinset))
      = Assignment (α := α) (B ∪ (v :: vs).toFinset))
    (a : Assignment (α := α) (B ∪ (v :: vs).toFinset)) :
    (extendOverList M B base (v :: vs) hpar) a =
      (extendOverList M B base vs (fun w hw => hpar w (List.mem_cons_of_mem v hw)))
        ((cast htype.symm a).restrict (Finset.subset_insert v (B ∪ vs.toFinset))) *
      (M.kernel v (((cast htype.symm a).restrict
          (Finset.subset_insert v (B ∪ vs.toFinset))).restrict
          (fun x hx => Finset.mem_union_left _ (hpar v List.mem_cons_self hx))))
        ((cast htype.symm a) ⟨v, Finset.mem_insert_self v (B ∪ vs.toFinset)⟩) := by
  simp only [extendOverList, PMF.bind_apply, PMF.map_apply, eq_comm (a := a)]
  simp only [cast_eq_iff_heq]
  simp only [← cast_eq_iff_heq (e := htype)]
  simp only [cast_eq_iff_eq_cast_symm]
  simp only [extend_eq_iff _ v hv]
  simp only [and_comm, ite_and, tsum_ite_eq]
  simp only [mul_ite, mul_zero, tsum_ite_eq]
/-- `extendOverList_cons` uttrykt med tilordningen på `insert`-formen.
Flytter transporten til kallstedet, så høyresiden er fri for `cast`. -/
lemma extendOverList_cons' (M : CausalModel G α) (B : Finset V)
    (base : Assignment (α := α) B) (v : V) (vs : List V)
    (hpar : ∀ w ∈ (v :: vs), G.parents w ⊆ B)
    (hv : v ∉ B ∪ vs.toFinset)
    (htype : Assignment (α := α) (insert v (B ∪ vs.toFinset))
      = Assignment (α := α) (B ∪ (v :: vs).toFinset))
    (b : Assignment (α := α) (insert v (B ∪ vs.toFinset))) :
    (extendOverList M B base (v :: vs) hpar) (cast htype b) =
      (extendOverList M B base vs (fun w hw => hpar w (List.mem_cons_of_mem v hw)))
        (b.restrict (Finset.subset_insert v (B ∪ vs.toFinset))) *
      (M.kernel v ((b.restrict (Finset.subset_insert v (B ∪ vs.toFinset))).restrict
          (fun x hx => Finset.mem_union_left _ (hpar v List.mem_cons_self hx))))
        (b ⟨v, Finset.mem_insert_self v (B ∪ vs.toFinset)⟩) := by
  have h := extendOverList_cons M B base v vs hpar hv htype (cast htype b)
  simpa using h


/-- Likhet mellom tilordninger splitter i `L`- og `R`-delene når `L ∪ R`
dekker mengden. Grunnlaget for `nil`-tilfellet i faktoriseringen. -/
lemma assignment_eq_iff_inter (L R B : Finset V) (hLR : B ⊆ L ∪ R)
    (base b : Assignment (α := α) B) :
    (b = base) ↔
      (b.restrict (Finset.inter_subset_right (s₁ := L)) =
         base.restrict (Finset.inter_subset_right (s₁ := L)) ∧
       b.restrict (Finset.inter_subset_right (s₁ := R)) =
         base.restrict (Finset.inter_subset_right (s₁ := R))) := by
  constructor
  · intro h
    subst h
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    funext u
    rcases Finset.mem_union.mp (hLR u.2) with hu | hu
    · exact congrFun h1 ⟨u.1, Finset.mem_inter.mpr ⟨hu, u.2⟩⟩
    · exact congrFun h2 ⟨u.1, Finset.mem_inter.mpr ⟨hu, u.2⟩⟩
/-- Kjernen av `nil`-tilfellet for den styrkede faktoriseringen: indikatoren
på likhet splitter i et produkt av `L`- og `R`-indikatorer, med `base` som
eksplisitt argument.

Formulert helt over `B`, uten `B ∪ [].toFinset`, så ingen transport oppstår.
Koblingen til `extendOverList_nil` gjøres separat. -/
lemma indicator_splits (L R B : Finset V) (hLR : B ⊆ L ∪ R) :
    ∃ (F : Assignment (α := α) (L ∩ B) → Assignment (α := α) (L ∩ B) → ENNReal)
      (Gf : Assignment (α := α) (R ∩ B) → Assignment (α := α) (R ∩ B) → ENNReal),
      ∀ (base a : Assignment (α := α) B),
        (if a = base then (1 : ENNReal) else 0) =
          F (base.restrict Finset.inter_subset_right)
            (a.restrict Finset.inter_subset_right) *
          Gf (base.restrict Finset.inter_subset_right)
            (a.restrict Finset.inter_subset_right) := by
  refine ⟨fun bp p => if p = bp then 1 else 0,
          fun bq q => if q = bq then 1 else 0, ?_⟩
  intro base a
  rw [assignment_eq_iff_inter L R B hLR base a]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← ite_and]
  congr 1
  exact propext and_comm


/-- Foreldrene til `v` ligger i `L`-snittet når familieklikken gjør det. -/
lemma parents_subset_inter (L B : Finset V) (v : V) (vs : List V)
    (hparv : G.parents v ⊆ B) (hcl : insert v (G.parents v) ⊆ L) :
    G.parents v ⊆ L ∩ (B ∪ (v :: vs).toFinset) := by
  intro x hx
  refine Finset.mem_inter.mpr ⟨?_, ?_⟩
  · exact hcl (Finset.mem_insert_of_mem hx)
  · exact Finset.mem_union_left _ (hparv hx)

/-- `v` selv ligger i `L`-snittet når familieklikken gjør det. -/
lemma self_mem_inter (L B : Finset V) (v : V) (vs : List V)
    (hcl : insert v (G.parents v) ⊆ L) :
    v ∈ L ∩ (B ∪ (v :: vs).toFinset) := by
  refine Finset.mem_inter.mpr ⟨hcl (Finset.mem_insert_self _ _), ?_⟩
  simp

/-- Snittet vokser når listen vokser. -/
lemma inter_mono_cons (L B : Finset V) (v : V) (vs : List V) :
    L ∩ (B ∪ vs.toFinset) ⊆ L ∩ (B ∪ (v :: vs).toFinset) := by
  intro x hx
  rcases Finset.mem_inter.mp hx with ⟨hL, hBvs⟩
  refine Finset.mem_inter.mpr ⟨hL, ?_⟩
  rcases Finset.mem_union.mp hBvs with h | h
  · exact Finset.mem_union_left _ h
  · exact Finset.mem_union_right _ (by simp at h ⊢; tauto)
/-- Verteksmengden vokser med rangnivået. -/
lemma verticesUpTo_mono_succ (n : ℕ) :
    G.verticesUpTo n ⊆ G.verticesUpTo (n + 1) := by
  intro x hx
  simp only [verticesUpTo, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  omega

/-- Snittet med en fast mengde vokser tilsvarende. -/
lemma inter_verticesUpTo_mono_succ (S : Finset V) (n : ℕ) :
    S ∩ G.verticesUpTo n ⊆ S ∩ G.verticesUpTo (n + 1) := by
  intro x hx
  rcases Finset.mem_inter.mp hx with ⟨h1, h2⟩
  exact Finset.mem_inter.mpr ⟨h1, verticesUpTo_mono_succ n h2⟩

/-- Snitt distribuerer over union. -/
lemma union_inter_distrib (L Z S : Finset V) :
    (L ∪ Z) ∩ S = (L ∩ S) ∪ (Z ∩ S) := by
  ext x
  simp [Finset.mem_inter, Finset.mem_union]
  tauto

/-- Disjunkthet bevares under snitt. -/
lemma disjoint_inter_of_disjoint (L Z S : Finset V) (hLZ : Disjoint L Z) :
    Disjoint (L ∩ S) (Z ∩ S) :=
  Finset.disjoint_of_subset_left Finset.inter_subset_left
    (Finset.disjoint_of_subset_right Finset.inter_subset_left hLZ)
/-- Tilordninger over en disjunkt union splitter i et produkt. -/
def assignmentSplit (s t : Finset V) (h : Disjoint s t) :
    Assignment (α := α) (s ∪ t) ≃ Assignment (α := α) s × Assignment (α := α) t := by
  unfold Assignment
  exact (Equiv.piCongrLeft _ (Equiv.Finset.union s t h)).symm.trans
    (Equiv.sumPiEquivProdPi _)

/-- Sett sammen en `L`-del og en `Z`-del til en tilordning på `(L ∪ Z) ∩ S`. -/
noncomputable def joinInter (L Z S : Finset V)
    (p : Assignment (α := α) (L ∩ S)) (q : Assignment (α := α) (Z ∩ S)) :
    Assignment (α := α) ((L ∪ Z) ∩ S) :=
  fun u =>
    if h : u.1 ∈ L then
      p ⟨u.1, Finset.mem_inter.mpr ⟨h, (Finset.mem_inter.mp u.2).2⟩⟩
    else
      q ⟨u.1, Finset.mem_inter.mpr ⟨by
        rcases Finset.mem_union.mp (Finset.mem_inter.mp u.2).1 with hL | hZ
        · exact absurd hL h
        · exact hZ, (Finset.mem_inter.mp u.2).2⟩⟩
/-- `joinInter` av de to restriksjonene er restriksjonen til `(L ∪ Z) ∩ S`.
Dette er koblingen `jointUpTo_factorizes` trenger. -/
lemma joinInter_restrict (L Z S : Finset V) (a : Assignment (α := α) S) :
    joinInter L Z S (a.restrict Finset.inter_subset_right)
      (a.restrict Finset.inter_subset_right)
      = a.restrict (Finset.inter_subset_right (s₁ := L ∪ Z)) := by
  funext u
  unfold joinInter Assignment.restrict
  by_cases h : u.1 ∈ L <;> simp [h]
/-- Å anvende en transportert `PMF` er å anvende originalen på det
tilbaketransporterte argumentet. -/
lemma cast_pmf_apply (S T : Finset V) (hset : S = T)
    (htype : PMF (Assignment (α := α) S) = PMF (Assignment (α := α) T))
    (htype2 : Assignment (α := α) T = Assignment (α := α) S)
    (p : PMF (Assignment (α := α) S)) (a : Assignment (α := α) T) :
    (cast htype p) a = p (cast htype2 a) := by
  subst hset
  simp
/-- En produktfaktorisering overlever transport langs en mengdelikhet.
Samler transporten på ett sted framfor å spre den utover beviset. -/
lemma transport_factorization (S T A B : Finset V) (hS : S = T)
    (F0 : Assignment (α := α) A → ENNReal)
    (Gf0 : Assignment (α := α) B → ENNReal)
    (rA : Assignment (α := α) S → Assignment (α := α) A)
    (rB : Assignment (α := α) S → Assignment (α := α) B)
    (p : PMF (Assignment (α := α) S))
    (h : ∀ x : Assignment (α := α) S, p x = F0 (rA x) * Gf0 (rB x)) :
    ∀ y : Assignment (α := α) T,
      (hS ▸ p) y = F0 ((hS ▸ rA) y) * Gf0 ((hS ▸ rB) y) := by
  subst hS
  simpa using h
/-- `cast` på en funksjon flyttes til argumentet. -/
lemma cast_fun_apply (S T A : Finset V) (hS : S = T)
    (htype : (Assignment (α := α) S → Assignment (α := α) A)
      = (Assignment (α := α) T → Assignment (α := α) A))
    (h2 : Assignment (α := α) T = Assignment (α := α) S)
    (f : Assignment (α := α) S → Assignment (α := α) A)
    (y : Assignment (α := α) T) :
    (cast htype f) y = f (cast h2 y) := by
  subst hS
  simp
/-- `jointUpTo` på nivå 0, med transporten skjult.

Eksponerer `extendOverList` direkte, slik at klientbevis slipper å håndtere
`cast`. Dette er mønsteret Mathlib bruker: `cast` i implementasjonen, rent
API utenpå. Å kjede sammen transportlemmaer i hvert klientbevis kostet flere
økter uten å lykkes; å samle transporten her gikk på første forsøk. -/
lemma jointUpTo_zero_apply (M : CausalModel G α)
    (a : Assignment (α := α) (G.verticesUpTo 0)) :
    (jointUpTo M 0) a =
      (M.extendOverList ∅ (fun v => absurd (jointUpTo._proof_2 v) (jointUpTo._proof_3 v))
        (G.verticesUpTo 0).toList jointUpTo._proof_4)
        (cast (by simp) a) := by
  unfold jointUpTo
  rw [cast_pmf_apply _ _ (by simp)]
/-- `jointUpTo` på nivå `n+1`, med transporten skjult.

Merk `conv_lhs`: et vanlig `unfold jointUpTo` ruller også ut `jointUpTo M n`
på høyresiden, og da matcher sidene aldri. Ni forsøk gikk med til å lete
etter feil i transporten før det viste seg å være dette. -/
lemma jointUpTo_succ_apply (M : CausalModel G α) (n : ℕ)
    (hset : G.verticesUpTo n ∪ (G.newAtRank (n + 1)).toList.toFinset = G.verticesUpTo (n + 1))
    (htype2 : Assignment (α := α) (G.verticesUpTo (n + 1))
      = Assignment (α := α) (G.verticesUpTo n ∪ (G.newAtRank (n + 1)).toList.toFinset))
    (a : Assignment (α := α) (G.verticesUpTo (n + 1))) :
    (jointUpTo M (n + 1)) a =
      ((M.jointUpTo n).bind fun asg =>
        M.extendOverList (G.verticesUpTo n) asg (G.newAtRank (n + 1)).toList
          (jointUpTo._proof_6 n))
        (cast htype2 a) := by
  conv_lhs => unfold jointUpTo
  rw [cast_pmf_apply _ _ hset _ htype2]
/-- `fullJoint` med transporten skjult. Samme mønster som
`jointUpTo_zero_apply` og `jointUpTo_succ_apply`. -/
lemma fullJoint_apply (M : CausalModel G α)
    (htype2 : Assignment (α := α) (Finset.univ : Finset V)
      = Assignment (α := α) (G.verticesUpTo G.maxRank))
    (a : Assignment (α := α) (Finset.univ : Finset V)) :
    (M.fullJoint) a = (jointUpTo M G.maxRank) (cast htype2 a) := by
  unfold fullJoint
  rw [cast_pmf_apply _ _ G.verticesUpTo_maxRank _ htype2]




/-- Restriksjon av en transportert tilordning er restriksjon av originalen,
når transporten kommer fra en mengdelikhet. -/
lemma restrict_cast_eq (S T U : Finset V) (hset : S = T)
    (htype : Assignment (α := α) T = Assignment (α := α) S)
    (a : Assignment (α := α) T) (h1 : U ⊆ S) (h2 : U ⊆ T) :
    (cast htype a).restrict h1 = a.restrict h2 := by
  subst hset
  simp
/-- Oppslag i en transportert tilordning er oppslag i originalen.
Motstykket til `restrict_cast_eq` for direkte oppslag framfor restriksjon. -/
lemma cast_apply_eq (S T : Finset V) (hST : S = T)
    (htype : Assignment (α := α) T = Assignment (α := α) S)
    (a : Assignment (α := α) T) (v : V) (h1 : v ∈ S) (h2 : v ∈ T) :
    (cast htype a) ⟨v, h1⟩ = a ⟨v, h2⟩ := by
  subst hST
  simp

/-- `cast` på en restriksjon flyttes ut når mengdene er like.
Motstykket til `restrict_cast_eq` — sammen dekker de begge retninger. -/
lemma cast_restrict_eq (S A B : Finset V) (hAB : A = B)
    (htype : Assignment (α := α) A = Assignment (α := α) B)
    (h1 : A ⊆ S) (h2 : B ⊆ S)
    (a : Assignment (α := α) S) :
    cast htype (a.restrict h1) = a.restrict h2 := by
  subst hAB
  simp
/-- Restriksjon og transport kommuterer når mengdene er like.
Formulert med `S` og `T` som separate variabler så `subst` er mulig —
`B ∪ [] = B` har `B` på begge sider og lar seg ikke substituere direkte. -/
lemma restrict_cast_comm (L S T : Finset V) (hST : S = T)
    (h1 : Assignment (α := α) S = Assignment (α := α) T)
    (h2 : Assignment (α := α) (L ∩ S) = Assignment (α := α) (L ∩ T))
    (base : Assignment (α := α) S) :
    (cast h1 base).restrict (Finset.inter_subset_right (s₁ := L))
      = cast h2 (base.restrict (Finset.inter_subset_right (s₁ := L))) := by
  subst hST
  simp
/-- Når mengden er hele `univ`, er restriksjon og transport inverse.
Lar indikatoren snus så `tsum_ite_eq` kan kollapse summen i `joint_splits`. -/
lemma eq_restrict_iff_eq_cast (S : Finset V) (hS : S = Finset.univ)
    (htypeA : Assignment (α := α) S = Assignment (α := α) (Finset.univ : Finset V))
    (a : Assignment (α := α) S) (a1 : Assignment (α := α) (Finset.univ : Finset V)) :
    (a = a1.restrict (by rw [hS])) ↔ (a1 = cast htypeA a) := by
  subst hS
  constructor
  · intro h
    subst h
    rfl
  · intro h
    subst h
    rfl
/-- Restriksjon og transport kommuterer, generelt: fire mengder, to
mengdelikheter. Generaliseringen av `restrict_cast_comm` som `joint_splits`
trenger, der `U` og `W` ikke er avledet fra `S` og `T`. -/
lemma restrict_cast_gen (S T U W : Finset V) (hST : S = T) (hUW : U = W)
    (h1 : Assignment (α := α) S = Assignment (α := α) T)
    (h2 : Assignment (α := α) U = Assignment (α := α) W)
    (a : Assignment (α := α) S) (hu : U ⊆ S) (hw : W ⊆ T) :
    (cast h1 a).restrict hw = cast h2 (a.restrict hu) := by
  subst hST
  subst hUW
  simp


/-- `nil`-tilfellet av den styrkede faktoriseringen, med `base` som
eksplisitt argument til `F` og `Gf`.

Koblingen mellom `indicator_splits` (som lever helt over `B`) og
`extendOverList_nil` (der `a` lever på `B ∪ [].toFinset`). `convert ... using 2`
gir tre delmål: en `Iff` for indikatorbetingelsen, og to `Eq ENNReal` for
`F0`- og `Gf0`-anvendelsene. -/
lemma extendOverList_factorizes_nil (M : CausalModel G α) (L R B : Finset V)
    (hLR : B ∪ ([] : List V).toFinset ⊆ L ∪ R)
    (hpar : ∀ w ∈ ([] : List V), G.parents w ⊆ B) :
    ∃ (F : Assignment (α := α) (L ∩ B) →
           Assignment (α := α) (L ∩ (B ∪ ([] : List V).toFinset)) → ENNReal)
      (Gf : Assignment (α := α) (R ∩ B) →
            Assignment (α := α) (R ∩ (B ∪ ([] : List V).toFinset)) → ENNReal),
      ∀ (base : Assignment (α := α) B)
        (a : Assignment (α := α) (B ∪ ([] : List V).toFinset)),
        (extendOverList M B base [] hpar) a =
          F (base.restrict Finset.inter_subset_right)
            (a.restrict Finset.inter_subset_right) *
          Gf (base.restrict Finset.inter_subset_right)
            (a.restrict Finset.inter_subset_right) := by
  have hB : B ⊆ L ∪ R := fun x hx => hLR (Finset.mem_union_left _ hx)
  obtain ⟨F0, Gf0, hF0⟩ := indicator_splits (α := α) L R B hB
  refine ⟨fun bp p => F0 bp (cast (by simp) p),
          fun bq q => Gf0 bq (cast (by simp) q), ?_⟩
  intro base a
  rw [extendOverList_nil]
  have hx := hF0 base (cast (by simp) a)
  simp only [eq_comm] at hx ⊢
  convert hx using 2
  · rw [eq_comm, cast_eq_iff_eq_cast_symm, eq_comm]
  · exact congrArg (F0 _) (restrict_cast_comm L (B ∪ ([] : List V).toFinset) B (by simp) (by simp) (by simp) a).symm
  · exact congrArg (Gf0 _) (restrict_cast_comm R (B ∪ ([] : List V).toFinset) B (by simp) (by simp) (by simp) a).symm



/-- `extendOverList` er null når tilordningen ikke utvider `base`.

Dette er brikken som får `bind`-summen i `jointUpTo_factorizes` sitt
`succ`-steg til å kollapse: bare den ene mellomtilstanden som stemmer med
`a` bidrar. Uten den går summen også over `Z`-delen, og faktoriseringen
ødelegges.

Merk plasseringen: lemmaet bruker både `extendOverList_cons'` og
`restrict_cast_eq`, så det må stå etter begge. -/
lemma extendOverList_eq_zero_of_ne (M : CausalModel G α) (B : Finset V)
    (base : Assignment (α := α) B) (l : List V)
    (hpar : ∀ w ∈ l, G.parents w ⊆ B)
    (hnodup : l.Nodup)
    (hdisj : ∀ w ∈ l, w ∉ B)
    (a : Assignment (α := α) (B ∪ l.toFinset))
    (hne : a.restrict Finset.subset_union_left ≠ base) :
    (extendOverList M B base l hpar) a = 0 := by
  induction l with
  | nil =>
    rw [extendOverList_nil]
    rw [if_neg]
    intro heq
    apply hne
    subst heq
    have hB : B ∪ ([] : List V).toFinset = B := by simp
    rw [restrict_cast_eq]
    · rfl
    · exact hB
    · exact Finset.Subset.refl B
  | cons v vs ih =>
    have hv : v ∉ B ∪ vs.toFinset := by
      intro hmem
      rcases Finset.mem_union.mp hmem with h | h
      · exact hdisj v List.mem_cons_self h
      · exact (List.nodup_cons.mp hnodup).1 (List.mem_toFinset.mp h)
    have htype : Assignment (α := α) (insert v (B ∪ vs.toFinset))
        = Assignment (α := α) (B ∪ (v :: vs).toFinset) := by
      congr 1
      ext y
      simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_cons]
      tauto
    have hab : a = cast htype (cast htype.symm a) := by simp
    rw [hab, extendOverList_cons' M B base v vs hpar hv htype (cast htype.symm a)]
    have hzero : (M.extendOverList B base vs
        (fun w hw => hpar w (List.mem_cons_of_mem v hw)))
        ((cast htype.symm a).restrict (Finset.subset_insert v (B ∪ vs.toFinset))) = 0 := by
      apply ih
      · exact (List.nodup_cons.mp hnodup).2
      · exact fun w hw => hdisj w (List.mem_cons_of_mem v hw)
      · rw [Assignment.restrict_restrict, restrict_cast_eq]
        · exact hne
        · simp
    rw [hzero, zero_mul]
/-- Spesialisering av `extendOverList_eq_zero_of_ne` til rangnivåene i
`jointUpTo`. Hypotesene om duplikatfrihet og disjunkthet er utledet fra
`newAtRank`, så kallstedet slipper å gjenta argumentet. -/
lemma extendOverList_level_eq_zero_of_ne (M : CausalModel G α) (n : ℕ)
    (b : Assignment (α := α) (G.verticesUpTo n ∪ (G.newAtRank (n + 1)).toList.toFinset))
    (a1 : Assignment (α := α) (G.verticesUpTo n))
    (hne : a1 ≠ b.restrict Finset.subset_union_left) :
    (M.extendOverList (G.verticesUpTo n) a1 (G.newAtRank (n + 1)).toList
      (jointUpTo._proof_6 n)) b = 0 := by
  apply extendOverList_eq_zero_of_ne
  · exact Finset.nodup_toList _
  · intro w hw
    have hw2 : w ∈ G.newAtRank (n + 1) := by simpa using hw
    simp only [newAtRank, Finset.mem_filter] at hw2
    simp only [verticesUpTo, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · exact fun h => hne h.symm
/-- `bind`-summen i `jointUpTo (n+1)` kollapser til ett ledd: bare den
mellomtilstanden som stemmer med `b` bidrar. -/
lemma jointUpTo_bind_collapse (M : CausalModel G α) (n : ℕ)
    (b : Assignment (α := α) (G.verticesUpTo n ∪ (G.newAtRank (n + 1)).toList.toFinset)) :
    (∑' a1 : Assignment (α := α) (G.verticesUpTo n),
      (M.jointUpTo n) a1 *
        (M.extendOverList (G.verticesUpTo n) a1 (G.newAtRank (n + 1)).toList
          (jointUpTo._proof_6 n)) b)
    = (M.jointUpTo n) (b.restrict Finset.subset_union_left) *
        (M.extendOverList (G.verticesUpTo n) (b.restrict Finset.subset_union_left)
          (G.newAtRank (n + 1)).toList (jointUpTo._proof_6 n)) b := by
  have step : ∀ a1 : Assignment (α := α) (G.verticesUpTo n),
      (M.jointUpTo n) a1 *
        (M.extendOverList (G.verticesUpTo n) a1 (G.newAtRank (n + 1)).toList
          (jointUpTo._proof_6 n)) b
      = if a1 = b.restrict Finset.subset_union_left then
          (M.jointUpTo n) a1 *
            (M.extendOverList (G.verticesUpTo n) a1 (G.newAtRank (n + 1)).toList
              (jointUpTo._proof_6 n)) b
        else 0 := by
    intro a1
    by_cases h : a1 = b.restrict Finset.subset_union_left
    · rw [if_pos h]
    · rw [if_neg h, extendOverList_level_eq_zero_of_ne M n b a1 h, mul_zero]
  rw [tsum_congr step]
  rw [tsum_ite_eq]



lemma extendOverList_factorizes' (M : CausalModel G α) (L R B : Finset V) (l : List V)
    (hpar : ∀ w ∈ l, G.parents w ⊆ B)
    (hLR : B ∪ l.toFinset ⊆ L ∪ R)
    (hnodup : l.Nodup)
    (hdisj : ∀ w ∈ l, w ∉ B)
    (hclique : ∀ w ∈ l, (insert w (G.parents w) ⊆ L) ∨ (insert w (G.parents w) ⊆ R)) :
    ∃ (F : Assignment (α := α) (L ∩ B) →
           Assignment (α := α) (L ∩ (B ∪ l.toFinset)) → ENNReal)
      (Gf : Assignment (α := α) (R ∩ B) →
            Assignment (α := α) (R ∩ (B ∪ l.toFinset)) → ENNReal),
      ∀ (base : Assignment (α := α) B) (a : Assignment (α := α) (B ∪ l.toFinset)),
        (extendOverList M B base l hpar) a =
          F (base.restrict Finset.inter_subset_right)
            (a.restrict Finset.inter_subset_right) *
          Gf (base.restrict Finset.inter_subset_right)
            (a.restrict Finset.inter_subset_right) := by
  induction l with
  | nil => exact extendOverList_factorizes_nil M L R B hLR hpar
  | cons v vs ih =>
    have hpar2 : ∀ w ∈ vs, G.parents w ⊆ B := fun w hw => hpar w (List.mem_cons_of_mem v hw)
    have hsub : B ∪ vs.toFinset ⊆ B ∪ (v :: vs).toFinset := by
      intro x hx
      rcases Finset.mem_union.mp hx with h | h
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ (by simp at h ⊢; tauto)
    have hLR2 : B ∪ vs.toFinset ⊆ L ∪ R := fun x hx => hLR (hsub hx)
    have hnodup2 : vs.Nodup := (List.nodup_cons.mp hnodup).2
    have hdisj2 : ∀ w ∈ vs, w ∉ B := fun w hw => hdisj w (List.mem_cons_of_mem v hw)
    have hclique2 : ∀ w ∈ vs, insert w (G.parents w) ⊆ L ∨ insert w (G.parents w) ⊆ R :=
      fun w hw => hclique w (List.mem_cons_of_mem v hw)
    obtain ⟨F0, Gf0, hF0⟩ := ih hpar2 hLR2 hnodup2 hdisj2 hclique2
    rcases hclique v List.mem_cons_self with hcl | hcl
    · refine ⟨fun bp p => F0 bp (p.restrict (inter_mono_cons L B v vs)) *
        (M.kernel v (p.restrict (parents_subset_inter L B v vs (hpar v List.mem_cons_self) hcl)))
          (p ⟨v, self_mem_inter L B v vs hcl⟩),
        fun bq q => Gf0 bq (q.restrict (inter_mono_cons R B v vs)), ?_⟩
      intro base a
      have hv : v ∉ B ∪ vs.toFinset := by
        intro hmem
        rcases Finset.mem_union.mp hmem with h | h
        · exact hdisj v List.mem_cons_self h
        · exact (List.nodup_cons.mp hnodup).1 (List.mem_toFinset.mp h)
      have htype : Assignment (α := α) (insert v (B ∪ vs.toFinset))
          = Assignment (α := α) (B ∪ (v :: vs).toFinset) := by
        congr 1
        ext y
        simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_cons]
        tauto
      have hab : a = cast htype (cast htype.symm a) := by simp
      rw [hab, extendOverList_cons' M B base v vs hpar hv htype (cast htype.symm a), hF0]
      simp only [Assignment.restrict_restrict]
      simp only [cast_cast, cast_eq]
      simp only [Assignment.restrict]
      rw [restrict_cast_eq (insert v (B ∪ vs.toFinset)) (B ∪ (v :: vs).toFinset),
        restrict_cast_eq (insert v (B ∪ vs.toFinset)) (B ∪ (v :: vs).toFinset),
        restrict_cast_eq (insert v (B ∪ vs.toFinset)) (B ∪ (v :: vs).toFinset)]
      all_goals first
        | (intro x hx; simp at hx ⊢; tauto)
        | (ext y; simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_cons]; tauto)
        | skip
      rw [cast_apply_eq (insert v (B ∪ vs.toFinset)) (B ∪ (v :: vs).toFinset)]
      all_goals first
        | (ext y; simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_cons]; tauto)
        | ring
        | simp
    · refine ⟨fun bp p => F0 bp (p.restrict (inter_mono_cons L B v vs)),
        fun bq q => Gf0 bq (q.restrict (inter_mono_cons R B v vs)) *
          (M.kernel v (q.restrict (parents_subset_inter R B v vs (hpar v List.mem_cons_self) hcl)))
            (q ⟨v, self_mem_inter R B v vs hcl⟩), ?_⟩
      intro base a
      have hv : v ∉ B ∪ vs.toFinset := by
        intro hmem
        rcases Finset.mem_union.mp hmem with h | h
        · exact hdisj v List.mem_cons_self h
        · exact (List.nodup_cons.mp hnodup).1 (List.mem_toFinset.mp h)
      have htype : Assignment (α := α) (insert v (B ∪ vs.toFinset))
          = Assignment (α := α) (B ∪ (v :: vs).toFinset) := by
        congr 1
        ext y
        simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_cons]
        tauto
      have hab : a = cast htype (cast htype.symm a) := by simp
      rw [hab, extendOverList_cons' M B base v vs hpar hv htype (cast htype.symm a), hF0]
      simp only [Assignment.restrict_restrict]
      simp only [cast_cast, cast_eq]
      simp only [Assignment.restrict]
      rw [restrict_cast_eq (insert v (B ∪ vs.toFinset)) (B ∪ (v :: vs).toFinset),
        restrict_cast_eq (insert v (B ∪ vs.toFinset)) (B ∪ (v :: vs).toFinset),
        restrict_cast_eq (insert v (B ∪ vs.toFinset)) (B ∪ (v :: vs).toFinset)]
      all_goals first
        | (intro x hx; simp at hx ⊢; tauto)
        | (ext y; simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_cons]; tauto)
        | skip
      rw [cast_apply_eq (insert v (B ∪ vs.toFinset)) (B ∪ (v :: vs).toFinset)]
      all_goals first
        | (ext y; simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_cons]; tauto)
        | ring
        | simp
/-- `jointUpTo` faktoriserer langs en separator: en `L`-del og en `R`-del,
begge med `Z` som felles argument.
Tre formuleringer ble prøvd. Todelt med `L ∩ ...` og `R ∩ ...` uten `Z`:
`bind` splitter ikke, siden delene overlapper på separatoren. Tredelt med
faste `L`, `Z`, `R` og `hcover : verticesUpTo n = L ∪ R ∪ Z`:
induksjonshypotesen blir ubrukelig, fordi den krever at nivå `n` dekker
samme mengder som `n+1`.

Denne formen virker: `L`, `Z`, `R` er globale og dekker `univ`, snittene med
`verticesUpTo n` vokser med `n`, og `hclique` er uavhengig av `n`. Da kommer
`ih` uten betingelser — verifisert.

Merk om `succ`-steget: `hclique` deler ikke nodene på nivå `n+1` disjunkt i
en `L`-liste og en `R`-liste. En node i `Z` oppfyller begge disjunkter, så
plasseringen må velges konsistent i faktoriseringen. Det er ikke en
teknikalitet — det er der separatoren faktisk gjør arbeid. -/
lemma jointUpTo_factorizes (M : CausalModel G α) (L Z R : Finset V) (n : ℕ)
    (hLZ : Disjoint L Z) (hLR : Disjoint L R) (hZR : Disjoint Z R)
    (hcover : L ∪ Z ∪ R = Finset.univ)
    (hclique : ∀ w : V, (insert w (G.parents w) ⊆ L ∪ Z) ∨ (insert w (G.parents w) ⊆ R ∪ Z)) :
    ∃ (F : Assignment (α := α) (L ∩ G.verticesUpTo n) →
           Assignment (α := α) (Z ∩ G.verticesUpTo n) → ENNReal)
      (Gf : Assignment (α := α) (R ∩ G.verticesUpTo n) →
            Assignment (α := α) (Z ∩ G.verticesUpTo n) → ENNReal),
      ∀ a : Assignment (α := α) (G.verticesUpTo n),
        (jointUpTo M n) a =
          F (a.restrict Finset.inter_subset_right) (a.restrict Finset.inter_subset_right) *
          Gf (a.restrict Finset.inter_subset_right) (a.restrict Finset.inter_subset_right) := by
  induction n with
  | zero =>
    have hLR2 : (∅ : Finset V) ∪ (G.verticesUpTo 0).toList.toFinset ⊆ (L ∪ Z) ∪ (R ∪ Z) := by
      intro x _
      have hx : x ∈ L ∪ Z ∪ R := hcover ▸ Finset.mem_univ x
      rcases Finset.mem_union.mp hx with h | h
      · rcases Finset.mem_union.mp h with h1 | h1
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ h1)
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ h1)
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ h)
    obtain ⟨F0, Gf0, hF0⟩ := extendOverList_factorizes' M (L ∪ Z) (R ∪ Z) ∅
      (G.verticesUpTo 0).toList jointUpTo._proof_4 hLR2 (Finset.nodup_toList _)
      (fun w _ => by simp) (fun w _ => hclique w)
    refine ⟨fun p q => F0 (fun v => absurd v.2 (by simp))
        (joinInter L Z _ (by simpa using p) (by simpa using q)),
      fun p q => Gf0 (fun v => absurd v.2 (by simp))
        (joinInter R Z _ (by simpa using p) (by simpa using q)), ?_⟩
    intro a
    rw [jointUpTo_zero_apply]
    have hx := hF0 (fun v => absurd v.2 (by first | exact Finset.not_mem_empty _ | exact Finset.notMem_empty _)) (cast (by simp) a)
    rw [hx]
    congr 1
    all_goals congr 1
    all_goals first
      | (funext u; exact absurd (Finset.mem_inter.mp u.2).2 (by first | exact Finset.not_mem_empty _ | exact Finset.notMem_empty _))
      | simp [← joinInter_restrict, restrict_cast_eq, cast_restrict_eq]
  | succ n ih =>
    obtain ⟨F0, Gf0, hF0⟩ := ih
    have hset : G.verticesUpTo n ∪ (G.newAtRank (n + 1)).toList.toFinset
        = G.verticesUpTo (n + 1) := by
      rw [G.verticesUpTo_succ n]
      simp
    have htype2 : Assignment (α := α) (G.verticesUpTo (n + 1))
        = Assignment (α := α) (G.verticesUpTo n ∪ (G.newAtRank (n + 1)).toList.toFinset) := by
      rw [hset]
    have hLR2 : G.verticesUpTo n ∪ (G.newAtRank (n + 1)).toList.toFinset
        ⊆ (L ∪ Z) ∪ (R ∪ Z) := by
      intro x _
      have hx : x ∈ L ∪ Z ∪ R := hcover ▸ Finset.mem_univ x
      rcases Finset.mem_union.mp hx with h | h
      · rcases Finset.mem_union.mp h with h1 | h1
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ h1)
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ h1)
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ h)
    have hdisjN : ∀ w ∈ (G.newAtRank (n + 1)).toList, w ∉ G.verticesUpTo n := by
      intro w hw
      have hw2 : w ∈ G.newAtRank (n + 1) := by simpa using hw
      simp only [newAtRank, Finset.mem_filter] at hw2
      simp only [verticesUpTo, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    obtain ⟨F1, Gf1, hF1⟩ := extendOverList_factorizes' M (L ∪ Z) (R ∪ Z)
      (G.verticesUpTo n) (G.newAtRank (n + 1)).toList (jointUpTo._proof_6 n) hLR2
      (Finset.nodup_toList _) hdisjN (fun w _ => hclique w)
    refine ⟨fun p q =>
        F0 (p.restrict (inter_verticesUpTo_mono_succ L n))
          (q.restrict (inter_verticesUpTo_mono_succ Z n)) *
        F1 ((joinInter L Z (G.verticesUpTo (n + 1)) p q).restrict
            (inter_verticesUpTo_mono_succ (L ∪ Z) n))
          ((joinInter L Z (G.verticesUpTo (n + 1)) p q).restrict (by rw [hset])),
      fun p q =>
        Gf0 (p.restrict (inter_verticesUpTo_mono_succ R n))
          (q.restrict (inter_verticesUpTo_mono_succ Z n)) *
        Gf1 ((joinInter R Z (G.verticesUpTo (n + 1)) p q).restrict
            (inter_verticesUpTo_mono_succ (R ∪ Z) n))
          ((joinInter R Z (G.verticesUpTo (n + 1)) p q).restrict (by rw [hset])), ?_⟩
    case _ =>
      intro a
      rw [jointUpTo_succ_apply M n hset htype2, PMF.bind_apply, jointUpTo_bind_collapse]
      have hx0 := hF0 ((cast htype2 a).restrict Finset.subset_union_left)
      have hx1 := hF1 ((cast htype2 a).restrict Finset.subset_union_left) (cast htype2 a)
      rw [hx0, hx1]
      simp only [Assignment.restrict_restrict]
      rw [joinInter_restrict L Z (G.verticesUpTo (n + 1)) a,
        joinInter_restrict R Z (G.verticesUpTo (n + 1)) a]
      simp only [Assignment.restrict_restrict]
      rw [restrict_cast_eq (G.verticesUpTo n ∪ (G.newAtRank (n + 1)).toList.toFinset) (G.verticesUpTo (n + 1)),
        restrict_cast_eq (G.verticesUpTo n ∪ (G.newAtRank (n + 1)).toList.toFinset) (G.verticesUpTo (n + 1)),
        restrict_cast_eq (G.verticesUpTo n ∪ (G.newAtRank (n + 1)).toList.toFinset) (G.verticesUpTo (n + 1)),
        restrict_cast_eq (G.verticesUpTo n ∪ (G.newAtRank (n + 1)).toList.toFinset) (G.verticesUpTo (n + 1)),
        restrict_cast_eq (G.verticesUpTo n ∪ (G.newAtRank (n + 1)).toList.toFinset) (G.verticesUpTo (n + 1)),
        restrict_cast_eq (G.verticesUpTo n ∪ (G.newAtRank (n + 1)).toList.toFinset) (G.verticesUpTo (n + 1)),
        restrict_cast_eq (G.verticesUpTo n ∪ (G.newAtRank (n + 1)).toList.toFinset) (G.verticesUpTo (n + 1))]
      all_goals first
        | exact hset
        | (intro x hx; rw [← hset]; exact Finset.mem_union_left _ (Finset.mem_inter.mp hx).2)
        | (intro x hx; rw [← hset]; exact (Finset.mem_inter.mp hx).2)
        | skip
      ring



/-- Eksplisitt produktform for `extendOverList`: indikator på basen
ganger kjernene til de nye nodene, som listeprodukt så induksjonen følger
`extendOverList_cons'`. Alle foreldre ligger i `B`, så kjerne-input er
`base` restriktert. -/
lemma extendOverList_apply_prod (M : CausalModel G α) (B : Finset V)
    (base : Assignment (α := α) B) :
    ∀ (l : List V) (hpar : ∀ v ∈ l, G.parents v ⊆ B),
      l.Nodup → (∀ v ∈ l, v ∉ B) →
      ∀ b : Assignment (α := α) (B ∪ l.toFinset),
        (extendOverList M B base l hpar) b =
          (if b.restrict Finset.subset_union_left = base then 1 else 0) *
          (l.attach.map (fun w => M.kernel w.1 (base.restrict (hpar w.1 w.2))
              (b ⟨w.1, Finset.mem_union_right B (List.mem_toFinset.mpr w.2)⟩))).prod := by
  intro l
  induction l with
  | nil =>
    intro hpar _ _ b
    have hB : B ∪ ([] : List V).toFinset = B := by simp
    rw [extendOverList_nil]
    simp only [List.attach_nil, List.map_nil, List.prod_nil, mul_one]
    by_cases hb : b.restrict Finset.subset_union_left = base
    · rw [if_pos hb, if_pos]
      funext ⟨x, hx⟩
      rw [cast_apply_eq _ _ hB _ base x hx (by simpa using hx)]
      exact congrFun hb ⟨x, _⟩
    · rw [if_neg hb, if_neg]
      intro h
      apply hb
      funext ⟨x, hx⟩
      rw [h]
      exact cast_apply_eq _ _ hB _ base x _ hx
  | cons v vs ih =>
    intro hpar hnd hdisj b
    have hnd' := List.nodup_cons.mp hnd
    have hv : v ∉ B ∪ vs.toFinset := by
      intro h
      rcases Finset.mem_union.mp h with h | h
      · exact hdisj v List.mem_cons_self h
      · exact hnd'.1 (List.mem_toFinset.mp h)
    have hset : insert v (B ∪ vs.toFinset) = B ∪ (v :: vs).toFinset := by
      ext y
      simp only [Finset.mem_insert, Finset.mem_union, List.mem_toFinset, List.mem_cons]
      tauto
    have htype : Assignment (α := α) (insert v (B ∪ vs.toFinset))
        = Assignment (α := α) (B ∪ (v :: vs).toFinset) := by rw [hset]
    obtain ⟨b', rfl⟩ : ∃ b', b = cast htype b' := ⟨cast htype.symm b, by simp⟩
    have hBsub : B ⊆ insert v (B ∪ vs.toFinset) :=
      fun x hx => Finset.mem_insert_of_mem (Finset.mem_union_left _ hx)
    have hev : ∀ (x : V) (hx : x ∈ B ∪ (v :: vs).toFinset),
        (cast htype b') ⟨x, hx⟩ = b' ⟨x, by rw [hset]; exact hx⟩ :=
      fun x hx => cast_apply_eq _ _ hset.symm htype b' x hx _
    rw [extendOverList_cons' M B base v vs hpar hv htype b',
      ih _ hnd'.2 (fun w hw => hdisj w (List.mem_cons_of_mem v hw)),
      restrict_cast_eq _ _ _ hset.symm htype b' Finset.subset_union_left hBsub]
    have hcond : (b'.restrict (Finset.subset_insert v (B ∪ vs.toFinset))).restrict
        Finset.subset_union_left = b'.restrict hBsub := rfl
    rw [hcond]
    simp only [List.attach_cons, List.map_cons, List.map_map, List.prod_cons, hev]
    by_cases hc : b'.restrict hBsub = base
    · have hk : (b'.restrict (Finset.subset_insert v (B ∪ vs.toFinset))).restrict
          (fun x hx => Finset.mem_union_left _ (hpar v List.mem_cons_self hx))
          = base.restrict (hpar v List.mem_cons_self) := by
        subst hc; rfl
      rw [hk]
      simp only [if_pos hc, one_mul]
      rw [mul_comm]
      congr 1
    · simp only [if_neg hc, zero_mul]

/-- Kjernefaktoren til `v` evaluert i en tilordning på `S`; lik 1 hvis `v`
eller en forelder ligger utenfor `S`. Total i `v`, så produkter over ulike
mengder kan sammenlignes uten subtype-bokføring. -/
noncomputable def kfac (M : CausalModel G α) (S : Finset V)
    (a : Assignment (α := α) S) (v : V) : ENNReal :=
  if h : v ∈ S ∧ G.parents v ⊆ S then M.kernel v (a.restrict h.2) (a ⟨v, h.1⟩) else 1

/-- Kjernefaktoren er upåvirket av restriksjon så lenge `v` og foreldrene
ligger i den mindre mengden. -/
lemma kfac_restrict (M : CausalModel G α) {S T : Finset V} (hTS : T ⊆ S)
    (a : Assignment (α := α) S) {v : V} (hv : v ∈ T) (hpa : G.parents v ⊆ T) :
    kfac M T (a.restrict hTS) v = kfac M S a v := by
  unfold kfac
  rw [dif_pos ⟨hv, hpa⟩, dif_pos ⟨hTS hv, hpa.trans hTS⟩]
  rfl

/-- Listeprodukt over `l.attach` er Finset-produkt over `l.toFinset`
når listen er uten duplikater og faktorene stemmer punktvis. -/
lemma list_attach_prod_eq {β : Type*} [CommMonoid β] :
    ∀ (l : List V) (f : {w // w ∈ l} → β) (g : V → β),
      l.Nodup → (∀ w (hw : w ∈ l), f ⟨w, hw⟩ = g w) →
      (l.attach.map f).prod = ∏ w ∈ l.toFinset, g w := by
  intro l
  induction l with
  | nil => intro f g _ _; simp
  | cons v vs ih =>
    intro f g hnd hfg
    have hnd' := List.nodup_cons.mp hnd
    rw [List.attach_cons, List.map_cons, List.prod_cons, List.map_map, List.toFinset_cons,
      Finset.prod_insert (by simpa using hnd'.1), hfg v List.mem_cons_self]
    congr 1
    exact ih _ g hnd'.2 (fun w hw => hfg w (List.mem_cons_of_mem v hw))

/-- **Steg 2.** Eksplisitt produktform for `jointUpTo`. -/
lemma jointUpTo_apply_prod (M : CausalModel G α) (n : ℕ)
    (a : Assignment (α := α) (G.verticesUpTo n)) :
    (jointUpTo M n) a = ∏ v ∈ G.verticesUpTo n, kfac M (G.verticesUpTo n) a v := by
  have hpaUp : ∀ (m : ℕ) (v : V), v ∈ G.verticesUpTo m → G.parents v ⊆ G.verticesUpTo m := by
    intro m v hv u hu
    simp only [DAG.verticesUpTo, DAG.parents, Finset.mem_filter, Finset.mem_univ,
      true_and] at hv hu ⊢
    exact le_trans (le_of_lt (G.rank_strict_mono u v hu)) hv
  induction n with
  | zero =>
    rw [jointUpTo_zero_apply]
    erw [extendOverList_apply_prod M ∅ _ _ _ (Finset.nodup_toList _)
      (fun v _ h => by simp at h)]
    have hemp : ∀ x y : Assignment (α := α) (∅ : Finset V), x = y :=
      fun x y => funext fun t => by obtain ⟨u, hu⟩ := t; simp at hu
    erw [if_pos (hemp _ _), one_mul,
      list_attach_prod_eq _ _ (kfac M (G.verticesUpTo 0) a) (Finset.nodup_toList _),
      Finset.toList_toFinset]
    intro w hw
    have hw' : w ∈ G.verticesUpTo 0 := Finset.mem_toList.mp hw
    have hnopa : ∀ t : {u // u ∈ G.parents w}, False := fun t => by
      have hedge : G.edge t.1 w := by
        have ht := t.2
        simp only [DAG.parents, Finset.mem_filter, Finset.mem_univ, true_and] at ht
        exact ht
      have hlt := G.rank_strict_mono t.1 w hedge
      simp only [DAG.verticesUpTo, Finset.mem_filter, Finset.mem_univ, true_and] at hw'
      omega
    unfold kfac
    rw [dif_pos ⟨hw', hpaUp 0 w hw'⟩]
    refine congrArg₂ (fun p x => M.kernel w p x) (funext fun t => (hnopa t).elim) ?_
    exact cast_apply_eq _ _ (by simp) _ a w _ hw'
  | succ n ih =>
    have hset : G.verticesUpTo n ∪ (G.newAtRank (n + 1)).toList.toFinset
        = G.verticesUpTo (n + 1) := by
      ext x
      simp only [DAG.verticesUpTo, DAG.newAtRank, Finset.mem_union, Finset.mem_filter,
        Finset.mem_univ, true_and, Finset.toList_toFinset]
      constructor <;> intro h <;> omega
    have hsub : G.verticesUpTo n ⊆ G.verticesUpTo (n + 1) := fun x hx => by
      simp only [DAG.verticesUpTo, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      omega
    have hdisj' : Disjoint (G.verticesUpTo n) (G.newAtRank (n + 1)) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [DAG.verticesUpTo, DAG.newAtRank, Finset.mem_filter, Finset.mem_univ,
        true_and] at hx hx'
      omega
    have hset2 : G.verticesUpTo (n + 1) = G.verticesUpTo n ∪ G.newAtRank (n + 1) := by
      rw [← hset, Finset.toList_toFinset]
    rw [jointUpTo_succ_apply M n hset (by rw [hset]) a, PMF.bind_apply,
      jointUpTo_bind_collapse, ih,
      extendOverList_apply_prod M _ _ _ _ (Finset.nodup_toList _)
        (fun v hv h => by
          simp only [Finset.mem_toList, DAG.newAtRank, DAG.verticesUpTo, Finset.mem_filter,
            Finset.mem_univ, true_and] at hv h
          omega),
      if_pos rfl, one_mul,
      list_attach_prod_eq _ _ (kfac M (G.verticesUpTo (n + 1)) a) (Finset.nodup_toList _),
      restrict_cast_eq _ _ _ hset _ a Finset.subset_union_left hsub,
      Finset.toList_toFinset]
    · have h1 : ∏ v ∈ G.verticesUpTo n, kfac M (G.verticesUpTo n) (a.restrict hsub) v
          = ∏ v ∈ G.verticesUpTo n, kfac M (G.verticesUpTo (n + 1)) a v :=
        Finset.prod_congr rfl (fun v hv => kfac_restrict M hsub a hv (hpaUp n v hv))
      rw [h1, ← Finset.prod_union hdisj']
      exact Finset.prod_congr hset2.symm (fun _ _ => rfl)
    · intro w hw
      have hwN : w ∈ G.newAtRank (n + 1) := Finset.mem_toList.mp hw
      have hwU : w ∈ G.verticesUpTo (n + 1) := by
        simp only [DAG.newAtRank, DAG.verticesUpTo, Finset.mem_filter, Finset.mem_univ,
          true_and] at hwN ⊢
        omega
      unfold kfac
      rw [dif_pos ⟨hwU, hpaUp (n + 1) w hwU⟩]
      refine congrArg₂ (fun p x => M.kernel w p x) ?_ ?_
      · funext t
        exact cast_apply_eq _ _ hset _ a t.1 _ (hpaUp (n + 1) w hwU t.2)
      · exact cast_apply_eq _ _ hset _ a w _ hwU

/-- Kjernefaktoren er upåvirket av transport langs en mengdelikhet. -/
lemma kfac_cast (M : CausalModel G α) {S T : Finset V} (hST : S = T)
    (h : Assignment (α := α) T = Assignment (α := α) S)
    (a : Assignment (α := α) T) (v : V) :
    kfac M S (cast h a) v = kfac M T a v := by
  subst hST
  rfl

/-- **Steg 3.** Eksplisitt produktform for `fullJoint`. -/
lemma fullJoint_apply_prod (M : CausalModel G α)
    (u : Assignment (α := α) (Finset.univ : Finset V)) :
    (M.fullJoint) u = ∏ v, kfac M Finset.univ u v := by
  rw [fullJoint_apply M (by rw [G.verticesUpTo_maxRank]) u, jointUpTo_apply_prod]
  exact Finset.prod_congr G.verticesUpTo_maxRank
    (fun v _ => kfac_cast M G.verticesUpTo_maxRank _ u v)

/-- Hjelpemodell for steg 4: kjernene i `A` er punktmasser på `a`,
resten er uendret. Samme graf som `M`, så ingen transport trengs. -/
noncomputable def pinTo (M : CausalModel G α) (A : Finset V)
    (a : Assignment (α := α) A) : CausalModel G α :=
  { fin := M.fin
    deq := M.deq
    kernel := fun v p => if hv : v ∈ A then PMF.pure (a ⟨v, hv⟩) else M.kernel v p }

/-- Kjernefaktoren til hjelpemodellen: indikator i `A`, uendret utenfor. -/
lemma kfac_pinTo (M : CausalModel G α) (A : Finset V) (a : Assignment (α := α) A)
    (u : Assignment (α := α) (Finset.univ : Finset V)) (v : V) :
    kfac (pinTo M A a) Finset.univ u v =
      if hv : v ∈ A then (if u ⟨v, Finset.mem_univ v⟩ = a ⟨v, hv⟩ then 1 else 0)
      else kfac M Finset.univ u v := by
  have hc : v ∈ (Finset.univ : Finset V) ∧ G.parents v ⊆ Finset.univ :=
    ⟨Finset.mem_univ v, Finset.subset_univ _⟩
  unfold kfac
  simp only [dif_pos hc]
  by_cases hv : v ∈ A
  · simp only [pinTo, dif_pos hv, PMF.pure_apply]
  · simp only [pinTo, dif_neg hv]

/-- **Steg 4.** Kjernefaktorene utenfor `A` summerer til 1 over alle
utvidelser av en fast tilordning på `A`. Gjelder for enhver `A`. -/
lemma sum_compl_kfac_eq_one (M : CausalModel G α) (A : Finset V)
    (a : Assignment (α := α) A) :
    ∑' u : Assignment (α := α) (Finset.univ : Finset V),
      (if u.restrict (Finset.subset_univ A) = a then 1 else 0) *
        ∏ v ∈ Aᶜ, kfac M Finset.univ u v = 1 := by
  have hsplit : ∀ u : Assignment (α := α) (Finset.univ : Finset V),
      ∏ v, kfac (pinTo M A a) Finset.univ u v =
        (if u.restrict (Finset.subset_univ A) = a then 1 else 0) *
          ∏ v ∈ Aᶜ, kfac M Finset.univ u v := by
    intro u
    rw [← Finset.prod_mul_prod_compl A]
    congr 1
    · by_cases h : u.restrict (Finset.subset_univ A) = a
      · rw [if_pos h]
        refine Finset.prod_eq_one (fun v hv => ?_)
        rw [kfac_pinTo, dif_pos hv, if_pos]
        exact congrFun h ⟨v, hv⟩
      · rw [if_neg h]
        obtain ⟨⟨v, hv⟩, hne⟩ := Function.ne_iff.mp h
        refine Finset.prod_eq_zero hv ?_
        rw [kfac_pinTo, dif_pos hv,
          if_neg (show ¬ (u ⟨v, Finset.mem_univ v⟩ = a ⟨v, hv⟩) from hne)]
    · exact Finset.prod_congr rfl (fun v hv => by
        rw [kfac_pinTo, dif_neg (Finset.mem_compl.mp hv)])
  calc _ = ∑' u, (pinTo M A a).fullJoint u :=
        tsum_congr (fun u => by rw [fullJoint_apply_prod, hsplit])
    _ = 1 := (pinTo M A a).fullJoint.tsum_coe

/-- **Steg 5.** Marginalen på en ancestralt lukket mengde er produktet av
kjernefaktorene over mengden. -/
lemma marginal_ancestral_apply (M : CausalModel G α) (A : Finset V)
    (hA : ∀ v ∈ A, ∀ w, G.edge w v → w ∈ A) (a : Assignment (α := α) A) :
    (M.marginal A) a = ∏ v ∈ A, kfac M A a v := by
  have hpa : ∀ v ∈ A, G.parents v ⊆ A := fun v hv u hu => by
    simp only [DAG.parents, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    exact hA v hv u hu
  have hterm : ∀ u : Assignment (α := α) (Finset.univ : Finset V),
      (if a = u.restrict (Finset.subset_univ A) then (M.fullJoint) u else 0)
        = (∏ v ∈ A, kfac M A a v) *
          ((if u.restrict (Finset.subset_univ A) = a then 1 else 0) *
            ∏ v ∈ Aᶜ, kfac M Finset.univ u v) := by
    intro u
    by_cases h : u.restrict (Finset.subset_univ A) = a
    · rw [if_pos h.symm, if_pos h, one_mul, fullJoint_apply_prod, ← h,
        ← Finset.prod_mul_prod_compl A]
      congr 1
      exact Finset.prod_congr rfl (fun v hv => (kfac_restrict M _ u hv (hpa v hv)).symm)
    · rw [if_neg (fun h' => h h'.symm), if_neg h, zero_mul, mul_zero]
  unfold CausalModel.marginal
  rw [PMF.map_apply]
  simp_rw [hterm]
  rw [ENNReal.tsum_mul_left, sum_compl_kfac_eq_one, mul_one]

/-- Restriction of a causal model to an ancestrally closed vertex set. -/
noncomputable def CausalModel.restrictTo (M : CausalModel G α) (A : Finset V)
    (hA : ∀ v ∈ A, ∀ w, G.edge w v → w ∈ A) [∀ v, Nonempty (α v)] :
    CausalModel (DAG.induce G A) α :=
  { fin := M.fin
    deq := M.deq
    kernel := fun v => by
      classical
      by_cases hv : v ∈ A
      · rw [DAG.induce_parents_eq A hA v hv]
        exact M.kernel v
      · exact fun _ => M.kernel v (fun u => Classical.arbitrary _) }

/-- `Eq.mpr` langs en likhet mellom foreldremengder flytter bare
medlemskapsbeviset i kjernens argument. -/
lemma mpr_kernel_apply {v : V} {s t : Finset V} (hst : s = t)
    (h : ((∀ u : {u // u ∈ s}, α u.1) → PMF (α v))
      = ((∀ u : {u // u ∈ t}, α u.1) → PMF (α v)))
    (f : (∀ u : {u // u ∈ t}, α u.1) → PMF (α v))
    (p : ∀ u : {u // u ∈ s}, α u.1) :
    (h.mpr f) p = f (fun u => p ⟨u.1, hst ▸ u.2⟩) := by
  subst hst
  rfl

/-- **Steg 6.** Den restrikterte modellen har samme kjernefaktorer på `A`. -/
lemma kfac_restrictTo (M : CausalModel G α) (A : Finset V)
    (hA : ∀ v ∈ A, ∀ w, G.edge w v → w ∈ A) [∀ v, Nonempty (α v)]
    (a : Assignment (α := α) A) {v : V} (hv : v ∈ A) :
    kfac (CausalModel.restrictTo M A hA) A a v = kfac M A a v := by
  have hpaM : G.parents v ⊆ A := fun u hu => by
    simp only [DAG.parents, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    exact hA v hv u hu
  have hpaN : (DAG.induce G A).parents v ⊆ A := by
    rw [DAG.induce_parents_eq A hA v hv]
    exact hpaM
  unfold kfac
  rw [dif_pos ⟨hv, hpaN⟩, dif_pos ⟨hv, hpaM⟩]
  simp only [CausalModel.restrictTo, dif_pos hv]
  erw [mpr_kernel_apply (DAG.induce_parents_eq A hA v hv)]
  all_goals rfl

/--
**Ancestral marginalisation.** The marginal of the full joint onto an
ancestrally closed `A` agrees with the restricted model's joint at every
assignment.

Budget several sessions. This is where `ENNReal` bites hardest.

Note the shape: `marginal` is a `PMF`, so both sides are applications of a
`PMF` to an `Assignment`.
-/
theorem marginal_eq_restricted_joint (M : CausalModel G α) (A : Finset V)
    (hA : ∀ v ∈ A, ∀ w, G.edge w v → w ∈ A) [∀ v, Nonempty (α v)]
    (a : Assignment (α := α) A) :
    (M.marginal A) a = ((CausalModel.restrictTo M A hA).marginal A) a := by
  rw [marginal_ancestral_apply M A hA a,
    marginal_ancestral_apply (CausalModel.restrictTo M A hA) A (fun _ _ _ hw => hw.1) a]
  exact Finset.prod_congr rfl (fun v hv => (kfac_restrictTo M A hA a hv).symm)
/-- Løft en vandring i den induserte grafen til en vandring i `G`. -/
def DAG.Walk.lift {A : Finset V} : {u w : V} →
    DAG.Walk (DAG.induce G A) u w → DAG.Walk G u w
  | _, _, .nil v => .nil v
  | _, _, .fwd e rest => .fwd (DAG.induce_edge e) (lift rest)
  | _, _, .bwd e rest => .bwd (DAG.induce_edge e) (lift rest)

/-- Blokkering bevares under løft. -/
lemma DAG.Walk.blockedAux_lift {A Z : Finset V} (inc : DAG.Incoming) :
    ∀ {u w : V} (p : DAG.Walk (DAG.induce G A) u w),
      DAG.Walk.blockedAux (G := G) Z inc (DAG.Walk.lift p) →
      DAG.Walk.blockedAux (G := DAG.induce G A) Z inc p := by
  intro u w p
  induction p generalizing inc with
  | nil v => intro h; exact h
  | fwd e rest ih =>
    cases inc <;> simp only [DAG.Walk.lift, DAG.Walk.blockedAux] at * <;>
      tauto
  | bwd e rest ih =>
    cases inc <;> simp only [DAG.Walk.lift, DAG.Walk.blockedAux] at * <;>
      first
        | tauto
        | (rintro (hr | hb)
           · exact Or.inl fun z hz hcon => hr z hz (DAG.induce_reaches hcon)
           · exact Or.inr (ih _ hb))
/--
d-separation survives restriction to an ancestral set containing the
relevant vertices. Pure graph theory — provable independently of Layer 1,
and a good second task after Layer 0.

Induct on the `DAG.Walk` structure: a walk in `DAG.induce G A` lifts to a
walk in `G` via `DAG.induce_edge`, and `blockedAux` is preserved because
`DAG.induce_reaches` carries reachability upward.
-/
theorem dsep_restrict (Z : Finset V) (x y : V)
    (h : G.DSeparated Z x y)
    (A : Finset V) (hA : ancestors G ({x, y} ∪ Z) ⊆ A) :
    (DAG.induce G A).DSeparated Z x y := by
  intro p
  exact DAG.Walk.blockedAux_lift .start p (h (DAG.Walk.lift p))

/-! ## Layer 2 — moralisation

The crux. Everything else is bookkeeping around this equivalence.

**Central observation.** A marriage edge `u — w` in `moralGraph G A` that
is not an edge of `G` comes from a shared child `c ∈ A`, i.e. `u → c ← w`
— a collider. Inside `A = ancestors G ({x,y} ∪ Z)` every vertex reaches
`x`, `y`, or some `z ∈ Z`. For an internal collider on a walk between `x`
and `y`, that witness can be pushed into `Z`, giving
`∃ z ∈ Z, G.Reaches c z` — precisely the negation of `blockedAux`'s
collider clause.

Marriage edges and open colliders are the same phenomenon. This is why the
ancestral reduction must come first: outside `A` the correspondence fails.

Only the forward direction is needed for soundness, but state both — the
converse is the completeness half, and proving them together tends to
force a cleaner statement.
-/

/-- A moral edge absent from `G` arises from a shared child. -/
lemma moral_edge_witness {A : Finset V} {u w : V}
    (h : (moralGraph G A).Adj u w) (h1 : ¬ G.edge u w) (h2 : ¬ G.edge w u) :
    ∃ c ∈ A, G.edge u c ∧ G.edge w c := by
  simp only [moralGraph, SimpleGraph.fromRel_adj] at h
  obtain ⟨-, hr | hr⟩ := h
  · obtain ⟨-, -, he | ⟨c, hc, huc, hwc⟩⟩ := hr
    · exact absurd he h1
    · exact ⟨c, hc, huc, hwc⟩
  · obtain ⟨-, -, he | ⟨c, hc, hwc, huc⟩⟩ := hr
    · exact absurd he h2
    · exact ⟨c, hc, huc, hwc⟩

/-- Every vertex of an ancestral set reaches its seed. -/
lemma reaches_seed_of_mem_ancestors {S : Finset V} {v : V}
    (hv : v ∈ ancestors G S) : ∃ s ∈ S, G.Reaches v s := by
  exact mem_ancestors_iff.mp hv

/-- Sterk induksjon på vandringslengde. Nødvendig fordi kollidertilfellet
i moraliseringen hopper over to konstruktører, ikke én. -/
lemma DAG.Walk.strong_length_induction
    {P : ∀ {x y : V}, DAG.Walk G x y → Prop}
    (step : ∀ {x y : V} (q : DAG.Walk G x y),
      (∀ {u w : V} (r : DAG.Walk G u w), r.length < q.length → P r) → P q)
    {x y : V} (q : DAG.Walk G x y) : P q := by
  have H : ∀ n : ℕ, ∀ {u w : V} (r : DAG.Walk G u w), r.length ≤ n → P r := by
    intro n
    induction n with
    | zero => intro u w r hr; exact step r (fun s hs => absurd hs (by omega))
    | succ m ihm =>
      intro u w r hr
      exact step r (fun s hs => ihm s (Nat.lt_succ_iff.mp (Nat.lt_of_lt_of_le hs hr)))
  exact H q.length q le_rfl


/-- `l.tail.dropLast` er en sublist av `l.dropLast`. -/
lemma tail_dropLast_sublist_dropLast {α : Type*} (l : List α) :
    l.tail.dropLast.Sublist l.dropLast := by
  cases l with
  | nil => simp
  | cons hd tl =>
    simp only [List.tail_cons]
    cases tl with
    | nil => simp
    | cons h t =>
      simp only [List.dropLast]
      exact List.sublist_cons_self _ _
/-- Er `z` ikke startnoden, overlever medlemskap i `dropLast` at hodet fjernes. -/
lemma mem_support_tail_dropLast {H : SimpleGraph V} {b c : V}
    (p : H.Walk b c) (z : V) (hzb : z ≠ b)
    (hmem : z ∈ p.support.dropLast) : z ∈ p.support.tail.dropLast := by
  cases hl : p.support with
  | nil => simp [hl] at hmem
  | cons hd tl =>
    have hhd : hd = b := by
      have h := SimpleGraph.Walk.head_support p
      simp [hl] at h
      exact h
    subst hhd
    rw [hl] at hmem
    cases tl with
    | nil => simp at hmem
    | cons h2 t2 =>
      simp [List.dropLast] at hmem ⊢
      rcases hmem with rfl | h
      · exact absurd rfl hzb
      · exact h
/--
From an open walk in `G` to a moral walk avoiding `Z` internally.

This is the direction Lauritzen's proof actually takes. On an open walk
every non-collider lies outside `Z` (else the walk would be blocked), and
every collider `u → c ← w` becomes a marriage edge `u — w`, so `c` drops
out of the moral walk's support entirely. Minimality is not needed —
openness supplies what is required.

Note: walks may self-intersect. Lauritzen (1996) is known to need this,
and `SimpleGraph.Walk` allows it, so the representation is on the right
side of that subtlety.
-/
lemma moral_walk_of_open {A Z : Finset V} (inc : DAG.Incoming)
    (hclosed : ∀ v ∈ A, ∀ w, G.edge w v → w ∈ A)
    {x y : V} (q : DAG.Walk G x y)
    (hq : ¬ DAG.Walk.blockedAux (G := G) Z inc q)
    (hsupp : ∀ v ∈ q.support, v ∈ A) :
    ∃ p : (moralGraph G A).Walk x y,
      ∀ z ∈ Z, z ∉ p.support.tail.dropLast := by
  induction q using DAG.Walk.strong_length_induction generalizing inc with
  | step q ihq =>
    match q, hq, hsupp with
    | .nil v, _, _ => exact ⟨SimpleGraph.Walk.nil, by simp⟩
    | @DAG.Walk.fwd _ _ _ _ a b c e rest, hq2, hsupp2 =>
      have hne : a ≠ b := fun h => G.not_self_edge a (h ▸ e)
      have hadj : (moralGraph G A).Adj a b := by
        simp only [moralGraph, SimpleGraph.fromRel_adj]
        refine ⟨hne, Or.inl ⟨?_, ?_, Or.inl e⟩⟩
        · exact hsupp2 a (by simp [DAG.Walk.support])
        · exact hsupp2 b (by cases rest <;> simp [DAG.Walk.support])
      have hrest : ¬ DAG.Walk.blockedAux (G := G) Z DAG.Incoming.fwd rest := by
        intro hb
        cases inc <;> simp [DAG.Walk.blockedAux] at hq2 <;> tauto
      cases hr : rest with
      | nil w =>
        subst hr
        refine ⟨SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil, ?_⟩
        intro z hz hmem
        simp [SimpleGraph.Walk.support_cons] at hmem
      | fwd e2 r2 =>
        obtain ⟨p, hp⟩ := ihq rest (by simp [DAG.Walk.length]) DAG.Incoming.fwd hrest
          (fun v hv => hsupp2 v (by simp [DAG.Walk.support]; tauto))
        refine ⟨SimpleGraph.Walk.cons hadj p, ?_⟩
        intro z hz hmem
        simp [SimpleGraph.Walk.support_cons] at hmem
        by_cases hzb : z = b
        · subst hzb
          exact hrest (by rw [hr]; simp [DAG.Walk.blockedAux]; exact Or.inl hz)
        · exact hp z hz (mem_support_tail_dropLast p z hzb hmem)
      | bwd e2 r2 =>
        rename_i d
        rw [hr] at hrest
        simp [DAG.Walk.blockedAux] at hrest
        obtain ⟨hopen, hr2⟩ := hrest
        by_cases hneab : a = d
        · subst hneab
          exact ihq r2 (by rw [hr]; simp [DAG.Walk.length]) DAG.Incoming.bwd hr2
            (fun v hv => hsupp2 v (by rw [hr]; simp [DAG.Walk.support]; tauto))
        · have hmarry : (moralGraph G A).Adj a d := by
            simp only [moralGraph, SimpleGraph.fromRel_adj]
            refine ⟨hneab, Or.inl ⟨hsupp2 a (by simp [DAG.Walk.support]), ?_, Or.inr ⟨b, ?_, e, e2⟩⟩⟩
            · exact hsupp2 d (by rw [hr]; cases r2 <;> simp [DAG.Walk.support])
            · exact hsupp2 b (by rw [hr]; simp [DAG.Walk.support])
          cases hr2c : r2 with
          | nil w =>
            refine ⟨SimpleGraph.Walk.cons hmarry SimpleGraph.Walk.nil, ?_⟩
            intro z hz hmem
            simp [SimpleGraph.Walk.support_cons] at hmem
          | fwd e3 r3 =>
            obtain ⟨p, hp⟩ := ihq r2 (by rw [hr]; simp [DAG.Walk.length]) DAG.Incoming.bwd hr2
              (fun v hv => hsupp2 v (by rw [hr]; simp [DAG.Walk.support]; tauto))
            refine ⟨SimpleGraph.Walk.cons hmarry p, ?_⟩
            intro z hz hmem
            simp [SimpleGraph.Walk.support_cons] at hmem
            by_cases hzd : z = d
            · subst hzd
              exact hr2 (by rw [hr2c]; simp [DAG.Walk.blockedAux]; exact Or.inl hz)
            · exact hp z hz (mem_support_tail_dropLast p z hzd hmem)
          | bwd e3 r3 =>
            obtain ⟨p, hp⟩ := ihq r2 (by rw [hr]; simp [DAG.Walk.length]) DAG.Incoming.bwd hr2
              (fun v hv => hsupp2 v (by rw [hr]; simp [DAG.Walk.support]; tauto))
            refine ⟨SimpleGraph.Walk.cons hmarry p, ?_⟩
            intro z hz hmem
            simp [SimpleGraph.Walk.support_cons] at hmem
            by_cases hzd : z = d
            · subst hzd
              exact hr2 (by rw [hr2c]; simp [DAG.Walk.blockedAux]; exact Or.inl hz)
            · exact hp z hz (mem_support_tail_dropLast p z hzd hmem)
    | @DAG.Walk.bwd _ _ _ _ a b c e rest, hq2, hsupp2 =>
      have hne : a ≠ b := fun h => G.not_self_edge b (h ▸ e)
      have hadj : (moralGraph G A).Adj a b := by
        simp only [moralGraph, SimpleGraph.fromRel_adj]
        refine ⟨hne, Or.inr ⟨?_, ?_, Or.inl e⟩⟩
        · exact hsupp2 b (by cases rest <;> simp [DAG.Walk.support])
        · exact hsupp2 a (by simp [DAG.Walk.support])
      have hrest : ¬ DAG.Walk.blockedAux (G := G) Z DAG.Incoming.bwd rest := by
        intro hb
        cases inc <;> simp [DAG.Walk.blockedAux] at hq2 <;> tauto
      cases hr : rest with
      | nil w =>
        subst hr
        refine ⟨SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil, ?_⟩
        intro z hz hmem
        simp [SimpleGraph.Walk.support_cons] at hmem
      | fwd e2 r2 =>
        obtain ⟨p, hp⟩ := ihq rest (by simp [DAG.Walk.length]) DAG.Incoming.bwd hrest
          (fun v hv => hsupp2 v (by simp [DAG.Walk.support]; tauto))
        refine ⟨SimpleGraph.Walk.cons hadj p, ?_⟩
        intro z hz hmem
        simp [SimpleGraph.Walk.support_cons] at hmem
        by_cases hzb : z = b
        · subst hzb
          exact hrest (by rw [hr]; simp [DAG.Walk.blockedAux]; exact Or.inl hz)
        · exact hp z hz (mem_support_tail_dropLast p z hzb hmem)
      | bwd e2 r2 =>
        obtain ⟨p, hp⟩ := ihq rest (by simp [DAG.Walk.length]) DAG.Incoming.bwd hrest
          (fun v hv => hsupp2 v (by simp [DAG.Walk.support]; tauto))
        refine ⟨SimpleGraph.Walk.cons hadj p, ?_⟩
        intro z hz hmem
        simp [SimpleGraph.Walk.support_cons] at hmem
        by_cases hzb : z = b
        · subst hzb
          exact hrest (by rw [hr]; simp [DAG.Walk.blockedAux]; exact Or.inl hz)
        · exact hp z hz (mem_support_tail_dropLast p z hzb hmem)
/-! ## Removed: `open_walk_of_moral` and `moral_sep_of_dsep`
Both were false as stated: an arbitrary ancestrally closed `A` is too weak.
See `Counterexample.lean` (graph `0 → 2 ← 1`). The corrected statement, with
`A = ancestors G ({x, y} ∪ Z)`, is `Lauritzen.moral_sep_of_dsep_lauritzen`. -/

/-- En node i støtten som verken er start eller slutt, er en indre node.
Siste steg (`hgl`) er en teknisk identitet om `getLast` som gjenstår. -/
lemma mem_support_interior {H : SimpleGraph V} {x y : V}
    (p : H.Walk x y) (z : V) (hzx : z ≠ x) (hzy : z ≠ y)
    (hmem : z ∈ p.support) : z ∈ p.support.tail.dropLast := by
  have hc := SimpleGraph.Walk.cons_tail_support p
  rw [← hc] at hmem
  rw [List.mem_cons] at hmem
  rcases hmem with h | h
  · exact absurd h hzx
  · have hne : p.support.tail ≠ [] := by
      intro he
      rw [he] at h
      simp at h
    refine List.mem_dropLast_of_mem_of_ne_getLast h ?_
    have hgl : p.support.tail.getLast hne = y := by
      simp
    rw [hgl]
    exact hzy

/--
**Moralisation.** Within the ancestral subgraph, d-separation and vertex
separation in the moral graph coincide.
Only the direction needed for soundness: separation in the moral graph
implies d-separation in `G`. The converse is completeness and is open.
-/
theorem dsep_of_moral_sep (Z : Finset V) (x y : V) (A : Finset V)
    (hclosed : ∀ v ∈ A, ∀ w, G.edge w v → w ∈ A)
    (hsep : Separates (moralGraph G A) Z x y)
    (hxy : ∀ (q : DAG.Walk G x y), ∀ v ∈ q.support, v ∈ A)
    (hxZ : x ∉ Z) (hyZ : y ∉ Z) :
    G.DSeparated Z x y := by
  intro q
  by_contra hopen
  obtain ⟨p, hp⟩ := moral_walk_of_open DAG.Incoming.start hclosed q hopen (hxy q)
  obtain ⟨z, hzZ, hzmem⟩ := hsep p
  by_cases hzx : z = x
  · exact hxZ (hzx ▸ hzZ)
  by_cases hzy : z = y
  · exact hyZ (hzy ▸ hzZ)
  exact hp z hzZ (mem_support_interior p z hzx hzy hzmem)


/-! ## Layer 3 — factorisation splits along a separator

Once separation is undirected the argument is algebraic; graphs enter only
through the clique condition.

If `Z` separates `x` from `y` in `H`, the vertex set splits as
`L ∪ Z ∪ R` with no `L`–`R` edge, `x ∈ L`, `y ∈ R`. Every clique lies
wholly in `L ∪ Z` or wholly in `R ∪ Z`. Each factor `P(v | parents v)` is
supported on the family clique `{v} ∪ parents v` (Layer 0), so the product
splits as `f(L,Z) · g(R,Z)` — which is `CondIndep` as already defined.
-/
/-- `v` er nåbar fra `x` uten å berøre `Z`. -/
def ReachAvoiding (H : SimpleGraph V) (Z : Finset V) (x v : V) : Prop :=
  ∃ p : H.Walk x v, ∀ z ∈ Z, z ∉ p.support

/-- Refleksivitet, gitt at `x` selv ikke ligger i `Z`. -/
lemma reachAvoiding_refl {H : SimpleGraph V} {Z : Finset V} {x : V} (hxZ : x ∉ Z) :
    ReachAvoiding H Z x x :=
  ⟨SimpleGraph.Walk.nil, by
    intro z hz hzmem
    simp at hzmem
    subst hzmem
    exact hxZ hz⟩


/-- A separator partitions the graph with no crossing edges. -/
lemma separator_partition {H : SimpleGraph V} {Z : Finset V} {x y : V}
    (h : Separates H Z x y) (hxZ : x ∉ Z) (hyZ : y ∉ Z) :
    ∃ L R : Finset V,
      x ∈ L ∧ y ∈ R ∧ Disjoint L R ∧ Disjoint L Z ∧ Disjoint R Z ∧
      L ∪ Z ∪ R = Finset.univ ∧
      ∀ u ∈ L, ∀ w ∈ R, ¬ H.Adj u w := by
  classical
  set L := Finset.univ.filter (fun v => v ∉ Z ∧ ReachAvoiding H Z x v) with hLdef
  set R := Finset.univ \ (L ∪ Z) with hRdef
  refine ⟨L, R, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hLdef, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hxZ, reachAvoiding_refl hxZ⟩
  · simp only [hRdef, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union, hLdef,
      Finset.mem_filter, not_or, not_and]
    refine ⟨?_, hyZ⟩
    intro _ hra
    obtain ⟨p, hp⟩ := hra
    obtain ⟨z, hzZ, hzmem⟩ := h p
    exact absurd hzmem (hp z hzZ)
  · rw [Finset.disjoint_left]
    intro v hvL hvR
    simp only [hRdef, Finset.mem_sdiff, Finset.mem_union] at hvR
    exact hvR.2 (Or.inl hvL)
  · rw [Finset.disjoint_left]
    intro v hvL hvZ
    simp only [hLdef, Finset.mem_filter] at hvL
    exact hvL.2.1 hvZ
  · rw [Finset.disjoint_left]
    intro v hvR hvZ
    simp only [hRdef, Finset.mem_sdiff, Finset.mem_union] at hvR
    exact hvR.2 (Or.inr hvZ)
  · rw [hRdef]
    ext v
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and, iff_true]
    by_cases hv : v ∈ L ∪ Z
    · rcases Finset.mem_union.mp hv with h1 | h1
      · exact Or.inl (Or.inl h1)
      · exact Or.inl (Or.inr h1)
    · exact Or.inr (fun hc => hv (Finset.mem_union.mpr hc))
  · intro u huL w hwR hadj
    simp only [hLdef, Finset.mem_filter, Finset.mem_univ, true_and] at huL
    obtain ⟨huZ, pu, hpu⟩ := huL
    simp only [hRdef, Finset.mem_sdiff, Finset.mem_union, Finset.mem_univ, true_and,
      not_or, hLdef, Finset.mem_filter, not_and] at hwR
    trace_state
    exact hwR.1 hwR.2 ⟨pu.concat hadj, by
      intro z hz hzmem
      rw [SimpleGraph.Walk.support_concat] at hzmem
      simp only [List.mem_append, List.mem_singleton] at hzmem
      rcases hzmem with h1 | h1
      · exact hpu z hz h1
      · subst h1; exact hwR.2 hz⟩
lemma clique_one_sided {H : SimpleGraph V} {Z L R K : Finset V}
    (hcross : ∀ u ∈ L, ∀ w ∈ R, ¬ H.Adj u w)
    (hcover : L ∪ Z ∪ R = Finset.univ)
    (hK : H.IsClique (↑K : Set V)) :
    K ⊆ L ∪ Z ∨ K ⊆ R ∪ Z := by
  by_cases hKR : ∃ w ∈ K, w ∈ R
  · right
    obtain ⟨w, hwK, hwR⟩ := hKR
    intro v hv
    have hvcov : v ∈ L ∪ Z ∪ R := hcover ▸ Finset.mem_univ v
    rcases Finset.mem_union.mp hvcov with h1 | h1
    · rcases Finset.mem_union.mp h1 with h2 | h2
      · by_cases hvw : v = w
        · subst hvw; exact Finset.mem_union_left _ hwR
        · exact absurd (hK (by simpa using hv) (by simpa using hwK) hvw) (hcross v h2 w hwR)
      · exact Finset.mem_union_right _ h2
    · exact Finset.mem_union_left _ h1
  · left
    push_neg at hKR
    intro v hv
    have hvcov : v ∈ L ∪ Z ∪ R := hcover ▸ Finset.mem_univ v
    rcases Finset.mem_union.mp hvcov with h1 | h1
    · exact h1
    · exact absurd h1 (hKR v hv)

/--
The joint splits into a product over the two sides of the separator.

Conclusion left as `True`. It should say that `(M.marginal (L ∪ Z ∪ R)) a`
equals a product of a function of `a.restrict` to `L ∪ Z` and one to
`R ∪ Z`. Write it once you have `Assignment.restrict`'s subset proofs in
hand — `CausalModel.lean` uses `subset_union3_left_right` and friends for
exactly this, so reuse those rather than proving new subset facts.
-/
theorem joint_splits (M : CausalModel G α) (L Z R : Finset V)
    (hLZ : Disjoint L Z) (hLR : Disjoint L R) (hZR : Disjoint Z R)
    (hcover : L ∪ Z ∪ R = Finset.univ)
    (hclique : ∀ w : V, (insert w (G.parents w) ⊆ L ∪ Z) ∨ (insert w (G.parents w) ⊆ R ∪ Z)) :
    ∃ (F : Assignment (α := α) L → Assignment (α := α) Z → ENNReal)
      (Gf : Assignment (α := α) R → Assignment (α := α) Z → ENNReal),
      ∀ a : Assignment (α := α) (L ∪ R ∪ Z),
        (M.marginal (L ∪ R ∪ Z)) a =
          F (a.restrict (subset_union3_left L R Z)) (a.restrict (subset_union3_right L R Z)) *
          Gf (a.restrict (subset_union3_mid L R Z)) (a.restrict (subset_union3_right L R Z)) := by
  have htypeU : Assignment (α := α) (Finset.univ : Finset V)
      = Assignment (α := α) (G.verticesUpTo G.maxRank) := by
    rw [G.verticesUpTo_maxRank]
  have hLu : Assignment (α := α) L = Assignment (α := α) (L ∩ G.verticesUpTo G.maxRank) := by
    rw [G.verticesUpTo_maxRank, Finset.inter_univ]
  have hZu : Assignment (α := α) Z = Assignment (α := α) (Z ∩ G.verticesUpTo G.maxRank) := by
    rw [G.verticesUpTo_maxRank, Finset.inter_univ]
  have hRu : Assignment (α := α) R = Assignment (α := α) (R ∩ G.verticesUpTo G.maxRank) := by
    rw [G.verticesUpTo_maxRank, Finset.inter_univ]
  obtain ⟨F0, Gf0, hF0⟩ := jointUpTo_factorizes M L Z R G.maxRank hLZ hLR hZR hcover hclique
  refine ⟨fun p q => F0 (cast hLu p) (cast hZu q),
    fun p q => Gf0 (cast hRu p) (cast hZu q), ?_⟩
  intro a
  unfold CausalModel.marginal
  rw [PMF.map_apply]
  simp only [fullJoint_apply M htypeU, hF0]
  have hcov2 : L ∪ R ∪ Z = Finset.univ := by
    rw [← hcover]
    ext x
    simp
    tauto
  have htypeA : Assignment (α := α) (L ∪ R ∪ Z)
      = Assignment (α := α) (Finset.univ : Finset V) := by
    rw [hcov2]
  simp only [eq_restrict_iff_eq_cast (L ∪ R ∪ Z) hcov2 htypeA]
  rw [tsum_ite_eq]
  simp only [cast_cast]
  rw [restrict_cast_gen (L ∪ R ∪ Z) (G.verticesUpTo G.maxRank) L
      (L ∩ G.verticesUpTo G.maxRank) (hcov2.trans G.verticesUpTo_maxRank.symm)
      (by rw [G.verticesUpTo_maxRank, Finset.inter_univ])
      (Eq.trans htypeA htypeU) hLu a (subset_union3_left L R Z),
    restrict_cast_gen (L ∪ R ∪ Z) (G.verticesUpTo G.maxRank) Z
      (Z ∩ G.verticesUpTo G.maxRank) (hcov2.trans G.verticesUpTo_maxRank.symm)
      (by rw [G.verticesUpTo_maxRank, Finset.inter_univ])
      (Eq.trans htypeA htypeU) hZu a (subset_union3_right L R Z),
    restrict_cast_gen (L ∪ R ∪ Z) (G.verticesUpTo G.maxRank) R
      (R ∩ G.verticesUpTo G.maxRank) (hcov2.trans G.verticesUpTo_maxRank.symm)
      (by rw [G.verticesUpTo_maxRank, Finset.inter_univ])
      (Eq.trans htypeA htypeU) hRu a (subset_union3_mid L R Z)]
/-- Restriksjon komponerer: `X∪Z` deretter `X` er `X` direkte. -/
@[simp] lemma restrict_XZ_X (X Y Z : Finset V) (u : Assignment (α := α) (X ∪ Y ∪ Z)) :
    (u.restrict (subset_union3_left_right X Y Z)).restrict Finset.subset_union_left
      = u.restrict (subset_union3_left X Y Z) := rfl

/-- Restriksjon komponerer: `X∪Z` deretter `Z` er `Z` direkte. -/
@[simp] lemma restrict_XZ_Z (X Y Z : Finset V) (u : Assignment (α := α) (X ∪ Y ∪ Z)) :
    (u.restrict (subset_union3_left_right X Y Z)).restrict Finset.subset_union_right
      = u.restrict (subset_union3_right X Y Z) := rfl

/-- Restriksjon komponerer: `Y∪Z` deretter `Y` er `Y` direkte. -/
@[simp] lemma restrict_YZ_Y (X Y Z : Finset V) (u : Assignment (α := α) (X ∪ Y ∪ Z)) :
    (u.restrict (subset_union3_mid_right X Y Z)).restrict Finset.subset_union_left
      = u.restrict (subset_union3_mid X Y Z) := rfl

/-- Restriksjon komponerer: `Y∪Z` deretter `Z` er `Z` direkte. -/
@[simp] lemma restrict_YZ_Z (X Y Z : Finset V) (u : Assignment (α := α) (X ∪ Y ∪ Z)) :
    (u.restrict (subset_union3_mid_right X Y Z)).restrict Finset.subset_union_right
      = u.restrict (subset_union3_right X Y Z) := rfl
/-- Marginalen på `X ∪ Z` er `f` ganger summen av `g`-faktorene. -/
lemma marginal_left_factor (M : CausalModel G α) (X Y Z : Finset V)
    (f : Assignment (α := α) (X ∪ Z) → ENNReal)
    (g : Assignment (α := α) (Y ∪ Z) → ENNReal)
    (hfactor : ∀ w : Assignment (α := α) (X ∪ Y ∪ Z),
      (M.marginal (X ∪ Y ∪ Z)) w =
        f (w.restrict (subset_union3_left_right X Y Z)) *
        g (w.restrict (subset_union3_mid_right X Y Z)))
    (w : Assignment (α := α) (X ∪ Y ∪ Z)) :
    (M.marginal (X ∪ Z)) (w.restrict (subset_union3_left_right X Y Z)) =
      f (w.restrict (subset_union3_left_right X Y Z)) *
      ∑' u : Assignment (α := α) (X ∪ Y ∪ Z),
        if w.restrict (subset_union3_left_right X Y Z) =
           u.restrict (subset_union3_left_right X Y Z)
        then g (u.restrict (subset_union3_mid_right X Y Z)) else 0 := by
  rw [← marginal_restrict M (subset_union3_left_right X Y Z), PMF.map_apply]
  rw [ENNReal.tsum_mul_left.symm]
  congr 1
  ext u
  by_cases hu : w.restrict (subset_union3_left_right X Y Z) =
      u.restrict (subset_union3_left_right X Y Z)
  · simp [hu, hfactor u]
  · simp [hu]
/-- Marginalen på `Y ∪ Z` er summen av `f`-faktorene ganger `g`. -/
lemma marginal_right_factor (M : CausalModel G α) (X Y Z : Finset V)
    (f : Assignment (α := α) (X ∪ Z) → ENNReal)
    (g : Assignment (α := α) (Y ∪ Z) → ENNReal)
    (hfactor : ∀ w : Assignment (α := α) (X ∪ Y ∪ Z),
      (M.marginal (X ∪ Y ∪ Z)) w =
        f (w.restrict (subset_union3_left_right X Y Z)) *
        g (w.restrict (subset_union3_mid_right X Y Z)))
    (w : Assignment (α := α) (X ∪ Y ∪ Z)) :
    (M.marginal (Y ∪ Z)) (w.restrict (subset_union3_mid_right X Y Z)) =
      (∑' u : Assignment (α := α) (X ∪ Y ∪ Z),
        if w.restrict (subset_union3_mid_right X Y Z) =
           u.restrict (subset_union3_mid_right X Y Z)
        then f (u.restrict (subset_union3_left_right X Y Z)) else 0) *
      g (w.restrict (subset_union3_mid_right X Y Z)) := by
  rw [← marginal_restrict M (subset_union3_mid_right X Y Z), PMF.map_apply]
  rw [ENNReal.tsum_mul_right.symm]
  congr 1
  ext u
  by_cases hu : w.restrict (subset_union3_mid_right X Y Z) =
      u.restrict (subset_union3_mid_right X Y Z)
  · simp [hu, hfactor u]
  · simp [hu]
/-- En sum over en disjunkt union faktoriserer når integranden gjør det. -/
lemma tsum_assignmentSplit (s t : Finset V) (h : Disjoint s t)
    (F : Assignment (α := α) s → ENNReal)
    (Gf : Assignment (α := α) t → ENNReal) :
    ∑' u : Assignment (α := α) (s ∪ t),
        F ((assignmentSplit s t h u).1) * Gf ((assignmentSplit s t h u).2) =
      (∑' a : Assignment (α := α) s, F a) * (∑' b : Assignment (α := α) t, Gf b) := by
  rw [(assignmentSplit s t h).tsum_eq (fun p => F p.1 * Gf p.2)]
  rw [ENNReal.tsum_prod']
  simp only [ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_mul_right]
/-- Er første komponent låst, kollapser summen til summen over andre. -/
lemma tsum_assignmentSplit_fixed_left (s t : Finset V) (h : Disjoint s t)
    (a0 : Assignment (α := α) s)
    (Gf : Assignment (α := α) t → ENNReal) :
    ∑' u : Assignment (α := α) (s ∪ t),
        (if a0 = (assignmentSplit s t h u).1 then Gf ((assignmentSplit s t h u).2) else 0) =
      ∑' b : Assignment (α := α) t, Gf b := by
  rw [(assignmentSplit s t h).tsum_eq
    (fun p => if a0 = p.1 then Gf p.2 else 0)]
  rw [ENNReal.tsum_prod']
  have h1 : ∀ a : Assignment (α := α) s,
      (∑' b : Assignment (α := α) t, if a0 = a then Gf b else 0)
      = if a0 = a then (∑' b, Gf b) else 0 := by
    intro a
    by_cases ha : a0 = a
    · simp [ha]
    · simp [ha]
  simp only [h1]
  simp only [eq_comm (a := a0)]
  rw [tsum_ite_eq]
/-- Tredelt splitting for parvis disjunkte mengder. -/
def assignmentSplit3 (X Y Z : Finset V) (hXY : Disjoint X Y)
    (hXYZ : Disjoint (X ∪ Y) Z) :
    Assignment (α := α) (X ∪ Y ∪ Z) ≃
      (Assignment (α := α) X × Assignment (α := α) Y) × Assignment (α := α) Z :=
  (assignmentSplit (X ∪ Y) Z hXYZ).trans
    (Equiv.prodCongrLeft (fun _ => assignmentSplit X Y hXY))
/-- Splittingens første komponent er restriksjonen. -/
@[simp] lemma assignmentSplit_fst (s t : Finset V) (h : Disjoint s t)
    (u : Assignment (α := α) (s ∪ t)) :
    (assignmentSplit s t h u).1 = u.restrict Finset.subset_union_left := rfl

/-- Splittingens andre komponent er restriksjonen. -/
@[simp] lemma assignmentSplit_snd (s t : Finset V) (h : Disjoint s t)
    (u : Assignment (α := α) (s ∪ t)) :
    (assignmentSplit s t h u).2 = u.restrict Finset.subset_union_right := rfl
/-- En tilordning er rekonstruksjonen av sine egne komponenter. -/
@[simp] lemma assignmentSplit_symm_restrict (s t : Finset V) (h : Disjoint s t)
    (a : Assignment (α := α) (s ∪ t)) :
    (assignmentSplit s t h).symm
      (a.restrict Finset.subset_union_left, a.restrict Finset.subset_union_right) = a := by
  have hp : (a.restrict Finset.subset_union_left, a.restrict Finset.subset_union_right)
      = assignmentSplit s t h a := rfl
  rw [hp, Equiv.symm_apply_apply]
/-- To tilordninger er like presis når begge komponenter er like. -/
lemma assignment_ext_split (s t : Finset V) (h : Disjoint s t)
    (a b : Assignment (α := α) (s ∪ t)) :
    a = b ↔ (a.restrict Finset.subset_union_left = b.restrict Finset.subset_union_left
           ∧ a.restrict Finset.subset_union_right = b.restrict Finset.subset_union_right) := by
  constructor
  · intro hab
    subst hab
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    have ha := assignmentSplit_symm_restrict s t h a
    have hb := assignmentSplit_symm_restrict s t h b
    rw [← ha, ← hb, h1, h2]
/-- Indikatoren på `X ∪ Z` splitter i komponentene. -/
lemma restrict_XZ_eq_iff (X Y Z : Finset V) (hXZ : Disjoint X Z)
    (w u : Assignment (α := α) (X ∪ Y ∪ Z)) :
    (w.restrict (subset_union3_left_right X Y Z)
       = u.restrict (subset_union3_left_right X Y Z))
    ↔ (w.restrict (subset_union3_left X Y Z) = u.restrict (subset_union3_left X Y Z)
     ∧ w.restrict (subset_union3_right X Y Z) = u.restrict (subset_union3_right X Y Z)) := by
  rw [assignment_ext_split X Z hXZ]
  simp only [restrict_XZ_X, restrict_XZ_Z]

/-- Indikatoren på `Y ∪ Z` splitter i komponentene. -/
lemma restrict_YZ_eq_iff (X Y Z : Finset V) (hYZ : Disjoint Y Z)
    (w u : Assignment (α := α) (X ∪ Y ∪ Z)) :
    (w.restrict (subset_union3_mid_right X Y Z)
       = u.restrict (subset_union3_mid_right X Y Z))
    ↔ (w.restrict (subset_union3_mid X Y Z) = u.restrict (subset_union3_mid X Y Z)
     ∧ w.restrict (subset_union3_right X Y Z) = u.restrict (subset_union3_right X Y Z)) := by
  rw [assignment_ext_split Y Z hYZ]
  simp only [restrict_YZ_Y, restrict_YZ_Z]
/-- Med `X ∪ Z` låst kollapser summen til summen over `Y`. -/
lemma tsum_fixed_XZ2 (X Y Z : Finset V) (hXY : Disjoint X Y) (hYZ : Disjoint Y Z)
    (a0 : Assignment (α := α) (X ∪ Z))
    (Gf : Assignment (α := α) Y → Assignment (α := α) Z → ENNReal) :
    (∑' u : Assignment (α := α) (X ∪ Y ∪ Z),
        if a0 = u.restrict (subset_union3_left_right X Y Z)
        then Gf (u.restrict (subset_union3_mid X Y Z)) (u.restrict (subset_union3_right X Y Z))
        else 0) =
      ∑' b : Assignment (α := α) Y, Gf b (a0.restrict Finset.subset_union_right) := by
  have step : ∀ u : Assignment (α := α) (X ∪ Y ∪ Z),
      (if a0 = u.restrict (subset_union3_left_right X Y Z)
        then Gf (u.restrict (subset_union3_mid X Y Z)) (u.restrict (subset_union3_right X Y Z))
        else 0)
      = (if a0 = u.restrict (subset_union3_left_right X Y Z)
        then Gf (u.restrict (subset_union3_mid X Y Z))
             (a0.restrict Finset.subset_union_right) else 0) := by
    intro u
    by_cases hu : a0 = u.restrict (subset_union3_left_right X Y Z)
    · simp [hu, Assignment.restrict_restrict]
    · simp [hu]
  simp only [step]
  have hd : Disjoint (X ∪ Z) Y := by
    simp [Finset.disjoint_union_left]
    exact ⟨hXY, hYZ.symm⟩
  rw! [Finset.union_assoc, Finset.union_comm Y Z, ← Finset.union_assoc]
  exact tsum_assignmentSplit_fixed_left (X ∪ Z) Y hd a0
    (fun b => Gf b (a0.restrict Finset.subset_union_right))
/-- Med `Y ∪ Z` låst kollapser summen til summen over `X`. -/
lemma tsum_fixed_YZ2 (X Y Z : Finset V) (hXY : Disjoint X Y) (hXZ : Disjoint X Z)
    (b0 : Assignment (α := α) (Y ∪ Z))
    (F : Assignment (α := α) X → Assignment (α := α) Z → ENNReal) :
    (∑' u : Assignment (α := α) (X ∪ Y ∪ Z),
        if b0 = u.restrict (subset_union3_mid_right X Y Z)
        then F (u.restrict (subset_union3_left X Y Z)) (u.restrict (subset_union3_right X Y Z))
        else 0) =
      ∑' a : Assignment (α := α) X, F a (b0.restrict Finset.subset_union_right) := by
  have step : ∀ u : Assignment (α := α) (X ∪ Y ∪ Z),
      (if b0 = u.restrict (subset_union3_mid_right X Y Z)
        then F (u.restrict (subset_union3_left X Y Z)) (u.restrict (subset_union3_right X Y Z))
        else 0)
      = (if b0 = u.restrict (subset_union3_mid_right X Y Z)
        then F (u.restrict (subset_union3_left X Y Z))
             (b0.restrict Finset.subset_union_right) else 0) := by
    intro u
    by_cases hu : b0 = u.restrict (subset_union3_mid_right X Y Z)
    · simp [hu, Assignment.restrict_restrict]
    · simp [hu]
  simp only [step]
  have hd : Disjoint (Y ∪ Z) X := by
    simp [Finset.disjoint_union_left]
    exact ⟨hXY.symm, hXZ.symm⟩
  rw! [Finset.union_comm X Y, Finset.union_assoc, Finset.union_comm X Z,
    ← Finset.union_assoc]
  exact tsum_assignmentSplit_fixed_left (Y ∪ Z) X hd b0
    (fun a => F a (b0.restrict Finset.subset_union_right))
/-- Med bare `Z` låst faktoriserer summen i produktet over `X` og `Y`. -/
lemma tsum_fixed_Z2 (X Y Z : Finset V) (hXY : Disjoint X Y)
    (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (c0 : Assignment (α := α) Z)
    (F : Assignment (α := α) X → Assignment (α := α) Z → ENNReal)
    (Gf : Assignment (α := α) Y → Assignment (α := α) Z → ENNReal) :
    (∑' u : Assignment (α := α) (X ∪ Y ∪ Z),
        if c0 = u.restrict (subset_union3_right X Y Z)
        then F (u.restrict (subset_union3_left X Y Z)) (u.restrict (subset_union3_right X Y Z)) *
             Gf (u.restrict (subset_union3_mid X Y Z)) (u.restrict (subset_union3_right X Y Z))
        else 0) =
      (∑' a : Assignment (α := α) X, F a c0) * (∑' b : Assignment (α := α) Y, Gf b c0) := by
  have step : ∀ u : Assignment (α := α) (X ∪ Y ∪ Z),
      (if c0 = u.restrict (subset_union3_right X Y Z)
        then F (u.restrict (subset_union3_left X Y Z)) (u.restrict (subset_union3_right X Y Z)) *
             Gf (u.restrict (subset_union3_mid X Y Z)) (u.restrict (subset_union3_right X Y Z))
        else 0)
      = (if c0 = u.restrict (subset_union3_right X Y Z)
        then F (u.restrict (subset_union3_left X Y Z)) c0 *
             Gf (u.restrict (subset_union3_mid X Y Z)) c0 else 0) := by
    intro u
    by_cases hu : c0 = u.restrict (subset_union3_right X Y Z)
    · simp [hu]
    · simp [hu]
  simp only [step]
  have hd : Disjoint Z (X ∪ Y) := by
    simp [Finset.disjoint_union_right]
    exact ⟨hXZ.symm, hYZ.symm⟩
  rw! [Finset.union_comm (X ∪ Y) Z]
  have hXY_sub : X ∪ Y ⊆ Z ∪ (X ∪ Y) := Finset.subset_union_right
  simp only [← Assignment.restrict_restrict hXY_sub Finset.subset_union_left,
    ← Assignment.restrict_restrict hXY_sub Finset.subset_union_right,
    ← assignmentSplit_snd Z (X ∪ Y) hd, ← assignmentSplit_fst Z (X ∪ Y) hd]
  rw [tsum_assignmentSplit_fixed_left Z (X ∪ Y) hd c0
    (fun v => F (v.restrict Finset.subset_union_left) c0 *
              Gf (v.restrict Finset.subset_union_right) c0)]
  exact tsum_assignmentSplit X Y hXY (fun a => F a c0) (fun b => Gf b c0)




/-- Marginalen på `Z` er summen av produktet over alle tilordninger som
matcher på `Z`. -/
lemma marginal_base_factor (M : CausalModel G α) (X Y Z : Finset V)
    (f : Assignment (α := α) (X ∪ Z) → ENNReal)
    (g : Assignment (α := α) (Y ∪ Z) → ENNReal)
    (hfactor : ∀ w : Assignment (α := α) (X ∪ Y ∪ Z),
      (M.marginal (X ∪ Y ∪ Z)) w =
        f (w.restrict (subset_union3_left_right X Y Z)) *
        g (w.restrict (subset_union3_mid_right X Y Z)))
    (w : Assignment (α := α) (X ∪ Y ∪ Z)) :
    (M.marginal Z) (w.restrict (subset_union3_right X Y Z)) =
      ∑' u : Assignment (α := α) (X ∪ Y ∪ Z),
        if w.restrict (subset_union3_right X Y Z) =
           u.restrict (subset_union3_right X Y Z)
        then f (u.restrict (subset_union3_left_right X Y Z)) *
             g (u.restrict (subset_union3_mid_right X Y Z)) else 0 := by
  rw [← marginal_restrict M (subset_union3_right X Y Z), PMF.map_apply]
  congr 1
  ext u
  by_cases hu : w.restrict (subset_union3_right X Y Z) =
      u.restrict (subset_union3_right X Y Z)
  · simp [hu, hfactor u]
  · simp [hu]


/--
Product form gives `CondIndep` directly, since `CondIndep` is already
multiplicative — no division, no positivity side conditions.
`joint_splits`. The hypothesis says the joint factors into a function of
`X ∪ Z` and one of `Y ∪ Z`.
-/
theorem condIndep_of_product_form (M : CausalModel G α) (X Y Z : Finset V)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (f : Assignment (α := α) (X ∪ Z) → ENNReal)
    (g : Assignment (α := α) (Y ∪ Z) → ENNReal)
    (F : Assignment (α := α) X → Assignment (α := α) Z → ENNReal)
    (Gf : Assignment (α := α) Y → Assignment (α := α) Z → ENNReal)
    (hf : ∀ a : Assignment (α := α) (X ∪ Z),
      f a = F (a.restrict Finset.subset_union_left) (a.restrict Finset.subset_union_right))
    (hg : ∀ b : Assignment (α := α) (Y ∪ Z),
      g b = Gf (b.restrict Finset.subset_union_left) (b.restrict Finset.subset_union_right))
    (hfactor : ∀ w : Assignment (α := α) (X ∪ Y ∪ Z),
      (M.marginal (X ∪ Y ∪ Z)) w =
        f (w.restrict (subset_union3_left_right X Y Z)) *
        g (w.restrict (subset_union3_mid_right X Y Z))) :
    CondIndep M X Y Z := by
  intro w
  rw [hfactor w]
  rw [marginal_left_factor M X Y Z f g hfactor w,
      marginal_right_factor M X Y Z f g hfactor w,
      marginal_base_factor M X Y Z f g hfactor w]
  have key : (∑' u : Assignment (α := α) (X ∪ Y ∪ Z),
      if w.restrict (subset_union3_right X Y Z) = u.restrict (subset_union3_right X Y Z)
      then f (u.restrict (subset_union3_left_right X Y Z)) *
           g (u.restrict (subset_union3_mid_right X Y Z)) else 0) =
      (∑' u : Assignment (α := α) (X ∪ Y ∪ Z),
        if w.restrict (subset_union3_left_right X Y Z) = u.restrict (subset_union3_left_right X Y Z)
        then g (u.restrict (subset_union3_mid_right X Y Z)) else 0) *
      (∑' u : Assignment (α := α) (X ∪ Y ∪ Z),
        if w.restrict (subset_union3_mid_right X Y Z) = u.restrict (subset_union3_mid_right X Y Z)
        then f (u.restrict (subset_union3_left_right X Y Z)) else 0) := by
    simp only [hf, hg, restrict_XZ_X, restrict_XZ_Z, restrict_YZ_Y, restrict_YZ_Z]
    rw [tsum_fixed_Z2 X Y Z hXY hXZ hYZ (w.restrict (subset_union3_right X Y Z)) F Gf,
      tsum_fixed_XZ2 X Y Z hXY hYZ (w.restrict (subset_union3_left_right X Y Z)) Gf,
      tsum_fixed_YZ2 X Y Z hXY hXZ (w.restrict (subset_union3_mid_right X Y Z)) F]
    simp only [Assignment.restrict_restrict]
    ring
  rw [key]
  ring

/-! Sluttmonteringen er `DSepSound.dsep_sound` i `DSepSound.lean`. -/

end PearlDoCalculus
