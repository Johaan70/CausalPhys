/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import PearlDoCalculus.DAG
import PearlDoCalculus.DSeparation
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# d-separasjonsfundamentet, forarbeid: generell kausalmodell over vilkårlig DAG

Steg 1–4 i 4b (Reachability, Walks, Blocking, DSeparation) ga det
kombinatoriske fundamentet — d-separasjon som en ren egenskap ved grafen,
uten referanse til sannsynlighet. Steg 5, soundness, krever å koble dette
til en faktisk generativ semantikk: at d-separasjon i grafen medfører
betinget uavhengighet i fordelingen grafen genererer.

Denne filen bygger den semantikken. `SimpleConfounderModel`, `MediatorModel`
og `FrontDoorModel` var hver håndbygd for én bestemt DAG-form; `CausalModel`
generaliserer dem til en vilkårlig `DAG V`, med typesignaturen selv som
håndhever Markov-faktoriseringen (en nodes kjerne kan bare avhenge av dens
foreldre). `jointUpTo` bygger fellesfordelingen rekursivt over rang, ett
steg i taket, og `fullJoint`/`marginal` gir fellesfordelingen over hele `V`
og marginalisering til vilkårlige delmengder.

## Hva er bevist

`CausalModel`, `Assignment` (med `restrict` og `extend`), `verticesUpTo`,
`newAtRank`, og deres foreldre-lemmaer — alt kombinatorisk forarbeid.
`extendOverList` og `jointUpTo` — selve konstruksjonen, verifisert uten
`sorry`: fellesfordelingen eksisterer og er korrekt typet for enhver
`CausalModel`. `maxRank`, `fullJoint`, `marginal` — fellesfordelingen
utvidet til hele grafen, med marginalisering.

## Hva gjenstår

`CondIndep` (betinget uavhengighet som en `Prop`) er ikke skrevet ennå —
den krever å uttrykke tre konsistente restriksjoner av én assignment på
`X ∪ Y ∪ Z` ned til `X ∪ Z`, `Y ∪ Z` og `Z`, som fortjener sin egen
testede runde før den kombineres med noe annet. Selve soundness-teoremet
(`DSeparated → CondIndep`) er deretter formulerbart, men beviset — en
strukturell induksjon over blokkerte/åpne vandringer, den faktiske
matematiske substansen i Verma–Pearl-argumentet — er et eget, betydelig
prosjekt, ikke en forlengelse av dagens forarbeid.
-/

namespace PearlDoCalculus
namespace DAG

universe u v
variable {V : Type u} [DecidableEq V] [Fintype V]

/--
A causal model over a DAG `G`: each vertex `v` gets a value type `α v`,
and a conditional kernel that depends *only* on the values of `v`'s parents
— exactly Pearl's Markov factorization, encoded so the type signature itself
forbids a kernel from depending on a non-parent.
-/
structure CausalModel (G : DAG V) (α : V → Type v) where
  /-- Fintype instance per vertex value type, needed for PMF/Finset sums. -/
  fin : ∀ v, Fintype (α v)
  /-- Decidable equality per vertex value type. -/
  deq : ∀ v, DecidableEq (α v)
  /-- The conditional kernel: value distribution at `v` given parent values. -/
  kernel : ∀ v, (∀ u : {u // u ∈ G.parents v}, α u.1) → PMF (α v)


/--
Vertices with rank at most `n` — the finite "prefix" of the topological
order used to build the joint distribution incrementally.

Defined here at the `DAG` level (not inside `CausalModel`) so that dot
notation `G.verticesUpTo n` resolves — a nested namespace would have made
this `DAG.CausalModel.verticesUpTo`, invisible to dot notation on `G : DAG V`.
-/
def verticesUpTo (G : DAG V) (n : ℕ) : Finset V :=
  (Finset.univ : Finset V).filter (fun v => G.rank v ≤ n)

/--
**Key structural fact**: if `v` has rank ≤ n+1, every parent of `v` has
rank ≤ n. This licenses feeding a `verticesUpTo n`-assignment into
`kernel v` when extending to `verticesUpTo (n+1)`.
-/
theorem parents_subset_verticesUpTo (G : DAG V) (n : ℕ) {v : V}
    (hv : v ∈ G.verticesUpTo (n + 1)) :
    G.parents v ⊆ G.verticesUpTo n := by
  intro u hu
  simp only [verticesUpTo, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  have hedge : G.edge u v := by simpa [parents, Finset.mem_filter] using hu
  have := G.rank_strict_mono u v hedge
  omega

/--
Vertices whose rank is *exactly* `n` — the "new" vertices added when
extending `verticesUpTo (n-1)` to `verticesUpTo n`. `jointUpTo` will process
these one at a time via `Assignment.extend`.
-/
def newAtRank (G : DAG V) (n : ℕ) : Finset V :=
  (Finset.univ : Finset V).filter (fun v => G.rank v = n)

/-- `verticesUpTo` grows by exactly `newAtRank` at each step. -/
theorem verticesUpTo_succ (G : DAG V) (n : ℕ) :
    G.verticesUpTo (n + 1) = G.verticesUpTo n ∪ G.newAtRank (n + 1) := by
  ext v
  simp only [verticesUpTo, newAtRank, Finset.mem_union, Finset.mem_filter,
    Finset.mem_univ, true_and]
  omega

/--
Every parent of a rank-`(n+1)` vertex already lies in `verticesUpTo n` —
the specialization of `parents_subset_verticesUpTo` that `jointUpTo`'s
successor step actually needs: it justifies feeding the *already-built*
assignment on `verticesUpTo n` into `kernel v` for each `v` newly appearing
at rank `n+1`, regardless of which other rank-`(n+1)` vertices have or
haven't been processed yet in the same step.
-/
theorem parents_subset_verticesUpTo_of_newAtRank (G : DAG V) (n : ℕ) {v : V}
    (hv : v ∈ G.newAtRank (n + 1)) :
    G.parents v ⊆ G.verticesUpTo n := by
  apply G.parents_subset_verticesUpTo n
  simp only [verticesUpTo, newAtRank, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  omega

/--
Rank-0 vertices have no parents: `rank_strict_mono` would force a parent's
rank strictly below 0, impossible in `ℕ`. This is what licenses `jointUpTo`'s
base case — every rank-0 vertex's kernel can be sampled unconditionally.
-/
theorem parents_empty_of_rank_zero (G : DAG V) {v : V} (hv : G.rank v = 0) :
    G.parents v = ∅ := by
  ext u
  constructor
  · intro hu
    have hedge : G.edge u v := by simpa [parents, Finset.mem_filter] using hu
    exact absurd (G.rank_strict_mono u v hedge) (by omega)
  · intro hu
    simp at hu

/--
The maximum rank appearing anywhere in the DAG. Finite since `V` is a
`Fintype`; `Finset.univ.sup` returns `0` gracefully if `V` is empty.
-/
def maxRank (G : DAG V) : ℕ := Finset.univ.sup G.rank

/--
At `n = maxRank`, `verticesUpTo` covers every vertex — this is what lets us
define the FULL joint distribution over `V`, not just a rank-bounded prefix.
-/
theorem verticesUpTo_maxRank (G : DAG V) : G.verticesUpTo G.maxRank = Finset.univ := by
  ext v
  simp only [verticesUpTo, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  exact Finset.le_sup (Finset.mem_univ v)

/--
`X` is a subset of `X ∪ Y ∪ Z` — the first of three subset facts `CondIndep`
needs to restrict a single assignment on `X ∪ Y ∪ Z` down to each of its
three constituent pieces.

Written via `Finset.mem_union.mpr` chains rather than named subset lemmas
(`Finset.subset_union_left` etc.) — those exact names/signatures caused
friction earlier in this project, while `Finset.mem_union` is confirmed
working throughout this file.
-/
theorem subset_union3_left (X Y Z : Finset V) : X ⊆ X ∪ Y ∪ Z :=
  fun x hx => Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hx)))

theorem subset_union3_mid (X Y Z : Finset V) : Y ⊆ X ∪ Y ∪ Z :=
  fun x hx => Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hx)))

theorem subset_union3_right (X Y Z : Finset V) : Z ⊆ X ∪ Y ∪ Z :=
  fun x hx => Finset.mem_union.mpr (Or.inr hx)

theorem subset_union3_left_right (X Y Z : Finset V) : X ∪ Z ⊆ X ∪ Y ∪ Z :=
  fun x hx => (Finset.mem_union.mp hx).elim
    (fun hxX => subset_union3_left X Y Z hxX)
    (fun hxZ => subset_union3_right X Y Z hxZ)

theorem subset_union3_mid_right (X Y Z : Finset V) : Y ∪ Z ⊆ X ∪ Y ∪ Z :=
  fun x hx => (Finset.mem_union.mp hx).elim
    (fun hxY => subset_union3_mid X Y Z hxY)
    (fun hxZ => subset_union3_right X Y Z hxZ)

namespace CausalModel

variable {G : DAG V} {α : V → Type v} (M : CausalModel G α)

/--
`Assignment S`: a full assignment of values to every vertex in a finite
set `S : Finset V` — a dependent function matching `kernel`'s own
signature, so that `restrict`/`extend` compose with it directly.
-/
def Assignment (S : Finset V) : Type (max u v) := ∀ v : {v // v ∈ S}, α v.1

/--
Restriction of an assignment on `S` to an assignment on a subset `T ⊆ S`.
Needed to feed a full assignment on "all lower-ranked vertices" into
`kernel v`, which only wants the assignment on `parents v`.
-/
def Assignment.restrict {S T : Finset V} (h : T ⊆ S) (a : Assignment (α := α) S) :
    Assignment (α := α) T :=
  fun t => a ⟨t.1, h t.2⟩

/--
Restricting twice in a row is the same as restricting once, along the
composed subset relation. Purely about our own `Assignment.restrict`
definition — no external lemma names needed, just unfolding.

This is the building block for the next real target: "the marginal of a
marginal is the smaller marginal" (`(M.marginal S).map (restrict h) =
M.marginal T`), which `CondIndep` sanity checks and eventually `dsep_sound`
will both lean on.
-/
theorem Assignment.restrict_restrict {S T U : Finset V} (hTS : T ⊆ S) (hUT : U ⊆ T)
    (a : Assignment (α := α) S) :
    (a.restrict hTS).restrict hUT = a.restrict (hUT.trans hTS) := by
  funext u
  rfl

/--
`Assignment.extend a x`: extend an assignment on `S` with a single new
value `x : α v` at a vertex `v ∉ S`, giving an assignment on `insert v S`.

This is the atomic gluing primitive `jointUpTo` will fold over — building
the joint distribution one vertex at a time, in any linear order extending
the rank order. Ties between same-rank vertices are safe to break
arbitrarily: `rank_strict_mono` guarantees no edge exists between them, so
sequential single-vertex binds (rather than a simultaneous multi-way bind
per rank level) suffice and are considerably more tractable to write.
-/
def Assignment.extend {S : Finset V} (a : Assignment (α := α) S) {v : V}
    (x : α v) : Assignment (α := α) (insert v S) :=
  fun w =>
    if h : w.1 = v then
      cast (congrArg α h.symm) x
    else
      a ⟨w.1, (Finset.mem_insert.mp w.2).resolve_left h⟩

/-- Extending then evaluating at the new vertex gives back `x`. -/
theorem Assignment.extend_self {S : Finset V} (a : Assignment (α := α) S) {v : V}
    (x : α v) (hv : v ∈ insert v S := Finset.mem_insert_self v S) :
    (Assignment.extend a x) ⟨v, hv⟩ = x := by
  unfold Assignment.extend
  simp

/-- Extending then evaluating at an old vertex agrees with the original. -/
theorem Assignment.extend_old {S : Finset V} (a : Assignment (α := α) S) {v : V}
    (x : α v) {w : V} (hw : w ∈ S) (hne : w ≠ v)
    (hw' : w ∈ insert v S := Finset.mem_insert_of_mem hw) :
    (Assignment.extend a x) ⟨w, hw'⟩ = a ⟨w, hw⟩ := by
  unfold Assignment.extend
  simp [hne]

/--
Fold `M.kernel` over a `List V` of vertices, extending an existing
assignment `base` on `B` by sampling each `v` in the list conditioned on the
(already-fixed) restriction of `base` to `parents v` — licensed by `hpar`.

Recurses directly over the `List` rather than via `Finset.induction`:
Mathlib's `Finset` induction principles are restricted to `Prop`-valued
motives, but ours is `Type`-valued (`PMF (Assignment ...)`). `List.rec` has
no such restriction, so recursing over `T.toList` sidesteps it cleanly.
-/
noncomputable def extendOverList (M : CausalModel G α) (B : Finset V)
    (base : Assignment (α := α) B) :
    ∀ l : List V, (∀ v ∈ l, G.parents v ⊆ B) → PMF (Assignment (α := α) (B ∪ l.toFinset))
  | [], _ =>
      cast (congrArg (fun S => PMF (Assignment (α := α) S)) (by simp : B ∪ ([] : List V).toFinset = B).symm)
        (PMF.pure base)
  | (v :: vs), hpar =>
      have hparvs : ∀ w ∈ vs, G.parents w ⊆ B := fun w hw => hpar w (List.mem_cons_of_mem v hw)
      have hparv : G.parents v ⊆ B := hpar v List.mem_cons_self
      (extendOverList M B base vs hparvs).bind (fun asg =>
        have hsub : G.parents v ⊆ B ∪ vs.toFinset :=
          fun x hx => Finset.mem_union.mpr (Or.inl (hparv hx))
        have huniq : B ∪ (v :: vs).toFinset = insert v (B ∪ vs.toFinset) := by
          ext y
          simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_cons]
          tauto
        (M.kernel v (asg.restrict hsub)).map (fun x =>
          cast (congrArg (fun S => Assignment (α := α) S) huniq.symm) (Assignment.extend asg x)))

/--
The joint distribution over `verticesUpTo n`, built by recursion on `n`:
rank-0 vertices are sampled unconditionally (their parent set is provably
empty), and each successive rank level extends the previous assignment via
`extendOverList`, licensed by `parents_subset_verticesUpTo_of_newAtRank`.
-/
noncomputable def jointUpTo (M : CausalModel G α) :
    ∀ n : ℕ, PMF (Assignment (α := α) (G.verticesUpTo n))
  | 0 =>
      cast (congrArg (fun S => PMF (Assignment (α := α) S))
        (by simp : (∅ : Finset V) ∪ (G.verticesUpTo 0).toList.toFinset = G.verticesUpTo 0))
        (extendOverList M ∅
          (fun v => absurd v.2 (show v.1 ∉ (∅ : Finset V) by
            first
            | exact Finset.not_mem_empty _
            | exact Finset.notMem_empty _
            | simp))
          (G.verticesUpTo 0).toList
          (fun v hv => by
            have hv' : v ∈ G.verticesUpTo 0 := by simpa using hv
            have hr0 : G.rank v = 0 := by
              apply Nat.le_zero.mp
              simp only [verticesUpTo, Finset.mem_filter, Finset.mem_univ, true_and] at hv'
              exact hv'
            simp [G.parents_empty_of_rank_zero hr0]))
  | (n + 1) =>
      cast (congrArg (fun S => PMF (Assignment (α := α) S))
        (by
          rw [G.verticesUpTo_succ n]
          simp : G.verticesUpTo n ∪ (G.newAtRank (n + 1)).toList.toFinset
              = G.verticesUpTo (n + 1)))
        ((jointUpTo M n).bind (fun asg =>
          extendOverList M (G.verticesUpTo n) asg (G.newAtRank (n + 1)).toList
            (fun v hv => by
              have hv' : v ∈ G.newAtRank (n + 1) := by simpa using hv
              exact G.parents_subset_verticesUpTo_of_newAtRank n hv')))

/--
The full joint distribution over every vertex in `V` — `jointUpTo` at the
maximum rank, transported along `verticesUpTo_maxRank` to land on `univ`
rather than a rank-bounded prefix. This is the object conditional
independence statements will ultimately be about.
-/
noncomputable def fullJoint (M : CausalModel G α) :
    PMF (Assignment (α := α) (Finset.univ : Finset V)) :=
  cast (congrArg (fun S => PMF (Assignment (α := α) S)) G.verticesUpTo_maxRank)
    (jointUpTo M G.maxRank)

/--
Marginal distribution over any subset `S` of vertices, pushed forward from
`fullJoint` via `Assignment.restrict`. `PMF.map` handles the
"sum out everything not in `S`" step automatically.
-/
noncomputable def marginal (M : CausalModel G α) (S : Finset V) :
    PMF (Assignment (α := α) S) :=
  (M.fullJoint).map (Assignment.restrict (Finset.subset_univ S))

/--
The marginal of a marginal is the smaller marginal: further-restricting an
already-marginalized distribution gives the same result as marginalizing
directly to the smaller set.

Proof strategy: both `marginal S` and `marginal T` are `fullJoint` pushed
forward through composed restrictions; `Assignment.restrict_restrict`
shows the two restrictions compose into one, and since `T ⊆ S`/`T ⊆ univ`
are `Prop`s, any two proofs of the same subset fact are definitionally
equal (proof irrelevance) — so the composed restriction IS `restrict
(subset_univ T)`, no separate rewriting needed for that part.
-/
theorem marginal_restrict (M : CausalModel G α) {S T : Finset V} (h : T ⊆ S) :
    (M.marginal S).map (Assignment.restrict h) = M.marginal T := by
  unfold marginal
  have hcomp : ∀ a : Assignment (α := α) (Finset.univ : Finset V),
      Assignment.restrict h (Assignment.restrict (Finset.subset_univ S) a)
        = Assignment.restrict (Finset.subset_univ T) a :=
    fun a => Assignment.restrict_restrict (Finset.subset_univ S) h a
  have hstep : (M.fullJoint.map (Assignment.restrict (Finset.subset_univ S))).map
      (Assignment.restrict h)
      = M.fullJoint.map (Assignment.restrict h ∘ Assignment.restrict (Finset.subset_univ S)) := by
    first
    | rw [PMF.map_map]
    | rw [PMF.map_comp]
    | simp [PMF.map_map]
    | simp [PMF.map_comp]
  rw [hstep]
  congr 1

/--
Conditional independence of `X` and `Y` given `Z` (three `Finset V`s of
vertices), in the distribution `M.fullJoint` generates.

Stated multiplicatively over a single assignment `w` on `X ∪ Y ∪ Z`, rather
than as a division `P(X,Y|Z) = P(X|Z)·P(Y|Z)` — the same style used
throughout this project (`backdoor_general`, `condY_eq_kernel`) to avoid
dividing by a possibly-zero marginal. Cross-multiplied:

  `P(X,Y,Z) · P(Z) = P(X,Z) · P(Y,Z)`

with each factor read off `w`'s restriction to the relevant subset, via
the `subset_union3_*` facts.
-/
def CondIndep (M : CausalModel G α) (X Y Z : Finset V) : Prop :=
  ∀ w : Assignment (α := α) (X ∪ Y ∪ Z),
    (M.marginal (X ∪ Y ∪ Z) w) * (M.marginal Z (w.restrict (subset_union3_right X Y Z)))
      = (M.marginal (X ∪ Z) (w.restrict (subset_union3_left_right X Y Z)))
        * (M.marginal (Y ∪ Z) (w.restrict (subset_union3_mid_right X Y Z)))


end CausalModel

end DAG
end PearlDoCalculus
