import PearlDoCalculus.DSepSoundSkeleton

/-!
# Counterexample: `moral_sep_of_dsep` is false as stated

Graph on `Fin 3`: `0 → 2 ← 1` (a collider at 2). With `Z = ∅` and `A = univ`:

* `A` is ancestrally closed and contains `0`, `1` and `Z`;
* `0` and `1` are d-separated by `∅` (every walk passes 2 as a collider);
* but the moral graph over `A` marries the parents `0` and `1`, so they are
  adjacent and cannot be separated by `∅`.

The fix is Lauritzen's formulation: take `A = ancestors G ({x, y} ∪ Z)`.
Here that is `{0, 1}`, which does not contain the collider, so no marriage.
-/

open PearlDoCalculus DAG

namespace Counterexample

/-- The collider graph `0 → 2 ← 1`. Rank 1 for the sink, 0 otherwise. -/
def ceG : DAG (Fin 3) where
  edge u v := v = 2 ∧ u ≠ 2
  decEdge := fun u v => inferInstanceAs (Decidable (v = 2 ∧ u ≠ 2))
  rank v := if v = 2 then 1 else 0
  rank_strict_mono := by
    intro u v h
    obtain ⟨hv, hu⟩ := h
    simp [hv, hu]

/-- Arriving at the sink 2 along an arrow, any continuation is blocked:
    the only way out of 2 is against an arrow, making 2 a collider. -/
lemma blocked_from_sink {t : Fin 3} (ht : t ≠ 2) (p : Walk ceG 2 t) :
    Walk.blockedAux (∅ : Finset (Fin 3)) .fwd p := by
  cases p with
  | nil => exact absurd rfl ht
  | fwd e rest => exact absurd e.2 (by decide)
  | bwd e rest => exact Or.inl (by simp)

/-- Every walk between two distinct non-sink vertices is blocked by `∅`. -/
lemma blocked_from_source {a t : Fin 3} (ha : a ≠ 2) (ht : t ≠ 2) (hat : a ≠ t)
    (p : Walk ceG a t) : Walk.Blocked (∅ : Finset (Fin 3)) p := by
  cases p with
  | nil => exact absurd rfl hat
  | fwd e rest =>
    have hb := e.1
    subst hb
    exact blocked_from_sink ht rest
  | bwd e rest => exact absurd e.1 ha

/-- `moral_sep_of_dsep` fails: all hypotheses hold, the conclusion does not. -/
theorem moral_sep_of_dsep_counterexample :
    ∃ (G : DAG (Fin 3)) (Z A : Finset (Fin 3)) (x y : Fin 3),
      (∀ v ∈ A, ∀ w, G.edge w v → w ∈ A) ∧ x ∈ A ∧ y ∈ A ∧ (∀ z ∈ Z, z ∈ A) ∧
      G.DSeparated Z x y ∧ ¬ Separates (moralGraph G A) Z x y := by
  refine ⟨ceG, ∅, Finset.univ, 0, 1,
    fun _ _ _ _ => Finset.mem_univ _, Finset.mem_univ _, Finset.mem_univ _,
    fun _ _ => Finset.mem_univ _, ?_, ?_⟩
  · intro p
    exact blocked_from_source (by decide) (by decide) (by decide) p
  · intro hsep
    have hadj : (moralGraph ceG Finset.univ).Adj 0 1 := by
      simp only [moralGraph, SimpleGraph.fromRel_adj]
      refine ⟨by decide, Or.inl ⟨Finset.mem_univ _, Finset.mem_univ _,
        Or.inr ⟨2, Finset.mem_univ _, ⟨rfl, by decide⟩, ⟨rfl, by decide⟩⟩⟩⟩
    obtain ⟨z, hz, _⟩ := hsep (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil)
    exact absurd hz (by simp)

end Counterexample

#print axioms Counterexample.moral_sep_of_dsep_counterexample
