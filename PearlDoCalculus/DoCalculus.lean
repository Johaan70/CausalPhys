import PearlDoCalculus.SetSound

/-!
# Do-kalkulus: intervensjoner, trunkert faktorisering og regel 1

`cutIn G X` er Pearls `G_{X̄}` (innkommende kanter til `X` fjernet), og
`cutOut G X` er `G_{X̲}` (utgående kanter fra `X` fjernet). `doModel M X x` er
intervensjonen `do(X = x)`: en kausalmodell på `cutIn G X` der nodene i `X` har
punktmasse på `x`, og resten beholder kjernene sine.

`doModel_fullJoint` er den trunkerte faktoriseringen, og viser at `doModel` er
Pearls intervensjon. Regel 1 følger da av `dsep_sound_set` på den manipulerte
modellen.
-/

open PearlDoCalculus DAG DAG.CausalModel Classical

namespace DoCalculus

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V}

/-- Pearls `G_{X̄}`: innkommende kanter til `X` fjernet. -/
def cutIn (G : DAG V) (X : Finset V) : DAG V where
  edge u v := G.edge u v ∧ v ∉ X
  decEdge := by infer_instance
  rank := G.rank
  rank_strict_mono := fun u v h => G.rank_strict_mono u v h.1

/-- Pearls `G_{X̲}`: utgående kanter fra `X` fjernet. -/
def cutOut (G : DAG V) (X : Finset V) : DAG V where
  edge u v := G.edge u v ∧ u ∉ X
  decEdge := by infer_instance
  rank := G.rank
  rank_strict_mono := fun u v h => G.rank_strict_mono u v h.1

lemma mem_parents_cutIn {X : Finset V} {u v : V} :
    u ∈ (cutIn G X).parents v ↔ u ∈ G.parents v ∧ v ∉ X := by
  simp [DAG.parents, cutIn]

/-- Nodene i `X` har ingen foreldre i `G_{X̄}`. -/
lemma parents_cutIn_of_mem {X : Finset V} {v : V} (hv : v ∈ X) :
    (cutIn G X).parents v = ∅ := by
  ext u
  simp [DAG.parents, cutIn, hv]

/-- Utenfor `X` er foreldrene de samme som i `G`. -/
lemma parents_cutIn_of_not_mem {X : Finset V} {v : V} (hv : v ∉ X) :
    (cutIn G X).parents v = G.parents v := by
  ext u
  simp [DAG.parents, cutIn, hv]

/-- **Intervensjonen `do(X = x)`.** Punktmasse på `x` i `X`; utenfor `X` er
kjernen uendret, med foreldretilordningen bygd direkte (ingen transport). -/
noncomputable def doModel {α : V → Type*} (M : G.CausalModel α) (X : Finset V)
    (x : Assignment (α := α) X) : (cutIn G X).CausalModel α where
  fin := M.fin
  deq := M.deq
  kernel := fun v p =>
    if hv : v ∈ X then PMF.pure (x ⟨v, hv⟩)
    else M.kernel v (fun u => p ⟨u.1, mem_parents_cutIn.mpr ⟨u.2, hv⟩⟩)

/-- Kjernefaktorene til intervensjonsmodellen: indikator i `X`, uendret utenfor. -/
lemma kfac_doModel {α : V → Type*} (M : G.CausalModel α) (X : Finset V)
    (x : Assignment (α := α) X)
    (u : Assignment (α := α) (Finset.univ : Finset V)) (v : V) :
    kfac (doModel M X x) Finset.univ u v =
      if hv : v ∈ X then (if u ⟨v, Finset.mem_univ v⟩ = x ⟨v, hv⟩ then 1 else 0)
      else kfac M Finset.univ u v := by
  have hc : v ∈ (Finset.univ : Finset V) ∧ (cutIn G X).parents v ⊆ Finset.univ :=
    ⟨Finset.mem_univ v, Finset.subset_univ _⟩
  have hc' : v ∈ (Finset.univ : Finset V) ∧ G.parents v ⊆ Finset.univ :=
    ⟨Finset.mem_univ v, Finset.subset_univ _⟩
  unfold kfac
  simp only [dif_pos hc, dif_pos hc']
  by_cases hv : v ∈ X
  · simp only [doModel, dif_pos hv, PMF.pure_apply]
  · simp only [doModel, dif_neg hv]
    all_goals rfl

/-- **Trunkert faktorisering.** Fellesfordelingen under `do(X = x)` er
indikatoren på `u_X = x` ganger kjernene utenfor `X`. -/
theorem doModel_fullJoint {α : V → Type*} (M : G.CausalModel α) (X : Finset V)
    (x : Assignment (α := α) X)
    (u : Assignment (α := α) (Finset.univ : Finset V)) :
    (doModel M X x).fullJoint u =
      (if u.restrict (Finset.subset_univ X) = x then 1 else 0) *
        ∏ v ∈ Xᶜ, kfac M Finset.univ u v := by
  rw [fullJoint_apply_prod, ← Finset.prod_mul_prod_compl X]
  congr 1
  · by_cases h : u.restrict (Finset.subset_univ X) = x
    · rw [if_pos h]
      refine Finset.prod_eq_one (fun v hv => ?_)
      rw [kfac_doModel, dif_pos hv, if_pos]
      exact congrFun h ⟨v, hv⟩
    · rw [if_neg h]
      obtain ⟨⟨v, hv⟩, hne⟩ := Function.ne_iff.mp h
      refine Finset.prod_eq_zero hv ?_
      rw [kfac_doModel, dif_pos hv,
        if_neg (show ¬ (u ⟨v, Finset.mem_univ v⟩ = x ⟨v, hv⟩) from hne)]
  · exact Finset.prod_congr rfl (fun v hv => by
      rw [kfac_doModel, dif_neg (Finset.mem_compl.mp hv)])

/-- **Kontroll: intervensjonen setter `X`.** Under `do(X = x)` er marginalen
på `X` en punktmasse på `x`. -/
theorem doModel_marginal_self {α : V → Type*} (M : G.CausalModel α) (X : Finset V)
    (x : Assignment (α := α) X) :
    (doModel M X x).marginal X x = 1 := by
  rw [PMF.apply_eq_one_iff]
  have hsub : ((doModel M X x).marginal X).support ⊆ {x} := by
    intro a ha
    unfold CausalModel.marginal at ha
    rw [PMF.support_map] at ha
    obtain ⟨u, hu, rfl⟩ := ha
    rw [Set.mem_singleton_iff]
    by_contra hne
    rw [PMF.mem_support_iff, doModel_fullJoint, if_neg hne, zero_mul] at hu
    exact hu rfl
  exact (PMF.support_nonempty _).subset_singleton_iff.mp hsub

/-- **Kontroll: `do(∅)` endrer ingenting.** -/
theorem doModel_empty {α : V → Type*} (M : G.CausalModel α)
    (x : Assignment (α := α) (∅ : Finset V))
    (u : Assignment (α := α) (Finset.univ : Finset V)) :
    (doModel M ∅ x).fullJoint u = M.fullJoint u := by
  have hemp : u.restrict (Finset.subset_univ (∅ : Finset V)) = x :=
    funext fun t => by obtain ⟨v, hv⟩ := t; simp at hv
  rw [doModel_fullJoint, if_pos hemp, one_mul, Finset.compl_empty, fullJoint_apply_prod]

/-- **Regel 1 (fjerning av observasjon).** Er `Y` og `Z` d-separert av `X ∪ W`
i `G_{X̄}`, er de betinget uavhengige gitt `X ∪ W` under `do(X = x)`. -/
theorem rule1 {α : V → Type*} (M : G.CausalModel α) (X W Y Z : Finset V)
    (x : Assignment (α := α) X)
    (hY : Disjoint Y (X ∪ W)) (hZ : Disjoint Z (X ∪ W))
    (h : SetSound.DSeparatedSet (cutIn G X) (X ∪ W) Y Z) :
    (doModel M X x).CondIndep Y Z (X ∪ W) :=
  SetSound.dsep_sound_set (doModel M X x) Y Z (X ∪ W) hY hZ h

/-! ## Regel 2: klemmodellen

`clampModel M Z z₀` er en kausalmodell på `G_{Z̲}` der hver node beholder kjernen
fra `M`, men foreldre i `Z` leses fra `z₀`. Den inneholder både `P` og `P_{z₀}`:
(i) når tilordningen har `Z = z₀`, er den lik `M`; (ii) utenfor `Z` er den lik
intervensjonen `do(Z = z₀)`, fordi nodene i `Z` er sluk i `G_{Z̲}`. Regel 2
følger da av `dsep_sound_set` anvendt på klemmodellen. -/

lemma mem_parents_cutOut {Z : Finset V} {u v : V} :
    u ∈ (cutOut G Z).parents v ↔ u ∈ G.parents v ∧ u ∉ Z := by
  simp [DAG.parents, cutOut]

/-- **Klemmodellen.** Kjernene fra `M`, med foreldre i `Z` klemt til `z₀`. -/
noncomputable def clampModel {α : V → Type*} (M : G.CausalModel α) (Z : Finset V)
    (z₀ : Assignment (α := α) Z) : (cutOut G Z).CausalModel α where
  fin := M.fin
  deq := M.deq
  kernel := fun v p => M.kernel v (fun u =>
    if hu : u.1 ∈ Z then z₀ ⟨u.1, hu⟩ else p ⟨u.1, mem_parents_cutOut.mpr ⟨u.2, hu⟩⟩)

/-- Er `u` og `u′` like utenfor `Z`, har `u′` verdien `z₀` på `Z`, og har `v`
samme verdi i begge, så er klemfaktoren i `u` lik `M`-faktoren i `u′`. -/
lemma kfac_clamp {α : V → Type*} (M : G.CausalModel α) (Z : Finset V)
    (z₀ : Assignment (α := α) Z)
    (u u' : Assignment (α := α) (Finset.univ : Finset V)) (v : V)
    (hagree : ∀ w, w ∉ Z → u ⟨w, Finset.mem_univ w⟩ = u' ⟨w, Finset.mem_univ w⟩)
    (hz : u'.restrict (Finset.subset_univ Z) = z₀)
    (hval : u ⟨v, Finset.mem_univ v⟩ = u' ⟨v, Finset.mem_univ v⟩) :
    kfac (clampModel M Z z₀) Finset.univ u v = kfac M Finset.univ u' v := by
  subst hz
  have hc : v ∈ (Finset.univ : Finset V) ∧ (cutOut G Z).parents v ⊆ Finset.univ :=
    ⟨Finset.mem_univ v, Finset.subset_univ _⟩
  have hc' : v ∈ (Finset.univ : Finset V) ∧ G.parents v ⊆ Finset.univ :=
    ⟨Finset.mem_univ v, Finset.subset_univ _⟩
  unfold kfac
  simp only [dif_pos hc, dif_pos hc', clampModel]
  refine congrArg₂ (fun p x => M.kernel v p x) ?_ hval
  funext w
  by_cases hw : w.1 ∈ Z
  · simp only [dif_pos hw]
    try rfl
  · simp only [dif_neg hw]
    exact hagree w.1 hw

/-- **Identitet (i).** For `S ⊇ Z` og en tilordning med `Z = z₀` er
klemmodellens marginal lik `M` sin. -/
lemma clamp_marginal_of_agree {α : V → Type*} (M : G.CausalModel α) (Z : Finset V)
    (z₀ : Assignment (α := α) Z) (S : Finset V) (hZS : Z ⊆ S)
    (a : Assignment (α := α) S) (ha : a.restrict hZS = z₀) :
    (clampModel M Z z₀).marginal S a = M.marginal S a := by
  unfold CausalModel.marginal
  rw [PMF.map_apply, PMF.map_apply]
  refine tsum_congr (fun u => ?_)
  split_ifs with hu
  · subst hu
    rw [fullJoint_apply_prod, fullJoint_apply_prod]
    exact Finset.prod_congr rfl
      (fun v _ => kfac_clamp M Z z₀ u u v (fun _ _ => rfl) ha rfl)
  · rfl

/-- Tilordningen som er `a` utenfor `Z` og `z₀` på `Z`. -/
def combineZ {α : V → Type*} (Z : Finset V) (z₀ : Assignment (α := α) Z)
    (a : Assignment (α := α) Zᶜ) : Assignment (α := α) (Finset.univ : Finset V) :=
  fun v => if h : v.1 ∈ Z then z₀ ⟨v.1, h⟩ else a ⟨v.1, Finset.mem_compl.mpr h⟩

lemma combine_restrict_compl {α : V → Type*} (Z : Finset V) (z₀ : Assignment (α := α) Z)
    (a : Assignment (α := α) Zᶜ) :
    (combineZ Z z₀ a).restrict (Finset.subset_univ Zᶜ) = a := by
  funext ⟨v, hv⟩
  have hvZ : v ∉ Z := Finset.mem_compl.mp hv
  simp only [Assignment.restrict, combineZ, dif_neg hvZ]

lemma combine_restrict_Z {α : V → Type*} (Z : Finset V) (z₀ : Assignment (α := α) Z)
    (a : Assignment (α := α) Zᶜ) :
    (combineZ Z z₀ a).restrict (Finset.subset_univ Z) = z₀ := by
  funext ⟨v, hv⟩
  simp only [Assignment.restrict, combineZ, dif_pos hv]

/-- En tilordning som er `a` utenfor `Z` og `z₀` på `Z`, *er* `combineZ Z z₀ a`. -/
lemma eq_combineZ {α : V → Type*} {Z : Finset V} {z₀ : Assignment (α := α) Z}
    {a : Assignment (α := α) Zᶜ} {u : Assignment (α := α) (Finset.univ : Finset V)}
    (h1 : u.restrict (Finset.subset_univ Zᶜ) = a)
    (h2 : u.restrict (Finset.subset_univ Z) = z₀) :
    u = combineZ Z z₀ a := by
  funext ⟨v, hv⟩
  by_cases hvZ : v ∈ Z
  · have := congrFun h2 ⟨v, hvZ⟩
    simp only [combineZ, dif_pos hvZ]
    exact this
  · have := congrFun h1 ⟨v, Finset.mem_compl.mpr hvZ⟩
    simp only [combineZ, dif_neg hvZ]
    exact this

/-- **Identitet (ii) på `Zᶜ`.** Klemmodellen og intervensjonen har samme marginal
utenfor `Z`: begge er lik produktet av `M`-faktorene utenfor `Z` i `combineZ`. -/
lemma clamp_marginal_compl_univ {α : V → Type*} (M : G.CausalModel α) (Z : Finset V)
    (z₀ : Assignment (α := α) Z) (a : Assignment (α := α) Zᶜ) :
    (clampModel M Z z₀).marginal Zᶜ a = (doModel M Z z₀).marginal Zᶜ a := by
  have hN : (clampModel M Z z₀).marginal Zᶜ a =
      ∏ v ∈ Zᶜ, kfac M Finset.univ (combineZ Z z₀ a) v := by
    have hterm : ∀ u : Assignment (α := α) (Finset.univ : Finset V),
        (if a = u.restrict (Finset.subset_univ Zᶜ) then (clampModel M Z z₀).fullJoint u else 0)
          = (∏ v ∈ Zᶜ, kfac M Finset.univ (combineZ Z z₀ a) v) *
            ((if u.restrict (Finset.subset_univ Zᶜ) = a then 1 else 0) *
              ∏ v ∈ Zᶜᶜ, kfac (clampModel M Z z₀) Finset.univ u v) := by
      intro u
      by_cases h : u.restrict (Finset.subset_univ Zᶜ) = a
      · have hag : ∀ w, w ∉ Z →
            u ⟨w, Finset.mem_univ w⟩ = combineZ Z z₀ a ⟨w, Finset.mem_univ w⟩ := by
          intro w hw
          have := congrFun h ⟨w, Finset.mem_compl.mpr hw⟩
          simp only [combineZ, dif_neg hw]
          exact this
        rw [if_pos h.symm, if_pos h, one_mul, fullJoint_apply_prod,
          ← Finset.prod_mul_prod_compl Zᶜ]
        congr 1
        exact Finset.prod_congr rfl (fun v hv =>
          kfac_clamp M Z z₀ u _ v hag (combine_restrict_Z Z z₀ a)
            (hag v (Finset.mem_compl.mp hv)))
      · rw [if_neg (fun h' => h h'.symm), if_neg h, zero_mul, mul_zero]
    unfold CausalModel.marginal
    rw [PMF.map_apply]
    simp_rw [hterm]
    rw [ENNReal.tsum_mul_left, sum_compl_kfac_eq_one, mul_one]
  have hD : (doModel M Z z₀).marginal Zᶜ a =
      ∏ v ∈ Zᶜ, kfac M Finset.univ (combineZ Z z₀ a) v := by
    unfold CausalModel.marginal
    rw [PMF.map_apply, tsum_eq_single (combineZ Z z₀ a)]
    · rw [if_pos (combine_restrict_compl Z z₀ a).symm, doModel_fullJoint,
        if_pos (combine_restrict_Z Z z₀ a), one_mul]
    · intro u hne
      split_ifs with h1
      · rw [doModel_fullJoint]
        have hneZ : u.restrict (Finset.subset_univ Z) ≠ z₀ :=
          fun h2 => hne (eq_combineZ h1.symm h2)
        rw [if_neg hneZ, zero_mul]
      · rfl
  rw [hN, hD]

/-- **Identitet (ii).** For `S` disjunkt fra `Z` er klemmodellens marginal lik
marginalen under `do(Z = z₀)`. -/
lemma clamp_marginal_compl {α : V → Type*} (M : G.CausalModel α) (Z : Finset V)
    (z₀ : Assignment (α := α) Z) (S : Finset V) (hS : S ⊆ Zᶜ)
    (s : Assignment (α := α) S) :
    (clampModel M Z z₀).marginal S s = (doModel M Z z₀).marginal S s := by
  have hPMF : (clampModel M Z z₀).marginal Zᶜ = (doModel M Z z₀).marginal Zᶜ :=
    PMF.ext (clamp_marginal_compl_univ M Z z₀)
  rw [← marginal_restrict (clampModel M Z z₀) hS,
    ← marginal_restrict (doModel M Z z₀) hS, hPMF]

/-- **Regel 2 uten `X` (bytte handling mot observasjon).** Er `Y` og `Z`
d-separert av `W` i `G_{Z̲}`, gjelder for enhver tilordning `t` på `Y ∪ Z ∪ W`
med `Z = z₀`:

`P(y, z₀, w) · P_{z₀}(w) = P_{z₀}(y, w) · P(z₀, w)`,

som er `P_{z₀}(y | w) = P(y | z₀, w)` i produktform (sann også der
betingingene ikke er definert). -/
theorem rule2_core {α : V → Type*} (M : G.CausalModel α) (Y Z W : Finset V)
    (z₀ : Assignment (α := α) Z)
    (hYZ : Disjoint Y Z) (hWZ : Disjoint W Z) (hYW : Disjoint Y W)
    (h : SetSound.DSeparatedSet (cutOut G Z) W Y Z)
    (t : Assignment (α := α) (Y ∪ Z ∪ W))
    (ht : t.restrict (show Z ⊆ Y ∪ Z ∪ W by
      intro v hv; simp only [Finset.mem_union]; tauto) = z₀) :
    M.marginal (Y ∪ Z ∪ W) t *
      (doModel M Z z₀).marginal W (t.restrict (show W ⊆ Y ∪ Z ∪ W by
        intro v hv; simp only [Finset.mem_union]; tauto)) =
    (doModel M Z z₀).marginal (Y ∪ W) (t.restrict (show Y ∪ W ⊆ Y ∪ Z ∪ W by
        intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
      M.marginal (Z ∪ W) (t.restrict (show Z ∪ W ⊆ Y ∪ Z ∪ W by
        intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := by
  have hWc : W ⊆ Zᶜ := fun v hv => Finset.mem_compl.mpr (Finset.disjoint_left.mp hWZ hv)
  have hYWc : Y ∪ W ⊆ Zᶜ := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Finset.mem_compl.mpr (Finset.disjoint_left.mp hYZ hv)
    · exact Finset.mem_compl.mpr (Finset.disjoint_left.mp hWZ hv)
  have hci := SetSound.dsep_sound_set (clampModel M Z z₀) Y Z W hYW hWZ.symm h t
  rw [clamp_marginal_of_agree M Z z₀ (Y ∪ Z ∪ W) _ t ht,
    clamp_marginal_compl M Z z₀ W hWc _,
    clamp_marginal_compl M Z z₀ (Y ∪ W) hYWc _,
    clamp_marginal_of_agree M Z z₀ (Z ∪ W) Finset.subset_union_left _ ht] at hci
  exact hci

/-- **Regel 2 (Pearl).** Er `Y` og `Z` d-separert av `X ∪ W` i `G_{X̄Z̲}`, er
observasjon av `Z = z₀` og intervensjon `do(Z = z₀)` utskiftbare under `do(X = x)`:
`P_{x,z₀}(y | x, w) = P_x(y | z₀, x, w)`, i produktform. -/
theorem rule2 {α : V → Type*} (M : G.CausalModel α) (X Y Z W : Finset V)
    (x : Assignment (α := α) X) (z₀ : Assignment (α := α) Z)
    (hYZ : Disjoint Y Z) (hXWZ : Disjoint (X ∪ W) Z) (hYXW : Disjoint Y (X ∪ W))
    (h : SetSound.DSeparatedSet (cutOut (cutIn G X) Z) (X ∪ W) Y Z)
    (t : Assignment (α := α) (Y ∪ Z ∪ (X ∪ W)))
    (ht : t.restrict (show Z ⊆ Y ∪ Z ∪ (X ∪ W) by
      intro v hv; simp only [Finset.mem_union]; tauto) = z₀) :
    (doModel M X x).marginal (Y ∪ Z ∪ (X ∪ W)) t *
      (doModel (doModel M X x) Z z₀).marginal (X ∪ W)
        (t.restrict (show X ∪ W ⊆ Y ∪ Z ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) =
    (doModel (doModel M X x) Z z₀).marginal (Y ∪ (X ∪ W))
        (t.restrict (show Y ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
      (doModel M X x).marginal (Z ∪ (X ∪ W))
        (t.restrict (show Z ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) :=
  rule2_core (doModel M X x) Y Z (X ∪ W) z₀ hYZ hXWZ hYXW h t ht

end DoCalculus

#print axioms DoCalculus.kfac_doModel
#print axioms DoCalculus.doModel_fullJoint
#print axioms DoCalculus.doModel_marginal_self
#print axioms DoCalculus.doModel_empty
#print axioms DoCalculus.rule1
#print axioms DoCalculus.kfac_clamp
#print axioms DoCalculus.clamp_marginal_of_agree
#print axioms DoCalculus.clamp_marginal_compl
#print axioms DoCalculus.rule2_core
#print axioms DoCalculus.rule2
