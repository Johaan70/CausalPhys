import PearlDoCalculus.Rule3Flag

/-!
# Justeringsformler: back-door og front-door

Utledet for en generell `CausalModel` fra do-kalkulusens regler.

**Back-door-kriteriet** for `(X, Y)` med `Z`: (i) ingen node i `Z` er etterkommer
av en node i `X`; (ii) `Y ⊥ X | Z` i `G_{X̲}`. Pearl viser at (ii), gitt (i), er det
samme som at `Z` blokkerer hver sti mellom `X` og `Y` med en pil inn i `X`.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Rule3 Classical

namespace Adjustment

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V}

/-- Er ingen node i `Z` etterkommer av en node i `X`, er `An(Z)` disjunkt fra `X`. -/
lemma disjoint_anc_of_nondesc {X Z : Finset V}
    (hdesc : ∀ x ∈ X, ∀ z ∈ Z, ¬ G.Reaches x z) :
    Disjoint (ancestors G Z) X := by
  rw [Finset.disjoint_left]
  intro v hv hvX
  obtain ⟨z, hz, hr⟩ := mem_ancestors_iff.mp hv
  exact hdesc v hvX z hz hr

/-- **Back-door, stratum for stratum.** Oppfyller `Z` back-door-kriteriet for
`(X, Y)`, så er `P(y, x, z) · P(z) = P_x(y, z) · P(x, z)`, uten positivitet. -/
theorem backdoor_stratum {α : V → Type*} (M : G.CausalModel α) (X Y Z : Finset V)
    (hYX : Disjoint Y X) (hZX : Disjoint Z X) (hYZ : Disjoint Y Z)
    (hdesc : ∀ x ∈ X, ∀ z ∈ Z, ¬ G.Reaches x z)
    (h : SetSound.DSeparatedSet (cutOut G X) Z Y X)
    (t : Assignment (α := α) (Y ∪ X ∪ Z)) :
    M.marginal (Y ∪ X ∪ Z) t *
      M.marginal Z (t.restrict (show Z ⊆ Y ∪ X ∪ Z by
        intro v hv; simp only [Finset.mem_union]; tauto)) =
    (doModel M X (t.restrict (show X ⊆ Y ∪ X ∪ Z by
        intro v hv; simp only [Finset.mem_union]; tauto))).marginal (Y ∪ Z)
        (t.restrict (show Y ∪ Z ⊆ Y ∪ X ∪ Z by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
      M.marginal (X ∪ Z) (t.restrict (show X ∪ Z ⊆ Y ∪ X ∪ Z by
        intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := by
  have sX : X ⊆ Y ∪ X ∪ Z := by intro v hv; simp only [Finset.mem_union]; tauto
  -- Regel 2 med Z := X og W := Z.
  have hr := rule2_core M Y X Z (t.restrict sX) hYX hZX hYZ h t rfl
  -- B2: P_x(z) = P(z), fordi An(Z) er ancestral og disjunkt fra X.
  rw [doModel_marginal_of_sub M X (t.restrict sX) (ancestors G Z)
    (DSepSound.A_closed (G := G) Z) (disjoint_anc_of_nondesc hdesc) Z
    (subset_ancestors _) _] at hr
  exact hr

open Rule3Flag in
/-- **Back-door-justeringsformelen.** Oppfyller `Z` back-door-kriteriet for
`(X, Y)`, og er `P(x, z) > 0` for alle `z`, så er
`P(y | do(x)) = Σ_z P(y, x, z) · P(z) / P(x, z)`. -/
theorem backdoor_adjustment {α : V → Type*} (M : G.CausalModel α) (X Y Z : Finset V)
    (hYX : Disjoint Y X) (hZX : Disjoint Z X) (hYZ : Disjoint Y Z)
    (hdesc : ∀ x ∈ X, ∀ z ∈ Z, ¬ G.Reaches x z)
    (h : SetSound.DSeparatedSet (cutOut G X) Z Y X)
    (t : Assignment (α := α) (Y ∪ X ∪ Z))
    (hpos : ∀ z : Assignment (α := α) Z,
      M.marginal (X ∪ Z) ((setZ Z (Y ∪ X ∪ Z) t z).restrict (show X ∪ Z ⊆ Y ∪ X ∪ Z by
        intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) ≠ 0) :
    (doModel M X (t.restrict (show X ⊆ Y ∪ X ∪ Z by
        intro v hv; simp only [Finset.mem_union]; tauto))).marginal Y
        (t.restrict (show Y ⊆ Y ∪ X ∪ Z by
          intro v hv; simp only [Finset.mem_union]; tauto)) =
      ∑' z : Assignment (α := α) Z,
        M.marginal (Y ∪ X ∪ Z) (setZ Z (Y ∪ X ∪ Z) t z) *
          M.marginal Z ((setZ Z (Y ∪ X ∪ Z) t z).restrict (show Z ⊆ Y ∪ X ∪ Z by
            intro v hv; simp only [Finset.mem_union]; tauto)) /
          M.marginal (X ∪ Z) ((setZ Z (Y ∪ X ∪ Z) t z).restrict
            (show X ∪ Z ⊆ Y ∪ X ∪ Z by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := by
  have sX : X ⊆ Y ∪ X ∪ Z := by intro v hv; simp only [Finset.mem_union]; tauto
  have sYZ : Y ∪ Z ⊆ Y ∪ X ∪ Z := by
    intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto
  have hXZ : Disjoint X Z := hZX.symm
  -- 1. Marginalisering: P_x(y) = Σ_z P_x(y, z).
  refine (marginal_sum_Z (doModel M X (t.restrict sX))
    (Finset.subset_union_right : Z ⊆ Y ∪ Z) (Finset.subset_union_left : Y ⊆ Y ∪ Z)
    hYZ (Finset.Subset.refl _) (t.restrict sYZ)).symm.trans ?_
  refine tsum_congr (fun z => ?_)
  -- 2. Stratum for stratum, med intervensjonsverdien uavhengig av z.
  have hb := backdoor_stratum M X Y Z hYX hZX hYZ hdesc h (setZ Z (Y ∪ X ∪ Z) t z)
  rw [setZ_restrict_disj _ hXZ] at hb
  -- 3. Løs ut P_x(y, z) under positivitet.
  rw [ENNReal.eq_div_iff (hpos z) (PMF.apply_ne_top _ _)]
  exact (mul_comm _ _).trans hb.symm

/-! ## Front-door, runde 1 -/

/-- Marginalen på `∅` er 1: alle tilordninger på `∅` er like. -/
lemma marginal_empty {α : V → Type*} (M : G.CausalModel α)
    (a : Assignment (α := α) (∅ : Finset V)) : M.marginal ∅ a = 1 := by
  have hall : ∀ b c : Assignment (α := α) (∅ : Finset V), b = c :=
    fun b c => funext fun ⟨v, hv⟩ => by simp at hv
  rw [PMF.apply_eq_one_iff]
  ext b
  simp only [Set.mem_singleton_iff]
  constructor
  · intro _
    exact hall b a
  · intro hb
    subst hb
    obtain ⟨c, hc⟩ := (M.marginal ∅).support_nonempty
    rwa [hall c b] at hc

/-- To uttrykk for samme mengde: `P_T(u) = P_S(u|_S)` når `S ⊆ T` og `T ⊆ S`. -/
lemma marginal_eq_of_subset' {α : V → Type*} (M : G.CausalModel α) {S T : Finset V}
    (hST : S ⊆ T) (hTS : T ⊆ S) (u : Assignment (α := α) T) :
    M.marginal T u = M.marginal S (u.restrict hST) := by
  rw [← marginal_restrict M hTS, PMF.map_apply, tsum_eq_single (u.restrict hST)]
  · rw [if_pos]
    funext ⟨v, hv⟩
    rfl
  · intro s' hs'
    rw [if_neg]
    intro h
    apply hs'
    funext ⟨v, hv⟩
    have := congrFun h ⟨v, hST hv⟩
    simpa [Assignment.restrict] using this.symm

/-- **FD1.** Er `Z ⊥ X` i `G_{X̲}`, så er `P(z, x) = P_x(z) · P(x)`. -/
theorem frontdoor_step1 {α : V → Type*} (M : G.CausalModel α) (X Z : Finset V)
    (hZX : Disjoint Z X) (h : SetSound.DSeparatedSet (cutOut G X) ∅ Z X)
    (t : Assignment (α := α) (Z ∪ X)) :
    M.marginal (Z ∪ X) t =
      (doModel M X (t.restrict (show X ⊆ Z ∪ X from Finset.subset_union_right))).marginal Z
          (t.restrict (show Z ⊆ Z ∪ X from Finset.subset_union_left)) *
        M.marginal X (t.restrict (show X ⊆ Z ∪ X from Finset.subset_union_right)) := by
  have s1 : Z ∪ X ∪ ∅ ⊆ Z ∪ X := by simp
  have hr := rule2_core M Z X ∅ (t.restrict (show X ⊆ Z ∪ X from Finset.subset_union_right))
    hZX (Finset.disjoint_empty_left _) (Finset.disjoint_empty_right _) h (t.restrict s1) rfl
  rw [marginal_empty, mul_one,
    marginal_eq_of_subset' M (S := Z ∪ X) (T := Z ∪ X ∪ ∅) (by simp) s1,
    marginal_eq_of_subset' (doModel M X _) (S := Z) (T := Z ∪ ∅) (by simp) (by simp),
    marginal_eq_of_subset' M (S := X) (T := X ∪ ∅) (by simp) (by simp)] at hr
  exact hr

/-! ## Front-door, runde 2 -/

/-- **FD2.** Er `Y ⊥ Z` i `G_{X̄Z̲}`, så er `P_x(y, z) = P_{x,z}(y) · P_x(z)`. -/
theorem frontdoor_step2 {α : V → Type*} (M : G.CausalModel α) (X Y Z : Finset V)
    (x : Assignment (α := α) X) (hYZ : Disjoint Y Z)
    (h : SetSound.DSeparatedSet (cutOut (cutIn G X) Z) ∅ Y Z)
    (t : Assignment (α := α) (Y ∪ Z)) :
    (doModel M X x).marginal (Y ∪ Z) t =
      (doModel (doModel M X x) Z (t.restrict (show Z ⊆ Y ∪ Z from Finset.subset_union_right))).marginal Y
          (t.restrict (show Y ⊆ Y ∪ Z from Finset.subset_union_left)) *
        (doModel M X x).marginal Z (t.restrict (show Z ⊆ Y ∪ Z from Finset.subset_union_right)) := by
  have s1 : Y ∪ Z ∪ ∅ ⊆ Y ∪ Z := by simp
  have hr := rule2_core (doModel M X x) Y Z ∅
    (t.restrict (show Z ⊆ Y ∪ Z from Finset.subset_union_right))
    hYZ (Finset.disjoint_empty_left _) (Finset.disjoint_empty_right _) h (t.restrict s1) rfl
  rw [marginal_empty, mul_one,
    marginal_eq_of_subset' (doModel M X x) (S := Y ∪ Z) (T := Y ∪ Z ∪ ∅) (by simp) s1,
    marginal_eq_of_subset' (doModel (doModel M X x) Z _) (S := Y) (T := Y ∪ ∅) (by simp) (by simp),
    marginal_eq_of_subset' (doModel M X x) (S := Z) (T := Z ∪ ∅) (by simp) (by simp)] at hr
  exact hr

/-- Med `W = ∅` er ingen node forfar til `W`, så `Z(∅)` er hele mengden. -/
lemma Z2_empty (H : DAG V) (X : Finset V) : Z2 H X ∅ = X := by
  ext v
  simp [Z2, mem_ancestors_iff]

/-- **FD3.** Er `Y ⊥ X` i `G_{Z̄X̄}`, så er `P_{x,z}(y) = P_z(y)`: intervensjonene
kommuterer (begge er `do(X ∪ Z)`), og regel 3 fjerner `do(x)` i `do(z)`-modellen. -/
theorem frontdoor_step3 {α : V → Type*} (M : G.CausalModel α) (X Y Z : Finset V)
    (hYX : Disjoint Y X) (hXZ : Disjoint X Z)
    (h : SetSound.DSeparatedSet (cutIn (cutIn G Z) X) ∅ Y X)
    (t : Assignment (α := α) (Y ∪ X ∪ Z)) :
    (doModel (doModel M X (t.restrict (show X ⊆ Y ∪ X ∪ Z by
        intro v hv; simp only [Finset.mem_union]; tauto))) Z
        (t.restrict (show Z ⊆ Y ∪ X ∪ Z by
          intro v hv; simp only [Finset.mem_union]; tauto))).marginal Y
        (t.restrict (show Y ⊆ Y ∪ X ∪ Z by
          intro v hv; simp only [Finset.mem_union]; tauto)) =
      (doModel M Z (t.restrict (show Z ⊆ Y ∪ X ∪ Z by
          intro v hv; simp only [Finset.mem_union]; tauto))).marginal Y
        (t.restrict (show Y ⊆ Y ∪ X ∪ Z by
          intro v hv; simp only [Finset.mem_union]; tauto)) := by
  have sXZ : X ∪ Z ⊆ Y ∪ X ∪ Z := by
    intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto
  have sY : Y ⊆ Y ∪ X ∪ Z := by intro v hv; simp only [Finset.mem_union]; tauto
  have sZ : Z ⊆ Y ∪ X ∪ Z := by intro v hv; simp only [Finset.mem_union]; tauto
  have sT : Y ∪ X ∪ ∅ ⊆ Y ∪ X ∪ Z :=
    Finset.union_subset Finset.subset_union_left (Finset.empty_subset _)
  -- 1–2. Begge rekkefølgene er do(X ∪ Z).
  have e1 := doModel_comp_marginal' M Z X (X ∪ Z) hXZ.symm (Finset.union_comm Z X)
    (t.restrict sXZ) Y (t.restrict sY)
  have e2 := doModel_comp_marginal' M X Z (X ∪ Z) hXZ rfl (t.restrict sXZ) Y (t.restrict sY)
  -- 3. Regel 3 i do(z)-modellen, med W = ∅.
  have h' : SetSound.DSeparatedSet (cutIn (cutIn G Z) (Z2 (cutIn G Z) X ∅)) ∅ Y X := by
    rw [Z2_empty]
    exact h
  have hr := Rule3Flag.rule3_gen (doModel M Z (t.restrict sZ)) Y X ∅ hYX
    (Finset.disjoint_empty_left _) (Finset.disjoint_empty_right _) h' (t.restrict sT)
  rw [marginal_empty, marginal_empty, mul_one, mul_one,
    marginal_eq_of_subset' (doModel (doModel M Z (t.restrict sZ)) X _) (S := Y) (T := Y ∪ ∅)
      (by simp) (by simp),
    marginal_eq_of_subset' (doModel M Z (t.restrict sZ)) (S := Y) (T := Y ∪ ∅)
      (by simp) (by simp)] at hr
  exact e1.trans (e2.symm.trans hr)

/-! ## Front-door, runde 3: per stratum og summen -/

open Rule3Flag in
/-- **Front-door per stratum.** `P_x(y, z) · P(x) = P_z(y) · P(z, x)`, der
`t_z` er `t` med `Z`-delen byttet ut med `z`. -/
theorem frontdoor_stratum {α : V → Type*} (M : G.CausalModel α) (X Y Z : Finset V)
    (hZX : Disjoint Z X) (hYX : Disjoint Y X) (hYZ : Disjoint Y Z)
    (h1 : SetSound.DSeparatedSet (cutOut G X) ∅ Z X)
    (h2 : SetSound.DSeparatedSet (cutOut (cutIn G X) Z) ∅ Y Z)
    (h3 : SetSound.DSeparatedSet (cutIn (cutIn G Z) X) ∅ Y X)
    (t : Assignment (α := α) (Y ∪ X ∪ Z)) (z : Assignment (α := α) Z) :
    (doModel M X (t.restrict (show X ⊆ Y ∪ X ∪ Z by
        intro v hv; simp only [Finset.mem_union]; tauto))).marginal (Y ∪ Z)
        ((setZ Z (Y ∪ X ∪ Z) t z).restrict (show Y ∪ Z ⊆ Y ∪ X ∪ Z by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
      M.marginal X (t.restrict (show X ⊆ Y ∪ X ∪ Z by
        intro v hv; simp only [Finset.mem_union]; tauto)) =
    (doModel M Z ((setZ Z (Y ∪ X ∪ Z) t z).restrict (show Z ⊆ Y ∪ X ∪ Z by
        intro v hv; simp only [Finset.mem_union]; tauto))).marginal Y
        ((setZ Z (Y ∪ X ∪ Z) t z).restrict (show Y ⊆ Y ∪ X ∪ Z by
          intro v hv; simp only [Finset.mem_union]; tauto)) *
      M.marginal (Z ∪ X) ((setZ Z (Y ∪ X ∪ Z) t z).restrict (show Z ∪ X ⊆ Y ∪ X ∪ Z by
        intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := by
  have sX : X ⊆ Y ∪ X ∪ Z := by intro v hv; simp only [Finset.mem_union]; tauto
  have sYZ : Y ∪ Z ⊆ Y ∪ X ∪ Z := by
    intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto
  have sZX : Z ∪ X ⊆ Y ∪ X ∪ Z := by
    intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto
  have hXZ : Disjoint X Z := hZX.symm
  -- FD2 i punktet t_z|_{Y∪Z}.
  have f2 := frontdoor_step2 M X Y Z (t.restrict sX) hYZ h2
    ((setZ Z (Y ∪ X ∪ Z) t z).restrict sYZ)
  -- FD3 i punktet t_z, med intervensjonsverdien på X skrevet om til t|_X.
  have f3 := frontdoor_step3 M X Y Z hYX hXZ h3 (setZ Z (Y ∪ X ∪ Z) t z)
  rw [setZ_restrict_disj _ hXZ] at f3
  have f3' : (doModel (doModel M X (t.restrict sX)) Z
        (((setZ Z (Y ∪ X ∪ Z) t z).restrict sYZ).restrict
          (show Z ⊆ Y ∪ Z from Finset.subset_union_right))).marginal Y
        (((setZ Z (Y ∪ X ∪ Z) t z).restrict sYZ).restrict
          (show Y ⊆ Y ∪ Z from Finset.subset_union_left)) =
      (doModel M Z ((setZ Z (Y ∪ X ∪ Z) t z).restrict (show Z ⊆ Y ∪ X ∪ Z by
        intro v hv; simp only [Finset.mem_union]; tauto))).marginal Y
        ((setZ Z (Y ∪ X ∪ Z) t z).restrict (show Y ⊆ Y ∪ X ∪ Z by
          intro v hv; simp only [Finset.mem_union]; tauto)) := f3
  -- FD1 i punktet t_z|_{Z∪X}, med intervensjonsverdien på X skrevet om til t|_X.
  have f1 := frontdoor_step1 M X Z hZX h1 ((setZ Z (Y ∪ X ∪ Z) t z).restrict sZX)
  have hx : ((setZ Z (Y ∪ X ∪ Z) t z).restrict sZX).restrict
      (show X ⊆ Z ∪ X from Finset.subset_union_right) = t.restrict sX :=
    setZ_restrict_disj sX hXZ t z
  rw [hx] at f1
  -- Z-delen er den samme via Y ∪ Z og via Z ∪ X.
  have hzz : ((setZ Z (Y ∪ X ∪ Z) t z).restrict sYZ).restrict
      (show Z ⊆ Y ∪ Z from Finset.subset_union_right) =
      ((setZ Z (Y ∪ X ∪ Z) t z).restrict sZX).restrict
      (show Z ⊆ Z ∪ X from Finset.subset_union_left) := rfl
  rw [hzz] at f2 f3'
  rw [f2, f1, f3']
  ring

open Rule3Flag in
/-- **Front-door i produktform.** `P_x(y) · P(x) = Σ_z P_z(y) · P(z, x)`, uten
positivitet. -/
theorem frontdoor_product {α : V → Type*} (M : G.CausalModel α) (X Y Z : Finset V)
    (hZX : Disjoint Z X) (hYX : Disjoint Y X) (hYZ : Disjoint Y Z)
    (h1 : SetSound.DSeparatedSet (cutOut G X) ∅ Z X)
    (h2 : SetSound.DSeparatedSet (cutOut (cutIn G X) Z) ∅ Y Z)
    (h3 : SetSound.DSeparatedSet (cutIn (cutIn G Z) X) ∅ Y X)
    (t : Assignment (α := α) (Y ∪ X ∪ Z)) :
    (doModel M X (t.restrict (show X ⊆ Y ∪ X ∪ Z by
        intro v hv; simp only [Finset.mem_union]; tauto))).marginal Y
        (t.restrict (show Y ⊆ Y ∪ X ∪ Z by
          intro v hv; simp only [Finset.mem_union]; tauto)) *
      M.marginal X (t.restrict (show X ⊆ Y ∪ X ∪ Z by
        intro v hv; simp only [Finset.mem_union]; tauto)) =
    ∑' z : Assignment (α := α) Z,
      (doModel M Z ((setZ Z (Y ∪ X ∪ Z) t z).restrict (show Z ⊆ Y ∪ X ∪ Z by
          intro v hv; simp only [Finset.mem_union]; tauto))).marginal Y
          ((setZ Z (Y ∪ X ∪ Z) t z).restrict (show Y ⊆ Y ∪ X ∪ Z by
            intro v hv; simp only [Finset.mem_union]; tauto)) *
        M.marginal (Z ∪ X) ((setZ Z (Y ∪ X ∪ Z) t z).restrict (show Z ∪ X ⊆ Y ∪ X ∪ Z by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := by
  have sX : X ⊆ Y ∪ X ∪ Z := by intro v hv; simp only [Finset.mem_union]; tauto
  have sYZ : Y ∪ Z ⊆ Y ∪ X ∪ Z := by
    intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto
  have hs := marginal_sum_Z (doModel M X (t.restrict sX))
    (Finset.subset_union_right : Z ⊆ Y ∪ Z) (Finset.subset_union_left : Y ⊆ Y ∪ Z)
    hYZ (Finset.Subset.refl _) (t.restrict sYZ)
  calc _ = (∑' z : Assignment (α := α) Z,
          (doModel M X (t.restrict sX)).marginal (Y ∪ Z) (setZ Z (Y ∪ Z) (t.restrict sYZ) z)) *
          M.marginal X (t.restrict sX) := (congrArg (· * M.marginal X (t.restrict sX)) hs).symm
    _ = ∑' z : Assignment (α := α) Z,
          (doModel M X (t.restrict sX)).marginal (Y ∪ Z) (setZ Z (Y ∪ Z) (t.restrict sYZ) z) *
            M.marginal X (t.restrict sX) := ENNReal.tsum_mul_right.symm
    _ = _ := tsum_congr (fun z => frontdoor_stratum M X Y Z hZX hYX hYZ h1 h2 h3 t z)

/-! ## Front-door, runde 4: den klassiske formelen -/

open Rule3Flag in
/-- **Front-door-justeringsformelen.**
`P(y | do(x)) = Σ_z [P(z, x) / P(x)] · Σ_{x′} P(y, z, x′) · P(x′) / P(z, x′)`,
under d-separasjonsbetingelsene i Pearls utledning og `P(x) > 0`, `P(z, x′) > 0`. -/
theorem frontdoor_adjustment {α : V → Type*} (M : G.CausalModel α) (X Y Z : Finset V)
    (hZX : Disjoint Z X) (hYX : Disjoint Y X) (hYZ : Disjoint Y Z)
    (h1 : SetSound.DSeparatedSet (cutOut G X) ∅ Z X)
    (h2 : SetSound.DSeparatedSet (cutOut (cutIn G X) Z) ∅ Y Z)
    (h3 : SetSound.DSeparatedSet (cutIn (cutIn G Z) X) ∅ Y X)
    (hdesc : ∀ z ∈ Z, ∀ x ∈ X, ¬ G.Reaches z x)
    (h4 : SetSound.DSeparatedSet (cutOut G Z) X Y Z)
    (t : Assignment (α := α) (Y ∪ X ∪ Z))
    (hx : M.marginal X (t.restrict (show X ⊆ Y ∪ X ∪ Z by
        intro v hv; simp only [Finset.mem_union]; tauto)) ≠ 0)
    (hpos : ∀ (z : Assignment (α := α) Z) (x' : Assignment (α := α) X),
      M.marginal (Z ∪ X)
        ((setZ X (Y ∪ Z ∪ X) ((setZ Z (Y ∪ X ∪ Z) t z).restrict
            (show Y ∪ Z ∪ X ⊆ Y ∪ X ∪ Z by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) x').restrict
          (show Z ∪ X ⊆ Y ∪ Z ∪ X by
            intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) ≠ 0) :
    (doModel M X (t.restrict (show X ⊆ Y ∪ X ∪ Z by
        intro v hv; simp only [Finset.mem_union]; tauto))).marginal Y
        (t.restrict (show Y ⊆ Y ∪ X ∪ Z by
          intro v hv; simp only [Finset.mem_union]; tauto)) =
    ∑' z : Assignment (α := α) Z,
      M.marginal (Z ∪ X) ((setZ Z (Y ∪ X ∪ Z) t z).restrict (show Z ∪ X ⊆ Y ∪ X ∪ Z by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) /
        M.marginal X (t.restrict (show X ⊆ Y ∪ X ∪ Z by
          intro v hv; simp only [Finset.mem_union]; tauto)) *
      ∑' x' : Assignment (α := α) X,
        M.marginal (Y ∪ Z ∪ X) (setZ X (Y ∪ Z ∪ X) ((setZ Z (Y ∪ X ∪ Z) t z).restrict
            (show Y ∪ Z ∪ X ⊆ Y ∪ X ∪ Z by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) x') *
          M.marginal X ((setZ X (Y ∪ Z ∪ X) ((setZ Z (Y ∪ X ∪ Z) t z).restrict
            (show Y ∪ Z ∪ X ⊆ Y ∪ X ∪ Z by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) x').restrict
            (show X ⊆ Y ∪ Z ∪ X by intro v hv; simp only [Finset.mem_union]; tauto)) /
          M.marginal (Z ∪ X) ((setZ X (Y ∪ Z ∪ X) ((setZ Z (Y ∪ X ∪ Z) t z).restrict
            (show Y ∪ Z ∪ X ⊆ Y ∪ X ∪ Z by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) x').restrict
            (show Z ∪ X ⊆ Y ∪ Z ∪ X by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := by
  have hXZ : Disjoint X Z := hZX.symm
  -- 1. Del produktformen med P(x).
  have hp := frontdoor_product M X Y Z hZX hYX hYZ h1 h2 h3 t
  have hdiv := (ENNReal.eq_div_iff hx (PMF.apply_ne_top _ _)).mpr ((mul_comm _ _).trans hp)
  rw [hdiv, div_eq_mul_inv, ← ENNReal.tsum_mul_right]
  refine tsum_congr (fun z => ?_)
  -- 2. Back-door for P_z(y), med X som justeringsmengde.
  have hb := backdoor_adjustment M Z Y X hYZ hXZ hYX hdesc h4
    ((setZ Z (Y ∪ X ∪ Z) t z).restrict (show Y ∪ Z ∪ X ⊆ Y ∪ X ∪ Z by
      intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) (hpos z)
  have hb' : (doModel M Z ((setZ Z (Y ∪ X ∪ Z) t z).restrict (show Z ⊆ Y ∪ X ∪ Z by
        intro v hv; simp only [Finset.mem_union]; tauto))).marginal Y
        ((setZ Z (Y ∪ X ∪ Z) t z).restrict (show Y ⊆ Y ∪ X ∪ Z by
          intro v hv; simp only [Finset.mem_union]; tauto)) =
      ∑' x' : Assignment (α := α) X,
        M.marginal (Y ∪ Z ∪ X) (setZ X (Y ∪ Z ∪ X) ((setZ Z (Y ∪ X ∪ Z) t z).restrict
            (show Y ∪ Z ∪ X ⊆ Y ∪ X ∪ Z by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) x') *
          M.marginal X ((setZ X (Y ∪ Z ∪ X) ((setZ Z (Y ∪ X ∪ Z) t z).restrict
            (show Y ∪ Z ∪ X ⊆ Y ∪ X ∪ Z by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) x').restrict
            (show X ⊆ Y ∪ Z ∪ X by intro v hv; simp only [Finset.mem_union]; tauto)) /
          M.marginal (Z ∪ X) ((setZ X (Y ∪ Z ∪ X) ((setZ Z (Y ∪ X ∪ Z) t z).restrict
            (show Y ∪ Z ∪ X ⊆ Y ∪ X ∪ Z by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) x').restrict
            (show Z ∪ X ⊆ Y ∪ Z ∪ X by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := hb
  rw [hb', div_eq_mul_inv]
  ring

/-! ## Back-door-kriteriet i stiformulering -/

/-- Er vandringen tom? -/
def wIsNil {H : DAG V} : {a b : V} → Walk H a b → Bool
  | _, _, .nil _ => true
  | _, _, .fwd _ _ => false
  | _, _, .bwd _ _ => false

/-- Siste steg i vandringen går langs en pil *inn i* sluttnoden. -/
def endsInto {H : DAG V} : {a b : V} → Walk H a b → Prop
  | _, _, .nil _ => False
  | _, _, .fwd _ p => wIsNil p = true ∨ endsInto p
  | _, _, .bwd _ p => wIsNil p = false ∧ endsInto p

lemma wIsNil_mapSub {H H' : DAG V} (hsub : ∀ u v, H'.edge u v → H.edge u v) :
    ∀ {a b : V} (p : Walk H' a b), wIsNil (mapSub hsub p) = wIsNil p := by
  intro a b p
  cases p <;> rfl

/-- En ikke-tom vandring i `G_{X̲}` som ender i `x ∈ X`, ender langs en pil inn i
`x`: kanten ut av `x` er fjernet. -/
lemma endsInto_of_cutOut {X : Finset V} (hsub : ∀ u v, (cutOut G X).edge u v → G.edge u v) :
    ∀ {a b : V} (p : Walk (cutOut G X) a b), b ∈ X → wIsNil p = false →
      endsInto (mapSub hsub p) := by
  intro a b p
  induction p with
  | nil v =>
    intro _ h
    simp [wIsNil] at h
  | fwd e p ih =>
    intro hb _
    simp only [mapSub, endsInto, wIsNil_mapSub]
    by_cases hp : wIsNil p = true
    · exact Or.inl hp
    · exact Or.inr (ih hb (by simpa using hp))
  | bwd e p ih =>
    intro hb _
    simp only [mapSub, endsInto, wIsNil_mapSub]
    cases p with
    | nil v => exact absurd hb e.2
    | fwd e' p' => exact ⟨rfl, ih hb rfl⟩
    | bwd e' p' => exact ⟨rfl, ih hb rfl⟩

/-- **Kriterium ⇒ d-separasjon.** Blokkerer `Z` hver sti i `G` fra `y ∈ Y` til
`x ∈ X` som ender med en pil inn i `x`, så er `Y ⊥ X | Z` i `G_{X̲}`. -/
theorem cutOut_dsep_of_backdoor {X Y Z : Finset V} (hXY : Disjoint X Y)
    (hcrit : ∀ y ∈ Y, ∀ x ∈ X, ∀ p : Walk G y x, p.IsPath → endsInto p → Walk.Blocked Z p) :
    SetSound.DSeparatedSet (cutOut G X) Z Y X := by
  intro y hy x hx p hp
  have hsub : ∀ u v, (cutOut G X).edge u v → G.edge u v := fun u v h => h.1
  have hne : wIsNil p = false := by
    cases p with
    | nil v => exact absurd hx (Finset.disjoint_right.mp hXY hy)
    | fwd _ _ => rfl
    | bwd _ _ => rfl
  have hpath : (mapSub hsub p).IsPath := by
    unfold Walk.IsPath
    rw [support_mapSub]
    exact hp
  exact blocked_of_mapSub hsub .start p
    (hcrit y hy x hx (mapSub hsub p) hpath (endsInto_of_cutOut hsub p hx hne))

/-- **Pearls back-door-kriterium.** (i) Ingen node i `Z` er etterkommer av en node
i `X`. (ii) `Z` blokkerer hver sti mellom `x ∈ X` og `y ∈ Y` med en pil inn i `x`,
her gjennomløpt fra `y` til `x`. -/
def BackdoorCriterion (G : DAG V) (X Y Z : Finset V) : Prop :=
  (∀ x ∈ X, ∀ z ∈ Z, ¬ G.Reaches x z) ∧
  ∀ y ∈ Y, ∀ x ∈ X, ∀ p : Walk G y x, p.IsPath → endsInto p → Walk.Blocked Z p

open Rule3Flag in
/-- **Back-door-justeringsformelen med Pearls kriterium.** -/
theorem backdoor_adjustment_criterion {α : V → Type*} (M : G.CausalModel α)
    (X Y Z : Finset V)
    (hYX : Disjoint Y X) (hZX : Disjoint Z X) (hYZ : Disjoint Y Z)
    (hcrit : BackdoorCriterion G X Y Z)
    (t : Assignment (α := α) (Y ∪ X ∪ Z))
    (hpos : ∀ z : Assignment (α := α) Z,
      M.marginal (X ∪ Z) ((setZ Z (Y ∪ X ∪ Z) t z).restrict (show X ∪ Z ⊆ Y ∪ X ∪ Z by
        intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) ≠ 0) :
    (doModel M X (t.restrict (show X ⊆ Y ∪ X ∪ Z by
        intro v hv; simp only [Finset.mem_union]; tauto))).marginal Y
        (t.restrict (show Y ⊆ Y ∪ X ∪ Z by
          intro v hv; simp only [Finset.mem_union]; tauto)) =
      ∑' z : Assignment (α := α) Z,
        M.marginal (Y ∪ X ∪ Z) (setZ Z (Y ∪ X ∪ Z) t z) *
          M.marginal Z ((setZ Z (Y ∪ X ∪ Z) t z).restrict (show Z ⊆ Y ∪ X ∪ Z by
            intro v hv; simp only [Finset.mem_union]; tauto)) /
          M.marginal (X ∪ Z) ((setZ Z (Y ∪ X ∪ Z) t z).restrict
            (show X ∪ Z ⊆ Y ∪ X ∪ Z by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) :=
  backdoor_adjustment M X Y Z hYX hZX hYZ hcrit.1
    (cutOut_dsep_of_backdoor hYX.symm hcrit.2) t hpos

/-! ## Front-door-kriteriet i stiformulering, runde 1 -/

/-- **Pearls front-door-kriterium.** (i) Enhver rettet vei fra `x ∈ X` til `y ∈ Y`
treffer `Z` (det finnes ingen rettet vei der alle noder etter `x` ligger utenfor
`Z`). (ii) Enhver sti mellom `x ∈ X` og `z ∈ Z` med en pil inn i `x` er blokkert
av `∅`, her gjennomløpt fra `z`. (iii) Enhver sti mellom `z ∈ Z` og `y ∈ Y` med en
pil inn i `z` er blokkert av `X`, her gjennomløpt fra `y`. -/
def FrontdoorCriterion (G : DAG V) (X Y Z : Finset V) : Prop :=
  (∀ x ∈ X, ∀ y ∈ Y, ¬ Relation.ReflTransGen (fun a b => G.edge a b ∧ b ∉ Z) x y) ∧
  (∀ z ∈ Z, ∀ x ∈ X, ∀ p : Walk G z x, p.IsPath → endsInto p → Walk.Blocked ∅ p) ∧
  (∀ y ∈ Y, ∀ z ∈ Z, ∀ p : Walk G y z, p.IsPath → endsInto p → Walk.Blocked X p)

/-- **h1 fra (ii):** `Z ⊥ X | ∅` i `G_{X̲}`. -/
lemma fd_h1 {X Y Z : Finset V} (hZX : Disjoint Z X) (hc : FrontdoorCriterion G X Y Z) :
    SetSound.DSeparatedSet (cutOut G X) ∅ Z X :=
  cutOut_dsep_of_backdoor hZX.symm hc.2.1

/-- **h4 fra (iii):** `Y ⊥ Z | X` i `G_{Z̲}`. -/
lemma fd_h4 {X Y Z : Finset V} (hYZ : Disjoint Y Z) (hc : FrontdoorCriterion G X Y Z) :
    SetSound.DSeparatedSet (cutOut G Z) X Y Z :=
  cutOut_dsep_of_backdoor hYZ.symm hc.2.2

/-- Fra en rettet vei `a → … → b` med `a ∉ X` og `b ∈ X` finnes en vandring i
`G_{X̲}` fra `a` til en `x′ ∈ X` med bare foroversteg; den er åpen gitt `∅`. -/
lemma exists_open_fwd {X : Finset V} {a b : V} (h : G.Reaches a b) :
    a ∉ X → b ∈ X → ∃ x' ∈ X, ∃ p : Walk (cutOut G X) a x',
      ¬ Walk.blockedAux ∅ .start p ∧ ¬ Walk.blockedAux ∅ .fwd p := by
  have h' : Relation.ReflTransGen G.edge a b := h
  clear h
  induction h' using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro ha hb
    exact absurd hb ha
  | @head a c hac _ ih =>
    intro ha hb
    by_cases hc : c ∈ X
    · exact ⟨c, hc, Walk.fwd ⟨hac, ha⟩ (Walk.nil c),
        by simp [Walk.blockedAux], by simp [Walk.blockedAux]⟩
    · obtain ⟨x', hx', p, _, hp2⟩ := ih hc hb
      exact ⟨x', hx', Walk.fwd ⟨hac, ha⟩ p,
        by simp [Walk.blockedAux, hp2], by simp [Walk.blockedAux, hp2]⟩

/-- **hdesc fra (ii), via h1:** ingen node i `X` er etterkommer av en node i `Z`. -/
lemma fd_hdesc {X Y Z : Finset V} (hZX : Disjoint Z X) (hc : FrontdoorCriterion G X Y Z) :
    ∀ z ∈ Z, ∀ x ∈ X, ¬ G.Reaches z x := by
  intro z hz x hx hr
  obtain ⟨x', hx', p, hp, _⟩ := exists_open_fwd hr (Finset.disjoint_left.mp hZX hz) hx
  exact hp (dsep_of_dsepPath (fd_h1 hZX hc z hz x' hx') p)

/-! ## Front-door-kriteriet, runde 2: h3 -/

/-- I en graf uten kanter inn i `X`: en vandring som er åpen gitt `∅` i tilstanden
`.fwd` og ender i `X`, starter i `X`. (Et bakoversteg gir en kollider, som blokkerer;
et foroversteg går inn i en node som da ikke er i `X`.) -/
lemma open_fwd_ends {H : DAG V} {X : Finset V} (hin : ∀ u v, H.edge u v → v ∉ X) :
    ∀ {c b : V} (q : Walk H c b), ¬ Walk.blockedAux ∅ .fwd q → b ∈ X → c ∈ X := by
  intro c b q
  induction q with
  | nil v =>
    intro _ hb
    exact hb
  | fwd e q ih =>
    intro hq hb
    have hq' : ¬ Walk.blockedAux ∅ .fwd q := fun h => hq (Or.inr h)
    exact absurd (ih hq' hb) (hin _ _ e)
  | bwd e q _ =>
    intro hq _
    exact absurd (Or.inl (fun z hz => by simp at hz)) hq

/-- I en graf uten kanter inn i `X`: en vandring fra `a` til `b ∈ X` som er åpen gitt
`∅` i en tilstand som ikke er `.fwd`, går bare bakover, og gir en rettet vei
`b → … → a`. -/
lemma open_nofwd_reach {H : DAG V} {X : Finset V} (hin : ∀ u v, H.edge u v → v ∉ X) :
    ∀ {a b : V} (q : Walk H a b) (inc : Incoming), inc ≠ .fwd →
      ¬ Walk.blockedAux ∅ inc q → b ∈ X → Relation.ReflTransGen H.edge b a := by
  intro a b q
  induction q with
  | nil v =>
    intro _ _ _ _
    exact Relation.ReflTransGen.refl
  | fwd e q _ =>
    intro inc hinc hq hb
    have hq' : ¬ Walk.blockedAux ∅ .fwd q := by
      cases inc with
      | start => exact hq
      | fwd => exact absurd rfl hinc
      | bwd => exact fun h => hq (Or.inr h)
    exact absurd (open_fwd_ends hin q hq' hb) (hin _ _ e)
  | bwd e q ih =>
    intro inc hinc hq hb
    have hq' : ¬ Walk.blockedAux ∅ .bwd q := by
      cases inc with
      | start => exact hq
      | fwd => exact absurd rfl hinc
      | bwd => exact fun h => hq (Or.inr h)
    exact (ih .bwd (by intro h; cases h) hq' hb).tail e

/-- **h3 fra (i):** `Y ⊥ X | ∅` i `G_{Z̄X̄}`. En åpen vandring fra `y` til `x` ville
gitt en rettet vei `x → … → y` som unngår `Z`. -/
lemma fd_h3 {X Y Z : Finset V} (hc : FrontdoorCriterion G X Y Z) :
    SetSound.DSeparatedSet (cutIn (cutIn G Z) X) ∅ Y X := by
  intro y hy x hx p _
  by_contra hp
  have hin : ∀ u v, (cutIn (cutIn G Z) X).edge u v → v ∉ X := fun u v e => e.2
  have hr := open_nofwd_reach hin p .start (by intro h; cases h) hp hx
  exact hc.1 x hx y hy (Relation.ReflTransGen.mono (fun u v e => e.1) hr)

/-! ## Front-door-kriteriet, runde 3: h2 og sluttteoremet -/

/-- `endsInto_of_cutOut` for en hvilken som helst graf uten kanter ut av `S`. -/
lemma endsInto_of_noOut {H : DAG V} {S : Finset V} (hsub : ∀ u v, H.edge u v → G.edge u v)
    (hout : ∀ u v, H.edge u v → u ∉ S) :
    ∀ {a b : V} (p : Walk H a b), b ∈ S → wIsNil p = false → endsInto (mapSub hsub p) := by
  intro a b p
  induction p with
  | nil v =>
    intro _ h
    simp [wIsNil] at h
  | fwd e p ih =>
    intro hb _
    simp only [mapSub, endsInto, wIsNil_mapSub]
    by_cases hp : wIsNil p = true
    · exact Or.inl hp
    · exact Or.inr (ih hb (by simpa using hp))
  | bwd e p ih =>
    intro hb _
    simp only [mapSub, endsInto, wIsNil_mapSub]
    cases p with
    | nil v => exact absurd hb (hout _ _ e)
    | fwd e' p' => exact ⟨rfl, ih hb rfl⟩
    | bwd e' p' => exact ⟨rfl, ih hb rfl⟩

/-- Åpen gitt `∅` og uten noder i `X` ⇒ åpen gitt `X` i den større grafen. -/
lemma open_mapSub_of_noX {H' : DAG V} {X : Finset V} (hsub : ∀ u v, H'.edge u v → G.edge u v) :
    ∀ {a b : V} (q : Walk H' a b) (inc : Incoming), (∀ v ∈ q.support, v ∉ X) →
      ¬ Walk.blockedAux ∅ inc q → ¬ Walk.blockedAux X inc (mapSub hsub q) := by
  intro a b q
  induction q with
  | nil v =>
    intro inc _ _ h
    cases inc <;> exact h
  | @fwd a a' _ e q ih =>
    intro inc hX hq
    have ha : a ∉ X := hX a (by simp [Walk.support])
    have hX' : ∀ v ∈ q.support, v ∉ X := fun v hv => hX v (by simp [Walk.support, hv])
    cases inc with
    | start => exact ih .fwd hX' hq
    | fwd =>
      simp only [mapSub, Walk.blockedAux]
      rintro (h | h)
      · exact ha h
      · exact ih .fwd hX' (fun h' => hq (Or.inr h')) h
    | bwd =>
      simp only [mapSub, Walk.blockedAux]
      rintro (h | h)
      · exact ha h
      · exact ih .fwd hX' (fun h' => hq (Or.inr h')) h
  | @bwd a a' _ e q ih =>
    intro inc hX hq
    have ha : a ∉ X := hX a (by simp [Walk.support])
    have hX' : ∀ v ∈ q.support, v ∉ X := fun v hv => hX v (by simp [Walk.support, hv])
    cases inc with
    | start => exact ih .bwd hX' hq
    | fwd => exact absurd (Or.inl (fun z hz => by simp at hz)) hq
    | bwd =>
      simp only [mapSub, Walk.blockedAux]
      rintro (h | h)
      · exact ha h
      · exact ih .bwd hX' (fun h' => hq (Or.inr h')) h

/-- Foroverfasen: i en graf uten kanter inn i `X` ligger ingen node på en åpen
vandring (gitt `∅`, tilstand `.fwd`) i `X`, så lenge startnoden ikke gjør det. -/
lemma open_fwd_noX {H : DAG V} {X : Finset V} (hin : ∀ u v, H.edge u v → v ∉ X) :
    ∀ {c b : V} (q : Walk H c b), c ∉ X → ¬ Walk.blockedAux ∅ .fwd q →
      ∀ v ∈ q.support, v ∉ X := by
  intro c b q
  induction q with
  | nil v =>
    intro hc _ w hw
    simp [Walk.support] at hw
    subst hw
    exact hc
  | @fwd c c' _ e q ih =>
    intro hc hq w hw
    simp only [Walk.support, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact hc
    · exact ih (hin _ _ e) (fun h => hq (Or.inr h)) w hw
  | bwd e q _ =>
    intro _ hq
    exact absurd (Or.inl (fun z hz => by simp at hz)) hq

/-- Bakoverfasen: vi fører med oss en rettet vei tilbake til `y` som unngår `Z`.
Ligger en node i `X`, motsier den veien kriteriet (i). -/
lemma open_bwd_noX {H : DAG V} {X Z : Finset V} {y : V}
    (hin : ∀ u v, H.edge u v → v ∉ X) (hout : ∀ u v, H.edge u v → u ∉ Z)
    (hG : ∀ u v, H.edge u v → G.edge u v)
    (hi : ∀ x ∈ X, ¬ Relation.ReflTransGen (fun a b => G.edge a b ∧ b ∉ Z) x y) :
    ∀ {a b : V} (q : Walk H a b) (inc : Incoming), inc ≠ .fwd →
      ¬ Walk.blockedAux ∅ inc q → a ∉ Z →
      Relation.ReflTransGen (fun a b => G.edge a b ∧ b ∉ Z) a y →
      ∀ v ∈ q.support, v ∉ X := by
  have key : ∀ a, Relation.ReflTransGen (fun a b => G.edge a b ∧ b ∉ Z) a y → a ∉ X :=
    fun a hr ha => hi a ha hr
  intro a b q
  induction q with
  | nil v =>
    intro _ _ _ _ hr w hw
    simp [Walk.support] at hw
    subst hw
    exact key _ hr
  | @fwd a a' _ e q _ =>
    intro inc hinc hq _ hr w hw
    have hq' : ¬ Walk.blockedAux ∅ .fwd q := by
      cases inc with
      | start => exact hq
      | fwd => exact absurd rfl hinc
      | bwd => exact fun h => hq (Or.inr h)
    simp only [Walk.support, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact key _ hr
    · exact open_fwd_noX hin q (hin _ _ e) hq' w hw
  | @bwd a a' _ e q ih =>
    intro inc hinc hq ha hr w hw
    have hq' : ¬ Walk.blockedAux ∅ .bwd q := by
      cases inc with
      | start => exact hq
      | fwd => exact absurd rfl hinc
      | bwd => exact fun h => hq (Or.inr h)
    simp only [Walk.support, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact key _ hr
    · exact ih .bwd (by intro h; cases h) hq' (hout _ _ e)
        (Relation.ReflTransGen.head ⟨hG _ _ e, ha⟩ hr) w hw

/-- **h2 fra (i) og (iii):** `Y ⊥ Z | ∅` i `G_{X̄Z̲}`. -/
lemma fd_h2 {X Y Z : Finset V} (hYZ : Disjoint Y Z) (hc : FrontdoorCriterion G X Y Z) :
    SetSound.DSeparatedSet (cutOut (cutIn G X) Z) ∅ Y Z := by
  intro y hy z hz p hpath
  by_contra hp
  have hin : ∀ u v, (cutOut (cutIn G X) Z).edge u v → v ∉ X := fun u v e => e.1.2
  have hout : ∀ u v, (cutOut (cutIn G X) Z).edge u v → u ∉ Z := fun u v e => e.2
  have hG : ∀ u v, (cutOut (cutIn G X) Z).edge u v → G.edge u v := fun u v e => e.1.1
  have hyZ : y ∉ Z := Finset.disjoint_left.mp hYZ hy
  -- Ingen node på p ligger i X (ellers en rettet vei X -> Y som unngår Z).
  have hnoX := open_bwd_noX (y := y) hin hout hG (fun x hx hr => hc.1 x hx y hy hr)
    p .start (by intro h; cases h) hp hyZ Relation.ReflTransGen.refl
  -- Da er p en åpen back-door-sti fra Z til Y i G, gitt X.
  have hne : wIsNil p = false := by
    cases p with
    | nil v => exact absurd hz hyZ
    | fwd _ _ => rfl
    | bwd _ _ => rfl
  have hpath' : (mapSub hG p).IsPath := by
    unfold Walk.IsPath
    rw [support_mapSub]
    exact hpath
  exact open_mapSub_of_noX hG p .start hnoX hp
    (hc.2.2 y hy z hz (mapSub hG p) hpath' (endsInto_of_noOut hG hout p hz hne))

open Rule3Flag in
/-- **Front-door-justeringsformelen med Pearls kriterium.** -/
theorem frontdoor_adjustment_criterion {α : V → Type*} (M : G.CausalModel α)
    (X Y Z : Finset V)
    (hZX : Disjoint Z X) (hYX : Disjoint Y X) (hYZ : Disjoint Y Z)
    (hc : FrontdoorCriterion G X Y Z)
    (t : Assignment (α := α) (Y ∪ X ∪ Z))
    (hx : M.marginal X (t.restrict (show X ⊆ Y ∪ X ∪ Z by
        intro v hv; simp only [Finset.mem_union]; tauto)) ≠ 0)
    (hpos : ∀ (z : Assignment (α := α) Z) (x' : Assignment (α := α) X),
      M.marginal (Z ∪ X)
        ((setZ X (Y ∪ Z ∪ X) ((setZ Z (Y ∪ X ∪ Z) t z).restrict
            (show Y ∪ Z ∪ X ⊆ Y ∪ X ∪ Z by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) x').restrict
          (show Z ∪ X ⊆ Y ∪ Z ∪ X by
            intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) ≠ 0) :
    (doModel M X (t.restrict (show X ⊆ Y ∪ X ∪ Z by
        intro v hv; simp only [Finset.mem_union]; tauto))).marginal Y
        (t.restrict (show Y ⊆ Y ∪ X ∪ Z by
          intro v hv; simp only [Finset.mem_union]; tauto)) =
    ∑' z : Assignment (α := α) Z,
      M.marginal (Z ∪ X) ((setZ Z (Y ∪ X ∪ Z) t z).restrict (show Z ∪ X ⊆ Y ∪ X ∪ Z by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) /
        M.marginal X (t.restrict (show X ⊆ Y ∪ X ∪ Z by
          intro v hv; simp only [Finset.mem_union]; tauto)) *
      ∑' x' : Assignment (α := α) X,
        M.marginal (Y ∪ Z ∪ X) (setZ X (Y ∪ Z ∪ X) ((setZ Z (Y ∪ X ∪ Z) t z).restrict
            (show Y ∪ Z ∪ X ⊆ Y ∪ X ∪ Z by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) x') *
          M.marginal X ((setZ X (Y ∪ Z ∪ X) ((setZ Z (Y ∪ X ∪ Z) t z).restrict
            (show Y ∪ Z ∪ X ⊆ Y ∪ X ∪ Z by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) x').restrict
            (show X ⊆ Y ∪ Z ∪ X by intro v hv; simp only [Finset.mem_union]; tauto)) /
          M.marginal (Z ∪ X) ((setZ X (Y ∪ Z ∪ X) ((setZ Z (Y ∪ X ∪ Z) t z).restrict
            (show Y ∪ Z ∪ X ⊆ Y ∪ X ∪ Z by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) x').restrict
            (show Z ∪ X ⊆ Y ∪ Z ∪ X by
              intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) :=
  frontdoor_adjustment M X Y Z hZX hYX hYZ (fd_h1 hZX hc) (fd_h2 hYZ hc) (fd_h3 hc)
    (fd_hdesc hZX hc) (fd_h4 hYZ hc) t hx hpos

end Adjustment

#print axioms Adjustment.backdoor_stratum
#print axioms Adjustment.backdoor_adjustment
#print axioms Adjustment.marginal_empty
#print axioms Adjustment.frontdoor_step1
#print axioms Adjustment.frontdoor_step2
#print axioms Adjustment.frontdoor_step3
#print axioms Adjustment.frontdoor_stratum
#print axioms Adjustment.frontdoor_product
#print axioms Adjustment.frontdoor_adjustment
#print axioms Adjustment.cutOut_dsep_of_backdoor
#print axioms Adjustment.backdoor_adjustment_criterion
#print axioms Adjustment.fd_h1
#print axioms Adjustment.fd_h4
#print axioms Adjustment.fd_hdesc
#print axioms Adjustment.fd_h3
#print axioms Adjustment.fd_h2
#print axioms Adjustment.frontdoor_adjustment_criterion
