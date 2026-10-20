import PearlDoCalculus.DoCalculus

/-!
# Regel 3

Kjeden er `P_z = P_{z₂,z₁} → P_{z₂} → P`, der `Z₂` er nodene i `Z` som ikke er
forfedre til `W`. Fase 1 i denne fila: subgraf-monotonitet for d-separasjon.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Classical

namespace Rule3

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- En vandring i en graf med færre kanter er en vandring i den større grafen. -/
def mapSub {H H' : DAG V} (hsub : ∀ u v, H'.edge u v → H.edge u v) :
    {a b : V} → Walk H' a b → Walk H a b
  | _, _, .nil v => .nil v
  | _, _, .fwd e p => .fwd (hsub _ _ e) (mapSub hsub p)
  | _, _, .bwd e p => .bwd (hsub _ _ e) (mapSub hsub p)

lemma support_mapSub {H H' : DAG V} (hsub : ∀ u v, H'.edge u v → H.edge u v) :
    ∀ {a b : V} (p : Walk H' a b), (mapSub hsub p).support = p.support := by
  intro a b p
  induction p with
  | nil v => rfl
  | fwd e p ih => simp [mapSub, Walk.support, ih]
  | bwd e p ih => simp [mapSub, Walk.support, ih]

/-- Nås en node i den mindre grafen, nås den i den større. -/
lemma reaches_mono {H H' : DAG V} (hsub : ∀ u v, H'.edge u v → H.edge u v)
    {u v : V} (h : H'.Reaches u v) : H.Reaches u v :=
  Relation.ReflTransGen.mono (fun a b hab => hsub a b hab) h

/-- Blokkert i den større grafen gir blokkert i den mindre: ikke-kollidere
blokkerer likt, og en kollider har færre etterkommere i den mindre grafen. -/
lemma blocked_of_mapSub {H H' : DAG V} (hsub : ∀ u v, H'.edge u v → H.edge u v)
    {Z : Finset V} : ∀ (inc : Incoming) {a b : V} (p : Walk H' a b),
    Walk.blockedAux Z inc (mapSub hsub p) → Walk.blockedAux Z inc p := by
  intro inc a b p
  induction p generalizing inc with
  | nil v => intro h; simpa [mapSub, Walk.blockedAux] using h
  | fwd e p ih =>
    cases inc <;> simp only [mapSub, Walk.blockedAux] <;>
      first
      | exact ih _
      | exact Or.imp_right (ih _)
  | bwd e p ih =>
    cases inc <;> simp only [mapSub, Walk.blockedAux] <;>
      first
      | exact ih _
      | exact Or.imp_right (ih _)
      | exact Or.imp (fun h z hz hr => h z hz (reaches_mono hsub hr)) (ih _)

/-- **Subgraf-monotonitet.** Stibasert d-separasjon overlever at kanter fjernes. -/
theorem dsepPath_mono {H H' : DAG V} (hsub : ∀ u v, H'.edge u v → H.edge u v)
    {Z : Finset V} {x y : V} (h : H.DSeparatedPath Z x y) :
    H'.DSeparatedPath Z x y := by
  intro p hp
  have hp' : (mapSub hsub p).IsPath := by
    unfold Walk.IsPath
    rw [support_mapSub]
    exact hp
  exact blocked_of_mapSub hsub .start p (h (mapSub hsub p) hp')

/-- Mengdeversjonen av subgraf-monotonitet. -/
theorem dsepSet_mono {H H' : DAG V} (hsub : ∀ u v, H'.edge u v → H.edge u v)
    {Z X Y : Finset V} (h : SetSound.DSeparatedSet H Z X Y) :
    SetSound.DSeparatedSet H' Z X Y :=
  fun x hx y hy => dsepPath_mono hsub (h x hx y hy)

variable {G : DAG V}

/-- For `v ∉ Z` er kjernefaktoren i intervensjonsmodellen den samme som i `M`,
på enhver mengde `S`. -/
lemma kfac_doModel_of_not_mem {α : V → Type*} (M : G.CausalModel α) (Z : Finset V)
    (z : Assignment (α := α) Z) (S : Finset V) (a : Assignment (α := α) S)
    {v : V} (hv : v ∉ Z) :
    kfac (doModel M Z z) S a v = kfac M S a v := by
  have hpar : (cutIn G Z).parents v = G.parents v := parents_cutIn_of_not_mem hv
  unfold kfac
  by_cases hc : v ∈ S ∧ G.parents v ⊆ S
  · have hc' : v ∈ S ∧ (cutIn G Z).parents v ⊆ S := ⟨hc.1, by rw [hpar]; exact hc.2⟩
    rw [dif_pos hc', dif_pos hc]
    simp only [doModel, dif_neg hv]
    all_goals rfl
  · have hc' : ¬ (v ∈ S ∧ (cutIn G Z).parents v ⊆ S) :=
      fun h => hc ⟨h.1, by rw [← hpar]; exact h.2⟩
    rw [dif_neg hc', dif_neg hc]

/-- **B2.** En intervensjon på `Z` endrer ikke marginalen på en ancestral mengde
disjunkt fra `Z`. -/
theorem doModel_marginal_of_ancestral {α : V → Type*} (M : G.CausalModel α)
    (Z : Finset V) (z : Assignment (α := α) Z) (A : Finset V)
    (hA : ∀ v ∈ A, ∀ w, G.edge w v → w ∈ A) (hAZ : Disjoint A Z)
    (a : Assignment (α := α) A) :
    (doModel M Z z).marginal A a = M.marginal A a := by
  have hA' : ∀ v ∈ A, ∀ w, (cutIn G Z).edge w v → w ∈ A :=
    fun v hv w hw => hA v hv w hw.1
  rw [marginal_ancestral_apply (doModel M Z z) A hA' a, marginal_ancestral_apply M A hA a]
  exact Finset.prod_congr rfl
    (fun v hv => kfac_doModel_of_not_mem M Z z A a (Finset.disjoint_left.mp hAZ hv))

/-- B2 for delmengder av en ancestral mengde disjunkt fra `Z`. -/
theorem doModel_marginal_of_sub {α : V → Type*} (M : G.CausalModel α)
    (Z : Finset V) (z : Assignment (α := α) Z) (A : Finset V)
    (hA : ∀ v ∈ A, ∀ w, G.edge w v → w ∈ A) (hAZ : Disjoint A Z)
    (S : Finset V) (hSA : S ⊆ A) (s : Assignment (α := α) S) :
    (doModel M Z z).marginal S s = M.marginal S s := by
  have hPMF : (doModel M Z z).marginal A = M.marginal A :=
    PMF.ext (doModel_marginal_of_ancestral M Z z A hA hAZ)
  rw [← marginal_restrict (doModel M Z z) hSA, ← marginal_restrict M hSA, hPMF]

/-- `Z(W)`: nodene i `Z` som ikke er forfedre til noen node i `W`. -/
noncomputable def Z2 (G : DAG V) (Z W : Finset V) : Finset V := Z.filter (fun z => z ∉ ancestors G W)

/-- Resten av `Z`: nodene som er forfedre til `W`. -/
noncomputable def Z1 (G : DAG V) (Z W : Finset V) : Finset V := Z.filter (fun z => z ∈ ancestors G W)

/-- Blokkert fra start gir blokkert i tilstand `.bwd`: `.bwd` legger bare til en
betingelse i første node. -/
lemma start_imp_bwd {H : DAG V} {Z : Finset V} {a b : V} (p : Walk H a b) :
    Walk.blockedAux Z .start p → Walk.blockedAux Z .bwd p := by
  cases p <;> simp [Walk.blockedAux] <;> tauto

/-- Nås `y` fra `z ∈ Z₂` i `G`, finnes en siste `Z₂`-node `z′` som når `y` i
`G_{\overline{Z₂}}`. -/
lemma reach_last {Z W : Finset V} {z y : V} (hz : z ∈ Z2 G Z W) (hr : G.Reaches z y) :
    ∃ z' ∈ Z2 G Z W, (cutIn G (Z2 G Z W)).Reaches z' y := by
  induction hr with
  | refl => exact ⟨z, hz, Relation.ReflTransGen.refl⟩
  | @tail b c _ hbc ih =>
    obtain ⟨z', hz', hr'⟩ := ih
    by_cases hc : c ∈ Z2 G Z W
    · exact ⟨c, hc, Relation.ReflTransGen.refl⟩
    · exact ⟨z', hz', Relation.ReflTransGen.tail hr' ⟨hbc, hc⟩⟩

/-- Nås `c` fra `z′` i `cutIn G Z`, og ligger ingen node `z′` når i `W`, finnes en
vandring fra `c` bakover til `z′` som er åpen i tilstand `.bwd`. -/
lemma open_back {Z W : Finset V} {z' : V} (hnW : ∀ v, G.Reaches z' v → v ∉ W) :
    ∀ {c : V}, (cutIn G Z).Reaches z' c →
      ∃ p : Walk (cutIn G Z) c z', ¬ Walk.blockedAux W .bwd p := by
  intro c hr
  induction hr with
  | refl => exact ⟨Walk.nil _, by simp [Walk.blockedAux]⟩
  | @tail b c hab hbc ih =>
    obtain ⟨p, hp⟩ := ih
    refine ⟨Walk.bwd hbc p, ?_⟩
    have hcW : c ∉ W :=
      hnW c (reaches_mono (H := G) (H' := cutIn G Z) (fun u v h => h.1)
        (Relation.ReflTransGen.tail hab hbc))
    simp only [Walk.blockedAux]
    tauto

/-- **B1 for `Y`.** Under hypotesen i regel 3 er ingen node i `Z₂` forfar til `Y`. -/
theorem not_reaches_Y {Y Z W : Finset V}
    (h : SetSound.DSeparatedSet (cutIn G (Z2 G Z W)) W Y Z)
    {z y : V} (hz : z ∈ Z2 G Z W) (hy : y ∈ Y) : ¬ G.Reaches z y := by
  intro hr
  obtain ⟨z', hz', hr'⟩ := reach_last hz hr
  have hz'Z : z' ∈ Z := (Finset.mem_filter.mp hz').1
  have hz'W : z' ∉ ancestors G W := (Finset.mem_filter.mp hz').2
  have hnW : ∀ v, G.Reaches z' v → v ∉ W :=
    fun v hv hvW => hz'W (mem_ancestors_iff.mpr ⟨v, hvW, hv⟩)
  obtain ⟨p, hp⟩ := open_back hnW hr'
  exact hp (start_imp_bwd p (dsep_of_dsepPath (h y hy z' hz'Z) p))

/-- **B1.** `Z₂` er disjunkt fra An(Y ∪ W). -/
theorem disjoint_anc_Z2 {Y Z W : Finset V}
    (h : SetSound.DSeparatedSet (cutIn G (Z2 G Z W)) W Y Z) :
    Disjoint (ancestors G (Y ∪ W)) (Z2 G Z W) := by
  rw [Finset.disjoint_left]
  intro v hv hvZ
  obtain ⟨s, hs, hr⟩ := mem_ancestors_iff.mp hv
  rcases Finset.mem_union.mp hs with hs | hs
  · exact not_reaches_Y h hvZ hs hr
  · exact (Finset.mem_filter.mp hvZ).2 (mem_ancestors_iff.mpr ⟨s, hs, hr⟩)

/-- **Komposisjon.** `do(A)` inne i `do(B)` har samme fellesfordeling som
`do(A ∪ B)`, for disjunkte `A` og `B`. -/
theorem doModel_comp {α : V → Type*} (M : G.CausalModel α) (A B : Finset V)
    (hAB : Disjoint A B) (z : Assignment (α := α) (A ∪ B))
    (u : Assignment (α := α) (Finset.univ : Finset V)) :
    (doModel (doModel M B (z.restrict (Finset.subset_union_right : B ⊆ A ∪ B))) A
        (z.restrict (Finset.subset_union_left : A ⊆ A ∪ B))).fullJoint u =
      (doModel M (A ∪ B) z).fullJoint u := by
  rw [doModel_fullJoint, doModel_fullJoint]
  by_cases h : u.restrict (Finset.subset_univ (A ∪ B)) = z
  · have hA : u.restrict (Finset.subset_univ A) =
        z.restrict (Finset.subset_union_left : A ⊆ A ∪ B) := by
      funext ⟨v, hv⟩
      exact congrFun h ⟨v, Finset.mem_union_left _ hv⟩
    rw [if_pos hA, if_pos h, one_mul, one_mul]
    have hsub : (A ∪ B)ᶜ ⊆ Aᶜ := Finset.compl_subset_compl.mpr Finset.subset_union_left
    have hprod : ∏ v ∈ (A ∪ B)ᶜ, kfac (doModel M B
          (z.restrict (Finset.subset_union_right : B ⊆ A ∪ B))) Finset.univ u v =
        ∏ v ∈ Aᶜ, kfac (doModel M B
          (z.restrict (Finset.subset_union_right : B ⊆ A ∪ B))) Finset.univ u v := by
      refine Finset.prod_subset hsub (fun v hvA hvAB => ?_)
      have hvB : v ∈ B := by
        by_contra hvB
        exact hvAB (Finset.mem_compl.mpr (fun h' =>
          (Finset.mem_union.mp h').elim (Finset.mem_compl.mp hvA) hvB))
      rw [kfac_doModel, dif_pos hvB, if_pos]
      exact congrFun h ⟨v, Finset.mem_union_right _ hvB⟩
    rw [← hprod]
    exact Finset.prod_congr rfl (fun v hv => by
      have hvB : v ∉ B := fun hb => (Finset.mem_compl.mp hv) (Finset.mem_union_right _ hb)
      rw [kfac_doModel, dif_neg hvB])
  · rw [if_neg h, zero_mul]
    by_cases hA : u.restrict (Finset.subset_univ A) =
        z.restrict (Finset.subset_union_left : A ⊆ A ∪ B)
    · rw [if_pos hA, one_mul]
      have hex : ∃ v, ∃ hvB : v ∈ B,
          u ⟨v, Finset.mem_univ v⟩ ≠ z ⟨v, Finset.mem_union_right _ hvB⟩ := by
        by_contra hno
        push_neg at hno
        apply h
        funext ⟨v, hv⟩
        rcases Finset.mem_union.mp hv with hvA | hvB
        · exact congrFun hA ⟨v, hvA⟩
        · exact hno v hvB
      obtain ⟨v, hvB, hne⟩ := hex
      have hvA : v ∈ Aᶜ := Finset.mem_compl.mpr (Finset.disjoint_right.mp hAB hvB)
      refine Finset.prod_eq_zero hvA ?_
      rw [kfac_doModel, dif_pos hvB,
        if_neg (show ¬ (u ⟨v, Finset.mem_univ v⟩ =
          (z.restrict (Finset.subset_union_right : B ⊆ A ∪ B)) ⟨v, hvB⟩) from hne)]
    · rw [if_neg hA, zero_mul]

/-- Komposisjon for marginaler. -/
theorem doModel_comp_marginal {α : V → Type*} (M : G.CausalModel α) (A B : Finset V)
    (hAB : Disjoint A B) (z : Assignment (α := α) (A ∪ B)) (S : Finset V)
    (s : Assignment (α := α) S) :
    (doModel (doModel M B (z.restrict (Finset.subset_union_right : B ⊆ A ∪ B))) A
        (z.restrict (Finset.subset_union_left : A ⊆ A ∪ B))).marginal S s =
      (doModel M (A ∪ B) z).marginal S s := by
  have hF : (doModel (doModel M B (z.restrict (Finset.subset_union_right : B ⊆ A ∪ B))) A
        (z.restrict (Finset.subset_union_left : A ⊆ A ∪ B))).fullJoint =
      (doModel M (A ∪ B) z).fullJoint :=
    PMF.ext (doModel_comp M A B hAB z)
  unfold CausalModel.marginal
  rw [hF]

/-- Komposisjon der unionen er gitt som en likhet `A ∪ B = C`. -/
theorem doModel_comp_marginal' {α : V → Type*} (M : G.CausalModel α) (A B C : Finset V)
    (hAB : Disjoint A B) (hC : A ∪ B = C) (z : Assignment (α := α) C) (S : Finset V)
    (s : Assignment (α := α) S) :
    (doModel (doModel M B (z.restrict (show B ⊆ C by rw [← hC]; exact Finset.subset_union_right)))
        A (z.restrict (show A ⊆ C by rw [← hC]; exact Finset.subset_union_left))).marginal S s =
      (doModel M C z).marginal S s := by
  subst hC
  exact doModel_comp_marginal M A B hAB z S s

lemma Z1_union_Z2 (Z W : Finset V) : Z1 G Z W ∪ Z2 G Z W = Z := by
  ext v
  simp only [Z1, Z2, Finset.mem_union, Finset.mem_filter]
  tauto

lemma disjoint_Z1_Z2 (Z W : Finset V) : Disjoint (Z1 G Z W) (Z2 G Z W) := by
  rw [Finset.disjoint_left]
  intro v h1 h2
  exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2

/-- Ren algebra: fra `a·b = c·d` og `a·e = f·d`, med `d ≠ 0, ∞`, følger `c·e = f·b`. -/
lemma cancel_aux {a b c d e f : ENNReal} (hd0 : d ≠ 0) (hdt : d ≠ ⊤)
    (h1 : a * b = c * d) (h2 : a * e = f * d) : c * e = f * b := by
  apply (ENNReal.mul_right_inj hd0 hdt).mp
  calc d * (c * e) = (c * d) * e := by ring
    _ = (a * b) * e := by rw [h1]
    _ = (a * e) * b := by ring
    _ = (f * d) * b := by rw [h2]
    _ = d * (f * b) := by ring

/-- **Regel 3 (fjerning av handling), med positivitet.** Er `Y` og `Z` d-separert
av `W` i `G_{\overline{Z(W)}}`, og er `P(z₁, w) > 0` for delen `Z₁` av `Z` som er
forfedre til `W`, så er `P_z(y | w) = P(y | w)`, i produktform. -/
theorem rule3_pos {α : V → Type*} (M : G.CausalModel α) (Y Z W : Finset V)
    (hYZ : Disjoint Y Z) (hWZ : Disjoint W Z) (hYW : Disjoint Y W)
    (h : SetSound.DSeparatedSet (cutIn G (Z2 G Z W)) W Y Z)
    (t : Assignment (α := α) (Y ∪ Z ∪ W))
    (hpos : M.marginal (Z1 G Z W ∪ W) (t.restrict (show Z1 G Z W ∪ W ⊆ Y ∪ Z ∪ W by
      intro v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.filter_subset _ _ hv))
      · exact Finset.mem_union_right _ hv)) ≠ 0) :
    (doModel M Z (t.restrict (show Z ⊆ Y ∪ Z ∪ W by
        intro v hv; simp only [Finset.mem_union]; tauto))).marginal (Y ∪ W)
        (t.restrict (show Y ∪ W ⊆ Y ∪ Z ∪ W by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
      M.marginal W (t.restrict (show W ⊆ Y ∪ Z ∪ W by
        intro v hv; simp only [Finset.mem_union]; tauto)) =
    M.marginal (Y ∪ W) (t.restrict (show Y ∪ W ⊆ Y ∪ Z ∪ W by
        intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
      (doModel M Z (t.restrict (show Z ⊆ Y ∪ Z ∪ W by
        intro v hv; simp only [Finset.mem_union]; tauto))).marginal W
        (t.restrict (show W ⊆ Y ∪ Z ∪ W by
          intro v hv; simp only [Finset.mem_union]; tauto)) := by
  have sZ : Z ⊆ Y ∪ Z ∪ W := by intro v hv; simp only [Finset.mem_union]; tauto
  have hZ1Z : Z1 G Z W ⊆ Z := Finset.filter_subset _ _
  have hZ2Z : Z2 G Z W ⊆ Z := Finset.filter_subset _ _
  have sT1 : Y ∪ Z1 G Z W ∪ W ⊆ Y ∪ Z ∪ W := by
    intro v hv
    simp only [Finset.mem_union] at hv ⊢
    rcases hv with (hv | hv) | hv
    · exact Or.inl (Or.inl hv)
    · exact Or.inl (Or.inr (hZ1Z hv))
    · exact Or.inr hv
  have hdisj := disjoint_Z1_Z2 (G := G) Z W
  have hYZ1 : Disjoint Y (Z1 G Z W) := Finset.disjoint_of_subset_right hZ1Z hYZ
  have hWZ1 : Disjoint W (Z1 G Z W) := Finset.disjoint_of_subset_right hZ1Z hWZ
  have h1 : SetSound.DSeparatedSet (cutIn G (Z2 G Z W)) W Y (Z1 G Z W) :=
    fun y hy z hz => h y hy z (hZ1Z hz)
  have h2 : SetSound.DSeparatedSet (cutOut (cutIn G (Z2 G Z W)) (Z1 G Z W)) W Y (Z1 G Z W) :=
    dsepSet_mono (H := cutIn G (Z2 G Z W))
      (H' := cutOut (cutIn G (Z2 G Z W)) (Z1 G Z W)) (fun u v huv => huv.1) h1
  -- Trinn A i M₂ = do(Z₂): regel 2 og betinget uavhengighet.
  have hr2 := rule2_core (doModel M (Z2 G Z W) ((t.restrict sZ).restrict hZ2Z))
    Y (Z1 G Z W) W ((t.restrict sZ).restrict hZ1Z) hYZ1 hWZ1 hYW h2 (t.restrict sT1) rfl
  have hci := SetSound.dsep_sound_set (doModel M (Z2 G Z W) ((t.restrict sZ).restrict hZ2Z))
    Y (Z1 G Z W) W hYW hWZ1.symm h1 (t.restrict sT1)
  -- B2: An(Y ∪ W) er ancestral og disjunkt fra Z₂.
  have hAcl := DSepSound.A_closed (G := G) (Y ∪ W)
  have hAZ := disjoint_anc_Z2 h
  have hYW_A : Y ∪ W ⊆ ancestors G (Y ∪ W) := subset_ancestors _
  have hW_A : W ⊆ ancestors G (Y ∪ W) :=
    fun v hv => subset_ancestors _ (Finset.mem_union_right _ hv)
  have hZ1W_A : Z1 G Z W ∪ W ⊆ ancestors G (Y ∪ W) := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨s, hs, hr⟩ := mem_ancestors_iff.mp (Finset.mem_filter.mp hv).2
      exact mem_ancestors_iff.mpr ⟨s, Finset.mem_union_right _ hs, hr⟩
    · exact hW_A hv
  -- Positivitet i M₂ er positivitet i M.
  have hd0 : (doModel M (Z2 G Z W) ((t.restrict sZ).restrict hZ2Z)).marginal (Z1 G Z W ∪ W)
      ((t.restrict sT1).restrict (show Z1 G Z W ∪ W ⊆ Y ∪ Z1 G Z W ∪ W by
        intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) ≠ 0 := by
    rw [doModel_marginal_of_sub M (Z2 G Z W) _ _ hAcl hAZ _ hZ1W_A]
    exact hpos
  have hA := cancel_aux hd0 (PMF.apply_ne_top _ _) hr2 hci
  -- Tilbake til do(Z) og M.
  rw [doModel_comp_marginal' M _ _ Z hdisj (Z1_union_Z2 Z W) (t.restrict sZ) (Y ∪ W) _,
    doModel_comp_marginal' M _ _ Z hdisj (Z1_union_Z2 Z W) (t.restrict sZ) W _,
    doModel_marginal_of_sub M (Z2 G Z W) _ _ hAcl hAZ (Y ∪ W) hYW_A _,
    doModel_marginal_of_sub M (Z2 G Z W) _ _ hAcl hAZ W hW_A _] at hA
  exact hA

/-- I `G_{X̄}` når ingen node utenfor `X` en node i `X`: den siste kanten inn i
`x` er fjernet. -/
lemma not_reaches_cutIn {X : Finset V} {z x : V} (hz : z ∉ X) (hx : x ∈ X) :
    ¬ (cutIn G X).Reaches z x := by
  intro h
  rcases Relation.ReflTransGen.cases_tail h with rfl | ⟨c, _, hc⟩
  · exact hz hx
  · exact hc.2 hx

/-- I `G_{X̄}` er `Z(X ∪ W) = Z(W)`: nodene i `X` har ingen forfedre utenfor `X`. -/
lemma Z2_cutIn_eq (X Z W : Finset V) (hZX : Disjoint Z X) :
    Z2 (cutIn G X) Z (X ∪ W) = Z2 (cutIn G X) Z W := by
  ext z
  simp only [Z2, Finset.mem_filter]
  constructor
  · rintro ⟨hz, hn⟩
    refine ⟨hz, fun hw => hn ?_⟩
    obtain ⟨s, hs, hr⟩ := mem_ancestors_iff.mp hw
    exact mem_ancestors_iff.mpr ⟨s, Finset.mem_union_right _ hs, hr⟩
  · rintro ⟨hz, hn⟩
    refine ⟨hz, fun hxw => ?_⟩
    obtain ⟨s, hs, hr⟩ := mem_ancestors_iff.mp hxw
    rcases Finset.mem_union.mp hs with hs | hs
    · exact not_reaches_cutIn (Finset.disjoint_left.mp hZX hz) hs hr
    · exact hn (mem_ancestors_iff.mpr ⟨s, hs, hr⟩)

/-- Tilsvarende for `Z₁`: forfedrene til `X ∪ W` i `Z` er forfedrene til `W`. -/
lemma Z1_cutIn_eq (X Z W : Finset V) (hZX : Disjoint Z X) :
    Z1 (cutIn G X) Z (X ∪ W) = Z1 (cutIn G X) Z W := by
  ext z
  simp only [Z1, Finset.mem_filter]
  constructor
  · rintro ⟨hz, hxw⟩
    refine ⟨hz, ?_⟩
    obtain ⟨s, hs, hr⟩ := mem_ancestors_iff.mp hxw
    rcases Finset.mem_union.mp hs with hs | hs
    · exact absurd hr (not_reaches_cutIn (Finset.disjoint_left.mp hZX hz) hs)
    · exact mem_ancestors_iff.mpr ⟨s, hs, hr⟩
  · rintro ⟨hz, hw⟩
    refine ⟨hz, ?_⟩
    obtain ⟨s, hs, hr⟩ := mem_ancestors_iff.mp hw
    exact mem_ancestors_iff.mpr ⟨s, Finset.mem_union_right _ hs, hr⟩

/-- **Regel 3 (Pearl), med positivitet.** Er `Y` og `Z` d-separert av `X ∪ W` i
`G_{X̄, \overline{Z(W)}}`, der `Z(W)` er nodene i `Z` som ikke er forfedre til `W`
i `G_{X̄}`, så er `P_{x,z}(y | x, w) = P_x(y | x, w)`, i produktform.

Positiviteten er `P_x(z₁, x, w) > 0` for delen `Z₁` av `Z` som er forfedre til
`X ∪ W` i `G_{X̄}`; ved `Z1_cutIn_eq` er det de samme nodene som er forfedre til `W`. -/
theorem rule3 {α : V → Type*} (M : G.CausalModel α) (X Y Z W : Finset V)
    (x : Assignment (α := α) X)
    (hYZ : Disjoint Y Z) (hXWZ : Disjoint (X ∪ W) Z) (hYXW : Disjoint Y (X ∪ W))
    (h : SetSound.DSeparatedSet (cutIn (cutIn G X) (Z2 (cutIn G X) Z W)) (X ∪ W) Y Z)
    (t : Assignment (α := α) (Y ∪ Z ∪ (X ∪ W)))
    (hpos : (doModel M X x).marginal (Z1 (cutIn G X) Z (X ∪ W) ∪ (X ∪ W))
      (t.restrict (show Z1 (cutIn G X) Z (X ∪ W) ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
        intro v hv
        rcases Finset.mem_union.mp hv with hv | hv
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.filter_subset _ _ hv))
        · exact Finset.mem_union_right _ hv)) ≠ 0) :
    (doModel (doModel M X x) Z (t.restrict (show Z ⊆ Y ∪ Z ∪ (X ∪ W) by
        intro v hv; simp only [Finset.mem_union]; tauto))).marginal (Y ∪ (X ∪ W))
        (t.restrict (show Y ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
      (doModel M X x).marginal (X ∪ W) (t.restrict (show X ∪ W ⊆ Y ∪ Z ∪ (X ∪ W) by
        intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) =
    (doModel M X x).marginal (Y ∪ (X ∪ W))
        (t.restrict (show Y ∪ (X ∪ W) ⊆ Y ∪ Z ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) *
      (doModel (doModel M X x) Z (t.restrict (show Z ⊆ Y ∪ Z ∪ (X ∪ W) by
        intro v hv; simp only [Finset.mem_union]; tauto))).marginal (X ∪ W)
        (t.restrict (show X ∪ W ⊆ Y ∪ Z ∪ (X ∪ W) by
          intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto)) := by
  have hZX : Disjoint Z X :=
    Finset.disjoint_of_subset_right Finset.subset_union_left hXWZ.symm
  rw [← Z2_cutIn_eq X Z W hZX] at h
  exact rule3_pos (doModel M X x) Y Z (X ∪ W) hYZ hXWZ hYXW h t hpos

end Rule3

#print axioms Rule3.dsepPath_mono
#print axioms Rule3.dsepSet_mono
#print axioms Rule3.doModel_marginal_of_ancestral
#print axioms Rule3.doModel_marginal_of_sub
#print axioms Rule3.not_reaches_Y
#print axioms Rule3.disjoint_anc_Z2
#print axioms Rule3.doModel_comp
#print axioms Rule3.doModel_comp_marginal
#print axioms Rule3.rule3_pos
#print axioms Rule3.Z2_cutIn_eq
#print axioms Rule3.Z1_cutIn_eq
#print axioms Rule3.rule3
