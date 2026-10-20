import PearlDoCalculus.Rule3
import PearlDoCalculus.DoAudit

/-!
# Regel 3 uten positivitet: flaggmodellen

Pearls utvidede graf legger til en intervensjonsnode `F_z → z` per `z ∈ Z`.
Siden `F_z` bare har ett barn, legges flagget her inn i verdien til `z`:
flaggmodellen har verdier i `Option (α v)`, der `none` på en `Z`-node betyr
«intervenert til `z₀`». Den inneholder både `P` (alle `some`) og `P_{z₀}`
(`Z`-nodene `none`), på samme graf, så `dsep_sound_set` gjelder direkte.
-/

open PearlDoCalculus DAG DAG.CausalModel DoCalculus Rule3 Classical

namespace Rule3Flag

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V} {α : V → Type*}

/-- Avbildning med `some` bevarer sannsynligheten i `some a`. -/
lemma map_some_apply {β : Type*} (p : PMF β) (a : β) : (p.map some) (some a) = p a := by
  rw [PMF.map_apply, tsum_eq_single a]
  · simp
  · intro b hb
    simp [Ne.symm hb]

/-- Avbildning med `some` gir ingen masse i `none`. -/
lemma map_some_none {β : Type*} (p : PMF β) : (p.map some) none = 0 := by
  rw [PMF.map_apply]
  simp

/-- Hvordan et barn leser en forelder: `some a` er `a`, `none` er `z₀` på `Z`
(og en vilkårlig verdi utenfor `Z`, der `none` aldri har positiv sannsynlighet). -/
noncomputable def readVal [∀ w, Nonempty (α w)] (Z : Finset V)
    (z₀ : Assignment (α := α) Z) (u : V) (o : Option (α u)) : α u :=
  o.elim (if hu : u ∈ Z then z₀ ⟨u, hu⟩ else Classical.arbitrary _) id

/-- **Flaggmodellen.** For `v ∈ Z`: med sannsynlighet ½ `none`, ellers `some` av
en verdi fra `M`. For `v ∉ Z`: `some` av en verdi fra `M`. Foreldre leses med
`readVal`. -/
noncomputable def flagModel [∀ w, Nonempty (α w)] (M : G.CausalModel α) (Z : Finset V)
    (z₀ : Assignment (α := α) Z) : G.CausalModel (fun v => Option (α v)) where
  fin := fun v => by haveI := M.fin v; infer_instance
  deq := fun v => by haveI := M.deq v; infer_instance
  kernel := fun v p =>
    if v ∈ Z then
      (PMF.uniformOfFintype Bool).bind (fun b =>
        if b then PMF.pure none
        else (M.kernel v (fun u => readVal Z z₀ u.1 (p u))).map some)
    else (M.kernel v (fun u => readVal Z z₀ u.1 (p u))).map some

/-- Observasjon: alle noder `some`. -/
def obs (u : Assignment (α := α) (Finset.univ : Finset V)) :
    Assignment (α := fun v => Option (α v)) (Finset.univ : Finset V) :=
  fun v => some (u v)

/-- Intervensjon: `Z`-nodene `none`, de andre `some`. -/
def intv (Z : Finset V) (u : Assignment (α := α) (Finset.univ : Finset V)) :
    Assignment (α := fun v => Option (α v)) (Finset.univ : Finset V) :=
  fun v => if v.1 ∈ Z then none else some (u v)

/-- Flaggkjernen på `Z` i `some a`: ½ ganger `M` sin. -/
lemma flag_kernel_some [∀ w, Nonempty (α w)] (M : G.CausalModel α) (Z : Finset V)
    (z₀ : Assignment (α := α) Z) {v : V} (hv : v ∈ Z)
    (p : ∀ u : {u // u ∈ G.parents v}, Option (α u.1)) (a : α v) :
    (flagModel M Z z₀).kernel v p (some a) =
      2⁻¹ * M.kernel v (fun u => readVal Z z₀ u.1 (p u)) a := by
  simp only [flagModel, if_pos hv]
  rw [PMF.bind_apply, tsum_fintype, Fintype.sum_bool]
  simp [PMF.uniformOfFintype_apply, PMF.pure_apply]
  congr 1
  refine (tsum_eq_single a ?_).trans ?_
  · intro b hb
    simp [Ne.symm hb]
  · simp

/-- Flaggkjernen på `Z` i `none`: ½. -/
lemma flag_kernel_none_mem [∀ w, Nonempty (α w)] (M : G.CausalModel α) (Z : Finset V)
    (z₀ : Assignment (α := α) Z) {v : V} (hv : v ∈ Z)
    (p : ∀ u : {u // u ∈ G.parents v}, Option (α u.1)) :
    (flagModel M Z z₀).kernel v p none = 2⁻¹ := by
  simp only [flagModel, if_pos hv]
  rw [PMF.bind_apply, tsum_fintype, Fintype.sum_bool]
  simp [PMF.uniformOfFintype_apply, PMF.pure_apply, map_some_none]

/-- Flaggkjernen utenfor `Z` i `some a`: `M` sin. -/
lemma flag_kernel_some_not_mem [∀ w, Nonempty (α w)] (M : G.CausalModel α) (Z : Finset V)
    (z₀ : Assignment (α := α) Z) {v : V} (hv : v ∉ Z)
    (p : ∀ u : {u // u ∈ G.parents v}, Option (α u.1)) (a : α v) :
    (flagModel M Z z₀).kernel v p (some a) =
      M.kernel v (fun u => readVal Z z₀ u.1 (p u)) a := by
  simp only [flagModel, if_neg hv]
  exact map_some_apply _ _

/-- **Punkt 1.** Kjernefaktorene i en observasjon: ½ ganger `M` sin på `Z`,
`M` sin utenfor. -/
lemma kfac_flag_obs [∀ w, Nonempty (α w)] (M : G.CausalModel α) (Z : Finset V)
    (z₀ : Assignment (α := α) Z) (u : Assignment (α := α) (Finset.univ : Finset V)) (v : V) :
    kfac (flagModel M Z z₀) Finset.univ (obs u) v =
      (if v ∈ Z then 2⁻¹ else 1) * kfac M Finset.univ u v := by
  rw [DoAudit.kfac_univ, DoAudit.kfac_univ]
  by_cases hv : v ∈ Z
  · rw [if_pos hv]
    exact flag_kernel_some M Z z₀ hv _ _
  · rw [if_neg hv, one_mul]
    exact flag_kernel_some_not_mem M Z z₀ hv _ _

/-- **Punkt 2.** Kjernefaktorene i en intervensjon: ½ på `Z`, og utenfor `Z`
`M` sin faktor i tilordningen med `Z` satt til `z₀`. -/
lemma kfac_flag_int [∀ w, Nonempty (α w)] (M : G.CausalModel α) (Z : Finset V)
    (z₀ : Assignment (α := α) Z) (u : Assignment (α := α) (Finset.univ : Finset V)) (v : V) :
    kfac (flagModel M Z z₀) Finset.univ (intv Z u) v =
      if v ∈ Z then 2⁻¹
      else kfac M Finset.univ (combineZ Z z₀ (u.restrict (Finset.subset_univ Zᶜ))) v := by
  rw [DoAudit.kfac_univ]
  by_cases hv : v ∈ Z
  · have hval : (intv Z u) ⟨v, Finset.mem_univ v⟩ = none := by simp [intv, hv]
    rw [if_pos hv, hval]
    exact flag_kernel_none_mem M Z z₀ hv _
  · have hval : (intv Z u) ⟨v, Finset.mem_univ v⟩ = some (u ⟨v, Finset.mem_univ v⟩) := by
      simp [intv, hv]
    rw [if_neg hv, DoAudit.kfac_univ, hval, flag_kernel_some_not_mem M Z z₀ hv]
    refine congrArg₂ (fun p x => M.kernel v p x) ?_ ?_
    · funext w
      by_cases hw : w.1 ∈ Z
      · simp [readVal, intv, combineZ, Assignment.restrict, hw]
      · simp [readVal, intv, combineZ, Assignment.restrict, hw]
    · simp [combineZ, Assignment.restrict, hv]

/-- **Fellesfordelingen i en observasjon:** `P⁺(obs u) = (½)^|Z| · P(u)`. -/
lemma flag_fullJoint_obs [∀ w, Nonempty (α w)] (M : G.CausalModel α) (Z : Finset V)
    (z₀ : Assignment (α := α) Z) (u : Assignment (α := α) (Finset.univ : Finset V)) :
    (flagModel M Z z₀).fullJoint (obs u) = (2⁻¹ : ENNReal) ^ Z.card * M.fullJoint u := by
  rw [fullJoint_apply_prod, fullJoint_apply_prod]
  simp_rw [kfac_flag_obs]
  rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

/-- **Fellesfordelingen i en intervensjon:** `P⁺(intv u) = (½)^|Z| · P_{z₀}(ũ)`,
der `ũ` er `u` utenfor `Z` og `z₀` på `Z`. -/
lemma flag_fullJoint_int [∀ w, Nonempty (α w)] (M : G.CausalModel α) (Z : Finset V)
    (z₀ : Assignment (α := α) Z) (u : Assignment (α := α) (Finset.univ : Finset V)) :
    (flagModel M Z z₀).fullJoint (intv Z u) =
      (2⁻¹ : ENNReal) ^ Z.card *
        (doModel M Z z₀).fullJoint (combineZ Z z₀ (u.restrict (Finset.subset_univ Zᶜ))) := by
  rw [fullJoint_apply_prod, doModel_fullJoint, if_pos (combine_restrict_Z Z z₀ _), one_mul]
  simp_rw [kfac_flag_int]
  rw [← Finset.prod_mul_prod_compl Z]
  have h1 : ∏ v ∈ Z, (if v ∈ Z then (2⁻¹ : ENNReal)
      else kfac M Finset.univ (combineZ Z z₀ (u.restrict (Finset.subset_univ Zᶜ))) v) =
      ∏ _v ∈ Z, (2⁻¹ : ENNReal) :=
    Finset.prod_congr rfl (fun v hv => if_pos hv)
  have h2 : ∏ v ∈ Zᶜ, (if v ∈ Z then (2⁻¹ : ENNReal)
      else kfac M Finset.univ (combineZ Z z₀ (u.restrict (Finset.subset_univ Zᶜ))) v) =
      ∏ v ∈ Zᶜ, kfac M Finset.univ (combineZ Z z₀ (u.restrict (Finset.subset_univ Zᶜ))) v :=
    Finset.prod_congr rfl (fun v hv => if_neg (Finset.mem_compl.mp hv))
  rw [h1, h2, Finset.prod_const]

/-- **Null utenfor `Z`:** er en node utenfor `Z` `none`, er `P⁺ = 0`. -/
lemma flag_fullJoint_zero [∀ w, Nonempty (α w)] (M : G.CausalModel α) (Z : Finset V)
    (z₀ : Assignment (α := α) Z)
    (u : Assignment (α := fun v => Option (α v)) (Finset.univ : Finset V))
    {v : V} (hv : v ∉ Z) (hnone : u ⟨v, Finset.mem_univ v⟩ = none) :
    (flagModel M Z z₀).fullJoint u = 0 := by
  rw [fullJoint_apply_prod]
  refine Finset.prod_eq_zero (Finset.mem_univ v) ?_
  rw [DoAudit.kfac_univ, hnone]
  simp only [flagModel, if_neg hv]
  exact map_some_none _

/-! ## Fase 4, runde 1: injektivitet og støtte -/

lemma obs_injective : Function.Injective (obs (V := V) (α := α)) := by
  intro u u' h
  funext v
  have := congrFun h v
  simpa [obs] using this

/-- Intervensjon indeksert av tilordninger utenfor `Z`: `none` på `Z`,
`some (a v)` utenfor. -/
def intC (Z : Finset V) (a : Assignment (α := α) Zᶜ) :
    Assignment (α := fun v => Option (α v)) (Finset.univ : Finset V) :=
  fun v => if h : v.1 ∈ Z then none else some (a ⟨v.1, Finset.mem_compl.mpr h⟩)

lemma intC_injective (Z : Finset V) : Function.Injective (intC (α := α) Z) := by
  intro a a' h
  funext ⟨v, hv⟩
  have hvZ : v ∉ Z := Finset.mem_compl.mp hv
  have := congrFun h ⟨v, Finset.mem_univ v⟩
  simpa [intC, hvZ] using this

lemma intC_eq_intv (Z : Finset V) (z₀ : Assignment (α := α) Z)
    (a : Assignment (α := α) Zᶜ) : intC Z a = intv Z (combineZ Z z₀ a) := by
  funext ⟨v, hv⟩
  by_cases hvZ : v ∈ Z
  · simp [intC, intv, hvZ]
  · simp [intC, intv, combineZ, hvZ]

/-- **Steg 1 i (M1).** Positiv masse og ingen `none` på `Z` gir en observasjon. -/
lemma exists_obs_of_ne_zero [∀ w, Nonempty (α w)] (M : G.CausalModel α) (Z : Finset V)
    (z₀ : Assignment (α := α) Z)
    (u : Assignment (α := fun v => Option (α v)) (Finset.univ : Finset V))
    (h : (flagModel M Z z₀).fullJoint u ≠ 0)
    (hZ : ∀ v ∈ Z, u ⟨v, Finset.mem_univ v⟩ ≠ none) :
    ∃ u₀ : Assignment (α := α) (Finset.univ : Finset V), obs u₀ = u := by
  have hsome : ∀ v : {v // v ∈ (Finset.univ : Finset V)}, ∃ a, u v = some a := by
    intro ⟨v, hv⟩
    by_cases hvZ : v ∈ Z
    · exact Option.ne_none_iff_exists'.mp (hZ v hvZ)
    · by_contra hno
      push_neg at hno
      exact h (flag_fullJoint_zero M Z z₀ u hvZ (Option.eq_none_iff_forall_ne_some.mpr hno))
  choose u₀ hu₀ using hsome
  exact ⟨u₀, funext fun v => (hu₀ v).symm⟩

/-- **Steg 1 i (M2).** Positiv masse og `none` på hele `Z` gir en intervensjon. -/
lemma exists_intC_of_ne_zero [∀ w, Nonempty (α w)] (M : G.CausalModel α) (Z : Finset V)
    (z₀ : Assignment (α := α) Z)
    (u : Assignment (α := fun v => Option (α v)) (Finset.univ : Finset V))
    (h : (flagModel M Z z₀).fullJoint u ≠ 0)
    (hZ : ∀ v ∈ Z, u ⟨v, Finset.mem_univ v⟩ = none) :
    ∃ a : Assignment (α := α) Zᶜ, intC Z a = u := by
  have hsome : ∀ v : {v // v ∈ (Zᶜ : Finset V)}, ∃ x, u ⟨v.1, Finset.mem_univ _⟩ = some x := by
    intro ⟨v, hv⟩
    have hvZ : v ∉ Z := Finset.mem_compl.mp hv
    by_contra hno
    push_neg at hno
    exact h (flag_fullJoint_zero M Z z₀ u hvZ (Option.eq_none_iff_forall_ne_some.mpr hno))
  choose a ha using hsome
  refine ⟨a, funext fun ⟨v, hv⟩ => ?_⟩
  by_cases hvZ : v ∈ Z
  · simp only [intC, dif_pos hvZ]
    exact (hZ v hvZ).symm
  · simp only [intC, dif_neg hvZ]
    exact (ha ⟨v, Finset.mem_compl.mpr hvZ⟩).symm

/-! ## Fase 4, runde 2: (M1) -/

/-- `obs` for tilordninger på en mengde `S`. -/
def obsS (S : Finset V) (s : Assignment (α := α) S) :
    Assignment (α := fun v => Option (α v)) S :=
  fun v => some (s v)

/-- **(M1).** For `S ⊇ Z`: `P⁺_S(obs s) = (½)^|Z| · P_S(s)`. -/
lemma flag_marginal_obs [∀ w, Nonempty (α w)] (M : G.CausalModel α) (Z : Finset V)
    (z₀ : Assignment (α := α) Z) (S : Finset V) (hZS : Z ⊆ S)
    (s : Assignment (α := α) S) :
    (flagModel M Z z₀).marginal S (obsS S s) = (2⁻¹ : ENNReal) ^ Z.card * M.marginal S s := by
  unfold CausalModel.marginal
  rw [PMF.map_apply, PMF.map_apply]
  refine Eq.trans (obs_injective.tsum_eq ?_).symm ?_
  · -- Steg 1: støtten ligger i bildet av `obs`.
    intro u hu
    have hu' : (if obsS S s = u.restrict (Finset.subset_univ S)
        then (flagModel M Z z₀).fullJoint u else 0) ≠ 0 := hu
    split_ifs at hu' with hs
    · refine exists_obs_of_ne_zero M Z z₀ u hu' (fun v hv hnone => ?_)
      have := congrFun hs ⟨v, hZS hv⟩
      simp [obsS, Assignment.restrict, hnone] at this
    · exact absurd rfl hu'
  · -- Steg 2 og 3: leddvis.
    beta_reduce
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr (fun u => ?_)
    have hiff : obsS S s = (obs u).restrict (Finset.subset_univ S) ↔
        s = u.restrict (Finset.subset_univ S) := by
      constructor
      · intro h
        funext v
        have := congrFun h v
        simpa [obsS, obs, Assignment.restrict] using this
      · intro h
        subst h
        rfl
    by_cases h : s = u.restrict (Finset.subset_univ S)
    · rw [if_pos (hiff.mpr h), if_pos h, flag_fullJoint_obs]
    · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h, mul_zero]

/-! ## Fase 4, runde 3: (M2) -/

/-- Intervensjonsmønsteret på en mengde `S`: `none` på `Z`, `some (s v)` ellers. -/
def intS (Z S : Finset V) (s : Assignment (α := α) S) :
    Assignment (α := fun v => Option (α v)) S :=
  fun v => if v.1 ∈ Z then none else some (s v)

lemma combineZ_injective (Z : Finset V) (z₀ : Assignment (α := α) Z) :
    Function.Injective (combineZ Z z₀) := by
  intro a a' h
  have := congrArg (fun u => u.restrict (Finset.subset_univ Zᶜ)) h
  simpa [combine_restrict_compl] using this

/-- **(M2).** For `S ⊇ Z`, `T ⊆ S`, `T ∩ Z = ∅` og `S ⊆ T ∪ Z`:
`P⁺_S(int s) = (½)^|Z| · (P_{z₀})_T(s|_T)`. -/
lemma flag_marginal_int [∀ w, Nonempty (α w)] (M : G.CausalModel α) (Z : Finset V)
    (z₀ : Assignment (α := α) Z) (S T : Finset V) (hZS : Z ⊆ S) (hTS : T ⊆ S)
    (hTZ : Disjoint T Z) (hST : S ⊆ T ∪ Z) (s : Assignment (α := α) S) :
    (flagModel M Z z₀).marginal S (intS Z S s) =
      (2⁻¹ : ENNReal) ^ Z.card * (doModel M Z z₀).marginal T (s.restrict hTS) := by
  unfold CausalModel.marginal
  rw [PMF.map_apply, PMF.map_apply]
  -- Høyre side omindeksert via `combineZ z₀`.
  have hR : (∑' u : Assignment (α := α) (Finset.univ : Finset V),
      if s.restrict hTS = u.restrict (Finset.subset_univ T)
      then (doModel M Z z₀).fullJoint u else 0) =
      ∑' a : Assignment (α := α) Zᶜ,
        if s.restrict hTS = (combineZ Z z₀ a).restrict (Finset.subset_univ T)
        then (doModel M Z z₀).fullJoint (combineZ Z z₀ a) else 0 := by
    refine ((combineZ_injective Z z₀).tsum_eq ?_).symm
    intro u hu
    have hu' : (if s.restrict hTS = u.restrict (Finset.subset_univ T)
        then (doModel M Z z₀).fullJoint u else 0) ≠ 0 := hu
    split_ifs at hu' with hs
    · have huZ : u.restrict (Finset.subset_univ Z) = z₀ := by
        by_contra hne
        apply hu'
        rw [doModel_fullJoint, if_neg hne, zero_mul]
      exact ⟨u.restrict (Finset.subset_univ Zᶜ), (eq_combineZ rfl huZ).symm⟩
    · exact absurd rfl hu'
  rw [hR]
  -- Venstre side omindeksert via `intC`.
  refine Eq.trans ((intC_injective Z).tsum_eq ?_).symm ?_
  · intro u hu
    have hu' : (if intS Z S s = u.restrict (Finset.subset_univ S)
        then (flagModel M Z z₀).fullJoint u else 0) ≠ 0 := hu
    split_ifs at hu' with hs
    · refine exists_intC_of_ne_zero M Z z₀ u hu' (fun v hv => ?_)
      have hnone : (intS Z S s) ⟨v, hZS hv⟩ = none := by simp [intS, hv]
      have := congrFun hs ⟨v, hZS hv⟩
      rw [hnone] at this
      exact this.symm
    · exact absurd rfl hu'
  · beta_reduce
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr (fun a => ?_)
    rw [intC_eq_intv Z z₀ a]
    have hiff : intS Z S s = (intv Z (combineZ Z z₀ a)).restrict (Finset.subset_univ S) ↔
        s.restrict hTS = (combineZ Z z₀ a).restrict (Finset.subset_univ T) := by
      constructor
      · intro h
        funext ⟨v, hv⟩
        have hvZ : v ∉ Z := Finset.disjoint_left.mp hTZ hv
        have := congrFun h ⟨v, hTS hv⟩
        simp [intS, intv, Assignment.restrict, hvZ] at this
        simpa [Assignment.restrict] using this
      · intro h
        funext ⟨v, hv⟩
        by_cases hvZ : v ∈ Z
        · simp [intS, intv, Assignment.restrict, hvZ]
        · have hvT : v ∈ T := by
            rcases Finset.mem_union.mp (hST hv) with h' | h'
            · exact h'
            · exact absurd h' hvZ
          have := congrFun h ⟨v, hvT⟩
          simp [intS, intv, Assignment.restrict, hvZ]
          simpa [Assignment.restrict] using this
    by_cases h : s.restrict hTS = (combineZ Z z₀ a).restrict (Finset.subset_univ T)
    · rw [if_pos (hiff.mpr h), if_pos h, flag_fullJoint_int, combine_restrict_compl]
    · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h, mul_zero]

/-! ## Fase 4, runde 4: (M3) -/

/-- Marginalen under `do(Z = z₀)` som sum over tilordninger utenfor `Z`. -/
lemma do_marginal_combine {α : V → Type*} (M : G.CausalModel α) (Z : Finset V)
    (z₀ : Assignment (α := α) Z) (T : Finset V) (t : Assignment (α := α) T) :
    (doModel M Z z₀).marginal T t =
      ∑' a : Assignment (α := α) Zᶜ,
        if t = (combineZ Z z₀ a).restrict (Finset.subset_univ T)
        then (doModel M Z z₀).fullJoint (combineZ Z z₀ a) else 0 := by
  unfold CausalModel.marginal
  rw [PMF.map_apply]
  refine ((combineZ_injective Z z₀).tsum_eq ?_).symm
  intro u hu
  have hu' : (if t = u.restrict (Finset.subset_univ T)
      then (doModel M Z z₀).fullJoint u else 0) ≠ 0 := hu
  split_ifs at hu' with hs
  · have huZ : u.restrict (Finset.subset_univ Z) = z₀ := by
      by_contra hne
      apply hu'
      rw [doModel_fullJoint, if_neg hne, zero_mul]
    exact ⟨u.restrict (Finset.subset_univ Zᶜ), (eq_combineZ rfl huZ).symm⟩
  · exact absurd rfl hu'

/-- Nedre skranke fra observasjonene: `(½)^|Z| · P_W(w) ≤ P⁺_W(obs w)`. -/
lemma flag_ge_obs [∀ w, Nonempty (α w)] (M : G.CausalModel α) (Z : Finset V)
    (z₀ : Assignment (α := α) Z) (W : Finset V) (w : Assignment (α := α) W) :
    (2⁻¹ : ENNReal) ^ Z.card * M.marginal W w ≤
      (flagModel M Z z₀).marginal W (obsS W w) := by
  unfold CausalModel.marginal
  rw [PMF.map_apply, PMF.map_apply, ← ENNReal.tsum_mul_left]
  refine le_trans (le_of_eq ?_) (ENNReal.tsum_comp_le_tsum_of_injective obs_injective _)
  refine tsum_congr (fun u => ?_)
  beta_reduce
  have hiff : obsS W w = (obs u).restrict (Finset.subset_univ W) ↔
      w = u.restrict (Finset.subset_univ W) := by
    constructor
    · intro h
      funext v
      have := congrFun h v
      simpa [obsS, obs, Assignment.restrict] using this
    · intro h
      subst h
      rfl
  by_cases h : w = u.restrict (Finset.subset_univ W)
  · rw [if_pos h, if_pos (hiff.mpr h), flag_fullJoint_obs]
  · rw [if_neg h, if_neg (fun h' => h (hiff.mp h')), mul_zero]

/-- Nedre skranke fra intervensjonene: `(½)^|Z| · (P_{z₀})_W(w) ≤ P⁺_W(obs w)`
for `W` disjunkt fra `Z`. -/
lemma flag_ge_int [∀ w, Nonempty (α w)] (M : G.CausalModel α) (Z : Finset V)
    (z₀ : Assignment (α := α) Z) (W : Finset V) (hWZ : Disjoint W Z)
    (w : Assignment (α := α) W) :
    (2⁻¹ : ENNReal) ^ Z.card * (doModel M Z z₀).marginal W w ≤
      (flagModel M Z z₀).marginal W (obsS W w) := by
  rw [do_marginal_combine, ← ENNReal.tsum_mul_left]
  unfold CausalModel.marginal
  rw [PMF.map_apply]
  refine le_trans (le_of_eq ?_) (ENNReal.tsum_comp_le_tsum_of_injective (intC_injective Z) _)
  refine tsum_congr (fun a => ?_)
  beta_reduce
  rw [intC_eq_intv Z z₀ a]
  have hiff : obsS W w = (intv Z (combineZ Z z₀ a)).restrict (Finset.subset_univ W) ↔
      w = (combineZ Z z₀ a).restrict (Finset.subset_univ W) := by
    constructor
    · intro h
      funext ⟨v, hv⟩
      have hvZ : v ∉ Z := Finset.disjoint_left.mp hWZ hv
      have := congrFun h ⟨v, hv⟩
      simp [obsS, intv, Assignment.restrict, hvZ] at this
      simpa [Assignment.restrict] using this
    · intro h
      funext ⟨v, hv⟩
      have hvZ : v ∉ Z := Finset.disjoint_left.mp hWZ hv
      have := congrFun h ⟨v, hv⟩
      simp [obsS, intv, Assignment.restrict, hvZ]
      simpa [Assignment.restrict] using this
  by_cases h : w = (combineZ Z z₀ a).restrict (Finset.subset_univ W)
  · rw [if_pos h, if_pos (hiff.mpr h), flag_fullJoint_int, combine_restrict_compl]
  · rw [if_neg h, if_neg (fun h' => h (hiff.mp h')), mul_zero]

/-- **(M3).** For `W` disjunkt fra `Z`: er `P⁺_W(obs w) = 0`, er både `P_W(w) = 0`
og `(P_{z₀})_W(w) = 0`. Dette er det som gjør forkortingen i trinn A fri for
positivitetsantakelser. -/
lemma flag_marginal_zero [∀ w, Nonempty (α w)] (M : G.CausalModel α) (Z : Finset V)
    (z₀ : Assignment (α := α) Z) (W : Finset V) (hWZ : Disjoint W Z)
    (w : Assignment (α := α) W) (h : (flagModel M Z z₀).marginal W (obsS W w) = 0) :
    M.marginal W w = 0 ∧ (doModel M Z z₀).marginal W w = 0 := by
  have hk : (2⁻¹ : ENNReal) ^ Z.card ≠ 0 :=
    pow_ne_zero _ (by simp)
  constructor
  · have := flag_ge_obs M Z z₀ W w
    rw [h] at this
    exact (mul_eq_zero.mp (le_zero_iff.mp this)).resolve_left hk
  · have := flag_ge_int M Z z₀ W hWZ w
    rw [h] at this
    exact (mul_eq_zero.mp (le_zero_iff.mp this)).resolve_left hk

/-! ## Fase 5, runde 1: marginalisering over `Z` og forkorting -/

/-- `a` på `A` med `Z`-delen byttet ut med `z`. -/
def setZ (Z A : Finset V) (a : Assignment (α := α) A) (z : Assignment (α := α) Z) :
    Assignment (α := α) A :=
  fun v => if h : v.1 ∈ Z then z ⟨v.1, h⟩ else a v

lemma setZ_restrict_Z {Z A : Finset V} (hZA : Z ⊆ A) (a : Assignment (α := α) A)
    (z : Assignment (α := α) Z) : (setZ Z A a z).restrict hZA = z := by
  funext ⟨v, hv⟩
  simp [setZ, Assignment.restrict, hv]

lemma setZ_restrict_disj {Z A B : Finset V} (hBA : B ⊆ A) (hBZ : Disjoint B Z)
    (a : Assignment (α := α) A) (z : Assignment (α := α) Z) :
    (setZ Z A a z).restrict hBA = a.restrict hBA := by
  funext ⟨v, hv⟩
  have hvZ : v ∉ Z := Finset.disjoint_left.mp hBZ hv
  simp [setZ, Assignment.restrict, hvZ]

lemma setZ_injective {Z A : Finset V} (hZA : Z ⊆ A) (a : Assignment (α := α) A) :
    Function.Injective (setZ Z A a) := by
  intro z z' h
  have := congrArg (fun b => b.restrict hZA) h
  simpa [setZ_restrict_Z hZA] using this

/-- **Marginalisering over `Z`.** For `A ⊇ Z`, `B ⊆ A`, `B ∩ Z = ∅` og
`A ⊆ B ∪ Z`: summen over `Z`-delen av `P_A` er `P_B`. -/
lemma marginal_sum_Z {α : V → Type*} (M : G.CausalModel α) {Z A B : Finset V}
    (hZA : Z ⊆ A) (hBA : B ⊆ A) (hBZ : Disjoint B Z) (hAB : A ⊆ B ∪ Z)
    (a : Assignment (α := α) A) :
    ∑' z : Assignment (α := α) Z, M.marginal A (setZ Z A a z) =
      M.marginal B (a.restrict hBA) := by
  rw [← marginal_restrict M hBA, PMF.map_apply]
  refine Eq.trans ?_ ((setZ_injective hZA a).tsum_eq ?_)
  · refine tsum_congr (fun z => ?_)
    beta_reduce
    rw [if_pos (setZ_restrict_disj hBA hBZ a z).symm]
  · intro a' ha'
    have ha'' : (if a.restrict hBA = a'.restrict hBA then M.marginal A a' else 0) ≠ 0 := ha'
    split_ifs at ha'' with hs
    · refine ⟨a'.restrict hZA, ?_⟩
      funext ⟨v, hv⟩
      by_cases hvZ : v ∈ Z
      · simp [setZ, Assignment.restrict, hvZ]
      · have hvB : v ∈ B := (Finset.mem_union.mp (hAB hv)).resolve_right hvZ
        have := congrFun hs ⟨v, hvB⟩
        simp [setZ, Assignment.restrict, hvZ]
        simpa [Assignment.restrict] using this
    · exact absurd rfl ha''

/-- **Forkortingen i trinn A.** Fra `A·d = c·B` og `C·d = c·D`, med `d ≠ ∞`,
følger `A·D = C·B`, forutsatt at `d = 0` gir `B = 0` og `D = 0` (det er (M3)). -/
lemma cancel_flag {A B C D c d : ENNReal} (hdt : d ≠ ⊤)
    (h1 : A * d = c * B) (h2 : C * d = c * D) (h0 : d = 0 → B = 0 ∧ D = 0) :
    A * D = C * B := by
  by_cases hd : d = 0
  · obtain ⟨hB, hD⟩ := h0 hd
    rw [hB, hD, mul_zero, mul_zero]
  · apply (ENNReal.mul_right_inj hd hdt).mp
    calc d * (A * D) = (A * d) * D := by ring
      _ = (c * B) * D := by rw [h1]
      _ = (c * D) * B := by ring
      _ = (C * d) * B := by rw [h2]
      _ = d * (C * B) := by ring

/-! ## Fase 5, runde 2: trinn A uten positivitet -/

lemma intS_restrict_disj {Z S T : Finset V} (h : T ⊆ S) (hTZ : Disjoint T Z)
    (s : Assignment (α := α) S) : (intS Z S s).restrict h = obsS T (s.restrict h) := by
  funext ⟨v, hv⟩
  have hvZ : v ∉ Z := Finset.disjoint_left.mp hTZ hv
  simp [intS, obsS, Assignment.restrict, hvZ]

lemma intS_restrict {Z S T : Finset V} (h : T ⊆ S) (s : Assignment (α := α) S) :
    (intS Z S s).restrict h = intS Z T (s.restrict h) := rfl

lemma obsS_restrict {S T : Finset V} (h : T ⊆ S) (s : Assignment (α := α) S) :
    (obsS S s).restrict h = obsS T (s.restrict h) := rfl

lemma setZ_restrict {Z A A' : Finset V} (h : A' ⊆ A) (a : Assignment (α := α) A)
    (z : Assignment (α := α) Z) : (setZ Z A a z).restrict h = setZ Z A' (a.restrict h) z := rfl

/-- Stryk en felles faktor `k ≠ 0, ∞`. -/
lemma cancel_half {k A d c B : ENNReal} (hk0 : k ≠ 0) (hkt : k ≠ ⊤)
    (h : (k * A) * d = c * (k * B)) : A * d = c * B := by
  apply (ENNReal.mul_right_inj hk0 hkt).mp
  calc k * (A * d) = (k * A) * d := by ring
    _ = c * (k * B) := h
    _ = k * (c * B) := by ring

/-- **Regel 3 uten kutt og uten positivitet.** Er `Y ⊥ Z | W` i `G`, så er
`P_{z₀}(y, w) · P(w) = P(y, w) · P_{z₀}(w)`, der `z₀` er `Z`-delen av `t`. -/
theorem rule3_nocut {α : V → Type*} (M : G.CausalModel α) (Y Z W : Finset V)
    (hYZ : Disjoint Y Z) (hWZ : Disjoint W Z) (hYW : Disjoint Y W)
    (h : SetSound.DSeparatedSet G W Y Z)
    (t : Assignment (α := α) (Y ∪ Z ∪ W)) :
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
  haveI : ∀ w, Nonempty (α w) := DSepSound.nonempty_of_model M
  have sZ : Z ⊆ Y ∪ Z ∪ W := by intro v hv; simp only [Finset.mem_union]; tauto
  have sW : W ⊆ Y ∪ Z ∪ W := by intro v hv; simp only [Finset.mem_union]; tauto
  have sYW : Y ∪ W ⊆ Y ∪ Z ∪ W := by
    intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto
  have sZW : Z ∪ W ⊆ Y ∪ Z ∪ W := by
    intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto
  have hYWZ : Disjoint (Y ∪ W) Z := Finset.disjoint_union_left.mpr ⟨hYZ, hWZ⟩
  have hSsub : Y ∪ Z ∪ W ⊆ (Y ∪ W) ∪ Z := by
    intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto
  have hZWsub : Z ∪ W ⊆ W ∪ Z := by
    intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto
  have hk0 : (2⁻¹ : ENNReal) ^ Z.card ≠ 0 := pow_ne_zero _ (by simp)
  have hkt : (2⁻¹ : ENNReal) ^ Z.card ≠ ⊤ := ENNReal.pow_ne_top (by simp)
  -- 1. Betinget uavhengighet i flaggmodellen.
  have hci := SetSound.dsep_sound_set (flagModel M Z (t.restrict sZ)) Y Z W hYW hWZ.symm h
  -- 2. (a): intervensjonsmønsteret.
  have hA := hci (intS Z (Y ∪ Z ∪ W) t)
  rw [intS_restrict_disj _ hWZ, intS_restrict_disj _ hYWZ, intS_restrict,
    flag_marginal_int M Z (t.restrict sZ) _ (Y ∪ W) sZ sYW hYWZ hSsub t,
    flag_marginal_int M Z (t.restrict sZ) (Z ∪ W) W Finset.subset_union_left
      Finset.subset_union_right hWZ hZWsub] at hA
  -- 3. (b): observasjonsmønsteret, summert over `z`.
  have hSum : ∑' z : Assignment (α := α) Z,
      ((2⁻¹ : ENNReal) ^ Z.card * M.marginal (Y ∪ Z ∪ W) (setZ Z (Y ∪ Z ∪ W) t z)) *
        (flagModel M Z (t.restrict sZ)).marginal W (obsS W (t.restrict sW)) =
      ∑' z : Assignment (α := α) Z,
        (flagModel M Z (t.restrict sZ)).marginal (Y ∪ W) (obsS (Y ∪ W) (t.restrict sYW)) *
          ((2⁻¹ : ENNReal) ^ Z.card *
            M.marginal (Z ∪ W) (setZ Z (Z ∪ W) (t.restrict sZW) z)) := by
    refine tsum_congr (fun z => ?_)
    have hB := hci (obsS (Y ∪ Z ∪ W) (setZ Z (Y ∪ Z ∪ W) t z))
    simp only [obsS_restrict] at hB
    rw [setZ_restrict_disj _ hWZ, setZ_restrict_disj _ hYWZ, setZ_restrict,
      flag_marginal_obs M Z (t.restrict sZ) _ sZ,
      flag_marginal_obs M Z (t.restrict sZ) (Z ∪ W) Finset.subset_union_left] at hB
    exact hB
  simp only [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left] at hSum
  rw [marginal_sum_Z M sZ sYW hYWZ hSsub t,
    marginal_sum_Z M Finset.subset_union_left Finset.subset_union_right hWZ hZWsub
      (t.restrict sZW)] at hSum
  -- 4. Stryk (½)^|Z|, og 5. forkort med (M3).
  exact cancel_flag (PMF.apply_ne_top _ _) (cancel_half hk0 hkt hA) (cancel_half hk0 hkt hSum)
    (fun hd => by
      obtain ⟨h1, h2⟩ := flag_marginal_zero M Z (t.restrict sZ) W hWZ (t.restrict sW) hd
      exact ⟨h2, h1⟩)

/-! ## Fase 5, runde 3: regel 3 uten positivitet -/

/-- **Regel 3 uten positivitet (uten `X`).** Er `Y` og `Z` d-separert av `W` i
`G_{\overline{Z(W)}}`, så er `P_z(y | w) = P(y | w)`, i produktform. -/
theorem rule3_gen {α : V → Type*} (M : G.CausalModel α) (Y Z W : Finset V)
    (hYZ : Disjoint Y Z) (hWZ : Disjoint W Z) (hYW : Disjoint Y W)
    (h : SetSound.DSeparatedSet (cutIn G (Z2 G Z W)) W Y Z)
    (t : Assignment (α := α) (Y ∪ Z ∪ W)) :
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
  -- Trinn A: do(Z₁) fjernes i M₂ = do(Z₂), uten positivitet.
  have hA := rule3_nocut (doModel M (Z2 G Z W) ((t.restrict sZ).restrict hZ2Z))
    Y (Z1 G Z W) W hYZ1 hWZ1 hYW h1 (t.restrict sT1)
  have hz : (t.restrict sT1).restrict (show Z1 G Z W ⊆ Y ∪ Z1 G Z W ∪ W by
      intro v hv; simp only [Finset.mem_union]; tauto) = (t.restrict sZ).restrict hZ1Z := rfl
  rw [hz] at hA
  -- Trinn B og komposisjon, som i `rule3_pos`.
  have hAcl := DSepSound.A_closed (G := G) (Y ∪ W)
  have hAZ := disjoint_anc_Z2 h
  have hYW_A : Y ∪ W ⊆ ancestors G (Y ∪ W) := subset_ancestors _
  have hW_A : W ⊆ ancestors G (Y ∪ W) :=
    fun v hv => subset_ancestors _ (Finset.mem_union_right _ hv)
  rw [doModel_comp_marginal' M _ _ Z hdisj (Z1_union_Z2 Z W) (t.restrict sZ) (Y ∪ W) _,
    doModel_comp_marginal' M _ _ Z hdisj (Z1_union_Z2 Z W) (t.restrict sZ) W _,
    doModel_marginal_of_sub M (Z2 G Z W) _ _ hAcl hAZ (Y ∪ W) hYW_A _,
    doModel_marginal_of_sub M (Z2 G Z W) _ _ hAcl hAZ W hW_A _] at hA
  exact hA

/-- **Regel 3 (Pearl), uten positivitet.** Er `Y` og `Z` d-separert av `X ∪ W` i
`G_{X̄, \overline{Z(W)}}`, der `Z(W)` er nodene i `Z` som ikke er forfedre til `W`
i `G_{X̄}`, så er `P_{x,z}(y | x, w) = P_x(y | x, w)`, i produktform. -/
theorem rule3_general {α : V → Type*} (M : G.CausalModel α) (X Y Z W : Finset V)
    (x : Assignment (α := α) X)
    (hYZ : Disjoint Y Z) (hXWZ : Disjoint (X ∪ W) Z) (hYXW : Disjoint Y (X ∪ W))
    (h : SetSound.DSeparatedSet (cutIn (cutIn G X) (Z2 (cutIn G X) Z W)) (X ∪ W) Y Z)
    (t : Assignment (α := α) (Y ∪ Z ∪ (X ∪ W))) :
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
  exact rule3_gen (doModel M X x) Y Z (X ∪ W) hYZ hXWZ hYXW h t

end Rule3Flag

#print axioms Rule3Flag.map_some_apply
#print axioms Rule3Flag.map_some_none
#print axioms Rule3Flag.kfac_flag_obs
#print axioms Rule3Flag.kfac_flag_int
#print axioms Rule3Flag.flag_fullJoint_obs
#print axioms Rule3Flag.flag_fullJoint_int
#print axioms Rule3Flag.flag_fullJoint_zero
#print axioms Rule3Flag.intC_eq_intv
#print axioms Rule3Flag.exists_obs_of_ne_zero
#print axioms Rule3Flag.exists_intC_of_ne_zero
#print axioms Rule3Flag.flag_marginal_obs
#print axioms Rule3Flag.flag_marginal_int
#print axioms Rule3Flag.flag_marginal_zero
#print axioms Rule3Flag.marginal_sum_Z
#print axioms Rule3Flag.cancel_flag
#print axioms Rule3Flag.rule3_nocut
#print axioms Rule3Flag.rule3_gen
#print axioms Rule3Flag.rule3_general
