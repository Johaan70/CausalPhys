/-
  CausalPhys.BlockExistence — løsningen bygges blokk for blokk.

    1. Monteringsteoremet (`exists_of_blocks`): la modellen ha blokkstruktur
       (foreldre i samme eller lavere blokk) og endelig mange nivåer. Kan hver
       blokk løses når alt under den er løst, finnes en global løsning.
       Blokkløseren er en vilkårlig hypotese, så teoremet tar imot eksplisitte
       formler, mellomverdisetningen, Banach eller noe annet.
       Sammen med blokk-entydighet gir det nøyaktig én løsning
       (`exists_unique_of_blocks`).

    2. Banach per blokk (`block_solvable_of_contractive`): er blokken en vektet
       kontraksjon INNE I BLOKKEN (`ContractiveAt` fra BlockSolvability.lean),
       kan den løses for alle verdier under den. Med 1 gir det
       (`exists_unique_of_blockContractive`): en modell der hvert nivå er
       kontraktivt, har nøyaktig én løsning, uten noen global kontraksjon.

    3. Markedet: med den eksplisitte likevektsformelen som blokkløser gir 1
       eksistens for ALLE b, e > 0; med 2 gir det eksistens når b < e.

  Ikke dekket: rene monotone blokker. Monotonitet gir høyst én løsning, men
  eksistens krever i tillegg kontinuitet og koersivitet (Minty–Browder), og
  det er ikke formalisert.
-/
import CausalPhys.Existence

set_option linter.unusedSectionVars false

namespace CausalPhys
namespace SCM

/-! ## 1. Monteringsteoremet -/

section Assembly

universe u
variable {V : Type} {α : Type u}

/-- `s` stemmer med `u` på alle eksogene, og løser alle ligninger under nivå n. -/
def SolvesBelow (M : SCM V α) (rank : V → ℕ) (u s : V → α) (n : ℕ) : Prop :=
  (∀ v, M.mech v = none → s v = u v) ∧
  (∀ v m, M.mech v = some m → rank v < n → s v = m.f s)

/-- Blokk n kan løses: gitt en tilstand som løser alt under, finnes en som bare
    endrer blokkens endogene variabler og løser blokkens ligninger. -/
def BlockSolvable (M : SCM V α) (rank : V → ℕ) (u : V → α) (n : ℕ) : Prop :=
  ∀ s, SolvesBelow M rank u s n →
    ∃ t, (∀ v, (rank v ≠ n ∨ M.mech v = none) → t v = s v) ∧
      (∀ v m, M.mech v = some m → rank v = n → t v = m.f t)

theorem solvesBelow_succ {M : SCM V α} {rank : V → ℕ} {u : V → α} {n : ℕ}
    (hp : ∀ v m, M.mech v = some m → ∀ p, p ∈ m.parents → rank p ≤ rank v)
    (hb : BlockSolvable M rank u n) {s : V → α} (hs : SolvesBelow M rank u s n) :
    ∃ t, SolvesBelow M rank u t (n + 1) := by
  obtain ⟨t, hkeep, hblk⟩ := hb s hs
  refine ⟨t, fun v hv => (hkeep v (Or.inr hv)).trans (hs.1 v hv), fun v m hm hlt => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt' | heq
  · -- lavere nivå: t = s på v og på foreldrene
    rw [hkeep v (Or.inl (Nat.ne_of_lt hlt')), hs.2 v m hm hlt']
    apply m.local_
    intro p hpp
    exact (hkeep p (Or.inl (Nat.ne_of_lt (lt_of_le_of_lt (hp v m hm p hpp) hlt')))).symm
  · exact hblk v m hm heq

/-- Monteringsteoremet. -/
theorem exists_of_blocks {M : SCM V α} {rank : V → ℕ} (u : V → α)
    (hp : ∀ v m, M.mech v = some m → ∀ p, p ∈ m.parents → rank p ≤ rank v)
    (hN : ∃ N, ∀ v, rank v ≤ N) (hb : ∀ n, BlockSolvable M rank u n) :
    ∃ s, M.Solves u s := by
  obtain ⟨N, hN⟩ := hN
  have key : ∀ n, ∃ s, SolvesBelow M rank u s n := by
    intro n
    induction n with
    | zero => exact ⟨u, fun _ _ => rfl, fun _ _ _ h => absurd h (Nat.not_lt_zero _)⟩
    | succ k ih =>
      obtain ⟨s, hs⟩ := ih
      exact solvesBelow_succ hp (hb k) hs
  obtain ⟨s, hs⟩ := key (N + 1)
  refine ⟨s, fun v => ?_⟩
  cases hm : M.mech v with
  | none => exact hs.1 v hm
  | some m => exact hs.2 v m hm (Nat.lt_succ_of_le (hN v))

/-- Med blokk-entydighet: nøyaktig én løsning. -/
theorem exists_unique_of_blocks {M : SCM V α} {rank : V → ℕ} (u : V → α)
    (hbr : M.BlockRecursive rank) (hN : ∃ N, ∀ v, rank v ≤ N)
    (hb : ∀ n, BlockSolvable M rank u n) : ∃! s, M.Solves u s := by
  obtain ⟨s, hs⟩ := exists_of_blocks u hbr.parents_le hN hb
  exact ⟨s, hs, fun t ht => hbr.unique ht hs⟩

end Assembly

/-! ## 2. Banach per blokk -/

section BlockBanach

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Endogen variabel i blokk n. -/
def InBlock (M : SCM V ℝ) (rank : V → ℕ) (n : ℕ) (v : V) : Prop :=
  rank v = n ∧ (M.mech v).isSome

instance (M : SCM V ℝ) (rank : V → ℕ) (n : ℕ) (v : V) : Decidable (InBlock M rank n v) := by
  unfold InBlock; infer_instance

/-- Behold blokkens koordinater fra `s`, resten fra `s0`. -/
noncomputable def fixB (M : SCM V ℝ) (rank : V → ℕ) (n : ℕ) (s0 s : V → ℝ) : V → ℝ :=
  fun w => if InBlock M rank n w then s w else s0 w

/-- Blokkoperatoren: blokkens endogene variabler får sin mekanisme, resten `s0`. -/
noncomputable def Tb (M : SCM V ℝ) (rank : V → ℕ) (n : ℕ) (s0 s : V → ℝ) : V → ℝ :=
  fun v => match M.mech v with
    | some m => if rank v = n then m.f (fixB M rank n s0 s) else s0 v
    | none => s0 v

noncomputable def Gb (M : SCM V ℝ) (rank : V → ℕ) (n : ℕ) (s0 μ : V → ℝ) (x : V → ℝ) : V → ℝ :=
  fun v => Tb M rank n s0 (fun w => μ w * x w) v / μ v

theorem Gb_lipschitz {M : SCM V ℝ} {rank : V → ℕ} {n : ℕ} {s0 μ : V → ℝ} {K : ℝ}
    (hμ : ∀ v, 0 < μ v) (hK0 : 0 ≤ K) (hc : ContractiveAt M rank n μ K) (x y : V → ℝ) :
    dist (Gb M rank n s0 μ x) (Gb M rank n s0 μ y) ≤ K * dist x y := by
  have hd := dist_nonneg (x := x) (y := y)
  rw [dist_pi_le_iff (mul_nonneg hK0 hd)]
  intro v
  have hμv := hμ v
  simp only [Gb, Real.dist_eq]
  rw [← sub_div, abs_div, abs_of_pos hμv, div_le_iff₀ hμv]
  unfold Tb
  cases hm : M.mech v with
  | none => simp only [sub_self, abs_zero]; positivity
  | some m =>
    simp only
    split_ifs with hv
    · have := hc (fixB M rank n s0 fun w => μ w * x w) (fixB M rank n s0 fun w => μ w * y w)
        (dist x y)
        (fun w hw => by
          have : ¬ InBlock M rank n w := fun h => absurd h.1 (Nat.ne_of_lt hw)
          simp only [fixB, this, ite_false])
        (fun w hw => by
          unfold fixB
          split_ifs with hin
          · rw [← mul_sub, abs_mul, abs_of_pos (hμ w)]
            exact mul_le_mul_of_nonneg_left
              (by simpa [Real.dist_eq] using dist_le_pi_dist x y w) (hμ w).le
          · simp only [sub_self, abs_zero]; exact mul_nonneg (hμ w).le hd)
        v m hv hm
      linarith
    · simp only [sub_self, abs_zero]; positivity

/-- Banach per blokk: en kontraktiv blokk kan løses for alle verdier under den. -/
theorem block_solvable_of_contractive {M : SCM V ℝ} {rank : V → ℕ} {n : ℕ} (u : V → ℝ)
    (μ : V → ℝ) (K : ℝ) (hμ : ∀ v, 0 < μ v) (hK0 : 0 ≤ K) (hK1 : K < 1)
    (hc : ContractiveAt M rank n μ K) : BlockSolvable M rank u n := by
  intro s0 _
  set K' : NNReal := ⟨K, hK0⟩
  have hcon : ContractingWith K' (Gb M rank n s0 μ) :=
    ⟨by exact_mod_cast hK1, LipschitzWith.of_dist_le_mul fun x y => Gb_lipschitz hμ hK0 hc x y⟩
  set x := ContractingWith.fixedPoint (Gb M rank n s0 μ) hcon
  have hx : Gb M rank n s0 μ x = x := hcon.fixedPoint_isFixedPt
  set t : V → ℝ := fun w => μ w * x w
  have ht : Tb M rank n s0 t = t := by
    funext v
    have := congrFun hx v
    simp only [Gb] at this
    rw [div_eq_iff (hμ v).ne'] at this
    show Tb M rank n s0 t v = μ v * x v
    rw [this, mul_comm]
  -- utenfor blokken er t = s0
  have hout : ∀ v, ¬ InBlock M rank n v → t v = s0 v := by
    intro v hv
    have := congrFun ht v
    unfold Tb at this
    cases hm : M.mech v with
    | none => simp only [hm] at this; exact this.symm
    | some m =>
      simp only [hm] at this
      have hr : rank v ≠ n := fun h => hv ⟨h, by simp [hm]⟩
      rw [ite_eq_right hr] at this
      exact this.symm
  have hfix : fixB M rank n s0 t = t := by
    funext w
    unfold fixB
    split_ifs with hw
    · rfl
    · exact (hout w hw).symm
  refine ⟨t, fun v hv => hout v ?_, fun v m hm hv => ?_⟩
  · rintro ⟨h1, h2⟩
    rcases hv with h | h
    · exact h h1
    · simp [h] at h2
  · have := congrFun ht v
    unfold Tb at this
    simp only [hm, ite_eq_left hv, hfix] at this
    exact this.symm

/-- Hvert nivå kontraktivt ⇒ nøyaktig én løsning, uten global kontraksjon. -/
theorem exists_unique_of_blockContractive {M : SCM V ℝ} {rank : V → ℕ}
    (hp : ∀ v m, M.mech v = some m → ∀ p, p ∈ m.parents → rank p ≤ rank v)
    (hc : ∀ n, ∃ μ : V → ℝ, ∃ K : ℝ, (∀ v, 0 < μ v) ∧ 0 ≤ K ∧ K < 1 ∧ ContractiveAt M rank n μ K)
    (u : V → ℝ) : ∃! s, M.Solves u s := by
  have hbr := BlockRecursive.of_contractive hp hc
  have hN : ∃ N, ∀ v, rank v ≤ N :=
    ⟨Finset.univ.sup rank, fun v => Finset.le_sup (Finset.mem_univ v)⟩
  refine exists_unique_of_blocks u hbr hN fun n => ?_
  obtain ⟨μ, K, hμ, hK0, hK1, hcn⟩ := hc n
  exact block_solvable_of_contractive u μ K hμ hK0 hK1 hcn

end BlockBanach
end SCM

/-! ## 3. Markedet -/

namespace Market

variable (m : Market)

/-- Blokkløser fra den eksplisitte formelen: virker for alle b, e > 0. -/
theorem blockSolvable (u : MV → ℝ) (n : ℕ) : SCM.BlockSolvable m.scm Market.rank u n := by
  intro s hs
  by_cases hn : n = 1
  · subst hn
    let x : Exo := ⟨s .t, s .y, s .w⟩
    let t : MV → ℝ := fun | .P => m.Pstar x | .Q => m.Qstar x | v => s v
    refine ⟨t, fun v hv => ?_, fun v mm hm hv => ?_⟩
    · cases v <;> simp_all [Market.rank, scm, t]
    · have hS := m.Qstar_supply x
      have he := m.he.ne'
      cases v <;> simp [scm] at hm <;> subst hm
      · show m.Pstar x = (m.Qstar x - m.d - m.f * s .w) / m.e + s .t
        rw [hS]; field_simp; ring
      · show m.Qstar x = m.a - m.b * m.Pstar x + m.c * s .y
        rfl
  · refine ⟨s, fun _ _ => rfl, fun v mm hm hv => ?_⟩
    cases v <;> simp [scm] at hm <;> simp [Market.rank] at hv <;> exact absurd hv.symm hn

/-- Eksistens og entydighet for alle b, e > 0, fra monteringsteoremet. -/
theorem exists_unique_of_assembly (u : MV → ℝ) : ∃! s, m.scm.Solves u s :=
  SCM.exists_unique_of_blocks u m.blockRecursive ⟨1, fun v => by cases v <;> simp [Market.rank]⟩
    (m.blockSolvable u)

/-- Det samme fra Banach per blokk, når b < e. -/
theorem exists_unique_of_blockBanach (hbe : m.b < m.e) (u : MV → ℝ) : ∃! s, m.scm.Solves u s :=
  SCM.exists_unique_of_blockContractive m.parents_le
    (fun n => ⟨_, m.Kc, fun v => by
        have := m.hb; have := m.he
        have hK : 0 < m.Kc := by unfold Kc; positivity
        cases v <;> simp only [] <;> positivity,
      by have := m.hb; have := m.he; unfold Kc; positivity,
      (m.Kc_lt_one_iff).2 hbe, m.contractive n⟩) u

end Market
end CausalPhys
