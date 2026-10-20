/-
  CausalPhys.BlockSolvability — generelle kriterier for at en syklisk blokk er
  entydig løsbar.

  `BlockRecursive` (Blocks.lean) antar entydighet blokk for blokk. Her bevises to
  generelle tilstrekkelige betingelser, så antakelsen kan erstattes av noe man
  sjekker på mekanismene:

    1. Vektet kontraksjon (Banach-typen): blokkens mekanismer krymper avstander
       med en faktor K < 1 i en vektet maksnorm  ⇒  høyst én løsning.
    2. Vektet streng monotonitet av residualen r_v(s) = s v − f_v(s), eventuelt
       bare på et domene D  ⇒  høyst én løsning i D.

  Anvendelser:
    • Markedet tilfredsstiller monotonitet for ALLE b, e > 0 (vekter e·b og 1),
      men kontraksjon i denne lesningen bare når b < e. Kontraksjon avhenger av
      lesningen, monotonitet gjør det ikke.
    • Kjemisk likevekt A + B ⇌ C som en selvløkke ξ := K(a₀−ξ)(b₀−ξ):
      entydig på det fysiske domenet (monotonitet), men to løsninger globalt.
      Det fysiske domenet er det som gjør blokken entydig løsbar.
-/
import CausalPhys.Blocks
import CausalPhys.Physics
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Archimedean.Basic

set_option linter.unusedSectionVars false

open Finset

namespace CausalPhys
namespace SCM

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## 1. Kontraksjon -/

/-- Blokken på nivå `n` er en vektet kontraksjon med faktor `K` og vekter `μ`:
    er alle blokkforskjeller høyst μ_w·δ, er mekanismeforskjellene høyst K·μ_v·δ. -/
def ContractiveAt (M : SCM V ℝ) (rank : V → ℕ) (n : ℕ) (μ : V → ℝ) (K : ℝ) : Prop :=
  ∀ s t : V → ℝ, ∀ δ : ℝ,
    (∀ v, rank v < n → s v = t v) →
    (∀ w, rank w = n → |s w - t w| ≤ μ w * δ) →
    ∀ v m, rank v = n → M.mech v = some m → |m.f s - m.f t| ≤ K * (μ v * δ)

/-- Hjelpelemma: er x ≤ μ·Kᵏ·c for alle k, med 0 ≤ K < 1, er x ≤ 0. -/
theorem le_zero_of_le_geom {x μ K c : ℝ} (hμ : 0 < μ) (_hK0 : 0 ≤ K) (hK1 : K < 1)
    (hc : 0 ≤ c) (h : ∀ k : ℕ, x ≤ μ * (K ^ k * c)) : x ≤ 0 := by
  by_contra hx
  replace hx := lt_of_not_ge hx
  rcases hc.eq_or_lt with hc0 | hcpos
  · have := h 0
    rw [← hc0] at this
    simp at this
    linarith
  · obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hx (mul_pos hμ hcpos)) hK1
    have h1 := h k
    have h2 : K ^ k * (μ * c) < x := by
      rwa [lt_div_iff₀ (mul_pos hμ hcpos)] at hk
    nlinarith [h1, h2]

/-- Kontraksjon ⇒ blokken er entydig bestemt av det som ligger under den. -/
theorem block_unique_of_contractive (M : SCM V ℝ) (rank : V → ℕ) (n : ℕ) (μ : V → ℝ) (K : ℝ)
    (hμ : ∀ v, 0 < μ v) (hK0 : 0 ≤ K) (hK1 : K < 1) (hc : ContractiveAt M rank n μ K) :
    ∀ u s t, M.Solves u s → M.Solves u t →
      (∀ v, rank v < n → s v = t v) → ∀ v, rank v = n → s v = t v := by
  intro u s t hs ht hlow
  set c := ∑ w, |s w - t w| / μ w with hcdef
  have hc0 : 0 ≤ c := sum_nonneg fun w _ => div_nonneg (abs_nonneg _) (hμ w).le
  have key : ∀ k : ℕ, ∀ w, rank w = n → |s w - t w| ≤ μ w * (K ^ k * c) := by
    intro k
    induction k with
    | zero =>
      intro w _
      have h1 : |s w - t w| / μ w ≤ c :=
        single_le_sum (f := fun w => |s w - t w| / μ w)
          (fun w _ => div_nonneg (abs_nonneg _) (hμ w).le) (mem_univ w)
      rw [div_le_iff₀ (hμ w)] at h1
      rw [pow_zero, one_mul, mul_comm]
      exact h1
    | succ k ih =>
      intro w hw
      have hsw := hs w
      have htw := ht w
      cases hm : M.mech w with
      | none =>
        rw [hm] at hsw htw
        rw [hsw, htw, sub_self, abs_zero]
        have := hμ w
        positivity
      | some m =>
        rw [hm] at hsw htw
        rw [hsw, htw]
        have := hc s t (K ^ k * c) hlow ih w m hw hm
        calc |m.f s - m.f t| ≤ K * (μ w * (K ^ k * c)) := this
          _ = μ w * (K ^ (k + 1) * c) := by ring
  intro v hv
  have h := le_zero_of_le_geom (hμ v) hK0 hK1 hc0 (fun k => key k v hv)
  have := abs_nonneg (s v - t v)
  have h0 : |s v - t v| = 0 := le_antisymm h this
  exact sub_eq_zero.1 (abs_eq_zero.1 h0)

/-- En modell der hvert nivå er en kontraksjon, er blokkrekursiv. -/
theorem BlockRecursive.of_contractive {M : SCM V ℝ} {rank : V → ℕ}
    (hp : ∀ v m, M.mech v = some m → ∀ p, p ∈ m.parents → rank p ≤ rank v)
    (hc : ∀ n, ∃ μ : V → ℝ, ∃ K : ℝ, (∀ v, 0 < μ v) ∧ 0 ≤ K ∧ K < 1 ∧ ContractiveAt M rank n μ K) :
    M.BlockRecursive rank where
  parents_le := hp
  block_unique u s t hs ht n hlow := by
    obtain ⟨μ, K, hμ, hK0, hK1, hcn⟩ := hc n
    exact block_unique_of_contractive M rank n μ K hμ hK0 hK1 hcn u s t hs ht hlow

/-! ## 2. Monotonitet -/

/-- Residualen r_v(s) = s v − f_v(s); null for eksogene variabler. -/
def resid (M : SCM V ℝ) (s : V → ℝ) (v : V) : ℝ :=
  match M.mech v with
  | none => 0
  | some m => s v - m.f s

/-- Vektet streng monotonitet av residualen på blokk `n`, innenfor domenet `D`. -/
def MonotoneAt (M : SCM V ℝ) (rank : V → ℕ) (n : ℕ) (lam : V → ℝ) (D : (V → ℝ) → Prop) : Prop :=
  ∀ s t : V → ℝ, D s → D t →
    (∀ v, rank v < n → s v = t v) →
    (∀ v, rank v = n → M.mech v = none → s v = t v) →
    (∃ v, rank v = n ∧ s v ≠ t v) →
    0 < ∑ v ∈ univ.filter (fun v => rank v = n), lam v * (s v - t v) * (resid M s v - resid M t v)

theorem resid_eq_zero {M : SCM V ℝ} {u s : V → ℝ} (hs : M.Solves u s) (v : V) : resid M s v = 0 := by
  have h := hs v
  unfold resid
  cases hm : M.mech v with
  | none => rfl
  | some m =>
    rw [hm] at h
    show s v - m.f s = 0
    rw [← h, sub_self]

/-- Monotonitet ⇒ høyst én løsning i domenet. -/
theorem block_unique_of_monotone (M : SCM V ℝ) (rank : V → ℕ) (n : ℕ) (lam : V → ℝ)
    (D : (V → ℝ) → Prop) (hm : MonotoneAt M rank n lam D) :
    ∀ u s t, D s → D t → M.Solves u s → M.Solves u t →
      (∀ v, rank v < n → s v = t v) → ∀ v, rank v = n → s v = t v := by
  intro u s t hDs hDt hs ht hlow v hv
  by_contra hne
  have hexo : ∀ w, rank w = n → M.mech w = none → s w = t w := by
    intro w _ hw
    have a := hs w
    have b := ht w
    rw [hw] at a b
    rw [a, b]
  have hpos := hm s t hDs hDt hlow hexo ⟨v, hv, hne⟩
  simp only [resid_eq_zero hs, resid_eq_zero ht, sub_self, mul_zero, sum_const_zero] at hpos
  exact lt_irrefl 0 hpos

theorem BlockRecursive.of_monotone {M : SCM V ℝ} {rank : V → ℕ}
    (hp : ∀ v m, M.mech v = some m → ∀ p, p ∈ m.parents → rank p ≤ rank v)
    (hm : ∀ n, ∃ lam : V → ℝ, MonotoneAt M rank n lam (fun _ => True)) :
    M.BlockRecursive rank where
  parents_le := hp
  block_unique u s t hs ht n hlow := by
    obtain ⟨lam, hmn⟩ := hm n
    exact block_unique_of_monotone M rank n lam _ hmn u s t trivial trivial hs ht hlow

end SCM

/-! ## 3. Markedet: monotont alltid, kontraktivt bare når b < e -/

instance : Fintype MV :=
  ⟨{.t, .y, .w, .P, .Q}, by intro x; cases x <;> simp⟩

namespace Market

variable (m : Market)

theorem filter_rank1 : univ.filter (fun v : MV => Market.rank v = 1) = {MV.P, MV.Q} := by decide
theorem filter_rank0 : univ.filter (fun v : MV => Market.rank v = 0) = {MV.t, MV.y, MV.w} := by decide

theorem rank_cases (v : MV) : (Market.rank v = 0 ∧ m.scm.mech v = none) ∨ v = .P ∨ v = .Q := by
  cases v <;> simp [Market.rank, scm]

/-- Monotonitet med vekter λ_P = e·b og λ_Q = 1, for ALLE parametre. -/
theorem monotone (n : ℕ) :
    SCM.MonotoneAt m.scm Market.rank n (fun | .P => m.e * m.b | _ => 1) (fun _ => True) := by
  intro s t _ _ hlow hexo ⟨v, hv, hne⟩
  -- nivå 0 består bare av eksogene variabler; nivå ≥ 2 er tomt
  rcases m.rank_cases v with ⟨h0, hnone⟩ | rfl | rfl
  · exact absurd (hexo v hv hnone) hne
  all_goals
    have hn : n = 1 := by simp [Market.rank] at hv; omega
    subst hn
    rw [filter_rank1, sum_pair (by decide)]
    have ht : s .t = t .t := hlow .t (by simp [Market.rank])
    have hy : s .y = t .y := hlow .y (by simp [Market.rank])
    have hw : s .w = t .w := hlow .w (by simp [Market.rank])
    simp only [SCM.resid, scm, demandMech, supplyMech]
    have he := m.he.ne'
    have key : m.e * m.b * (s .P - t .P) *
          (s .P - ((s .Q - m.d - m.f * s .w) / m.e + s .t) - (t .P - ((t .Q - m.d - m.f * t .w) / m.e + t .t)))
        + 1 * (s .Q - t .Q) * (s .Q - (m.a - m.b * s .P + m.c * s .y) - (t .Q - (m.a - m.b * t .P + m.c * t .y)))
        = m.e * m.b * (s .P - t .P) ^ 2 + (s .Q - t .Q) ^ 2 := by
      rw [ht, hy, hw]; field_simp; ring
    show 0 < m.e * m.b * (s .P - t .P) *
          (s .P - ((s .Q - m.d - m.f * s .w) / m.e + s .t) - (t .P - ((t .Q - m.d - m.f * t .w) / m.e + t .t)))
        + 1 * (s .Q - t .Q) * (s .Q - (m.a - m.b * s .P + m.c * s .y) - (t .Q - (m.a - m.b * t .P + m.c * t .y)))
    rw [key]
    have heb : 0 < m.e * m.b := mul_pos m.he m.hb
  · have : 0 < (s .P - t .P) ^ 2 := by
      have : s .P - t .P ≠ 0 := sub_ne_zero.2 hne
      positivity
    nlinarith [sq_nonneg (s .Q - t .Q)]
  · have : 0 < (s .Q - t .Q) ^ 2 := by
      have : s .Q - t .Q ≠ 0 := sub_ne_zero.2 hne
      positivity
    nlinarith [sq_nonneg (s .P - t .P), mul_nonneg heb.le (sq_nonneg (s .P - t .P))]

theorem parents_le : ∀ v mm, m.scm.mech v = some mm → ∀ p, p ∈ mm.parents → Market.rank p ≤ Market.rank v :=
  m.blockRecursive.parents_le

/-- Markedets entydighet, nå utledet fra det generelle monotonikriteriet. -/
theorem blockRecursive_of_monotone : m.scm.BlockRecursive Market.rank :=
  SCM.BlockRecursive.of_monotone m.parents_le fun n => ⟨_, m.monotone n⟩

/-- Kontraksjonsfaktoren (1 + b/e)/2, skrevet uten brøk i brøk. -/
noncomputable def Kc : ℝ := (m.b + m.e) / (2 * m.e)

/-- Kontraksjonsulikhetene for lesningen «etterspørsel → Q, tilbud → P», med
    vekter μ_P = K/b og μ = 1 ellers. Faktoren K er under 1 nøyaktig når b < e. -/
theorem contractive (n : ℕ) :
    SCM.ContractiveAt m.scm Market.rank n (fun | .P => m.Kc / m.b | _ => 1) m.Kc := by
  intro s t δ hlow hblk v mm hv hm
  have hb := m.hb
  have he := m.he
  have hK : 0 < m.Kc := by unfold Kc; positivity
  rcases m.rank_cases v with ⟨_, hnone⟩ | rfl | rfl
  · rw [hnone] at hm; cases hm
  all_goals
    have hn : n = 1 := by simp [Market.rank] at hv; omega
    subst hn
    have ht : s .t = t .t := hlow .t (by simp [Market.rank])
    have hy : s .y = t .y := hlow .y (by simp [Market.rank])
    have hw : s .w = t .w := hlow .w (by simp [Market.rank])
    have hQ : |s .Q - t .Q| ≤ 1 * δ := hblk .Q (by simp [Market.rank])
    have hP : |s .P - t .P| ≤ m.Kc / m.b * δ := hblk .P (by simp [Market.rank])
    have hδ : 0 ≤ δ := by have := abs_nonneg (s .Q - t .Q); linarith
  · -- P := (Q − d − f·w)/e + t
    simp only [scm, Option.some.injEq] at hm
    subst hm
    show |(s .Q - m.d - m.f * s .w) / m.e + s .t - ((t .Q - m.d - m.f * t .w) / m.e + t .t)|
        ≤ m.Kc * (m.Kc / m.b * δ)
    have hrw : (s .Q - m.d - m.f * s .w) / m.e + s .t - ((t .Q - m.d - m.f * t .w) / m.e + t .t)
        = (s .Q - t .Q) / m.e := by rw [ht, hw]; field_simp; ring
    rw [hrw, abs_div, abs_of_pos he, div_le_iff₀ he]
    have hKK : m.b ≤ m.e * (m.Kc * m.Kc) := by
      unfold Kc
      rw [show m.e * ((m.b + m.e) / (2 * m.e) * ((m.b + m.e) / (2 * m.e))) = (m.b + m.e) ^ 2 / (4 * m.e) by
        field_simp; ring]
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (m.b - m.e)]
    have : 1 * δ ≤ m.Kc * (m.Kc / m.b * δ) * m.e := by
      rw [show m.Kc * (m.Kc / m.b * δ) * m.e = (m.e * (m.Kc * m.Kc)) / m.b * δ by field_simp]
      rw [one_mul]
      have : 1 ≤ (m.e * (m.Kc * m.Kc)) / m.b := by rw [le_div_iff₀ hb]; linarith
      nlinarith
    linarith
  · -- Q := a − b·P + c·y
    simp only [scm, Option.some.injEq] at hm
    subst hm
    show |m.a - m.b * s .P + m.c * s .y - (m.a - m.b * t .P + m.c * t .y)| ≤ m.Kc * (1 * δ)
    have hrw : m.a - m.b * s .P + m.c * s .y - (m.a - m.b * t .P + m.c * t .y)
        = -(m.b * (s .P - t .P)) := by rw [hy]; ring
    rw [hrw, abs_neg, abs_mul, abs_of_pos hb]
    calc m.b * |s .P - t .P| ≤ m.b * (m.Kc / m.b * δ) := mul_le_mul_of_nonneg_left hP hb.le
      _ = m.Kc * (1 * δ) := by field_simp

/-- Kontraksjonsfaktoren er under 1 nøyaktig når b < e. -/
theorem Kc_lt_one_iff : m.Kc < 1 ↔ m.b < m.e := by
  have he := m.he
  unfold Kc
  rw [div_lt_one (by positivity)]
  constructor <;> intro h <;> linarith

theorem blockRecursive_of_contractive (hbe : m.b < m.e) : m.scm.BlockRecursive Market.rank :=
  SCM.BlockRecursive.of_contractive m.parents_le fun n =>
    ⟨_, m.Kc, fun v => by
        have := m.hb; have := m.he
        have hK : 0 < m.Kc := by unfold Kc; positivity
        cases v <;> simp only [] <;> positivity,
     by have := m.hb; have := m.he; unfold Kc; positivity,
     (m.Kc_lt_one_iff).2 hbe, m.contractive n⟩

end Market

/-! ## 4. Kjemisk likevekt som selvløkke: domenet gir entydighet -/

namespace Rxn

variable (r : Rxn)

/-- ξ := K(a₀ − ξ)(b₀ − ξ), en blokk med én variabel som leser seg selv. -/
def scm : SCM Unit ℝ :=
  ⟨fun _ => some ⟨[()], fun s => r.K * (r.a0 - s ()) * (r.b0 - s ()), by
    intro s t h; show _ = _; rw [h () (by simp)]⟩⟩

/-- Det fysiske domenet: ingen negative konsentrasjoner av A og B. -/
def dom (s : Unit → ℝ) : Prop := s () < r.a0 ∧ s () < r.b0

theorem monotone : SCM.MonotoneAt r.scm (fun _ => 0) 0 (fun _ => 1) r.dom := by
  intro s t hs ht _ _ ⟨_, _, hne⟩
  have hu : univ.filter (fun _ : Unit => (0 : ℕ) = 0) = {()} := by decide
  rw [hu, sum_singleton]
  simp only [SCM.resid, scm, one_mul]
  have hx : s () - t () ≠ 0 := sub_ne_zero.2 hne
  have hfac : 0 < 1 + r.K * (r.a0 + r.b0 - s () - t ()) := by
    have := r.hK
    have : 0 < r.a0 + r.b0 - s () - t () := by
      obtain ⟨h1, h2⟩ := hs; obtain ⟨h3, h4⟩ := ht; linarith
    positivity
  have key : (s () - t ()) * (s () - r.K * (r.a0 - s ()) * (r.b0 - s ())
      - (t () - r.K * (r.a0 - t ()) * (r.b0 - t ())))
      = (s () - t ()) ^ 2 * (1 + r.K * (r.a0 + r.b0 - s () - t ())) := by ring
  rw [key]
  have : 0 < (s () - t ()) ^ 2 := by positivity
  positivity

/-- På det fysiske domenet er likevekten entydig. -/
theorem unique_on_domain {u s t : Unit → ℝ} (hs : r.scm.Solves u s) (ht : r.scm.Solves u t)
    (hDs : r.dom s) (hDt : r.dom t) : s = t := by
  funext x
  exact SCM.block_unique_of_monotone r.scm (fun _ => 0) 0 (fun _ => 1) r.dom r.monotone
    u s t hDs hDt hs ht (fun v h => absurd h (Nat.not_lt_zero _)) x rfl

/-- Uten domenet er blokken IKKE entydig løsbar: det finnes en fysisk og en
    ufysisk løsning. -/
theorem two_global_solutions : ∃ u s t : Unit → ℝ,
    r.scm.Solves u s ∧ r.scm.Solves u t ∧ s ≠ t ∧ r.dom s ∧ ¬ r.dom t := by
  obtain ⟨x1, h0, ha, hb, e1⟩ := r.eq_exists
  set mm := min r.a0 r.b0 with hmm
  have hK := r.hK
  set M := r.a0 + r.b0 + 1 / r.K with hM
  let g : ℝ → ℝ := fun x => r.K * (r.a0 - x) * (r.b0 - x) - x
  have hg : Continuous g := by fun_prop
  have hmle : mm ≤ M := by
    have : mm ≤ r.a0 := min_le_left _ _
    have := r.hb
    have : 0 < 1 / r.K := by positivity
    linarith
  have hgm : g mm ≤ 0 := by
    have hz : (r.a0 - mm) * (r.b0 - mm) = 0 := by
      rcases min_choice r.a0 r.b0 with h | h
      · rw [hmm, h, sub_self, zero_mul]
      · rw [hmm, h, sub_self, mul_zero]
    have : 0 < mm := lt_min r.ha r.hb
    show r.K * (r.a0 - mm) * (r.b0 - mm) - mm ≤ 0
    rw [mul_assoc, hz, mul_zero]
    linarith
  have hgM : 0 ≤ g M := by
    show 0 ≤ r.K * (r.a0 - M) * (r.b0 - M) - M
    have hKne : r.K ≠ 0 := hK.ne'
    have : r.K * (r.a0 - M) * (r.b0 - M) - M = r.K * r.a0 * r.b0 := by
      rw [hM]; field_simp; ring
    rw [this]
    have := r.ha; have := r.hb
    positivity
  obtain ⟨x2, ⟨hx2m, _⟩, hgx2⟩ := intermediate_value_Icc hmle hg.continuousOn ⟨hgm, hgM⟩
  have e2 : x2 = r.K * (r.a0 - x2) * (r.b0 - x2) := by
    have : r.K * (r.a0 - x2) * (r.b0 - x2) - x2 = 0 := hgx2
    linarith
  have hx1m : x1 < mm := lt_min ha hb
  refine ⟨fun _ => 0, fun _ => x1, fun _ => x2, ?_, ?_, ?_, ⟨ha, hb⟩, ?_⟩
  · intro v; cases v; exact e1
  · intro v; cases v; exact e2
  · intro h
    have : x1 = x2 := congrFun h ()
    linarith
  · rintro ⟨h1, h2⟩
    have : x2 < mm := lt_min h1 h2
    linarith

end Rxn
end CausalPhys
