/-
  CausalPhys.Economics — Simon-orden og do-operatoren i økonomi.

  Del 1  Et generelt kjerne-teorem: i en rekursiv modell kan et inngrep aldri
         endre noe som ligger lavere i den kausale orden («fremtiden påvirker
         ikke fortiden»).
  Del 2  Marked med tilbud og etterspørsel. Pris og mengde er én simultan
         Simon-blokk, så likevekten behandles som en betingelse (som kjemisk
         likevekt i Physics.lean). Bevist:
           • likevekten finnes og er entydig,
           • skatteinsidens: do(skatt) deles mellom kjøper og selger,
           • identifikasjon: et tilbudssjokk sporer etterspørselskurven og
             omvendt (instrumentvariabler),
           • ikke-identifikasjon: uten sjokk kan én observasjon ikke skille
             ulike etterspørselshellinger,
           • Lucas-kritikken: hvis en «strukturell» ligning avhenger av
             politikken, bommer den naive do-prediksjonen med et eksakt beløp.
  Del 3  Spindelvevmodellen (cobweb) som rekursiv SCM i tid: entydig løsning,
         inngrep virker bare fremover, og stabilitet når tilbudet er mindre
         prisfølsomt enn etterspørselen.
-/
import CausalPhys.Core
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.Field.Basic

set_option linter.unusedSectionVars false

namespace CausalPhys

/-! ## Del 1. Inngrep virker bare nedover i Simon-orden -/

namespace SCM

variable {V : Type} {α : Type} [DecidableEq V]

/-- Hvis `rank v < rank x`, endrer do(x := c) ikke verdien av `v`. -/
theorem Recursive.doI_past {M : SCM V α} {rank : V → Nat} (hr : M.Recursive rank)
    (x : V) (c : α) {u s s' : V → α}
    (hs : M.Solves u s) (hs' : (M.doI x c).Solves u s') :
    ∀ v, rank v < rank x → s v = s' v := by
  have key : ∀ n, ∀ v, rank v = n → n < rank x → s v = s' v := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro v hv hlt
      have hvx : v ≠ x := by
        rintro rfl
        omega
      have h1 := hs v
      have h2 := hs' v
      rw [doI_mech_ne M c hvx] at h2
      cases hm : M.mech v with
      | none =>
        rw [hm] at h1 h2
        rw [h1, h2]
      | some m =>
        rw [hm] at h1 h2
        rw [h1, h2]
        apply m.local_
        intro p hp
        have := hr v m hm p hp
        exact ih (rank p) (by omega) p rfl (by omega)
  intro v hv
  exact key (rank v) v rfl hv

end SCM

/-! ## Del 2. Marked med tilbud og etterspørsel -/

/-- Lineært marked.
    Etterspørsel: Q = a − b·P + c·y   (y = inntekt, etterspørselssjokk)
    Tilbud:       Q = d + e·(P − t) + f·w   (t = stykkskatt, w = vær, tilbudssjokk)
    Fallende etterspørsel (b > 0) og stigende tilbud (e > 0). -/
structure Market where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  e : ℝ
  f : ℝ
  hb : 0 < b
  he : 0 < e

/-- Eksogene variabler: det labben — her politikken og naturen — setter. -/
structure Exo where
  t : ℝ
  y : ℝ
  w : ℝ

namespace Market

variable (m : Market) (x : Exo)

/-- (P, Q) er en markedslikevekt. -/
def IsEq (P Q : ℝ) : Prop :=
  Q = m.a - m.b * P + m.c * x.y ∧ Q = m.d + m.e * (P - x.t) + m.f * x.w

/-- Likevektspris (kjøperpris). -/
noncomputable def Pstar : ℝ :=
  (m.a - m.d + m.c * x.y - m.f * x.w + m.e * x.t) / (m.b + m.e)

/-- Likevektsmengde. -/
noncomputable def Qstar : ℝ := m.a - m.b * m.Pstar x + m.c * x.y

theorem sum_pos : 0 < m.b + m.e := add_pos m.hb m.he

theorem sum_ne : m.b + m.e ≠ 0 := (m.sum_pos).ne'

/-- Likevektsmengden ligger også på tilbudskurven. -/
theorem Qstar_supply : m.Qstar x = m.d + m.e * (m.Pstar x - x.t) + m.f * x.w := by
  have h := m.sum_ne
  unfold Qstar Pstar
  field_simp
  ring

/-- Likevekten finnes og er entydig: (P, Q) er likevekt ⇔ (P, Q) = (P*, Q*). -/
theorem isEq_iff (P Q : ℝ) : m.IsEq x P Q ↔ P = m.Pstar x ∧ Q = m.Qstar x := by
  constructor
  · rintro ⟨h1, h2⟩
    have hP : P = m.Pstar x := by
      unfold Pstar
      rw [eq_div_iff m.sum_ne]
      have h3 := h1.symm.trans h2
      have h4 : P * (m.b + m.e) - (m.a - m.d + m.c * x.y - m.f * x.w + m.e * x.t)
          = -((m.a - m.b * P + m.c * x.y) - (m.d + m.e * (P - x.t) + m.f * x.w)) := by ring
      rw [h3, sub_self, neg_zero] at h4
      exact sub_eq_zero.1 h4
    refine ⟨hP, ?_⟩
    rw [h1, hP]
    rfl
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, m.Qstar_supply x⟩

/-! ### Skatteinsidens: do(t := t + Δ) -/

/-- Kjøperprisen stiger med andelen e/(b+e) av skatteøkningen. -/
theorem tax_passthrough (Δ : ℝ) :
    m.Pstar { x with t := x.t + Δ } - m.Pstar x = m.e / (m.b + m.e) * Δ := by
  have h := m.sum_ne
  unfold Pstar
  field_simp
  ring

/-- Byrdene summerer til hele skatten: kjøperens andel e/(b+e),
    selgerens andel b/(b+e). -/
theorem burden_shares : m.e / (m.b + m.e) + m.b / (m.b + m.e) = 1 := by
  have h := m.sum_ne
  field_simp
  ring

/-- Kjøperne bærer en ekte del av skatten, men aldri hele: 0 < ΔP < Δ. -/
theorem consumer_burden_between (Δ : ℝ) (hΔ : 0 < Δ) :
    0 < m.Pstar { x with t := x.t + Δ } - m.Pstar x ∧
    m.Pstar { x with t := x.t + Δ } - m.Pstar x < Δ := by
  rw [tax_passthrough]
  have hs := m.sum_pos
  have hfrac : m.e / (m.b + m.e) < 1 := by
    rw [div_lt_one hs]
    linarith [m.hb]
  constructor
  · exact mul_pos (div_pos m.he hs) hΔ
  · exact mul_lt_of_lt_one_left hΔ hfrac

/-- Når etterspørselssjokket y er uendret, beveger mengden seg langs
    etterspørselskurven: ΔQ = −b·ΔP. -/
theorem dQ_along_demand (x' : Exo) (hy : x'.y = x.y) :
    m.Qstar x' - m.Qstar x = -m.b * (m.Pstar x' - m.Pstar x) := by
  unfold Qstar
  rw [hy]
  ring

/-- … og når skatt og vær er uendret, langs tilbudskurven: ΔQ = e·ΔP. -/
theorem dQ_along_supply (x' : Exo) (ht : x'.t = x.t) (hw : x'.w = x.w) :
    m.Qstar x' - m.Qstar x = m.e * (m.Pstar x' - m.Pstar x) := by
  rw [Qstar_supply, Qstar_supply, ht, hw]
  ring

/-- En skatt reduserer omsatt mengde. -/
theorem tax_reduces_quantity (Δ : ℝ) (hΔ : 0 < Δ) :
    m.Qstar { x with t := x.t + Δ } < m.Qstar x := by
  have h := m.dQ_along_demand x { x with t := x.t + Δ } rfl
  have hp := (m.consumer_burden_between x Δ hΔ).1
  have := mul_pos m.hb hp
  linarith

/-! ### Identifikasjon (Simon 1953: «Causal Ordering and Identifiability») -/

/-- Et værsjokk flytter prisen med −f·δ/(b+e). -/
theorem weather_moves_price (δ : ℝ) :
    m.Pstar { x with w := x.w + δ } - m.Pstar x = -(m.f * δ) / (m.b + m.e) := by
  have h := m.sum_ne
  unfold Pstar
  field_simp
  ring

/-- Instrumentvariabel: når været (som bare inngår i tilbudet) varierer,
    avslører forholdet −ΔQ/ΔP etterspørselshellingen b eksakt. -/
theorem weather_identifies_demand (δ : ℝ) (hf : m.f ≠ 0) (hδ : δ ≠ 0) :
    -(m.Qstar { x with w := x.w + δ } - m.Qstar x) /
      (m.Pstar { x with w := x.w + δ } - m.Pstar x) = m.b := by
  have hP : m.Pstar { x with w := x.w + δ } - m.Pstar x ≠ 0 := by
    rw [weather_moves_price]
    exact div_ne_zero (neg_ne_zero.2 (mul_ne_zero hf hδ)) m.sum_ne
  rw [m.dQ_along_demand x { x with w := x.w + δ } rfl]
  field_simp

/-- Speilbildet: et inntektssjokk (bare i etterspørselen) avslører tilbudshellingen e. -/
theorem income_identifies_supply (δ : ℝ) (hc : m.c ≠ 0) (hδ : δ ≠ 0) :
    (m.Qstar { x with y := x.y + δ } - m.Qstar x) /
      (m.Pstar { x with y := x.y + δ } - m.Pstar x) = m.e := by
  have hP : m.Pstar { x with y := x.y + δ } - m.Pstar x ≠ 0 := by
    have h := m.sum_ne
    have : m.Pstar { x with y := x.y + δ } - m.Pstar x = m.c * δ / (m.b + m.e) := by
      unfold Pstar
      field_simp
      ring
    rw [this]
    exact div_ne_zero (mul_ne_zero hc hδ) m.sum_ne
  rw [m.dQ_along_supply x { x with y := x.y + δ } rfl rfl]
  field_simp

/-- Ikke-identifikasjon: uten variasjon i sjokkene er ÉN likevektsobservasjon
    forenlig med en hvilken som helst positiv etterspørselshelling b'. -/
theorem slope_not_identified (b' : ℝ) (hb' : 0 < b') :
    ∃ m' : Market, m'.b = b' ∧ m'.IsEq x (m.Pstar x) (m.Qstar x) := by
  refine ⟨{ m with a := m.a + (b' - m.b) * m.Pstar x, b := b', hb := hb' }, rfl, ?_, ?_⟩
  · show m.Qstar x = m.a + (b' - m.b) * m.Pstar x - b' * m.Pstar x + m.c * x.y
    unfold Qstar
    ring
  · exact m.Qstar_supply x

/-! ### Lucas-kritikken -/

/-- Etterspørselen reagerer på politikken selv (forventninger):
    konstantleddet blir a + κ·t. -/
def withPolicy (κ t : ℝ) : Market := { m with a := m.a + κ * t }

/-- En analytiker estimerer modellen ved dagens politikk t og predikerer
    effekten av do(t := t + Δ) med den gamle ligningen. Feilen er eksakt κΔ/(b+e). -/
theorem lucas_error (κ Δ : ℝ) :
    (m.withPolicy κ (x.t + Δ)).Pstar { x with t := x.t + Δ }
      - (m.withPolicy κ x.t).Pstar { x with t := x.t + Δ }
      = κ * Δ / (m.b + m.e) := by
  have h := m.sum_ne
  unfold Pstar withPolicy
  field_simp
  ring

/-- Den naive do-prediksjonen er riktig hvis og bare hvis ligningen er
    invariant under politikken (κ = 0) — Simons «strukturelle» krav. -/
theorem lucas_naive_correct_iff (κ Δ : ℝ) (hΔ : Δ ≠ 0) :
    (m.withPolicy κ (x.t + Δ)).Pstar { x with t := x.t + Δ }
      = (m.withPolicy κ x.t).Pstar { x with t := x.t + Δ } ↔ κ = 0 := by
  rw [← sub_eq_zero, lucas_error, div_eq_zero_iff, mul_eq_zero]
  constructor
  · rintro ((h | h) | h)
    · exact h
    · exact absurd h hΔ
    · exact absurd h m.sum_ne
  · intro h
    exact Or.inl (Or.inl h)

end Market

/-! ## Del 3. Spindelvevmodellen som rekursiv SCM -/

/-- Variabler indeksert med periode: pris og mengde. -/
inductive CW
  | P (n : ℕ)
  | Q (n : ℕ)
deriving DecidableEq

/-- Bønder planlegger produksjonen etter fjorårets pris:
      Q₀ eksogen,  Qₙ₊₁ = d + e·Pₙ  (tilbud),  Pₙ = (a − Qₙ)/b  (etterspørsel). -/
structure Cobweb where
  a : ℝ
  b : ℝ
  d : ℝ
  e : ℝ
  hb : 0 < b
  he : 0 < e

namespace Cobweb

variable (cw : Cobweb)

noncomputable def demandMech (n : ℕ) : Mech CW ℝ :=
  ⟨[.Q n], fun s => (cw.a - s (.Q n)) / cw.b, by
    intro s t h
    show _ = _
    rw [h (.Q n) (by simp)]⟩

def supplyMech (n : ℕ) : Mech CW ℝ :=
  ⟨[.P n], fun s => cw.d + cw.e * s (.P n), by
    intro s t h
    show _ = _
    rw [h (.P n) (by simp)]⟩

noncomputable def scm : SCM CW ℝ :=
  ⟨fun
    | .P n => some (cw.demandMech n)
    | .Q 0 => none
    | .Q (n + 1) => some (cw.supplyMech n)⟩

/-- Simon-orden = tid: Q₀ < P₀ < Q₁ < P₁ < … -/
def rank : CW → ℕ
  | .Q n => 2 * n
  | .P n => 2 * n + 1

theorem recursive : cw.scm.Recursive rank := by
  intro v m hm p hp
  match v, hm with
  | .P n, hm =>
    simp only [scm, Option.some.injEq] at hm
    subst hm
    simp [demandMech] at hp
    subst hp
    simp [rank]
  | .Q (n + 1), hm =>
    simp only [scm, Option.some.injEq] at hm
    subst hm
    simp [supplyMech] at hp
    subst hp
    simp [rank]
    omega

/-- Gitt startavlingen er hele prisbanen entydig bestemt. -/
theorem unique {u s t : CW → ℝ} (hs : cw.scm.Solves u s) (ht : cw.scm.Solves u t) :
    s = t :=
  cw.recursive.unique hs ht

/-- Et prisinngrep i periode k (f.eks. en makspris) endrer ingen tidligere priser … -/
theorem doP_past_prices {u s s' : CW → ℝ} (k : ℕ) (c : ℝ)
    (hs : cw.scm.Solves u s) (hs' : (cw.scm.doI (.P k) c).Solves u s')
    (j : ℕ) (hj : j < k) : s (.P j) = s' (.P j) :=
  cw.recursive.doI_past (.P k) c hs hs' (.P j) (by simp [rank]; omega)

/-- … og ingen avlinger til og med periode k. -/
theorem doP_past_quantities {u s s' : CW → ℝ} (k : ℕ) (c : ℝ)
    (hs : cw.scm.Solves u s) (hs' : (cw.scm.doI (.P k) c).Solves u s')
    (j : ℕ) (hj : j ≤ k) : s (.Q j) = s' (.Q j) :=
  cw.recursive.doI_past (.P k) c hs hs' (.Q j) (by simp [rank]; omega)

/-- Stasjonær likevektspris. -/
noncomputable def Pbar : ℝ := (cw.a - cw.d) / (cw.b + cw.e)

/-- Spindelvevdynamikken: avviket fra likevekt skifter fortegn og skaleres med e/b. -/
theorem dynamics {u s : CW → ℝ} (hs : cw.scm.Solves u s) (n : ℕ) :
    s (.P (n + 1)) - cw.Pbar = -(cw.e / cw.b) * (s (.P n) - cw.Pbar) := by
  have hP : s (.P (n + 1)) = (cw.a - s (.Q (n + 1))) / cw.b := hs (.P (n + 1))
  have hQ : s (.Q (n + 1)) = cw.d + cw.e * s (.P n) := hs (.Q (n + 1))
  have hb := cw.hb.ne'
  have hbe : cw.b + cw.e ≠ 0 := (add_pos cw.hb cw.he).ne'
  rw [hP, hQ]
  unfold Pbar
  field_simp
  ring

/-- Spindelvevteoremet: er tilbudet mindre prisfølsomt enn etterspørselen (e < b),
    krymper avviket fra likevekt for hver periode. -/
theorem converges_step {u s : CW → ℝ} (hs : cw.scm.Solves u s) (hlt : cw.e < cw.b)
    (n : ℕ) (hne : s (.P n) ≠ cw.Pbar) :
    |s (.P (n + 1)) - cw.Pbar| < |s (.P n) - cw.Pbar| := by
  rw [cw.dynamics hs n, abs_mul, abs_neg, abs_of_pos (div_pos cw.he cw.hb)]
  exact mul_lt_of_lt_one_left (abs_pos.2 (sub_ne_zero.2 hne)) ((div_lt_one cw.hb).2 hlt)

/-- … og er det mer prisfølsomt (e > b), vokser avviket: eksplosive sykluser. -/
theorem diverges_step {u s : CW → ℝ} (hs : cw.scm.Solves u s) (hgt : cw.b < cw.e)
    (n : ℕ) (hne : s (.P n) ≠ cw.Pbar) :
    |s (.P n) - cw.Pbar| < |s (.P (n + 1)) - cw.Pbar| := by
  rw [cw.dynamics hs n, abs_mul, abs_neg, abs_of_pos (div_pos cw.he cw.hb)]
  exact lt_mul_of_one_lt_left (abs_pos.2 (sub_ne_zero.2 hne)) ((one_lt_div cw.hb).2 hgt)

end Cobweb
end CausalPhys
