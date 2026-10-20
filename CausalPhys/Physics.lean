/-
  CausalPhys.Physics — ideell gass og kjemisk likevekt oppå kjernen.

  Hovedpoeng:
    1. Dimensjoner er typer: pV og nRT kan bare sammenlignes med et bevis
       for at dimensjonene stemmer.
    2. Én lov (pV = nRT), to kausale oppsett. do(T) flytter p i det ene og
       V i det andre — og rører aldri den variabelen labben holder fast.
    3. Inngrep på eksogene variabler bevarer loven; inngrep på en effekt kan bryte den.
    4. A + B ⇌ C: likevekten finnes, er entydig, og Le Chatelier er et teorem.
-/
import CausalPhys.Core
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue

set_option linter.unusedSectionVars false

namespace CausalPhys
open SCM

/-! ## 1. Dimensjoner som typer -/

/-- SI-eksponenter: masse, lengde, tid, temperatur, stoffmengde. -/
structure Dim where
  M : ℤ
  L : ℤ
  T : ℤ
  Θ : ℤ
  N : ℤ
deriving DecidableEq, Repr

instance : Mul Dim := ⟨fun a b => ⟨a.M + b.M, a.L + b.L, a.T + b.T, a.Θ + b.Θ, a.N + b.N⟩⟩

namespace Dim
def pressure    : Dim := ⟨1, -1, -2, 0, 0⟩
def volume      : Dim := ⟨0, 3, 0, 0, 0⟩
def temperature : Dim := ⟨0, 0, 0, 1, 0⟩
def amount      : Dim := ⟨0, 0, 0, 0, 1⟩
/-- Dimensjonen til R: J·mol⁻¹·K⁻¹ = kg·m²·s⁻²·mol⁻¹·K⁻¹. -/
def gasConst    : Dim := ⟨1, 2, -2, -1, -1⟩
end Dim

/-- En størrelse med dimensjon `d`. -/
structure Q (d : Dim) where
  val : ℝ

instance {d : Dim} : Add (Q d) := ⟨fun x y => ⟨x.val + y.val⟩⟩
instance {a b : Dim} : HMul (Q a) (Q b) (Q (a * b)) := ⟨fun x y => ⟨x.val * y.val⟩⟩

/-- Bytte dimensjon krever et bevis for at dimensjonene er like. -/
def Q.cast {a b : Dim} (_h : a = b) (x : Q a) : Q b := ⟨x.val⟩

/-- pV og nRT har samme dimensjon (energi) — sjekket av maskinen. -/
theorem idealGas_dim_ok :
    Dim.amount * Dim.gasConst * Dim.temperature = Dim.pressure * Dim.volume := by decide

/-- … men pV og nT har det ikke. En elev som glemmer R får en typefeil. -/
theorem forgot_R : Dim.amount * Dim.temperature ≠ Dim.pressure * Dim.volume := by decide

/-- Den typede loven: kompilerer bare fordi `idealGas_dim_ok` er bevist. -/
def IdealGasTyped (p : Q .pressure) (V : Q .volume) (n : Q .amount)
    (R : Q .gasConst) (T : Q .temperature) : Prop :=
  p * V = (n * R * T).cast idealGas_dim_ok

/-! ## 2. Ideell gass: én lov, to kausale grafer -/

inductive Gas | p | Vol | T | n
deriving DecidableEq, Repr

/-- Gasskonstanten (J·mol⁻¹·K⁻¹). -/
noncomputable def R : ℝ := 8.314462618

theorem R_pos : 0 < R := by unfold R; norm_num

/-- Loven, uten kausal retning. -/
def idealGas : Law Gas ℝ := fun s => s .p * s .Vol = s .n * R * s .T

/-- Mekanisme «løs for p». -/
noncomputable def mechP : Mech Gas ℝ :=
  ⟨[.n, .T, .Vol], fun s => s .n * R * s .T / s .Vol, by
    intro s t h
    show _ = _
    rw [h .n (by simp), h .T (by simp), h .Vol (by simp)]⟩

/-- Mekanisme «løs for V». -/
noncomputable def mechV : Mech Gas ℝ :=
  ⟨[.n, .T, .p], fun s => s .n * R * s .T / s .p, by
    intro s t h
    show _ = _
    rw [h .n (by simp), h .T (by simp), h .p (by simp)]⟩

/-- Oppsett A: varmebad (T), fast stempel (V), lukket beholder (n). Trykket er effekten. -/
noncomputable def setupA : SCM Gas ℝ := ⟨fun | .p => some mechP | _ => none⟩

/-- Oppsett B: varmebad (T), lodd på stempelet (p), lukket beholder (n). Volumet er effekten. -/
noncomputable def setupB : SCM Gas ℝ := ⟨fun | .Vol => some mechV | _ => none⟩

/-- Simon-orden for A: p ligger over de andre. -/
theorem setupA_recursive : setupA.Recursive (fun | .p => 1 | _ => 0) := by
  intro v m hm q hq
  cases v <;> simp [setupA] at hm
  subst hm
  simp [mechP] at hq
  rcases hq with rfl | rfl | rfl <;> decide

theorem setupB_recursive : setupB.Recursive (fun | .Vol => 1 | _ => 0) := by
  intro v m hm q hq
  cases v <;> simp [setupB] at hm
  subst hm
  simp [mechV] at hq
  rcases hq with rfl | rfl | rfl <;> decide

/-- Oppsett A realiserer loven (når volumet er ≠ 0). -/
theorem setupA_lawful (u s : Gas → ℝ) (h : setupA.Solves u s) (hV : u .Vol ≠ 0) :
    idealGas s := by
  have hp : s .p = s .n * R * s .T / s .Vol := h .p
  have hv : s .Vol = u .Vol := h .Vol
  have hV' : s .Vol ≠ 0 := hv ▸ hV
  unfold idealGas
  rw [hp]
  field_simp

/-- Oppsett B realiserer samme lov (når trykket er ≠ 0). -/
theorem setupB_lawful (u s : Gas → ℝ) (h : setupB.Solves u s) (hp : u .p ≠ 0) :
    idealGas s := by
  have hV : s .Vol = s .n * R * s .T / s .p := h .Vol
  have hpp : s .p = u .p := h .p
  have hp' : s .p ≠ 0 := hpp ▸ hp
  unfold idealGas
  rw [hV]
  field_simp

/-! ### Kausal asymmetri: samme lov, ulike svar på do(T) -/

/-- A: do(T := c) lar volumet stå … -/
theorem A_doT_fixes_V (c : ℝ) (u s : Gas → ℝ) (h : (setupA.doI .T c).Solves u s) :
    s .Vol = u .Vol :=
  doI_exo setupA c u s (by decide) rfl h

/-- … og flytter trykket til p = nRc / V. -/
theorem A_doT_moves_p (c : ℝ) (u s : Gas → ℝ) (h : (setupA.doI .T c).Solves u s) :
    s .p = u .n * R * c / u .Vol := by
  have hp : s .p = s .n * R * s .T / s .Vol := doI_other setupA c u s mechP (by decide) rfl h
  rw [hp, doI_self setupA .T c u s h, doI_exo setupA c u s (by decide) rfl h,
    A_doT_fixes_V c u s h]

/-- B: do(T := c) lar trykket stå … -/
theorem B_doT_fixes_p (c : ℝ) (u s : Gas → ℝ) (h : (setupB.doI .T c).Solves u s) :
    s .p = u .p :=
  doI_exo setupB c u s (by decide) rfl h

/-- … og flytter volumet til V = nRc / p. -/
theorem B_doT_moves_V (c : ℝ) (u s : Gas → ℝ) (h : (setupB.doI .T c).Solves u s) :
    s .Vol = u .n * R * c / u .p := by
  have hV : s .Vol = s .n * R * s .T / s .p := doI_other setupB c u s mechV (by decide) rfl h
  rw [hV, doI_self setupB .T c u s h, doI_exo setupB c u s (by decide) rfl h,
    B_doT_fixes_p c u s h]

/-! ### Hvilke inngrep er fysisk lovlige? -/

/-- Å skru på en eksogen variabel (her: flytte stempelet i A) bevarer loven. -/
theorem A_doV_lawful (c : ℝ) (hc : c ≠ 0) (u s : Gas → ℝ)
    (h : (setupA.doI .Vol c).Solves u s) : idealGas s := by
  have hp : s .p = s .n * R * s .T / s .Vol := doI_other setupA c u s mechP (by decide) rfl h
  have hv : s .Vol = c := doI_self setupA .Vol c u s h
  have hv' : s .Vol ≠ 0 := hv ▸ hc
  unfold idealGas
  rw [hp]
  field_simp

/-- Å tvinge en EFFEKT (trykket i A) kan bryte loven:
    do(p := 0) med n = T = V = 1 gir 0 · 1 ≠ 1 · R · 1. -/
theorem A_doP_breaks_law : ∃ u s : Gas → ℝ,
    (setupA.doI .p 0).Solves u s ∧ ¬ idealGas s := by
  let s : Gas → ℝ := fun | .p => 0 | _ => 1
  refine ⟨s, s, ?_, ?_⟩
  · intro v
    cases v <;> simp [SCM.doI, SCM.Mech.const, setupA, s]
  · simp only [idealGas, s]
    have := R_pos
    intro h
    linarith

/-! ## 3. Kjemisk likevekt: A + B ⇌ C -/

/-- Startkonsentrasjoner og likevektskonstant. -/
structure Rxn where
  a0 : ℝ
  b0 : ℝ
  K  : ℝ
  ha : 0 < a0
  hb : 0 < b0
  hK : 0 < K

/-- ξ er reaksjonsomfanget ved likevekt: [C] = K·[A]·[B],
    med [A] = a0 − ξ, [B] = b0 − ξ, [C] = ξ. -/
def Rxn.IsEq (r : Rxn) (ξ : ℝ) : Prop :=
  0 ≤ ξ ∧ ξ < r.a0 ∧ ξ < r.b0 ∧ ξ = r.K * (r.a0 - ξ) * (r.b0 - ξ)

/-- do(a0 := a0 + δ): tilsett mer A. -/
def Rxn.addA (r : Rxn) (δ : ℝ) (hδ : 0 < δ) : Rxn :=
  { r with a0 := r.a0 + δ, ha := by linarith [r.ha] }

/-- Hjelpelemma: større faktorer gir større produkt. -/
theorem prod_lt {K x y x' y' : ℝ} (hK : 0 < K) (hx : 0 < x) (hy : 0 < y)
    (hxx : x < x') (hyy : y ≤ y') : K * x * y < K * x' * y' := by
  have h1 : x * y < x' * y' := by
    nlinarith [mul_pos (sub_pos.2 hxx) (lt_of_lt_of_le hy hyy),
      mul_nonneg hx.le (sub_nonneg.2 hyy)]
  calc K * x * y = K * (x * y) := by ring
    _ < K * (x' * y') := mul_lt_mul_of_pos_left h1 hK
    _ = K * x' * y' := by ring

/-- Likevekten er entydig. -/
theorem Rxn.eq_unique (r : Rxn) {ξ₁ ξ₂ : ℝ} (h₁ : r.IsEq ξ₁) (h₂ : r.IsEq ξ₂) :
    ξ₁ = ξ₂ := by
  obtain ⟨_, ha₁, hb₁, e₁⟩ := h₁
  obtain ⟨_, ha₂, hb₂, e₂⟩ := h₂
  rcases lt_trichotomy ξ₁ ξ₂ with hlt | heq | hgt
  · have := prod_lt r.hK (sub_pos.2 ha₂) (sub_pos.2 hb₂)
      (by linarith : r.a0 - ξ₂ < r.a0 - ξ₁) (by linarith : r.b0 - ξ₂ ≤ r.b0 - ξ₁)
    linarith
  · exact heq
  · have := prod_lt r.hK (sub_pos.2 ha₁) (sub_pos.2 hb₁)
      (by linarith : r.a0 - ξ₁ < r.a0 - ξ₂) (by linarith : r.b0 - ξ₁ ≤ r.b0 - ξ₂)
    linarith

/-- Likevekten finnes (mellomverdisetningen). -/
theorem Rxn.eq_exists (r : Rxn) : ∃ ξ, r.IsEq ξ := by
  set m := min r.a0 r.b0 with hm
  have hm0 : 0 < m := lt_min r.ha r.hb
  have hma : m ≤ r.a0 := min_le_left _ _
  have hmb : m ≤ r.b0 := min_le_right _ _
  let f : ℝ → ℝ := fun ξ => r.K * (r.a0 - ξ) * (r.b0 - ξ) - ξ
  have hf : Continuous f := by fun_prop
  have hf0 : 0 ≤ f 0 := by
    have := mul_pos (mul_pos r.hK r.ha) r.hb
    simp only [f, sub_zero]; linarith
  have hfm : f m < 0 := by
    have hz : (r.a0 - m) * (r.b0 - m) = 0 := by
      rcases min_choice r.a0 r.b0 with h | h
      · rw [hm, h, sub_self, zero_mul]
      · rw [hm, h, sub_self, mul_zero]
    simp only [f]
    have : r.K * (r.a0 - m) * (r.b0 - m) = 0 := by rw [mul_assoc, hz, mul_zero]
    linarith
  obtain ⟨ξ, ⟨hξ0, hξm⟩, hfξ⟩ :=
    intermediate_value_Icc' hm0.le hf.continuousOn ⟨hfm.le, hf0⟩
  have e : ξ = r.K * (r.a0 - ξ) * (r.b0 - ξ) := by simp only [f] at hfξ; linarith
  refine ⟨ξ, hξ0, ?_, ?_, e⟩
  · refine lt_of_le_of_ne (hξm.trans hma) ?_
    intro hx
    rw [hx, sub_self, mul_zero, zero_mul] at e
    linarith [r.ha]
  · refine lt_of_le_of_ne (hξm.trans hmb) ?_
    intro hx
    rw [hx, sub_self, mul_zero] at e
    linarith [r.hb]

/-- Dermed er likevekten veldefinert: den finnes og er entydig. -/
theorem Rxn.eq_exists_unique (r : Rxn) : ∃! ξ, r.IsEq ξ := by
  obtain ⟨ξ, hξ⟩ := r.eq_exists
  exact ⟨ξ, hξ, fun η hη => r.eq_unique hη hξ⟩

/-- Le Chatelier som teorem: do(tilsett A) flytter likevekten mot mer C. -/
theorem leChatelier (r : Rxn) (δ : ℝ) (hδ : 0 < δ) {ξ ξ' : ℝ}
    (h : r.IsEq ξ) (h' : (r.addA δ hδ).IsEq ξ') : ξ < ξ' := by
  obtain ⟨_, ha, hb, e⟩ := h
  obtain ⟨_, _, hb', e'⟩ := h'
  simp only [Rxn.addA] at e' hb'
  by_contra hle
  replace hle := not_lt.mp hle
  have := prod_lt r.hK (sub_pos.2 ha) (sub_pos.2 hb)
    (by linarith : r.a0 - ξ < r.a0 + δ - ξ') (by linarith : r.b0 - ξ ≤ r.b0 - ξ')
  linarith

end CausalPhys
