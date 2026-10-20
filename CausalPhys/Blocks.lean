/-
  CausalPhys.Blocks — sykliske Simon-blokker.

  Likevekter (kjemi, markeder) er sykliske: variablene i en blokk bestemmer
  hverandre. Simon samler dem i blokker og krever at hver blokk er entydig
  løsbar gitt blokkene under. Denne modulen beviser:

    1. `BlockRecursive.unique`  Blokkvis entydighet gir global entydighet.
    2. `Recursive.toBlock`      Den asykliske kjernen er et spesialtilfelle.
    3. `doI_exo_iff`            Inngrep på en eksogen variabel er bare nye
                                eksogene verdier, så all struktur bevares.
    4. Markedet fra Economics.lean som en ekte SCM med én likevektsblokk {P, Q}:
       entydig løsning, do(skatt) gir lærebokas skatteinsidens, og do(pris)
       (makspris) gir et overskudd av etterspørsel på nøyaktig (b+e)(P* − c).
    5. Et moteksempel: et inngrep INNE i en syklisk blokk kan ødelegge entydig
       løsbarhet (uendelig mange løsninger) eller fjerne alle løsninger.
       I motsetning til det asykliske tilfellet bevarer do ikke blokkstruktur.
-/
import CausalPhys.Core
import CausalPhys.Economics
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Logic.Function.Basic

set_option linter.unusedSectionVars false

namespace CausalPhys
namespace SCM

universe u
variable {V : Type} {α : Type u}

/-- Blokkrekursiv modell: foreldre ligger i samme eller lavere blokk, og hver blokk
    er entydig bestemt når alt under den er bestemt. -/
structure BlockRecursive (M : SCM V α) (rank : V → Nat) : Prop where
  parents_le   : ∀ v m, M.mech v = some m → ∀ p, p ∈ m.parents → rank p ≤ rank v
  block_unique : ∀ u s t, M.Solves u s → M.Solves u t →
                 ∀ n, (∀ v, rank v < n → s v = t v) → ∀ v, rank v = n → s v = t v

/-- 1. Blokkvis entydighet gir global entydighet. -/
theorem BlockRecursive.unique {M : SCM V α} {rank : V → Nat} (hb : M.BlockRecursive rank)
    {u s t : V → α} (hs : M.Solves u s) (ht : M.Solves u t) : s = t := by
  have key : ∀ n, ∀ v, rank v = n → s v = t v := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      exact hb.block_unique u s t hs ht n (fun v hv => ih (rank v) hv v rfl)
  funext v
  exact key (rank v) v rfl

/-- 2. Asykliske (rekursive) modeller er blokkrekursive med enkeltvariabel-blokker. -/
theorem Recursive.toBlock {M : SCM V α} {rank : V → Nat} (hr : M.Recursive rank) :
    M.BlockRecursive rank where
  parents_le v m hm p hp := Nat.le_of_lt (hr v m hm p hp)
  block_unique u s t hs ht n ih v hv := by
    have hsv := hs v
    have htv := ht v
    cases hm : M.mech v with
    | none =>
      rw [hm] at hsv htv
      rw [hsv, htv]
    | some m =>
      rw [hm] at hsv htv
      rw [hsv, htv]
      apply m.local_
      intro p hp
      exact ih p (hv ▸ hr v m hm p hp)

variable [DecidableEq V]

/-- 3. Et inngrep på en eksogen variabel er det samme som en ny eksogen verdi. -/
theorem doI_exo_iff (M : SCM V α) {x : V} (c : α) (u s : V → α) (hx : M.mech x = none) :
    (M.doI x c).Solves u s ↔ M.Solves (Function.update u x c) s := by
  constructor
  · intro h v
    by_cases hv : v = x
    · subst hv
      rw [hx]
      show s v = Function.update u v c v
      rw [Function.update_self]
      exact doI_self M v c u s h
    · have h' := h v
      rw [doI_mech_ne M c hv] at h'
      cases hm : M.mech v with
      | none =>
        rw [hm] at h'
        show s v = Function.update u x c v
        rw [Function.update_of_ne hv]
        exact h'
      | some m =>
        rw [hm] at h'
        exact h'
  · intro h v
    by_cases hv : v = x
    · subst hv
      have h' := h v
      rw [hx] at h'
      have h'' : s v = Function.update u v c v := h'
      rw [Function.update_self] at h''
      have hm : (M.doI v c).mech v = some (Mech.const c) := by simp [doI]
      rw [hm]
      exact h''
    · rw [doI_mech_ne M c hv]
      have h' := h v
      cases hm : M.mech v with
      | none =>
        rw [hm] at h'
        have h'' : s v = Function.update u x c v := h'
        rw [Function.update_of_ne hv] at h''
        exact h''
      | some m =>
        rw [hm] at h'
        exact h'

end SCM

/-! ## 4. Markedet som SCM med én likevektsblokk -/

inductive MV | t | y | w | P | Q
deriving DecidableEq

namespace Market

variable (m : Market)

/-- Etterspørselen bestemmer mengden. -/
def demandMech : Mech MV ℝ :=
  ⟨[.P, .y], fun s => m.a - m.b * s .P + m.c * s .y, by
    intro s t h
    show _ = _
    rw [h .P (by simp), h .y (by simp)]⟩

/-- Tilbudet, løst for prisen: P = (Q − d − f·w)/e + t. -/
noncomputable def supplyMech : Mech MV ℝ :=
  ⟨[.Q, .t, .w], fun s => (s .Q - m.d - m.f * s .w) / m.e + s .t, by
    intro s t h
    show _ = _
    rw [h .Q (by simp), h .t (by simp), h .w (by simp)]⟩

/-- Markedet: skatt, inntekt og vær er eksogene; P og Q danner en syklus. -/
noncomputable def scm : SCM MV ℝ :=
  ⟨fun
    | .Q => some m.demandMech
    | .P => some m.supplyMech
    | _  => none⟩

/-- Blokkene: {t, y, w} under {P, Q}. -/
def rank : MV → Nat
  | .P => 1
  | .Q => 1
  | _  => 0

def exoOf (u : MV → ℝ) : Exo := ⟨u .t, u .y, u .w⟩

/-- Løsningene av SCM-en er nøyaktig likevekten fra Economics.lean. -/
theorem scm_solves_iff (u s : MV → ℝ) :
    m.scm.Solves u s ↔
      (s .t = u .t ∧ s .y = u .y ∧ s .w = u .w) ∧
      s .P = m.Pstar (exoOf u) ∧ s .Q = m.Qstar (exoOf u) := by
  have he := m.he.ne'
  constructor
  · intro h
    have ht : s .t = u .t := h .t
    have hy : s .y = u .y := h .y
    have hw : s .w = u .w := h .w
    have hQ : s .Q = m.a - m.b * s .P + m.c * s .y := h .Q
    have hP : s .P = (s .Q - m.d - m.f * s .w) / m.e + s .t := h .P
    have hS : s .Q = m.d + m.e * (s .P - s .t) + m.f * s .w := by
      rw [hP]
      field_simp
      ring
    rw [ht, hy, hw] at *
    have := (m.isEq_iff (exoOf u) (s .P) (s .Q)).1 ⟨hQ, hS⟩
    exact ⟨⟨rfl, rfl, rfl⟩, this⟩
  · rintro ⟨⟨ht, hy, hw⟩, hP, hQ⟩
    have heq := (m.isEq_iff (exoOf u) (s .P) (s .Q)).2 ⟨hP, hQ⟩
    obtain ⟨hD, hS⟩ := heq
    intro v
    cases v
    · exact ht
    · exact hy
    · exact hw
    · show s .P = (s .Q - m.d - m.f * s .w) / m.e + s .t
      rw [hS, ht, hw]
      simp only [exoOf]
      field_simp
      ring
    · show s .Q = m.a - m.b * s .P + m.c * s .y
      rw [hD, hy]
      rfl

/-- Markedet er blokkrekursivt. -/
theorem blockRecursive : m.scm.BlockRecursive rank where
  parents_le v mm hm p hp := by
    cases v <;> simp [scm] at hm <;> subst hm <;>
      simp [demandMech, supplyMech] at hp <;> rcases hp with rfl | rfl | rfl <;> simp [rank]
  block_unique u s t hs ht _ _ v _ := by
    obtain ⟨⟨st, sy, sw⟩, sP, sQ⟩ := (m.scm_solves_iff u s).1 hs
    obtain ⟨⟨tt, ty, tw⟩, tP, tQ⟩ := (m.scm_solves_iff u t).1 ht
    cases v
    · rw [st, tt]
    · rw [sy, ty]
    · rw [sw, tw]
    · rw [sP, tP]
    · rw [sQ, tQ]

/-- Entydig løsning. -/
theorem scm_unique {u s t : MV → ℝ} (hs : m.scm.Solves u s) (ht : m.scm.Solves u t) : s = t :=
  m.blockRecursive.unique hs ht

/-- do(skatt := t + Δ) i SCM-en gir lærebokas skatteinsidens: ΔP = e/(b+e)·Δ. -/
theorem do_tax_incidence (u s s' : MV → ℝ) (Δ : ℝ)
    (hs : m.scm.Solves u s) (hs' : (m.scm.doI .t (u .t + Δ)).Solves u s') :
    s' .P - s .P = m.e / (m.b + m.e) * Δ := by
  rw [SCM.doI_exo_iff m.scm _ u s' rfl] at hs'
  have h1 := ((m.scm_solves_iff u s).1 hs).2.1
  have h2 := ((m.scm_solves_iff _ s').1 hs').2.1
  rw [h1, h2]
  have hx : exoOf (Function.update u .t (u .t + Δ)) = { exoOf u with t := (exoOf u).t + Δ } := by
    simp [exoOf, Function.update]
  rw [hx]
  exact m.tax_passthrough (exoOf u) Δ

/-- do(P := c), en makspris, kutter tilbudsligningen. Mengden følger etterspørselen,
    og overskuddet av etterspørsel over tilbud er nøyaktig (b+e)(P* − c). -/
theorem do_price_excess_demand (u s : MV → ℝ) (c : ℝ)
    (h : (m.scm.doI .P c).Solves u s) :
    s .Q - (m.d + m.e * (c - u .t) + m.f * u .w) = (m.b + m.e) * (m.Pstar (exoOf u) - c) := by
  have hP : s .P = c := SCM.doI_self _ .P c u s h
  have hQ : s .Q = m.a - m.b * s .P + m.c * s .y :=
    SCM.doI_other m.scm (v := .Q) c u s m.demandMech (by decide) rfl h
  have hy : s .y = u .y := SCM.doI_exo m.scm (v := .y) c u s (by decide) rfl h
  have hbe : m.b + m.e ≠ 0 := m.sum_ne
  rw [hQ, hP, hy]
  unfold Pstar exoOf
  field_simp
  ring

/-- Makspris under likevektsprisen gir mangel (etterspørsel > tilbud). -/
theorem price_ceiling_shortage (u s : MV → ℝ) (c : ℝ)
    (h : (m.scm.doI .P c).Solves u s) (hc : c < m.Pstar (exoOf u)) :
    m.d + m.e * (c - u .t) + m.f * u .w < s .Q := by
  have := m.do_price_excess_demand u s c h
  have hpos : 0 < (m.b + m.e) * (m.Pstar (exoOf u) - c) := mul_pos m.sum_pos (by linarith)
  linarith

end Market

/-! ## 5. Inngrep inne i en syklus kan ødelegge entydig løsbarhet -/

inductive XYZ | x | y | z
deriving DecidableEq

/-- x := y,  y := x + z,  z := x − 1. Syklisk, men entydig: (1, 1, 0). -/
def cyc : SCM XYZ ℝ :=
  ⟨fun
    | .x => some ⟨[.y], fun s => s .y, by intro s t h; exact h .y (by simp)⟩
    | .y => some ⟨[.x, .z], fun s => s .x + s .z, by
        intro s t h
        show _ = _
        rw [h .x (by simp), h .z (by simp)]⟩
    | .z => some ⟨[.x], fun s => s .x - 1, by
        intro s t h
        show _ = _
        rw [h .x (by simp)]⟩⟩

theorem cyc_solves_iff (u s : XYZ → ℝ) : cyc.Solves u s ↔ s .x = 1 ∧ s .y = 1 ∧ s .z = 0 := by
  constructor
  · intro h
    have hx : s .x = s .y := h .x
    have hy : s .y = s .x + s .z := h .y
    have hz : s .z = s .x - 1 := h .z
    refine ⟨?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨hx, hy, hz⟩ v
    cases v
    · show s .x = s .y
      rw [hx, hy]
    · show s .y = s .x + s .z
      rw [hx, hy, hz]; norm_num
    · show s .z = s .x - 1
      rw [hx, hz]; norm_num

/-- Modellen er blokkrekursiv med én blokk. -/
theorem cyc_block : cyc.BlockRecursive (fun _ => 0) where
  parents_le _ _ _ _ _ := le_refl 0
  block_unique u s t hs ht _ _ v _ := by
    obtain ⟨a1, a2, a3⟩ := (cyc_solves_iff u s).1 hs
    obtain ⟨b1, b2, b3⟩ := (cyc_solves_iff u t).1 ht
    cases v
    · rw [a1, b1]
    · rw [a2, b2]
    · rw [a3, b3]

/-- do(z := 0): uendelig mange løsninger. Her er to ulike. -/
theorem cyc_do_z0_not_unique :
    ∃ u s t : XYZ → ℝ, (cyc.doI .z 0).Solves u s ∧ (cyc.doI .z 0).Solves u t ∧ s ≠ t := by
  refine ⟨fun _ => 0, fun _ => 0, fun | .z => 0 | _ => 1, ?_, ?_, ?_⟩
  · intro v
    cases v <;> simp [SCM.doI, SCM.Mech.const, cyc]
  · intro v
    cases v <;> simp [SCM.doI, SCM.Mech.const, cyc]
  · intro h
    have := congrFun h .x
    simp at this

/-- do(z := 1): ingen løsning i det hele tatt. -/
theorem cyc_do_z1_no_solution (u s : XYZ → ℝ) : ¬ (cyc.doI .z 1).Solves u s := by
  intro h
  have hz : s .z = 1 := SCM.doI_self cyc .z 1 u s h
  have hx : s .x = s .y := SCM.doI_other cyc (v := .x) 1 u s _ (by decide) rfl h
  have hy : s .y = s .x + s .z := SCM.doI_other cyc (v := .y) 1 u s _ (by decide) rfl h
  linarith

end CausalPhys
