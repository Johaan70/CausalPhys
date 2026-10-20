/-
  CausalPhys.Brouwer — Brouwers fikspunktteorem.

  Mathlib har ikke Brouwers teorem. Her bevises det for kuben [0,1]ⁿ (og
  dermed for alle lukkede rektangler), med Kuhns kombinatoriske rute:

    1. Freudenthal–Kuhn-trianguleringen av gitteret {0,…,k}ⁿ: et simpleks er
       et basispunkt v og en permutasjon τ (koordinat i økes ved «tid» τ i).
    2. Naboavbildningen på fasetter er en involusjon uten fikspunkter på de
       indre fasettene; randfasettene klassifiseres eksplisitt.
    3. Sperners lemma (kubeversjonen): med en merking som oppfyller
       randbetingelsene er antallet fullt merkede simplekser ODDE.
       Bevis ved induksjon på dimensjonen med «dør»-telling.
    4. Brouwer: en kontinuerlig f : [0,1]ⁿ → [0,1]ⁿ har et fikspunkt
       (uniform kontinuitet + finere og finere gitter).
-/
import CausalPhys.GaleNikaido

set_option linter.unusedSectionVars false

open Finset

namespace CausalPhys
namespace Brouwer

/-! ## 1. Telling av dører i ett simpleks -/

/-- Et simpleks med n+1 hjørner og merker L har (mod 2) like mange «dører»
    (fasetter med merkene 0,…,m−1) som det er fullt merket. -/
theorem doors_parity (m : ℕ) (L : Fin (m+1) → ℕ) (hL : ∀ j, L j ≤ m) :
    ((univ.filter (fun j => (univ.erase j).image L = range m)).card : ZMod 2)
      = if univ.image L = range (m+1) then 1 else 0 := by
  set A := univ.image L with hAdef
  have hAsub : A ⊆ range (m+1) := by
    intro x hx
    simp only [hAdef, mem_image, mem_univ, true_and] at hx
    obtain ⟨j, rfl⟩ := hx
    simp only [mem_range]; have := hL j; omega
  have hmemA : ∀ j, L j ∈ A := fun j => mem_image_of_mem L (mem_univ j)
  by_cases hfull : A = range (m+1)
  · rw [ite_eq_left hfull]
    have hinj : Function.Injective L := by
      have hc : A.card = (univ : Finset (Fin (m+1))).card := by rw [hfull]; simp
      have := Finset.card_image_iff.1 hc
      exact fun a b h => this (by simp) (by simp) h
    have hdoor : ∀ j, (univ.erase j).image L = range m ↔ L j = m := by
      intro j
      rw [Finset.image_erase hinj, ← hAdef, hfull]
      constructor
      · intro h
        by_contra hne
        have : m ∈ (range (m+1)).erase (L j) := by
          simp only [mem_erase, mem_range]; exact ⟨Ne.symm hne, by omega⟩
        rw [h] at this; simp at this
      · intro h
        rw [h, Finset.range_add_one, Finset.erase_insert (by simp)]
    have hset : univ.filter (fun j => (univ.erase j).image L = range m) = univ.filter (fun j => L j = m) := by
      ext j; simp [hdoor j]
    rw [hset]
    have hm : m ∈ A := by rw [hfull]; simp
    obtain ⟨j0, -, hj0⟩ := mem_image.1 hm
    have : univ.filter (fun j => L j = m) = {j0} := by
      ext j; simp only [mem_filter, mem_univ, true_and, mem_singleton]
      exact ⟨fun h => hinj (h.trans hj0.symm), fun h => h ▸ hj0⟩
    rw [this]; simp
  · rw [ite_eq_right hfull]
    by_cases hsub : range m ⊆ A
    · have hmA : m ∉ A := by
        intro hm
        apply hfull
        apply Finset.Subset.antisymm hAsub
        intro x hx
        rw [Finset.range_add_one, mem_insert] at hx
        rcases hx with rfl | hx
        · exact hm
        · exact hsub hx
      have hAeq : A = range m := by
        apply Finset.Subset.antisymm _ hsub
        intro x hx
        have h1 := hAsub hx
        simp only [mem_range] at h1 ⊢
        have : x ≠ m := fun h => hmA (h ▸ hx)
        omega
      set c : ℕ → ℕ := fun a => (univ.filter (fun j => L j = a)).card with hcdef
      have hsum : (m+1) = ∑ a ∈ range m, c a := by
        have := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (Fin (m+1)))) (t := range m)
          (f := L) (fun j _ => by rw [← hAeq]; exact hmemA j)
        simpa [c] using this
      have hc1 : ∀ a ∈ range m, 1 ≤ c a := by
        intro a ha
        rw [← hAeq] at ha
        obtain ⟨j, -, hj⟩ := mem_image.1 ha
        exact Finset.card_pos.2 ⟨j, by simp [hj]⟩
      obtain ⟨a0, ha0, hc2⟩ : ∃ a0 ∈ range m, 2 ≤ c a0 := by
        by_contra hcon
        push Not at hcon
        have : ∑ a ∈ range m, c a ≤ ∑ _a ∈ range m, 1 :=
          Finset.sum_le_sum fun a ha => by have := hcon a ha; omega
        simp at this; omega
      have hrest : ∀ a ∈ range m, a ≠ a0 → c a = 1 := by
        intro a ha hne
        by_contra hc
        have hca : 2 ≤ c a := by have := hc1 a ha; omega
        have h1 := Finset.add_sum_erase (range m) c ha0
        have ha' : a ∈ (range m).erase a0 := mem_erase.2 ⟨hne, ha⟩
        have h2 := Finset.add_sum_erase ((range m).erase a0) c ha'
        have h3 : (((range m).erase a0).erase a).card = m - 2 := by
          rw [card_erase_of_mem ha', card_erase_of_mem ha0, card_range]; omega
        have h4 : ∑ x ∈ ((range m).erase a0).erase a, 1 ≤ ∑ x ∈ ((range m).erase a0).erase a, c x :=
          Finset.sum_le_sum fun x hx => hc1 x (mem_of_mem_erase (mem_of_mem_erase hx))
        simp only [sum_const, smul_eq_mul, mul_one] at h4
        have hm2 : 2 ≤ m := by
          have : a0 < m := mem_range.1 ha0
          have : a < m := mem_range.1 ha
          omega
        omega
      have hc0 : c a0 = 2 := by
        have h1 := Finset.add_sum_erase (range m) c ha0
        have h4 : ∑ x ∈ (range m).erase a0, 1 ≤ ∑ x ∈ (range m).erase a0, c x :=
          Finset.sum_le_sum fun x hx => hc1 x (mem_of_mem_erase hx)
        simp only [sum_const, smul_eq_mul, mul_one, card_erase_of_mem ha0, card_range] at h4
        have : 1 ≤ m := by have := mem_range.1 ha0; omega
        omega
      have hdoor : ∀ j, (univ.erase j).image L = range m ↔ L j = a0 := by
        intro j
        constructor
        · intro h
          by_contra hne
          have hLj : L j ∈ range m := by rw [← hAeq]; exact hmemA j
          have hc := hrest (L j) hLj hne
          rw [← h] at hLj
          obtain ⟨j', hj', hLj'⟩ := mem_image.1 hLj
          have hj'ne : j' ≠ j := ne_of_mem_erase hj'
          have : 2 ≤ c (L j) := by
            have hsub2 : ({j, j'} : Finset (Fin (m+1))) ⊆ univ.filter (fun i => L i = L j) := by
              intro x hx
              simp only [mem_insert, mem_singleton] at hx
              rcases hx with rfl | rfl <;> simp [hLj']
            have := Finset.card_le_card hsub2
            rw [Finset.card_pair (Ne.symm hj'ne)] at this
            exact this
          omega
        · intro h
          apply Finset.Subset.antisymm
          · intro x hx
            rw [← hAeq]
            obtain ⟨i, -, rfl⟩ := mem_image.1 hx
            exact hmemA i
          · intro a ha
            by_cases haa : a = a0
            · subst haa
              have hlt : 1 < (univ.filter (fun i => L i = a)).card := by
                have : c a = 2 := hc0
                simp only [c] at this; omega
              obtain ⟨j', hj', hne⟩ := Finset.exists_mem_ne hlt j
              exact mem_image.2 ⟨j', mem_erase.2 ⟨hne, mem_univ _⟩, (mem_filter.1 hj').2⟩
            · rw [← hAeq] at ha
              obtain ⟨j', -, hj'⟩ := mem_image.1 ha
              have hne : j' ≠ j := by
                intro he; subst he; exact haa (hj'.symm.trans h)
              exact mem_image.2 ⟨j', mem_erase.2 ⟨hne, mem_univ _⟩, hj'⟩
      have hset : univ.filter (fun j => (univ.erase j).image L = range m)
          = univ.filter (fun j => L j = a0) := by
        ext j; simp [hdoor j]
      rw [hset]
      have : (univ.filter (fun j => L j = a0)).card = 2 := hc0
      rw [this]; rfl
    · have : univ.filter (fun j => (univ.erase j).image L = range m) = ∅ := by
        apply Finset.filter_false_of_mem
        intro j _ h
        apply hsub
        rw [← h]
        intro x hx
        obtain ⟨i, -, rfl⟩ := mem_image.1 hx
        exact hmemA i
      rw [this]; simp


/-! ## 2. Freudenthal–Kuhn-trianguleringen -/

/-- Et simpleks i trianguleringen av {0,…,k}ᵐ: basispunkt v og «tider» τ.
    Hjørne j er v + Σ{ eᵢ : τ i < j }. -/
abbrev Sx (m k : ℕ) := (Fin m → Fin k) × Equiv.Perm (Fin m)

def vert {m k : ℕ} (S : Sx m k) (j : Fin (m+1)) : Fin m → ℕ :=
  fun i => (S.1 i : ℕ) + if ((S.2 i : Fin m) : ℕ) < (j : ℕ) then 1 else 0

theorem vert_le {m k : ℕ} (S : Sx m k) (j : Fin (m+1)) (i : Fin m) : vert S j i ≤ k := by
  unfold vert; have := (S.1 i).isLt; split_ifs <;> omega

theorem coe_rot {n : ℕ} (x : Fin (n+1)) :
    ((finRotate (n+1) x : Fin (n+1)) : ℕ) = if x = Fin.last n then 0 else (x : ℕ) + 1 :=
  coe_finRotate x

theorem coe_rot_inv {n : ℕ} (x : Fin (n+1)) :
    (((finRotate (n+1))⁻¹ x : Fin (n+1)) : ℕ) = if (x : ℕ) = 0 then n else (x : ℕ) - 1 := by
  set y := (finRotate (n+1))⁻¹ x with hy
  have hx : finRotate (n+1) y = x := by rw [hy]; simp
  have h := coe_rot y
  rw [hx] at h
  by_cases hl : y = Fin.last n
  · rw [ite_eq_left hl] at h; rw [ite_eq_left h, hl]; simp
  · rw [ite_eq_right hl] at h
    have : (y : ℕ) < n := Fin.val_lt_last hl
    rw [ite_eq_right (by omega)]; omega

variable {n k : ℕ}

/-- Nabo over fasetten uten hjørne 0. -/
def up0 (S : Sx (n+1) k) (h : (S.1 (S.2⁻¹ 0) : ℕ) + 1 < k) : Sx (n+1) k :=
  (Function.update S.1 (S.2⁻¹ 0) ⟨_, h⟩, (finRotate (n+1))⁻¹ * S.2)

/-- Nabo over fasetten uten det siste hjørnet. -/
def dnL (S : Sx (n+1) k) (h : 0 < (S.1 (S.2⁻¹ (Fin.last n)) : ℕ)) : Sx (n+1) k :=
  (Function.update S.1 (S.2⁻¹ (Fin.last n))
    ⟨(S.1 (S.2⁻¹ (Fin.last n)) : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) (S.1 _).isLt⟩,
    finRotate (n+1) * S.2)

/-- Nabo over en indre fasett: bytt to nabotider. -/
def sw (S : Sx (n+1) k) (j : Fin (n+2)) (hl : j ≠ Fin.last (n+1)) : Sx (n+1) k :=
  (S.1, Equiv.swap (⟨(j : ℕ) - 1, by have := Fin.val_lt_last hl; omega⟩ : Fin (n+1))
    ⟨j, Fin.val_lt_last hl⟩ * S.2)

/-- Naboavbildningen på fasetter; `none` betyr randfasett. -/
def nb (S : Sx (n+1) k) (j : Fin (n+2)) : Option (Sx (n+1) k × Fin (n+2)) :=
  if j = 0 then
    if h : (S.1 (S.2⁻¹ 0) : ℕ) + 1 < k then some (up0 S h, Fin.last _) else none
  else if hl : j = Fin.last (n+1) then
    if h : 0 < (S.1 (S.2⁻¹ (Fin.last n)) : ℕ) then some (dnL S h, 0) else none
  else some (sw S j hl, j)

theorem last_ne_zero' : (Fin.last (n+1) : Fin (n+2)) ≠ 0 := by
  intro h; have := congrArg Fin.val h; simp at this

theorem up0_fst_val (S : Sx (n+1) k) (h) (i : Fin (n+1)) :
    ((up0 S h).1 i : ℕ) = if i = S.2⁻¹ 0 then (S.1 i : ℕ) + 1 else S.1 i := by
  by_cases hi : i = S.2⁻¹ 0
  · rw [ite_eq_left hi, hi]; simp [up0]
  · rw [ite_eq_right hi]; simp only [up0]; rw [Function.update_of_ne hi]

theorem dnL_fst_val (S : Sx (n+1) k) (h) (i : Fin (n+1)) :
    ((dnL S h).1 i : ℕ) = if i = S.2⁻¹ (Fin.last n) then (S.1 i : ℕ) - 1 else S.1 i := by
  by_cases hi : i = S.2⁻¹ (Fin.last n)
  · rw [ite_eq_left hi, hi]; simp [dnL]
  · rw [ite_eq_right hi]; simp only [dnL]; rw [Function.update_of_ne hi]

theorem up0_snd_val (S : Sx (n+1) k) (h) (i : Fin (n+1)) :
    ((up0 S h).2 i : ℕ) = if ((S.2 i : Fin (n+1)) : ℕ) = 0 then n else (S.2 i : ℕ) - 1 := by
  simp only [up0, Equiv.Perm.mul_apply]
  exact coe_rot_inv _

theorem dnL_snd_val (S : Sx (n+1) k) (h) (i : Fin (n+1)) :
    ((dnL S h).2 i : ℕ) = if S.2 i = Fin.last n then 0 else (S.2 i : ℕ) + 1 := by
  simp only [dnL, Equiv.Perm.mul_apply]
  exact coe_rot _

theorem vert_up0 (S : Sx (n+1) k) (h) (t : Fin (n+1)) :
    vert (up0 S h) t.castSucc = vert S t.succ := by
  funext i
  have ht := t.isLt
  simp only [vert, up0_fst_val, up0_snd_val, Fin.val_castSucc, Fin.val_succ]
  by_cases hi : i = S.2⁻¹ 0
  · have h2 : ((S.2 i : Fin (n+1)) : ℕ) = 0 := by rw [hi]; simp
    simp only [ite_eq_left hi, h2, ite_true]
    split_ifs <;> omega
  · have hv : ((S.2 i : Fin (n+1)) : ℕ) ≠ 0 := by
      intro h0
      apply hi
      rw [Equiv.Perm.eq_inv_iff_eq]
      exact Fin.ext h0
    simp only [ite_eq_right hi, ite_eq_right hv]
    split_ifs <;> omega

theorem vert_dnL (S : Sx (n+1) k) (h) (t : Fin (n+1)) :
    vert (dnL S h) t.succ = vert S t.castSucc := by
  funext i
  have ht := t.isLt
  simp only [vert, dnL_fst_val, dnL_snd_val, Fin.val_castSucc, Fin.val_succ]
  by_cases hi : i = S.2⁻¹ (Fin.last n)
  · have h2 : S.2 i = Fin.last n := by rw [hi]; simp
    have h3 : 0 < (S.1 i : ℕ) := by rw [hi]; exact h
    simp only [ite_eq_left hi, h2, ite_true, Fin.val_last]
    split_ifs <;> omega
  · have hv : S.2 i ≠ Fin.last n := by
      intro h0
      apply hi
      rw [Equiv.Perm.eq_inv_iff_eq]
      exact h0
    simp only [ite_eq_right hi, ite_eq_right hv]
    split_ifs <;> omega

theorem vert_sw (S : Sx (n+1) k) (j : Fin (n+2)) (hj0 : j ≠ 0) (hl : j ≠ Fin.last (n+1))
    (t : Fin (n+2)) (ht : t ≠ j) : vert (sw S j hl) t = vert S t := by
  have hj1 : 1 ≤ (j : ℕ) := by
    rcases Nat.eq_zero_or_pos (j : ℕ) with h | h
    · exact absurd (Fin.ext h) hj0
    · exact h
  have hjl : (j : ℕ) < n + 1 := Fin.val_lt_last hl
  have htj : (t : ℕ) ≠ j := fun h => ht (Fin.ext h)
  have key : ∀ x : Fin (n+1),
      ((Equiv.swap (⟨(j : ℕ) - 1, by omega⟩ : Fin (n+1)) ⟨j, hjl⟩ x : Fin (n+1)) : ℕ) < t
        ↔ (x : ℕ) < t := by
    intro x
    rcases eq_or_ne x ⟨(j : ℕ) - 1, by omega⟩ with hxp | hxp
    · rw [hxp, Equiv.swap_apply_left]
      simp only
      omega
    · rcases eq_or_ne x ⟨j, hjl⟩ with hxq | hxq
      · rw [hxq, Equiv.swap_apply_right]
        simp only
        omega
      · rw [Equiv.swap_apply_of_ne_of_ne hxp hxq]
  funext i
  simp only [vert, sw, Equiv.Perm.mul_apply, key]

/-! ### Involusjon -/

theorem up0_dnL (S : Sx (n+1) k) (h) (h') : dnL (up0 S h) h' = S := by
  have ha : (up0 S h).2⁻¹ (Fin.last n) = S.2⁻¹ 0 := by
    simp only [up0, mul_inv_rev, inv_inv, Equiv.Perm.mul_apply, finRotate_last]
  ext i
  · simp only [dnL_fst_val, up0_fst_val, ha]
    split_ifs <;> omega
  · simp [dnL, up0]

theorem dnL_up0 (S : Sx (n+1) k) (h) (h') : up0 (dnL S h) h' = S := by
  have hb : (finRotate (n+1))⁻¹ 0 = Fin.last n := by
    rw [Equiv.Perm.inv_eq_iff_eq, finRotate_last]
  have ha : (dnL S h).2⁻¹ 0 = S.2⁻¹ (Fin.last n) := by
    simp only [dnL, mul_inv_rev, Equiv.Perm.mul_apply, hb]
  ext i
  · simp only [dnL_fst_val, up0_fst_val, ha]
    split_ifs with h1 <;> try omega
    subst h1
    omega
  · simp [dnL, up0]

theorem sw_sw (S : Sx (n+1) k) (j : Fin (n+2)) (hl) : sw (sw S j hl) j hl = S := by
  simp [sw, Equiv.swap_mul_self_mul]

theorem sw_ne (S : Sx (n+1) k) (j : Fin (n+2)) (hj0 : j ≠ 0) (hl) : sw S j hl ≠ S := by
  intro h
  have h2 := congrArg Prod.snd h
  simp only [sw] at h2
  have : Equiv.swap (⟨(j : ℕ) - 1, by have := Fin.val_lt_last hl; omega⟩ : Fin (n+1))
      ⟨j, Fin.val_lt_last hl⟩ = 1 := by
    have := congrArg (· * S.2⁻¹) h2
    simpa using this
  have hj1 : 1 ≤ (j : ℕ) := by
    rcases Nat.eq_zero_or_pos (j : ℕ) with h | h
    · exact absurd (Fin.ext h) hj0
    · exact h
  have h3 := congrArg (fun e : Equiv.Perm (Fin (n+1)) => (e ⟨(j:ℕ) - 1, by have := Fin.val_lt_last hl; omega⟩ : ℕ)) this
  simp only [Equiv.swap_apply_left, Equiv.Perm.coe_one, id] at h3
  omega

theorem nb_invol (S : Sx (n+1) k) (j : Fin (n+2)) {T : Sx (n+1) k} {j' : Fin (n+2)}
    (h : nb S j = some (T, j')) : nb T j' = some (S, j) ∧ (T, j') ≠ (S, j) := by
  unfold nb at h
  by_cases h0 : j = 0
  · rw [ite_eq_left h0] at h
    by_cases hk : (S.1 (S.2⁻¹ 0) : ℕ) + 1 < k
    · rw [dite_eq_left hk] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have h' : 0 < ((up0 S hk).1 ((up0 S hk).2⁻¹ (Fin.last n)) : ℕ) := by
        simp [up0, finRotate_last]
      refine ⟨?_, ?_⟩
      · unfold nb
        rw [ite_eq_right last_ne_zero', dite_eq_left rfl, dite_eq_left h', up0_dnL, h0]
      · intro he
        have := congrArg Prod.snd he
        simp only at this
        rw [h0] at this
        exact last_ne_zero' this
    · rw [dite_eq_right hk] at h; exact absurd h (by simp)
  · rw [ite_eq_right h0] at h
    by_cases hl : j = Fin.last (n+1)
    · rw [dite_eq_left hl] at h
      by_cases hk : 0 < (S.1 (S.2⁻¹ (Fin.last n)) : ℕ)
      · rw [dite_eq_left hk] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have h' : ((dnL S hk).1 ((dnL S hk).2⁻¹ 0) : ℕ) + 1 < k := by
          have hb : (finRotate (n+1))⁻¹ 0 = Fin.last n := by
            rw [Equiv.Perm.inv_eq_iff_eq, finRotate_last]
          simp only [dnL, mul_inv_rev, Equiv.Perm.mul_apply, hb, Function.update_self]
          have := (S.1 (S.2⁻¹ (Fin.last n))).isLt
          omega
        refine ⟨?_, ?_⟩
        · unfold nb
          rw [ite_eq_left rfl, dite_eq_left h', dnL_up0, hl]
        · intro he
          have := congrArg Prod.snd he
          simp only at this
          exact h0 this.symm
      · rw [dite_eq_right hk] at h; exact absurd h (by simp)
    · rw [dite_eq_right hl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨?_, ?_⟩
      · unfold nb
        rw [ite_eq_right h0, dite_eq_right hl, sw_sw]
      · intro he
        exact sw_ne S j h0 hl (congrArg Prod.fst he)

/-! ### Fasetter -/

theorem mem_facet_zero {α : Type*} [DecidableEq α] (f : Fin (n+2) → α) (x : α) :
    x ∈ (univ.erase 0).image f ↔ ∃ s : Fin (n+1), f s.succ = x := by
  constructor
  · rintro hx
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hx
    have ht0 : t ≠ 0 := ne_of_mem_erase ht
    exact ⟨t.pred ht0, by simp⟩
  · rintro ⟨s, rfl⟩
    exact mem_image.2 ⟨s.succ, mem_erase.2 ⟨Fin.succ_ne_zero s, mem_univ _⟩, rfl⟩

theorem mem_facet_last {α : Type*} [DecidableEq α] (f : Fin (n+2) → α) (x : α) :
    x ∈ (univ.erase (Fin.last (n+1))).image f ↔ ∃ s : Fin (n+1), f s.castSucc = x := by
  constructor
  · rintro hx
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hx
    have htl : t ≠ Fin.last (n+1) := ne_of_mem_erase ht
    exact ⟨t.castPred htl, by simp⟩
  · rintro ⟨s, rfl⟩
    exact mem_image.2 ⟨s.castSucc, mem_erase.2 ⟨Fin.castSucc_ne_last s, mem_univ _⟩, rfl⟩

/-- Nabofasetter har de samme merkene. -/
theorem nb_labels (ℓ : (Fin (n+1) → ℕ) → ℕ) (S : Sx (n+1) k) (j : Fin (n+2))
    {T : Sx (n+1) k} {j' : Fin (n+2)} (h : nb S j = some (T, j')) :
    (univ.erase j).image (fun t => ℓ (vert S t)) = (univ.erase j').image (fun t => ℓ (vert T t)) := by
  unfold nb at h
  by_cases h0 : j = 0
  · rw [ite_eq_left h0] at h
    by_cases hk : (S.1 (S.2⁻¹ 0) : ℕ) + 1 < k
    · rw [dite_eq_left hk] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      subst h0
      ext x
      rw [mem_facet_zero, mem_facet_last]
      simp only [vert_up0]
    · rw [dite_eq_right hk] at h; exact absurd h (by simp)
  · rw [ite_eq_right h0] at h
    by_cases hl : j = Fin.last (n+1)
    · rw [dite_eq_left hl] at h
      by_cases hk : 0 < (S.1 (S.2⁻¹ (Fin.last n)) : ℕ)
      · rw [dite_eq_left hk] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        subst hl
        ext x
        rw [mem_facet_zero, mem_facet_last]
        simp only [vert_dnL]
      · rw [dite_eq_right hk] at h; exact absurd h (by simp)
    · rw [dite_eq_right hl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      ext x
      simp only [mem_image, mem_erase, mem_univ, and_true]
      constructor
      · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, by rw [vert_sw S j h0 hl t ht]⟩
      · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, by rw [vert_sw S j h0 hl t ht]⟩


/-! ## 3. Sperners lemma for kuben -/

/-- En fikspunkt-ærlig merking av gitteret {0,…,k}ᵐ med merkene 0,…,m. -/
structure Labeling (m k : ℕ) (ℓ : (Fin m → ℕ) → ℕ) : Prop where
  A : ∀ p : Fin m → ℕ, (∀ i, p i ≤ k) → ∀ i : Fin m, p i = 0 → ℓ p ≠ i
  B : ∀ p : Fin m → ℕ, (∀ i, p i ≤ k) → ∀ i : Fin m, p i = k → ℓ p ≤ i
  R : ∀ p : Fin m → ℕ, (∀ i, p i ≤ k) → ℓ p ≤ m

/-- Fullt merket simpleks. -/
def full {m k : ℕ} (ℓ : (Fin m → ℕ) → ℕ) (S : Sx m k) : Prop :=
  univ.image (fun j => ℓ (vert S j)) = range (m+1)

/-- Dør: fasett med merkene 0,…,m−1. -/
def door {m k : ℕ} (ℓ : (Fin m → ℕ) → ℕ) (S : Sx m k) (j : Fin (m+1)) : Prop :=
  (univ.erase j).image (fun t => ℓ (vert S t)) = range m

instance {m k : ℕ} (ℓ : (Fin m → ℕ) → ℕ) : DecidablePred (full (k := k) ℓ) :=
  fun S => by unfold full; infer_instance

instance {m k : ℕ} (ℓ : (Fin m → ℕ) → ℕ) (S : Sx m k) : DecidablePred (door ℓ S) :=
  fun j => by unfold door; infer_instance

theorem even_card_of_invol {α : Type*} [DecidableEq α] : ∀ (c : ℕ) (s : Finset α) (g : α → α),
    s.card = c → (∀ x ∈ s, g x ∈ s) → (∀ x ∈ s, g (g x) = x) → (∀ x ∈ s, g x ≠ x) → Even c := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
  intro s g hc hs hg hne
  rcases s.eq_empty_or_nonempty with h0 | ⟨x, hx⟩
  · rw [h0] at hc; simp at hc; subst hc; exact ⟨0, rfl⟩
  · have hgx : g x ∈ s.erase x := mem_erase.2 ⟨hne x hx, hs x hx⟩
    set s' := (s.erase x).erase (g x)
    have hc' : s'.card + 2 = c := by
      rw [card_erase_of_mem hgx, card_erase_of_mem hx, ← hc]
      have : 2 ≤ s.card := Finset.one_lt_card.2 ⟨x, hx, g x, hs x hx, (hne x hx).symm⟩
      omega
    have hcl : ∀ y ∈ s', g y ∈ s' := by
      intro y hy
      have hy1 : y ≠ g x := ne_of_mem_erase hy
      have hy2 : y ≠ x := ne_of_mem_erase (mem_of_mem_erase hy)
      have hys : y ∈ s := mem_of_mem_erase (mem_of_mem_erase hy)
      refine mem_erase.2 ⟨?_, mem_erase.2 ⟨?_, hs y hys⟩⟩
      · intro h; apply hy2; rw [← hg y hys, h, hg x hx]
      · intro h; apply hy1; rw [← hg y hys, h]
    have := ih s'.card (by omega) s' g rfl hcl
      (fun y hy => hg y (mem_of_mem_erase (mem_of_mem_erase hy)))
      (fun y hy => hne y (mem_of_mem_erase (mem_of_mem_erase hy)))
    obtain ⟨r, hr⟩ := this
    exact ⟨r + 1, by omega⟩

/-! ### Sideflaten x_last = k -/

def liftFun (σ : Equiv.Perm (Fin n)) : Fin (n+1) → Fin (n+1) :=
  fun x => Fin.lastCases 0 (fun i => (σ i).succ) x

theorem liftFun_inj (σ : Equiv.Perm (Fin n)) : Function.Injective (liftFun σ) := by
  intro x y h
  induction x using Fin.lastCases with
  | last =>
    induction y using Fin.lastCases with
    | last => rfl
    | cast j =>
      simp only [liftFun, Fin.lastCases_last, Fin.lastCases_castSucc] at h
      exact absurd h.symm (Fin.succ_ne_zero _)
  | cast i =>
    induction y using Fin.lastCases with
    | last =>
      simp only [liftFun, Fin.lastCases_last, Fin.lastCases_castSucc] at h
      exact absurd h (Fin.succ_ne_zero _)
    | cast j =>
      simp only [liftFun, Fin.lastCases_castSucc, Fin.succ_inj, EmbeddingLike.apply_eq_iff_eq] at h
      rw [h]

noncomputable def lift (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n+1)) :=
  Equiv.ofBijective (liftFun σ) (Finite.injective_iff_bijective.1 (liftFun_inj σ))

@[simp] theorem lift_castSucc (σ : Equiv.Perm (Fin n)) (i : Fin n) : lift σ i.castSucc = (σ i).succ := by
  simp [lift, liftFun]

@[simp] theorem lift_last (σ : Equiv.Perm (Fin n)) : lift σ (Fin.last n) = 0 := by
  simp [lift, liftFun]

/-- Et simpleks på sideflaten løftet til et simpleks i én dimensjon høyere. -/
noncomputable def Φ (hk : 0 < k) (W : Sx n k) : Sx (n+1) k :=
  (Fin.snoc (α := fun _ => Fin k) W.1 ⟨k - 1, by omega⟩, lift W.2)

/-- Merkingen av sideflaten. -/
def faceL (k : ℕ) (ℓ : (Fin (n+1) → ℕ) → ℕ) : (Fin n → ℕ) → ℕ :=
  fun w => ℓ (Fin.snoc (α := fun _ => ℕ) w k)

theorem vert_Φ (hk : 0 < k) (W : Sx n k) (t : Fin (n+1)) :
    vert (Φ hk W) t.succ = Fin.snoc (α := fun _ => ℕ) (vert W t) k := by
  funext x
  induction x using Fin.lastCases with
  | last =>
    simp only [vert, Φ, Fin.snoc_last, lift_last, Fin.val_zero, Fin.val_succ]
    simp only [show (0:ℕ) < (t:ℕ) + 1 by omega, ite_true]
    omega
  | cast i =>
    simp only [vert, Φ, Fin.snoc_castSucc, lift_castSucc, Fin.val_succ, Fin.val_castSucc]
    simp only [Nat.add_lt_add_iff_right]

theorem snoc_grid {w : Fin n → ℕ} (hw : ∀ i, w i ≤ k) :
    ∀ i, Fin.snoc (α := fun _ => ℕ) w k i ≤ k := by
  intro i
  induction i using Fin.lastCases with
  | last => simp
  | cast i => simp [hw i]

theorem face_labeling {ℓ : (Fin (n+1) → ℕ) → ℕ} (hL : Labeling (n+1) k ℓ) :
    Labeling n k (faceL k ℓ) where
  A p hp i h0 := by
    have := hL.A _ (snoc_grid hp) i.castSucc (by simp [h0])
    simpa [faceL] using this
  B p hp i hk' := by
    have := hL.B _ (snoc_grid hp) i.castSucc (by simp [hk'])
    simpa [faceL] using this
  R p hp := by
    have := hL.B _ (snoc_grid hp) (Fin.last n) (by simp)
    simpa [faceL] using this

theorem door_Φ (hk : 0 < k) (ℓ : (Fin (n+1) → ℕ) → ℕ) (W : Sx n k) :
    door ℓ (Φ hk W) 0 ↔ full (faceL k ℓ) W := by
  unfold door full
  have : (univ.erase 0).image (fun t => ℓ (vert (Φ hk W) t))
      = univ.image (fun t => faceL k ℓ (vert W t)) := by
    ext x
    rw [mem_facet_zero]
    simp [vert_Φ, faceL]
  rw [this]

theorem Φ_inv_zero (hk : 0 < k) (W : Sx n k) : (Φ hk W).2⁻¹ 0 = Fin.last n := by
  rw [Equiv.Perm.inv_eq_iff_eq]; simp [Φ]

theorem nb_Φ (hk : 0 < k) (W : Sx n k) : nb (Φ hk W) 0 = none := by
  unfold nb
  rw [ite_eq_left rfl, dite_eq_right]
  rw [Φ_inv_zero]
  simp only [Φ, Fin.snoc_last]
  omega

theorem Φ_inj (hk : 0 < k) {W W' : Sx n k} (h : Φ hk W = Φ hk W') : W = W' := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [Φ] at h1 h2
  ext i
  · have := congrFun h1 i.castSucc
    simp only [Fin.snoc_castSucc] at this
    rw [this]
  · have := congrArg (fun e : Equiv.Perm (Fin (n+1)) => e i.castSucc) h2
    simp only [lift_castSucc, Fin.succ_inj] at this
    rw [this]

/-! ### Hovedteoremet -/

theorem card_Sx_zero (k : ℕ) : Fintype.card (Sx 0 k) = 1 := by
  simp [Fintype.card_prod, Fintype.card_perm]

/-- **Sperners lemma (kubeversjonen).** Antallet fullt merkede simplekser er odde. -/
theorem sperner : ∀ (m k : ℕ), 0 < k → ∀ ℓ : (Fin m → ℕ) → ℕ, Labeling m k ℓ →
    Odd (univ.filter (full (k := k) ℓ)).card := by
  intro m
  induction m with
  | zero =>
    intro k hk ℓ hL
    have hall : ∀ S : Sx 0 k, full ℓ S := by
      intro S
      have h := hL.R (vert S 0) (fun i => i.elim0)
      unfold full
      ext x
      simp only [mem_image, mem_univ, true_and, mem_range]
      constructor
      · rintro ⟨j, rfl⟩
        have : j = 0 := Fin.ext (by have := j.isLt; omega)
        rw [this]; omega
      · intro hx
        exact ⟨0, by omega⟩
    rw [Finset.filter_true_of_mem (fun S _ => hall S), Finset.card_univ, card_Sx_zero]
    exact odd_one
  | succ n ih =>
    intro k hk ℓ hL
    set D := (univ : Finset (Sx (n+1) k × Fin (n+2))).filter (fun p => door ℓ p.1 p.2) with hDdef
    -- (1) dører talt per simpleks
    have hD : (D.card : ZMod 2) = ((univ.filter (full (k := k) ℓ)).card : ZMod 2) := by
      have h1 : D.card = ∑ S : Sx (n+1) k, (univ.filter (fun j => door ℓ S j)).card := by
        rw [hDdef, Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product]
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [Finset.card_filter]
      rw [h1, Nat.cast_sum]
      have h2 : ∀ S : Sx (n+1) k, ((univ.filter (fun j => door ℓ S j)).card : ZMod 2)
          = if full ℓ S then 1 else 0 := by
        intro S
        have := doors_parity (n+1) (fun t => ℓ (vert S t))
          (fun j => hL.R _ (vert_le S j))
        simpa [door, full] using this
      rw [Finset.sum_congr rfl fun S _ => h2 S, Finset.sum_boole]
    -- (2) indre dører kommer i par
    set Dint := D.filter (fun p => nb p.1 p.2 ≠ none) with hDint
    set Dbd := D.filter (fun p => ¬ (nb p.1 p.2 ≠ none)) with hDbd
    have hsplit : Dint.card + Dbd.card = D.card := Finset.card_filter_add_card_filter_not _
    have heven : Even Dint.card := by
      refine even_card_of_invol _ Dint (fun p => (nb p.1 p.2).getD p) rfl ?_ ?_ ?_
      · intro p hp
        obtain ⟨hpD, hpn⟩ := mem_filter.1 hp
        obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.1 hpn
        obtain ⟨hinv, -⟩ := nb_invol p.1 p.2 (T := q.1) (j' := q.2) (by rw [hq])
        rw [hq]
        simp only [Option.getD_some]
        refine mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, ?_⟩, by rw [hinv]; simp⟩
        have hl := nb_labels ℓ p.1 p.2 (T := q.1) (j' := q.2) (by rw [hq])
        have hpd := (mem_filter.1 hpD).2
        unfold door at hpd ⊢
        rw [← hl]; exact hpd
      · intro p hp
        obtain ⟨-, hpn⟩ := mem_filter.1 hp
        obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.1 hpn
        obtain ⟨hinv, -⟩ := nb_invol p.1 p.2 (T := q.1) (j' := q.2) (by rw [hq])
        simp only [hq, Option.getD_some, hinv]
      · intro p hp
        obtain ⟨-, hpn⟩ := mem_filter.1 hp
        obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.1 hpn
        obtain ⟨-, hne⟩ := nb_invol p.1 p.2 (T := q.1) (j' := q.2) (by rw [hq])
        simp only [hq, Option.getD_some]
        exact hne
    -- (3) randdørene svarer til fullt merkede simplekser på sideflaten
    have hbd : Dbd.card = (univ.filter (full (k := k) (faceL k ℓ))).card := by
      symm
      refine Finset.card_bij (fun W _ => (Φ hk W, (0 : Fin (n+2)))) ?_ ?_ ?_
      · intro W hW
        refine mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, ?_⟩, ?_⟩
        · exact (door_Φ hk ℓ W).2 (mem_filter.1 hW).2
        · simp [nb_Φ]
      · intro W _ W' _ h
        exact Φ_inj hk (congrArg Prod.fst h)
      · rintro ⟨S, j⟩ hp
        obtain ⟨hpD, hpn⟩ := mem_filter.1 hp
        have hdoor : door ℓ S j := (mem_filter.1 hpD).2
        have hnone : nb S j = none := by simpa using hpn
        -- j = 0
        have hj0 : j = 0 := by
          by_contra hj0
          unfold nb at hnone
          rw [ite_eq_right hj0] at hnone
          by_cases hl : j = Fin.last (n+1)
          · rw [dite_eq_left hl] at hnone
            by_cases hk' : 0 < (S.1 (S.2⁻¹ (Fin.last n)) : ℕ)
            · rw [dite_eq_left hk'] at hnone; exact absurd hnone (by simp)
            · set b := S.2⁻¹ (Fin.last n) with hb
              have hb0 : (S.1 b : ℕ) = 0 := by omega
              have hSb : S.2 b = Fin.last n := by rw [hb]; simp
              have hbmem : (b : ℕ) ∈ range (n+1) := mem_range.2 b.isLt
              unfold door at hdoor
              rw [← hdoor, hl, mem_facet_last] at hbmem
              obtain ⟨s, hs⟩ := hbmem
              have hv : vert S s.castSucc b = 0 := by
                simp only [vert, hSb, Fin.val_last, Fin.val_castSucc, hb0]
                have := s.isLt
                simp only [show ¬ (n < (s : ℕ)) by omega, ite_false]
              exact hL.A _ (vert_le S _) b hv hs
          · rw [dite_eq_right hl] at hnone; exact absurd hnone (by simp)
        subst hj0
        unfold nb at hnone
        rw [ite_eq_left rfl] at hnone
        set a := S.2⁻¹ 0 with ha
        have hk' : ¬ ((S.1 a : ℕ) + 1 < k) := by
          intro h; rw [dite_eq_left h] at hnone; exact absurd hnone (by simp)
        have hSa : S.2 a = 0 := by rw [ha]; simp
        have hva : (S.1 a : ℕ) = k - 1 := by have := (S.1 a).isLt; omega
        -- a er den siste koordinaten
        have hal : a = Fin.last n := by
          have hnmem : n ∈ range (n+1) := by simp
          unfold door at hdoor
          rw [← hdoor, mem_facet_zero] at hnmem
          obtain ⟨s, hs⟩ := hnmem
          have hv : vert S s.succ a = k := by
            simp only [vert, hSa, Fin.val_zero, Fin.val_succ, hva]
            simp only [show (0:ℕ) < (s:ℕ) + 1 by omega, ite_true]
            omega
          have := hL.B _ (vert_le S _) a hv
          rw [hs] at this
          exact Fin.ext (le_antisymm (Nat.lt_succ_iff.1 a.isLt) this)
        have hSl : S.2 (Fin.last n) = 0 := by rw [← hal]; exact hSa
        -- konstruer simplekset på sideflaten
        have hne : ∀ i : Fin n, S.2 i.castSucc ≠ 0 := by
          intro i h
          have := S.2.injective (h.trans hSl.symm)
          exact Fin.castSucc_ne_last i this
        let σf : Fin n → Fin n := fun i => (S.2 i.castSucc).pred (hne i)
        have hσinj : Function.Injective σf := by
          intro i j h
          simp only [σf, Fin.pred_inj] at h
          exact Fin.castSucc_injective _ (S.2.injective h)
        let W : Sx n k := (fun i => S.1 i.castSucc,
          Equiv.ofBijective σf (Finite.injective_iff_bijective.1 hσinj))
        have hW : Φ hk W = S := by
          ext x
          · induction x using Fin.lastCases with
            | last =>
              simp only [Φ, Fin.snoc_last]
              rw [← hal, hva]
            | cast i => simp [Φ, W]
          · induction x using Fin.lastCases with
            | last => simp [Φ, hSl]
            | cast i => simp [Φ, W, σf]
        refine ⟨W, mem_filter.2 ⟨mem_univ _, ?_⟩, ?_⟩
        · rw [← door_Φ hk ℓ W, hW]; exact hdoor
        · simp only [hW]
    have hodd := ih k hk (faceL k ℓ) (face_labeling hL)
    rw [← ZMod.natCast_eq_one_iff_odd, ← hD, ← hsplit, Nat.cast_add,
      (ZMod.natCast_eq_zero_iff_even).2 heven, hbd, (ZMod.natCast_eq_one_iff_odd).2 hodd, zero_add]


/-! ## 4. Brouwers fikspunktteorem for kuben -/

theorem vert_close {m k : ℕ} (S : Sx m k) (j j' : Fin (m+1)) (i : Fin m) :
    (vert S j i : ℝ) ≤ vert S j' i + 1 := by
  unfold vert; split_ifs <;> push_cast <;> linarith

/-- **Brouwers fikspunktteorem** for enhetskuben [0,1]ⁿ. -/
theorem brouwer_cube {m : ℕ} (f : (Fin m → ℝ) → (Fin m → ℝ))
    (hf : ContinuousOn f (Set.Icc 0 1)) (hmap : Set.MapsTo f (Set.Icc 0 1) (Set.Icc 0 1)) :
    ∃ x ∈ Set.Icc (0 : Fin m → ℝ) 1, f x = x := by
  classical
  by_contra hno
  push Not at hno
  set Q : Set (Fin m → ℝ) := Set.Icc 0 1 with hQ
  have hQc : IsCompact Q := isCompact_Icc
  have hQne : Q.Nonempty := ⟨0, le_refl _, zero_le_one⟩
  have hQi : ∀ x ∈ Q, ∀ i, 0 ≤ x i ∧ x i ≤ 1 := fun x hx i => ⟨hx.1 i, hx.2 i⟩
  -- (a) f flytter alle punkter minst δ
  have hcont : ContinuousOn (fun x => ‖f x - x‖) Q := (hf.sub continuousOn_id).norm
  obtain ⟨x0, hx0, hmin⟩ := hQc.exists_isMinOn hQne hcont
  set δ := ‖f x0 - x0‖ with hδdef
  have hδ : 0 < δ := norm_pos_iff.2 (sub_ne_zero.2 (hno x0 hx0))
  have hδx : ∀ x ∈ Q, δ ≤ ‖f x - x‖ := fun x hx => hmin hx
  have hδ1 : δ ≤ 1 := by
    rw [hδdef, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have h1 := hQi _ (hmap hx0) i
    have h2 := hQi _ hx0 i
    rw [Pi.sub_apply, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  -- (b) krymp f litt inn i det indre
  set η := δ / 4 with hη
  have hη0 : 0 < η := by positivity
  have hη1 : η ≤ 1 / 4 := by rw [hη]; linarith
  let g : (Fin m → ℝ) → (Fin m → ℝ) := fun x => (1 - η) • f x + η • (fun _ => (1:ℝ) / 2)
  have hg_apply : ∀ x i, g x i = (1 - η) * f x i + η / 2 := by
    intro x i; simp [g]; ring
  have hgc : ContinuousOn g Q := (hf.const_smul (1 - η)).add continuousOn_const
  have hg_far : ∀ x ∈ Q, 3 * δ / 4 ≤ ‖g x - x‖ := by
    intro x hx
    have h1 := hδx x hx
    have h2 : ‖g x - f x‖ ≤ η := by
      rw [pi_norm_le_iff_of_nonneg hη0.le]
      intro i
      have := hQi _ (hmap hx) i
      rw [Pi.sub_apply, hg_apply, Real.norm_eq_abs, abs_le]
      constructor <;> nlinarith
    have h3 : ‖f x - x‖ ≤ ‖g x - f x‖ + ‖g x - x‖ := by
      calc ‖f x - x‖ = ‖-(g x - f x) + (g x - x)‖ := by congr 1; abel
        _ ≤ ‖-(g x - f x)‖ + ‖g x - x‖ := norm_add_le _ _
        _ = _ := by rw [norm_neg]
    linarith
  have hg_pos : ∀ x ∈ Q, ∀ i, 0 < g x i := by
    intro x hx i; rw [hg_apply]; have := hQi _ (hmap hx) i; nlinarith
  have hg_lt : ∀ x ∈ Q, ∀ i, g x i < 1 := by
    intro x hx i; rw [hg_apply]; have := hQi _ (hmap hx) i; nlinarith
  -- (c) uniform kontinuitet
  have hgu := hQc.uniformContinuousOn_of_continuous hgc
  rw [Metric.uniformContinuousOn_iff] at hgu
  obtain ⟨ρ, hρ, hgu⟩ := hgu η hη0
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (lt_min hρ hη0)
  set K : ℕ := N + 1 with hK
  have hK0 : 0 < K := Nat.succ_pos N
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK0
  have hKinv : 1 / (K : ℝ) < min ρ η := by rw [hK]; push_cast; exact hN
  -- (d) merkingen
  let pt : (Fin m → ℕ) → (Fin m → ℝ) := fun p i => (p i : ℝ) / K
  have hpt : ∀ p : Fin m → ℕ, (∀ i, p i ≤ K) → pt p ∈ Q := by
    intro p hp
    refine ⟨fun i => by simp only [pt, Pi.zero_apply]; positivity, fun i => ?_⟩
    simp only [pt, Pi.one_apply]
    rw [div_le_one hKr]; exact_mod_cast hp i
  let P : (Fin m → ℕ) → Fin m → Prop := fun p i => g (pt p) i < pt p i
  let ℓ : (Fin m → ℕ) → ℕ := fun p =>
    if h : (univ.filter (P p)).Nonempty then ((univ.filter (P p)).min' h : ℕ) else m
  have hℓ_min : ∀ p (h : (univ.filter (P p)).Nonempty), ℓ p = ((univ.filter (P p)).min' h : ℕ) := by
    intro p h; simp only [ℓ, dite_eq_left h]
  have hℓ_none : ∀ p, ¬ (univ.filter (P p)).Nonempty → ℓ p = m := by
    intro p h; simp only [ℓ, dite_eq_right h]
  have hL : Labeling m K ℓ := by
    refine ⟨fun p hp i h0 => ?_, fun p hp i hK' => ?_, fun p hp => ?_⟩
    · have hnot : ¬ P p i := by
        simp only [P, not_lt]
        have : pt p i = 0 := by simp [pt, h0]
        rw [this]; exact (hg_pos _ (hpt p hp) i).le
      by_cases hne : (univ.filter (P p)).Nonempty
      · rw [hℓ_min p hne]
        intro heq
        have hm := Finset.min'_mem _ hne
        have : (univ.filter (P p)).min' hne = i := Fin.ext heq
        rw [this] at hm
        exact hnot (mem_filter.1 hm).2
      · rw [hℓ_none p hne]; exact (Fin.is_lt i).ne'
    · have hPi : P p i := by
        simp only [P]
        have : pt p i = 1 := by simp [pt, hK', hKr.ne']
        rw [this]; exact hg_lt _ (hpt p hp) i
      have hne : (univ.filter (P p)).Nonempty := ⟨i, mem_filter.2 ⟨mem_univ _, hPi⟩⟩
      rw [hℓ_min p hne]
      exact Finset.min'_le _ _ (mem_filter.2 ⟨mem_univ _, hPi⟩)
    · by_cases hne : (univ.filter (P p)).Nonempty
      · rw [hℓ_min p hne]; exact (Fin.is_lt _).le
      · rw [hℓ_none p hne]
  -- (e) et fullt merket simpleks
  have hodd := sperner m K hK0 ℓ hL
  obtain ⟨S, hS⟩ : (univ.filter (full (k := K) ℓ)).Nonempty := by
    rw [← Finset.card_pos]; exact hodd.pos
  have hfull : full ℓ S := (mem_filter.1 hS).2
  have hlab : ∀ a ∈ range (m+1), ∃ j, ℓ (vert S j) = a := by
    intro a ha
    unfold full at hfull
    rw [← hfull] at ha
    obtain ⟨j, -, hj⟩ := mem_image.1 ha
    exact ⟨j, hj⟩
  obtain ⟨jm, hjm⟩ := hlab m (by simp)
  set x := pt (vert S jm) with hx
  have hxQ : x ∈ Q := hpt _ (vert_le S jm)
  have hx_up : ∀ i, x i ≤ g x i := by
    intro i
    by_contra hlt
    push Not at hlt
    have hne : (univ.filter (P (vert S jm))).Nonempty := ⟨i, mem_filter.2 ⟨mem_univ _, hlt⟩⟩
    rw [hℓ_min _ hne] at hjm
    have := Fin.is_lt ((univ.filter (P (vert S jm))).min' hne)
    omega
  have hclose : ∀ i, g x i - x i < 2 * η := by
    intro i
    obtain ⟨ji, hji⟩ := hlab i (by simp)
    set y := pt (vert S ji) with hy
    have hyQ : y ∈ Q := hpt _ (vert_le S ji)
    have hne : (univ.filter (P (vert S ji))).Nonempty := by
      by_contra hne
      rw [hℓ_none _ hne] at hji
      exact (Fin.is_lt i).ne' hji
    rw [hℓ_min _ hne] at hji
    have hmin_eq : (univ.filter (P (vert S ji))).min' hne = i := Fin.ext hji
    have hPy : g y i < y i := by
      have := Finset.min'_mem _ hne
      rw [hmin_eq] at this
      exact (mem_filter.1 this).2
    have hdist : dist x y < ρ := by
      have : dist x y ≤ 1 / K := by
        rw [dist_pi_le_iff (by positivity)]
        intro i'
        rw [Real.dist_eq, abs_le]
        simp only [hx, hy, pt]
        have h1 := vert_close S jm ji i'
        have h2 := vert_close S ji jm i'
        constructor
        · rw [div_sub_div_same, ← neg_div, div_le_div_iff_of_pos_right hKr]
          linarith
        · rw [div_sub_div_same, div_le_div_iff_of_pos_right hKr]
          linarith
      linarith [min_le_left ρ η]
    have hg := hgu x hxQ y hyQ hdist
    have hgi : |g x i - g y i| < η := by
      have := dist_le_pi_dist (g x) (g y) i
      rw [Real.dist_eq] at this
      linarith
    have hyx : y i - x i ≤ 1 / K := by
      simp only [hx, hy, pt]
      rw [div_sub_div_same, div_le_div_iff_of_pos_right hKr]
      have := vert_close S ji jm i
      linarith
    have := abs_lt.1 hgi
    linarith [min_le_right ρ η]
  have hsmall : ‖g x - x‖ < δ / 2 := by
    rw [pi_norm_lt_iff (by positivity)]
    intro i
    rw [Pi.sub_apply, Real.norm_eq_abs, abs_lt]
    have h1 := hx_up i
    have h2 := hclose i
    constructor <;> linarith
  have := hg_far x hxQ
  linarith

/-- Brouwer for et vilkårlig lukket rektangel [a, b]. -/
theorem brouwer_box {m : ℕ} {a b : Fin m → ℝ} (hab : a ≤ b) (f : (Fin m → ℝ) → (Fin m → ℝ))
    (hf : ContinuousOn f (Set.Icc a b)) (hmap : Set.MapsTo f (Set.Icc a b) (Set.Icc a b)) :
    ∃ x ∈ Set.Icc a b, f x = x := by
  classical
  -- φ : [0,1]ⁿ → [a,b], φ t = a + (b - a) t ; ψ : [a,b] → [0,1]ⁿ (der b i > a i)
  let φ : (Fin m → ℝ) → (Fin m → ℝ) := fun t i => a i + (b i - a i) * t i
  let ψ : (Fin m → ℝ) → (Fin m → ℝ) := fun x i => if a i < b i then (x i - a i) / (b i - a i) else 0
  have hφQ : ∀ t ∈ Set.Icc (0 : Fin m → ℝ) 1, φ t ∈ Set.Icc a b := by
    intro t ht
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have := ht.1 i; have := hab i; simp only [φ, Pi.zero_apply] at *; nlinarith
    · have := ht.2 i; have := hab i; simp only [φ, Pi.one_apply] at *; nlinarith
  have hψ : ∀ x ∈ Set.Icc a b, ψ x ∈ Set.Icc (0 : Fin m → ℝ) 1 := by
    intro x hx
    refine ⟨fun i => ?_, fun i => ?_⟩
    · simp only [ψ, Pi.zero_apply]
      split_ifs with h
      · exact div_nonneg (by linarith [hx.1 i]) (by linarith)
      · exact le_refl _
    · simp only [ψ, Pi.one_apply]
      split_ifs with h
      · rw [div_le_one (by linarith)]; linarith [hx.2 i]
      · exact zero_le_one
  have hφψ : ∀ x ∈ Set.Icc a b, φ (ψ x) = x := by
    intro x hx
    funext i
    simp only [φ, ψ]
    split_ifs with h
    · field_simp; ring
    · have : a i = b i := le_antisymm (hab i) (not_lt.1 h)
      have h1 := hx.1 i; have h2 := hx.2 i
      simp only [mul_zero, add_zero]; linarith
  have hφc : Continuous φ := by fun_prop
  have hψc : Continuous ψ := by
    refine continuous_pi fun i => ?_
    simp only [ψ]
    split_ifs
    · fun_prop
    · exact continuous_const
  obtain ⟨t, htQ, ht⟩ := brouwer_cube (fun t => ψ (f (φ t)))
    (hψc.comp_continuousOn (hf.comp hφc.continuousOn hφQ))
    (fun t ht => hψ _ (hmap (hφQ t ht)))
  refine ⟨φ t, hφQ t htQ, ?_⟩
  have := congrArg φ ht
  rwa [hφψ _ (hmap (hφQ t htQ))] at this

end Brouwer
end CausalPhys
