/-
  CausalPhys.Core — den kausale kjernen (ren Lean 4, ingen Mathlib).

  Pearl-ideen uten do-kalkulus:
    * en MEKANISME er en ligning løst for én variabel (Simon-orden),
    * en SCM sier hvilke variabler som er eksogene (labben holder dem fast),
    * do(x := c) bytter ut mekanismen til x med en konstant.

  Verdiene har en vilkårlig type α, så kjernen gjelder for ℝ, ℚ, intervaller …
-/

set_option linter.unusedSectionVars false

namespace CausalPhys

universe u

variable {V : Type} {α : Type u}

/-- En mekanisme: foreldrene den leser, og funksjonen som gir verdien.
    `local_` er beviset på at funksjonen BARE leser foreldrene. -/
structure Mech (V : Type) (α : Type u) where
  parents : List V
  f       : (V → α) → α
  local_  : ∀ s t : V → α, (∀ v, v ∈ parents → s v = t v) → f s = f t

/-- SCM: hver variabel er eksogen (`none`) eller har en mekanisme. -/
structure SCM (V : Type) (α : Type u) where
  mech : V → Option (Mech V α)

namespace SCM

/-- `s` er en løsning av `M` når de eksogene variablene har verdiene `u`. -/
def Solves (M : SCM V α) (u : V → α) (s : V → α) : Prop :=
  ∀ v, match M.mech v with
       | none   => s v = u v
       | some m => s v = m.f s

/-- Konstant mekanisme: ingen foreldre. -/
def Mech.const (c : α) : Mech V α :=
  ⟨[], fun _ => c, fun _ _ _ => rfl⟩

variable [DecidableEq V]

/-- do(x := c). -/
def doI (M : SCM V α) (x : V) (c : α) : SCM V α :=
  ⟨fun v => if v = x then some (Mech.const c) else M.mech v⟩

/-- En lov er en akausal relasjon på tilstander. -/
abbrev Law (V : Type) (α : Type u) := (V → α) → Prop

/-- Oppsettet realiserer loven: alle løsninger oppfyller den. -/
def Realizes (M : SCM V α) (L : Law V α) : Prop :=
  ∀ u s, M.Solves u s → L s

/-! ### Grunnleggende lover for do -/

/-- Etter do(x := c) har x verdien c. -/
theorem doI_self (M : SCM V α) (x : V) (c : α) (u s : V → α)
    (h : (M.doI x c).Solves u s) : s x = c := by
  have hx := h x
  simpa [doI, Mech.const] using hx

/-- do(x) rører ikke en annen variabels mekanisme. -/
theorem doI_mech_ne (M : SCM V α) {x v : V} (c : α) (hv : v ≠ x) :
    (M.doI x c).mech v = M.mech v := by
  simp [doI, hv]

/-- Kausal skjerming: en ANNEN eksogen variabel forblir der labben satte den. -/
theorem doI_exo (M : SCM V α) {x v : V} (c : α) (u s : V → α)
    (hv : v ≠ x) (hexo : M.mech v = none)
    (h : (M.doI x c).Solves u s) : s v = u v := by
  have hs := h v
  rw [doI_mech_ne M c hv, hexo] at hs
  exact hs

/-- Andre mekanismer gjelder uendret etter do(x). -/
theorem doI_other (M : SCM V α) {x v : V} (c : α) (u s : V → α) (m : Mech V α)
    (hv : v ≠ x) (hm : M.mech v = some m)
    (h : (M.doI x c).Solves u s) : s v = m.f s := by
  have hs := h v
  rw [doI_mech_ne M c hv, hm] at hs
  exact hs

/-- To inngrep på samme variabel: det siste vinner. -/
theorem doI_doI_same (M : SCM V α) (x : V) (c d : α) :
    (M.doI x c).doI x d = M.doI x d := by
  simp only [doI, SCM.mk.injEq]
  funext v
  by_cases h : v = x <;> simp [h]

/-- Inngrep på ulike variabler kommuterer. -/
theorem doI_comm (M : SCM V α) {x y : V} (c d : α) (hxy : x ≠ y) :
    (M.doI x c).doI y d = (M.doI y d).doI x c := by
  simp only [doI, SCM.mk.injEq]
  funext v
  by_cases hx : v = x
  · subst hx; simp [hxy]
  · by_cases hy : v = y
    · subst hy; simp [hx]
    · simp [hx, hy]

/-! ### Simon-orden: rekursive (asykliske) modeller har entydige løsninger -/

/-- En rang (kausal orden) der alle foreldre har lavere rang. -/
def Recursive (M : SCM V α) (rank : V → Nat) : Prop :=
  ∀ v m, M.mech v = some m → ∀ p, p ∈ m.parents → rank p < rank v

omit [DecidableEq V] in
/-- I en rekursiv modell bestemmer de eksogene verdiene hele tilstanden. -/
theorem Recursive.unique {M : SCM V α} {rank : V → Nat} (hr : M.Recursive rank)
    {u s t : V → α} (hs : M.Solves u s) (ht : M.Solves u t) : s = t := by
  have key : ∀ n, ∀ v, rank v = n → s v = t v := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro v hv
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
        exact ih (rank p) (hv ▸ hr v m hm p hp) p rfl
  funext v
  exact key (rank v) v rfl

/-- do bevarer rekursivitet: et inngrep kan aldri lage en syklus. -/
theorem Recursive.doI {M : SCM V α} {rank : V → Nat} (hr : M.Recursive rank)
    (x : V) (c : α) : (M.doI x c).Recursive rank := by
  intro v m hm p hp
  by_cases hv : v = x
  · simp only [SCM.doI, hv, ite_true] at hm
    cases hm
    simp [Mech.const] at hp
  · rw [doI_mech_ne M c hv] at hm
    exact hr v m hm p hp

/-- Følgelig: utfallet av et inngrep er entydig bestemt. -/
theorem Recursive.doI_unique {M : SCM V α} {rank : V → Nat} (hr : M.Recursive rank)
    (x : V) (c : α) {u s t : V → α}
    (hs : (M.doI x c).Solves u s) (ht : (M.doI x c).Solves u t) : s = t :=
  (hr.doI x c).unique hs ht

end SCM
end CausalPhys
