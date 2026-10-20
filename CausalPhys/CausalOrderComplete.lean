/-
  CausalPhys.CausalOrderComplete — algoritmen lykkes alltid.

  CausalOrder.lean beviste at HVERT SVAR algoritmen gir og som består sjekken,
  er riktig. Her bevises at algoritmen ALLTID gir et svar som består:

    1. Matching (`computeC_valid`): finnes det i det hele tatt en perfekt
       matching av ligningene på de endogene variablene, returnerer
       `computeC` en gyldig. Kuhns algoritme er den raske veien; mislykkes
       den, søker en uttømmende reserve gjennom alle valg, og den er bevist
       fullstendig.

    2. Orden (`computeC_acyclic`): er avhengighetsgrafen til den funne
       matchingen asyklisk, gir `computeC` en streng orden. Rangen er lengste
       vei, beregnet med |E| iterasjoner. Beviset viser at iterasjonen da har
       nådd et fikspunkt: ellers fantes en kjede med |E| + 2 ulike ligninger
       (skuffeprinsippet).

  Ikke bevist: at blokkene er de samme for enhver perfekt matching
  (Dulmage–Mendelsohn), og at Kuhns algoritme alene alltid lykkes.
-/
import CausalPhys.CausalOrder
import Mathlib.Data.List.Sections
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Perm.Subperm

set_option linter.unusedSectionVars false

namespace CausalPhys
namespace Order

variable {E V : Type} [DecidableEq E] [DecidableEq V] [Inhabited V]

/-! ## 1. Matching: uttømmende reserve, bevist fullstendig -/

/-- Funksjon fra en liste av valg, ett per ligning i rekkefølge. -/
def pick : List E → List V → E → V
  | [], _, _ => default
  | _ :: _, [], _ => default
  | e' :: es, v :: vs, e => if e = e' then v else pick es vs e

theorem pick_map (f : E → V) : ∀ (l : List E) (e : E), e ∈ l → pick l (l.map f) e = f e
  | [], _, h => absurd h (by simp)
  | e' :: es, e, h => by
    simp only [List.map_cons, pick]
    by_cases he : e = e'
    · subst he; simp
    · rw [ite_eq_right he]
      exact pick_map f es e (by simpa [he] using h)

/-- Sertifikatet en matching σ gir (rangen er irrelevant for gyldighet). -/
def certOf (S : Struct E V) (σ : E → V) : Cert E V :=
  ⟨σ, fun v => S.eqList.find? (fun e => decide (σ e = v)), fun _ => 0⟩

/-- Alle kandidater: ett valg fra `canSolve e` for hver ligning. -/
def candidates (S : Struct E V) : List (Cert E V) :=
  (List.sections (S.eqList.map S.canSolve)).map fun l => certOf S (pick S.eqList l)

def brute (S : Struct E V) : Option (Cert E V) :=
  (candidates S).find? fun c => decide (Valid S c)

theorem forall2_map (f : E → V) (g : E → List V) :
    ∀ l : List E, (∀ e ∈ l, f e ∈ g e) → List.Forall₂ (· ∈ ·) (l.map f) (l.map g)
  | [], _ => List.Forall₂.nil
  | e :: es, h => by
    simp only [List.map_cons]
    exact List.Forall₂.cons (h e (by simp)) (forall2_map f g es fun x hx => h x (by simp [hx]))

/-- Et gyldig sertifikat gir et gyldig `certOf` av samme matching. -/
theorem certOf_valid {S : Struct E V} {c : Cert E V} (hc : Valid S c) : Valid S (certOf S c.σ) := by
  have inj : ∀ e e', c.σ e = c.σ e' → e = e' := by
    intro e e' h
    have h1 := (hc.inv_iff (c.σ e) e).2 rfl
    have h2 := (hc.inv_iff (c.σ e) e').2 h.symm
    rw [h1] at h2
    exact Option.some.inj h2
  refine ⟨fun e _ => hc.mem e, fun v _ e _ => ?_, fun v _ => ?_⟩
  · show S.eqList.find? (fun e => decide (c.σ e = v)) = some e ↔ c.σ e = v
    constructor
    · intro h
      have h' := List.find?_some h
      exact of_decide_eq_true h'
    · intro h
      have hex : (S.eqList.find? (fun e => decide (c.σ e = v))).isSome = true :=
        List.find?_isSome.2 ⟨e, S.eq_complete e, decide_eq_true h⟩
      obtain ⟨e', he'⟩ := Option.isSome_iff_exists.1 hex
      have h'' := List.find?_some he'
      have := of_decide_eq_true h''
      rw [he', inj e' e (this.trans h.symm)]
  · show S.eqList.find? (fun e => decide (c.σ e = v)) = none ↔ v ∈ S.exo
    rw [List.find?_eq_none, ← hc.inv_none v]
    constructor
    · intro h
      cases hi : c.inv v with
      | none => rfl
      | some e =>
        exact absurd ((hc.inv_iff v e).1 hi) (by simpa using h e (S.eq_complete e))
    · intro h e _
      simp only [decide_eq_true_eq]
      intro he
      rw [(hc.inv_iff v e).2 he] at h
      cases h

/-- Den uttømmende reserven er fullstendig. -/
theorem brute_complete {S : Struct E V} (h : ∃ c, Valid S c) :
    ∃ c, brute S = some c ∧ Valid S c := by
  obtain ⟨c, hc⟩ := h
  have hmem : certOf S c.σ ∈ candidates S := by
    apply List.mem_map.2
    refine ⟨S.eqList.map c.σ, ?_, ?_⟩
    · exact List.mem_sections.2 (forall2_map _ _ _ fun e _ => hc.mem e)
    · congr 1
      funext e
      exact pick_map c.σ S.eqList e (S.eq_complete e)
  have hsome : (brute S).isSome := List.find?_isSome.2 ⟨_, hmem, by simpa using certOf_valid hc⟩
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.1 hsome
  exact ⟨c', hc', by simpa using List.find?_some hc'⟩

/-! ## 2. Orden: lengste vei -/

/-- Kant c → e: ligning e leser variabelen ligning c bestemmer. -/
def Edge (S : Struct E V) (σ : E → V) (inv : V → Option E) (c e : E) : Prop :=
  ∃ p ∈ S.deps e (σ e), inv p = some c

instance (S : Struct E V) (σ : E → V) (inv : V → Option E) (c e : E) :
    Decidable (Edge S σ inv c e) := by unfold Edge; infer_instance

def maxOf : List ℕ → ℕ
  | [] => 0
  | x :: xs => max x (maxOf xs)

theorem le_maxOf : ∀ {l : List ℕ} {x : ℕ}, x ∈ l → x ≤ maxOf l
  | x :: xs, y, h => by
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (le_maxOf h) (le_max_right _ _)

theorem maxOf_le : ∀ {l : List ℕ} {B : ℕ}, (∀ x ∈ l, x ≤ B) → maxOf l ≤ B
  | [], _, _ => Nat.zero_le _
  | x :: xs, B, h => max_le (h x (by simp)) (maxOf_le fun y hy => h y (by simp [hy]))

theorem maxOf_mem : ∀ {l : List ℕ}, maxOf l = 0 ∨ maxOf l ∈ l
  | [] => Or.inl rfl
  | x :: xs => by
    simp only [maxOf]
    rcases le_total x (maxOf xs) with h | h
    · rw [max_eq_right h]
      rcases maxOf_mem (l := xs) with h0 | hm
      · exact Or.inl h0
      · exact Or.inr (by simp [hm])
    · rw [max_eq_left h]; exact Or.inr (by simp)

theorem maxOf_mono : ∀ {l : List E} {f g : E → ℕ}, (∀ x ∈ l, f x ≤ g x) →
    maxOf (l.map f) ≤ maxOf (l.map g)
  | [], _, _, _ => le_refl _
  | x :: xs, f, g, h => by
    simp only [List.map_cons, maxOf]
    exact max_le_max (h x (by simp)) (maxOf_mono fun y hy => h y (by simp [hy]))

/-- Lengste vei med høyst k kanter som ender i e. -/
def lp (S : Struct E V) (σ : E → V) (inv : V → Option E) : ℕ → E → ℕ
  | 0, _ => 0
  | k + 1, e => maxOf ((S.eqList.filter fun c => decide (Edge S σ inv c e)).map fun c => lp S σ inv k c + 1)

variable (S : Struct E V) (σ : E → V) (inv : V → Option E)

theorem lp_le_k : ∀ k e, lp S σ inv k e ≤ k
  | 0, _ => le_refl _
  | k + 1, e => maxOf_le fun x hx => by
    simp only [List.mem_map] at hx
    obtain ⟨c, _, rfl⟩ := hx
    exact Nat.succ_le_succ (lp_le_k k c)

theorem lp_mono : ∀ k e, lp S σ inv k e ≤ lp S σ inv (k + 1) e
  | 0, _ => Nat.zero_le _
  | k + 1, e => maxOf_mono fun c _ => Nat.succ_le_succ (lp_mono k c)

theorem lp_edge (k : ℕ) {c e : E} (h : Edge S σ inv c e) : lp S σ inv k c + 1 ≤ lp S σ inv (k + 1) e :=
  le_maxOf (List.mem_map.2 ⟨c, List.mem_filter.2 ⟨S.eq_complete c, by simpa using h⟩, rfl⟩)

/-- Hopp-lemma: endrer verdien seg fra k til k+1, er den nøyaktig k+1. -/
theorem lp_jump : ∀ k e, lp S σ inv k e < lp S σ inv (k + 1) e → lp S σ inv (k + 1) e = k + 1
  | 0, e, h => le_antisymm (lp_le_k S σ inv 1 e) h
  | k + 1, e, h => by
    apply le_antisymm (lp_le_k S σ inv (k + 1 + 1) e)
    rcases maxOf_mem (l := (S.eqList.filter fun c => decide (Edge S σ inv c e)).map
        fun c => lp S σ inv (k + 1) c + 1) with h0 | hm
    · exfalso
      have : lp S σ inv (k + 1 + 1) e = 0 := h0
      omega
    · simp only [List.mem_map, List.mem_filter] at hm
      obtain ⟨c, ⟨_, hce⟩, hval⟩ := hm
      have hce' : Edge S σ inv c e := by simpa using hce
      have hlt : lp S σ inv k c < lp S σ inv (k + 1) c := by
        have := lp_edge S σ inv k hce'
        have h2 : lp S σ inv (k + 1 + 1) e = lp S σ inv (k + 1) c + 1 := hval.symm
        omega
      have := lp_jump k c hlt
      show k + 1 + 1 ≤ lp S σ inv (k + 1 + 1) e
      have : lp S σ inv (k + 1 + 1) e = lp S σ inv (k + 1) c + 1 := hval.symm
      omega

/-- Kjede: hver verdi er nådd langs en kjede av ligninger (lest baklengs). -/
theorem lp_chain : ∀ k e, ∃ l : List E, l.length = lp S σ inv k e + 1 ∧ l.head? = some e ∧
    l.IsChain (fun a b => Edge S σ inv b a)
  | 0, e => ⟨[e], rfl, rfl, List.isChain_singleton _⟩
  | k + 1, e => by
    rcases maxOf_mem (l := (S.eqList.filter fun c => decide (Edge S σ inv c e)).map
        fun c => lp S σ inv k c + 1) with h0 | hm
    · exact ⟨[e], by simp [lp, h0], rfl, List.isChain_singleton _⟩
    · simp only [List.mem_map, List.mem_filter] at hm
      obtain ⟨c, ⟨_, hce⟩, hval⟩ := hm
      obtain ⟨l, hlen, hhead, hch⟩ := lp_chain k c
      refine ⟨e :: l, ?_, rfl, ?_⟩
      · simp only [List.length_cons, hlen]
        show lp S σ inv k c + 1 + 1 = lp S σ inv (k + 1) e + 1
        rw [show lp S σ inv (k + 1) e = lp S σ inv k c + 1 from hval.symm]
      · cases l with
        | nil => simp at hlen
        | cons x xs =>
          simp only [List.head?_cons, Option.some.injEq] at hhead
          subst hhead
          exact hch.cons_cons (by simpa using hce)

/-- Med en streng rangering ρ er en kjede uten gjentakelser. -/
theorem chain_nodup {ρ : E → ℕ} (hρ : ∀ c e, Edge S σ inv c e → ρ c < ρ e) :
    ∀ {l : List E}, l.IsChain (fun a b => Edge S σ inv b a) → l.Nodup := by
  intro l hl
  have h2 : l.IsChain (fun a b => ρ b < ρ a) := hl.imp fun a b h => hρ b a h
  have h3 : l.Pairwise (fun a b => ρ b < ρ a) := List.isChain_iff_pairwise.1 h2
  exact h3.imp fun h heq => by subst heq; exact lt_irrefl _ h

/-- Fikspunkt etter |E| steg, når grafen er asyklisk. -/
theorem lp_fix {ρ : E → ℕ} (hρ : ∀ c e, Edge S σ inv c e → ρ c < ρ e) (e : E) :
    lp S σ inv (S.eqList.length + 1) e = lp S σ inv S.eqList.length e := by
  set L := S.eqList.length
  by_contra hne
  have hlt : lp S σ inv L e < lp S σ inv (L + 1) e :=
    lt_of_le_of_ne (lp_mono S σ inv L e) (Ne.symm hne)
  have hj := lp_jump S σ inv L e hlt
  obtain ⟨l, hlen, _, hch⟩ := lp_chain S σ inv (L + 1) e
  have hnd := chain_nodup S σ inv hρ hch
  have hsub : l ⊆ S.eqList := fun x _ => S.eq_complete x
  have := (hnd.subperm hsub).length_le
  omega

/-- Rangen: lengste vei etter |E| steg. -/
def lpRank (S : Struct E V) (c : Cert E V) : E → ℕ := lp S c.σ c.inv S.eqList.length

theorem orderedLT_iff {S : Struct E V} {c : Cert E V} :
    OrderedLT S c ↔ ∀ e' e, Edge S c.σ c.inv e' e → c.rank e' < c.rank e := by
  constructor
  · rintro h e' e ⟨p, hp, hi⟩
    exact h e (S.eq_complete e) p hp e' (S.eq_complete e') hi
  · intro h e _ p hp e' _ hi
    exact h e' e ⟨p, hp, hi⟩

/-- Er grafen asyklisk, gir lengste vei en streng orden. -/
theorem lpRank_ordered {S : Struct E V} {c : Cert E V}
    (hacyc : ∃ r, OrderedLT S ⟨c.σ, c.inv, r⟩) : OrderedLT S ⟨c.σ, c.inv, lpRank S c⟩ := by
  obtain ⟨r, hr⟩ := hacyc
  have hρ : ∀ c' e, Edge S c.σ c.inv c' e → r c' < r e := fun c' e h => (orderedLT_iff.1 hr) c' e h
  apply orderedLT_iff.2
  intro e' e h
  show lp S c.σ c.inv S.eqList.length e' < lp S c.σ c.inv S.eqList.length e
  have h1 := lp_edge S c.σ c.inv S.eqList.length h
  rw [lp_fix S c.σ c.inv hρ e] at h1
  omega

/-! ## 3. Den komplette algoritmen -/

/-- Matching: Kuhn først; mislykkes den, den uttømmende reserven. -/
def matchC (S : Struct E V) : Cert E V :=
  if Valid S (compute S) then compute S else (brute S).getD (compute S)

/-- Den komplette algoritmen: lengste vei som rang hvis den raske rangen
    ikke gir streng orden. -/
def computeC (S : Struct E V) : Cert E V :=
  if OrderedLT S (matchC S) then matchC S else ⟨(matchC S).σ, (matchC S).inv, lpRank S (matchC S)⟩

theorem matchC_valid {S : Struct E V} (h : ∃ c, Valid S c) : Valid S (matchC S) := by
  unfold matchC
  split_ifs with h1
  · exact h1
  · obtain ⟨c, hc, hv⟩ := brute_complete h
    rw [hc]; exact hv

/-- Teorem A: finnes en perfekt matching, lykkes algoritmen. -/
theorem computeC_valid {S : Struct E V} (h : ∃ c, Valid S c) : Valid S (computeC S) := by
  have hm := matchC_valid h
  unfold computeC
  split_ifs
  · exact hm
  · exact hm

/-- Teorem B: er avhengighetsgrafen til den funne matchingen asyklisk, gir
    algoritmen en streng orden. -/
theorem computeC_acyclic {S : Struct E V}
    (h : ∃ r, OrderedLT S ⟨(matchC S).σ, (matchC S).inv, r⟩) : OrderedLT S (computeC S) := by
  unfold computeC
  split_ifs with h2
  · exact h2
  · exact lpRank_ordered h

/-- Samlet: finnes en perfekt matching, og er grafen til den asyklisk, så
    lykkes algoritmen med begge deler. -/
theorem computeC_complete {S : Struct E V} (hm : ∃ c, Valid S c)
    (ha : ∃ r, OrderedLT S ⟨(matchC S).σ, (matchC S).inv, r⟩) :
    Valid S (computeC S) ∧ OrderedLT S (computeC S) :=
  ⟨computeC_valid hm, computeC_acyclic ha⟩

end Order
end CausalPhys
