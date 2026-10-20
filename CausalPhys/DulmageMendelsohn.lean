/-
  CausalPhys.DulmageMendelsohn — den kausale ordenen avhenger ikke av matchingen.

  Et ligningssystem kan ha flere perfekte matchinger (lesninger). Simon-ordenen
  er likevel veldefinert:

    1. Abstrakt (`reach_eq`): la σ og σ' være to perfekte matchinger av de
       samme ligningene på de samme variablene. Da har avhengighetsgrafene
       nøyaktig samme nåbarhetsrelasjon. Følgelig er blokkene (sterkt
       sammenhengende komponenter), rekkefølgen mellom dem og asyklisiteten
       uavhengige av matchingen (`sameBlock_iff`, `acyclic_iff`).

       Bevis: π = σ⁻¹ ∘ σ' er en permutasjon av ligningene. Siden σ(π e) = σ' e
       står i ligning e, går det en kant π e → e. Følger man π rundt sin
       (endelige) syklus, når man tilbake til e, så e og π e ligger i samme
       blokk. En kant c → e for σ' gir da en vei c ⇝ π c → e for σ.

    2. Algoritmen (`computeC_acyclic_any`): for systemer der hver løsning leser
       resten av ligningens variabler («uniforme», avgjørbart), gjelder: finnes
       det ÉN gyldig asyklisk lesning, returnerer algoritmen en gyldig, streng
       orden. Teorem 10b er dermed ikke lenger relativt til matchingen den fant.

  Dette er invariansdelen av Dulmage–Mendelsohn-dekomposisjonen for
  velbestemte systemer. Den grove dekomposisjonen av over- og underbestemte
  systemer er ikke formalisert.
-/
import CausalPhys.CausalOrderComplete
import CausalPhys.CausalOrderCompleteExamples
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Logic.Relation

set_option linter.unusedSectionVars false
set_option linter.ambiguousOpen false

namespace CausalPhys
namespace DM

/-! ## 1. Abstrakt invarians -/

section Abstract

variable {E V : Type} [Finite E] (inc : E → V → Prop)

/-- Avhengighetsgrafen til matchingen σ: c → e når ligning e inneholder
    variabelen c bestemmer (og c ≠ e). -/
def G (σ : E → V) (c e : E) : Prop := c ≠ e ∧ inc e (σ c)

/-- Nåbarhet i avhengighetsgrafen. -/
def Reach (σ : E → V) : E → E → Prop := Relation.ReflTransGen (G inc σ)

variable {inc} {σ σ' : E → V}

/-- π e er ligningen som σ bruker til variabelen σ' bestemmer med e. -/
noncomputable def piF (himg : ∀ e, ∃ c, σ c = σ' e) : E → E := fun e => Classical.choose (himg e)

theorem piF_spec (himg : ∀ e, ∃ c, σ c = σ' e) (e : E) : σ (piF himg e) = σ' e :=
  Classical.choose_spec (himg e)

theorem piF_injective (hσ' : Function.Injective σ') (himg : ∀ e, ∃ c, σ c = σ' e) :
    Function.Injective (piF himg) := by
  intro a b h
  apply hσ'
  rw [← piF_spec himg a, ← piF_spec himg b, h]

/-- π som permutasjon (injektiv på en endelig mengde). -/
noncomputable def piP (hσ' : Function.Injective σ') (himg : ∀ e, ∃ c, σ c = σ' e) : Equiv.Perm E :=
  Equiv.ofBijective (piF himg)
    ⟨piF_injective hσ' himg, Finite.injective_iff_surjective.1 (piF_injective hσ' himg)⟩

theorem piP_apply (hσ' : Function.Injective σ') (himg : ∀ e, ∃ c, σ c = σ' e) (e : E) :
    piP hσ' himg e = piF himg e := rfl

/-- Kant π e → e (eller π e = e). -/
theorem step (hσ' : Function.Injective σ') (hm' : ∀ e, inc e (σ' e))
    (himg : ∀ e, ∃ c, σ c = σ' e) (e : E) : Reach inc σ (piP hσ' himg e) e := by
  by_cases h : piP hσ' himg e = e
  · rw [h]; exact Relation.ReflTransGen.refl
  · apply Relation.ReflTransGen.single
    refine ⟨h, ?_⟩
    rw [piP_apply, piF_spec himg e]
    exact hm' e

theorem chain (hσ' : Function.Injective σ') (hm' : ∀ e, inc e (σ' e))
    (himg : ∀ e, ∃ c, σ c = σ' e) : ∀ (m : ℕ) (x : E), Reach inc σ ((piP hσ' himg ^ m) x) x
  | 0, x => by simp only [pow_zero, Equiv.Perm.one_apply]; exact Relation.ReflTransGen.refl
  | m + 1, x => by
    have h1 : (piP hσ' himg ^ (m + 1)) x = piP hσ' himg ((piP hσ' himg ^ m) x) := by
      rw [pow_succ', Equiv.Perm.mul_apply]
    rw [h1]
    exact (step hσ' hm' himg _).trans (chain hσ' hm' himg m x)

/-- e og π e ligger i samme blokk: e når π e ved å gå rundt π-syklusen. -/
theorem back (hσ' : Function.Injective σ') (hm' : ∀ e, inc e (σ' e))
    (himg : ∀ e, ∃ c, σ c = σ' e) (e : E) : Reach inc σ e (piP hσ' himg e) := by
  set P := piP hσ' himg
  have hpos : 0 < orderOf P := orderOf_pos P
  have hpow : P ^ orderOf P = 1 := pow_orderOf_eq_one P
  have := chain hσ' hm' himg (orderOf P - 1) (P e)
  have heq : (P ^ (orderOf P - 1)) (P e) = e := by
    rw [← Equiv.Perm.mul_apply, ← pow_succ, Nat.sub_add_cancel hpos, hpow]
    rfl
  rwa [heq] at this

/-- Nåbarhet for σ' medfører nåbarhet for σ. -/
theorem reach_mono (hσ' : Function.Injective σ') (hm' : ∀ e, inc e (σ' e))
    (himg : ∀ e, ∃ c, σ c = σ' e) {c e : E} (h : Reach inc σ' c e) : Reach inc σ c e := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b d _ hstep ih =>
    obtain ⟨_, hinc⟩ := hstep
    refine ih.trans ((back hσ' hm' himg b).trans ?_)
    by_cases hb : piP hσ' himg b = d
    · rw [hb]
    · apply Relation.ReflTransGen.single
      refine ⟨hb, ?_⟩
      rw [piP_apply, piF_spec himg b]
      exact hinc

end Abstract

section Symmetric

variable {E V : Type} [Finite E] {inc : E → V → Prop} {σ σ' : E → V}

/-- To perfekte matchinger (samme bilde) gir samme nåbarhet. -/
theorem reach_eq (hσ : Function.Injective σ) (hσ' : Function.Injective σ')
    (hm : ∀ e, inc e (σ e)) (hm' : ∀ e, inc e (σ' e))
    (himg : ∀ e, ∃ c, σ c = σ' e) (himg' : ∀ e, ∃ c, σ' c = σ e) (c e : E) :
    Reach inc σ c e ↔ Reach inc σ' c e :=
  ⟨reach_mono hσ hm himg', reach_mono hσ' hm' himg⟩

def SameBlock (inc : E → V → Prop) (σ : E → V) (c e : E) : Prop :=
  Reach inc σ c e ∧ Reach inc σ e c

def Acyclic (inc : E → V → Prop) (σ : E → V) : Prop :=
  ∀ c e, Reach inc σ c e → Reach inc σ e c → c = e

theorem sameBlock_iff (hσ : Function.Injective σ) (hσ' : Function.Injective σ')
    (hm : ∀ e, inc e (σ e)) (hm' : ∀ e, inc e (σ' e))
    (himg : ∀ e, ∃ c, σ c = σ' e) (himg' : ∀ e, ∃ c, σ' c = σ e) (c e : E) :
    SameBlock inc σ c e ↔ SameBlock inc σ' c e := by
  unfold SameBlock
  rw [reach_eq hσ hσ' hm hm' himg himg', reach_eq hσ hσ' hm hm' himg himg']

theorem acyclic_iff (hσ : Function.Injective σ) (hσ' : Function.Injective σ')
    (hm : ∀ e, inc e (σ e)) (hm' : ∀ e, inc e (σ' e))
    (himg : ∀ e, ∃ c, σ c = σ' e) (himg' : ∀ e, ∃ c, σ' c = σ e) :
    Acyclic inc σ ↔ Acyclic inc σ' := by
  unfold Acyclic
  simp only [reach_eq hσ hσ' hm hm' himg himg']

end Symmetric

/-! ## 2. Kobling til strukturen og algoritmen -/

open CausalPhys.Order

variable {E V : Type} [DecidableEq E] [DecidableEq V] [Inhabited V]

/-- Uniform struktur: ligning e har variabelmengden `vars e`; den kan bare
    løses for variabler den inneholder, og løsningen leser resten. -/
def Uniform (S : Struct E V) (vars : E → List V) : Prop :=
  ∀ e ∈ S.eqList, ∀ v ∈ S.canSolve e, v ∈ vars e ∧
    ∀ p ∈ S.varList, (p ∈ S.deps e v ↔ p ∈ vars e ∧ p ≠ v)

instance (S : Struct E V) (vars : E → List V) : Decidable (Uniform S vars) := by
  unfold Uniform; infer_instance

theorem valid_injective {S : Struct E V} {c : Cert E V} (hc : Valid S c) :
    Function.Injective c.σ := by
  intro a b h
  have h1 := (hc.inv_iff (c.σ a) a).2 rfl
  have h2 := (hc.inv_iff (c.σ a) b).2 h.symm
  rw [h1] at h2
  exact Option.some.inj h2

theorem valid_img {S : Struct E V} {c c' : Cert E V} (hc : Valid S c) (hc' : Valid S c') (e : E) :
    ∃ x, c.σ x = c'.σ e := by
  have h1 : c'.inv (c'.σ e) = some e := (hc'.inv_iff _ e).2 rfl
  have hnex : c'.σ e ∉ S.exo := by
    intro hx
    rw [(hc'.inv_none _).2 hx] at h1
    cases h1
  cases hi : c.inv (c'.σ e) with
  | none => exact absurd ((hc.inv_none _).1 hi) hnex
  | some x => exact ⟨x, (hc.inv_iff _ x).1 hi⟩

/-- For en gyldig lesning av en uniform struktur er algoritmens kantrelasjon
    nøyaktig avhengighetsgrafen G. -/
theorem edge_iff_G {S : Struct E V} {vars : E → List V} (hu : Uniform S vars)
    {c : Cert E V} (hc : Valid S c) (x e : E) :
    Edge S c.σ c.inv x e ↔ G (fun e v => v ∈ vars e) c.σ x e := by
  have hue := hu e (S.eq_complete e) (c.σ e) (hc.mem e)
  constructor
  · rintro ⟨p, hp, hi⟩
    have hpx : c.σ x = p := (hc.inv_iff p x).1 hi
    subst hpx
    have := (hue.2 _ (S.var_complete _)).1 hp
    exact ⟨fun hxe => this.2 (by rw [hxe]), this.1⟩
  · rintro ⟨hne, hinc⟩
    refine ⟨c.σ x, (hue.2 _ (S.var_complete _)).2 ⟨hinc, fun h => hne (valid_injective hc h)⟩, ?_⟩
    exact (hc.inv_iff _ x).2 rfl

/-- Rangen fra én gyldig, asyklisk lesning virker for enhver annen gyldig lesning. -/
theorem transfer {S : Struct E V} {vars : E → List V} (hu : Uniform S vars)
    {c1 c2 : Cert E V} (h1 : Valid S c1) (h2 : Valid S c2) (hlt : OrderedLT S c1) :
    OrderedLT S ⟨c2.σ, c2.inv, c1.rank⟩ := by
  have : Fintype E := Fintype.ofList S.eqList S.eq_complete
  apply orderedLT_iff.2
  intro x e hedge
  have hG2 := (edge_iff_G hu h2 x e).1 hedge
  have hR2 : Reach (fun e v => v ∈ vars e) c2.σ x e := Relation.ReflTransGen.single hG2
  have hR1 := reach_mono (valid_injective h2) (fun e => (hu e (S.eq_complete e) _ (h2.mem e)).1)
    (fun e => valid_img h1 h2 e) hR2
  rcases Relation.reflTransGen_iff_eq_or_transGen.1 hR1 with heq | htg
  · exact absurd heq.symm hG2.1
  · show c1.rank x < c1.rank e
    clear hedge hG2 hR2 hR1
    induction htg with
    | single hg =>
      exact (orderedLT_iff.1 hlt) _ _ ((edge_iff_G hu h1 _ _).2 hg)
    | tail _ hg ih =>
      exact lt_trans ih ((orderedLT_iff.1 hlt) _ _ ((edge_iff_G hu h1 _ _).2 hg))

/-- Hovedteoremet: finnes det én gyldig asyklisk lesning av en uniform
    struktur, returnerer algoritmen en gyldig, streng orden. -/
theorem computeC_acyclic_any {S : Struct E V} {vars : E → List V} (hu : Uniform S vars)
    (h : ∃ c, Valid S c ∧ OrderedLT S c) :
    Valid S (computeC S) ∧ OrderedLT S (computeC S) := by
  obtain ⟨c, hc, hlt⟩ := h
  have hm := matchC_valid ⟨c, hc⟩
  refine ⟨computeC_valid ⟨c, hc⟩, computeC_acyclic ⟨c.rank, ?_⟩⟩
  exact transfer hu hc hm hlt

/-- Og blokkstrukturen er den samme for alle gyldige lesninger. -/
theorem blocks_independent {S : Struct E V} {vars : E → List V} (hu : Uniform S vars)
    {c1 c2 : Cert E V} (h1 : Valid S c1) (h2 : Valid S c2) (x e : E) :
    Reach (fun e v => v ∈ vars e) c1.σ x e ↔ Reach (fun e v => v ∈ vars e) c2.σ x e := by
  have : Fintype E := Fintype.ofList S.eqList S.eq_complete
  exact reach_eq (valid_injective h1) (valid_injective h2)
    (fun e => (hu e (S.eq_complete e) _ (h1.mem e)).1)
    (fun e => (hu e (S.eq_complete e) _ (h2.mem e)).1)
    (fun e => valid_img h1 h2 e) (fun e => valid_img h2 h1 e) x e

/-! ## 3. Eksemplene er uniforme -/

def gasVars : Unit → List Gas := fun _ => [.p, .Vol, .n, .T]
theorem gasA_uniform : Uniform gasA gasVars := by decide
theorem gasB_uniform : Uniform gasB gasVars := by decide

def circVars : CEq → List Circ
  | .joule => [.P, .U, .I]
  | .ohm => [.U, .Rr, .I]
  | .newton => [.T, .Ta, .k, .P]
theorem voltage_uniform : Uniform voltageSource circVars := by decide
theorem current_uniform : Uniform currentSource circVars := by decide

def marketVars : MEq → List MV
  | .demand => [.Q, .P, .y]
  | .supply => [.P, .Q, .t, .w]
theorem market_uniform : Uniform marketS marketVars := by decide

end DM
end CausalPhys
