import PearlDoCalculus.DSepSound

/-!
# Vandringer og stier

`DSeparated` er definert over vandringer (gjentatte noder tillatt). Den klassiske
definisjonen bruker stier. Denne fila viser at de er ekvivalente, og løfter dermed
`dsep_sound` til den klassiske stibaserte hypotesen.

Retningen vandring ⇒ sti er triviell, siden enhver sti er en vandring. Retningen
sti ⇒ vandring er kontrapositivt «åpen vandring ⇒ åpen sti», og bevises ved å
fjerne løkker fra hodet av vandringen uten å miste åpenhet.
-/

namespace PearlDoCalculus
namespace DAG

variable {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V}

namespace Walk

/-- Startnoden er med i støtten. -/
lemma start_mem_support {a b : V} (p : Walk G a b) : a ∈ p.support := by
  cases p <;> simp [support]

/-- Sluttnoden er med i støtten. -/
lemma end_mem_support {a b : V} (p : Walk G a b) : b ∈ p.support := by
  induction p with
  | nil v => simp [support]
  | fwd e q ih => simp [support, ih]
  | bwd e q ih => simp [support, ih]

/-- En sti: ingen node besøkes to ganger. Støtten inneholder både start- og
sluttnoden (`start_mem_support`, `end_mem_support`), så dette er nøyaktig
den klassiske sti-egenskapen. -/
def IsPath {a b : V} (p : Walk G a b) : Prop := p.support.Nodup

end Walk

/-- Klassisk d-separasjon: alle *stier* fra `x` til `y` er blokkert av `Z`. -/
def DSeparatedPath (G : DAG V) (Z : Finset V) (x y : V) : Prop :=
  ∀ p : Walk G x y, p.IsPath → Walk.Blocked Z p

/-- Den trivielle retningen: vandringsbasert d-separasjon gir stibasert. -/
theorem dsepPath_of_dsep {Z : Finset V} {x y : V} (h : G.DSeparated Z x y) :
    G.DSeparatedPath Z x y :=
  fun p _ => h p

/-- **Nedstigning.** Kom vandringen inn i `b` langs en pil (`.fwd`) og er åpen,
så når `b` enten en node i `Z`, eller alle noder på vandringen. Det andre
alternativet er det som gjør asyklisitet nyttig: dukker en tidligere node opp
igjen, får vi en rettet sykel. -/
lemma descend_of_open {Z : Finset V} : ∀ {b c : V} (q : Walk G b c),
    ¬ Walk.blockedAux Z .fwd q →
    (∃ z ∈ Z, G.Reaches b z) ∨ (∀ v ∈ q.support, G.Reaches b v) := by
  intro b c q
  induction q with
  | nil v =>
    intro _
    right
    intro w hw
    simp [Walk.support] at hw
    subst hw
    exact Reaches.refl G _
  | @fwd a b' c e rest ih =>
    intro hq
    simp only [Walk.blockedAux] at hq
    push_neg at hq
    rcases ih hq.2 with ⟨z, hz, hr⟩ | hall
    · left
      exact ⟨z, hz, Reaches.trans G (Reaches.of_edge G e) hr⟩
    · right
      intro w hw
      simp only [Walk.support, List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact Reaches.refl G _
      · exact Reaches.trans G (Reaches.of_edge G e) (hall w hw)
  | @bwd a b' c e rest ih =>
    intro hq
    simp only [Walk.blockedAux] at hq
    push_neg at hq
    left
    exact hq.1

/-- Er vandringen åpen, er resten etter et `fwd`-steg åpen i tilstand `.fwd`. -/
lemma open_tail_fwd {Z : Finset V} {inc : Incoming} {a a₁ b : V}
    (e : G.edge a a₁) (rest : Walk G a₁ b)
    (h : ¬ Walk.blockedAux Z inc (Walk.fwd e rest)) :
    ¬ Walk.blockedAux Z .fwd rest := by
  intro hr
  apply h
  cases inc <;> simp [Walk.blockedAux, hr]

/-- Er vandringen åpen, er resten etter et `bwd`-steg åpen i tilstand `.bwd`. -/
lemma open_tail_bwd {Z : Finset V} {inc : Incoming} {a a₁ b : V}
    (e : G.edge a₁ a) (rest : Walk G a₁ b)
    (h : ¬ Walk.blockedAux Z inc (Walk.bwd e rest)) :
    ¬ Walk.blockedAux Z .bwd rest := by
  intro hr
  apply h
  cases inc <;> simp [Walk.blockedAux, hr]

/-- **Hopp til siste forekomst.** For en node `x` på en åpen vandring finnes et
suffiks som starter i siste forekomst av `x`, med tilstanden der. Enten er
tilstanden uendret, eller så skjedde hoppet fra en indre posisjon, og `x` lå i
halen av den opprinnelige vandringen. -/
lemma exists_fromLast {Z : Finset V} (x : V) : ∀ {a b : V} (p : Walk G a b)
    (inc : Incoming), x ∈ p.support → ¬ Walk.blockedAux Z inc p →
    ∃ (inc' : Incoming) (q : Walk G x b),
      q.support ⊆ p.support ∧ x ∉ q.support.tail ∧ q.length ≤ p.length ∧
      ¬ Walk.blockedAux Z inc' q ∧
      (inc' = inc ∨ (inc' ≠ .start ∧ x ∈ p.support.tail)) := by
  intro a b p
  induction p with
  | nil v =>
    intro inc hx hp
    simp [Walk.support] at hx
    subst hx
    exact ⟨inc, Walk.nil _, List.Subset.refl _, by simp [Walk.support], le_refl _, hp,
      Or.inl rfl⟩
  | @fwd a a₁ b e rest ih =>
    intro inc hx hp
    have hrest := open_tail_fwd e rest hp
    by_cases hxr : x ∈ rest.support
    · obtain ⟨inc', q, hsub, hnot, hlen, hopen, hcase⟩ := ih .fwd hxr hrest
      refine ⟨inc', q, ?_, hnot, ?_, hopen, Or.inr ⟨?_, ?_⟩⟩
      · intro w hw
        simp only [Walk.support, List.mem_cons]
        exact Or.inr (hsub hw)
      · simp only [Walk.length]
        omega
      · rcases hcase with rfl | ⟨h, _⟩
        · intro h; cases h
        · exact h
      · simpa [Walk.support] using hxr
    · have hxa : x = a := by
        simp only [Walk.support, List.mem_cons] at hx
        rcases hx with h | h
        · exact h
        · exact absurd h hxr
      subst hxa
      exact ⟨inc, Walk.fwd e rest, List.Subset.refl _, by simpa [Walk.support] using hxr,
        le_refl _, hp, Or.inl rfl⟩
  | @bwd a a₁ b e rest ih =>
    intro inc hx hp
    have hrest := open_tail_bwd e rest hp
    by_cases hxr : x ∈ rest.support
    · obtain ⟨inc', q, hsub, hnot, hlen, hopen, hcase⟩ := ih .bwd hxr hrest
      refine ⟨inc', q, ?_, hnot, ?_, hopen, Or.inr ⟨?_, ?_⟩⟩
      · intro w hw
        simp only [Walk.support, List.mem_cons]
        exact Or.inr (hsub hw)
      · simp only [Walk.length]
        omega
      · rcases hcase with rfl | ⟨h, _⟩
        · intro h; cases h
        · exact h
      · simpa [Walk.support] using hxr
    · have hxa : x = a := by
        simp only [Walk.support, List.mem_cons] at hx
        rcases hx with h | h
        · exact h
        · exact absurd h hxr
      subst hxa
      exact ⟨inc, Walk.bwd e rest, List.Subset.refl _, by simpa [Walk.support] using hxr,
        le_refl _, hp, Or.inl rfl⟩

/-- **Hoppet bevarer åpenhet.** Fra en åpen vandring finnes et suffiks fra siste
forekomst av startnoden som er åpent i den *opprinnelige* tilstanden. Startnoden
beholder sin innkommende kant, men får ny utgående kant; kasusanalysen viser at
statusen forblir åpen. Den nye kollideren i `a` håndteres med `descend_of_open`
og asyklisitet. -/
lemma exists_jump {Z : Finset V} (inc : Incoming) {a b : V} (p : Walk G a b)
    (hp : ¬ Walk.blockedAux Z inc p) :
    ∃ q : Walk G a b, q.support ⊆ p.support ∧ a ∉ q.support.tail ∧
      q.length ≤ p.length ∧ ¬ Walk.blockedAux Z inc q := by
  obtain ⟨inc', q, hsub, hnot, hlen, hopen, hcase⟩ :=
    exists_fromLast a p inc (Walk.start_mem_support p) hp
  refine ⟨q, hsub, hnot, hlen, ?_⟩
  rcases hcase with rfl | ⟨hstart, ha⟩
  · exact hopen
  · cases q with
    | nil => simp [Walk.blockedAux]
    | fwd e' r =>
      have hr := open_tail_fwd e' r hopen
      have haZ : a ∉ Z := by
        intro haZ
        apply hopen
        cases inc' with
        | start => exact absurd rfl hstart
        | fwd => simp [Walk.blockedAux, haZ]
        | bwd => simp [Walk.blockedAux, haZ]
      cases inc <;> simp [Walk.blockedAux, haZ, hr]
    | bwd e' r =>
      have hr := open_tail_bwd e' r hopen
      cases inc with
      | start => simp [Walk.blockedAux, hr]
      | bwd =>
        have haZ : a ∉ Z := by
          cases p with
          | nil => simp [Walk.support] at ha
          | fwd e rest => intro haZ; apply hp; simp [Walk.blockedAux, haZ]
          | bwd e rest => intro haZ; apply hp; simp [Walk.blockedAux, haZ]
        simp [Walk.blockedAux, haZ, hr]
      | fwd =>
        have hz : ∃ z ∈ Z, G.Reaches a z := by
          cases p with
          | nil => simp [Walk.support] at ha
          | @fwd _ a₁ _ e rest =>
            have hrest := open_tail_fwd e rest hp
            have ha' : a ∈ rest.support := by simpa [Walk.support] using ha
            rcases descend_of_open rest hrest with ⟨z, hz, hreach⟩ | hall
            · exact ⟨z, hz, Reaches.trans G (Reaches.of_edge G e) hreach⟩
            · exfalso
              have h1 := G.rank_strict_mono _ _ e
              have h2 := G.rank_le_of_reaches (hall a ha')
              omega
          | bwd e rest =>
            by_contra hno
            apply hp
            simp only [Walk.blockedAux]
            left
            intro z hz hreach
            exact hno ⟨z, hz, hreach⟩
        intro hb
        simp only [Walk.blockedAux] at hb
        rcases hb with hb | hb
        · obtain ⟨z, hz', hreach⟩ := hz
          exact hb z hz' hreach
        · exact hr hb

/-- **Løkkefjerning.** Fra en åpen vandring finnes en åpen sti med samme
endepunkter, samme innkommende tilstand, og støtte inni den opprinnelige.
Sterk induksjon på lengden: hopp til siste forekomst av startnoden
(`exists_jump`), ta ett steg, og rens resten rekursivt. -/
lemma exists_open_path {Z : Finset V} : ∀ (n : ℕ) {a b : V} (p : Walk G a b),
    p.length ≤ n → ∀ inc : Incoming, ¬ Walk.blockedAux Z inc p →
    ∃ q : Walk G a b, q.IsPath ∧ q.support ⊆ p.support ∧ ¬ Walk.blockedAux Z inc q := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b p hlen inc hp
    obtain ⟨q, hsub, hnot, hqlen, hq⟩ := exists_jump inc p hp
    cases q with
    | nil =>
      exact ⟨Walk.nil _, by simp [Walk.IsPath, Walk.support], hsub, hq⟩
    | @fwd _ a₁ _ e r =>
      have hr := open_tail_fwd e r hq
      have hrlen : r.length < n := by
        simp only [Walk.length] at hqlen
        omega
      obtain ⟨r', hr'path, hr'sub, hr'open⟩ := ih r.length hrlen r le_rfl .fwd hr
      refine ⟨Walk.fwd e r', ?_, ?_, ?_⟩
      · simp only [Walk.IsPath, Walk.support, List.nodup_cons]
        refine ⟨fun ha => hnot ?_, hr'path⟩
        simp only [Walk.support, List.tail_cons]
        exact hr'sub ha
      · intro w hw
        simp only [Walk.support, List.mem_cons] at hw
        rcases hw with rfl | hw
        · exact Walk.start_mem_support p
        · exact hsub (by simp only [Walk.support, List.mem_cons]; exact Or.inr (hr'sub hw))
      · cases inc <;> simp only [Walk.blockedAux] at hq ⊢ <;>
          first
          | exact hr'open
          | exact fun h => h.elim (fun h1 => hq (Or.inl h1)) hr'open
    | @bwd _ a₁ _ e r =>
      have hr := open_tail_bwd e r hq
      have hrlen : r.length < n := by
        simp only [Walk.length] at hqlen
        omega
      obtain ⟨r', hr'path, hr'sub, hr'open⟩ := ih r.length hrlen r le_rfl .bwd hr
      refine ⟨Walk.bwd e r', ?_, ?_, ?_⟩
      · simp only [Walk.IsPath, Walk.support, List.nodup_cons]
        refine ⟨fun ha => hnot ?_, hr'path⟩
        simp only [Walk.support, List.tail_cons]
        exact hr'sub ha
      · intro w hw
        simp only [Walk.support, List.mem_cons] at hw
        rcases hw with rfl | hw
        · exact Walk.start_mem_support p
        · exact hsub (by simp only [Walk.support, List.mem_cons]; exact Or.inr (hr'sub hw))
      · cases inc <;> simp only [Walk.blockedAux] at hq ⊢ <;>
          first
          | exact hr'open
          | exact fun h => h.elim (fun h1 => hq (Or.inl h1)) hr'open

/-- Hovedresultatet: stibasert d-separasjon gir vandringsbasert. Kontrapositivt:
fra en åpen vandring finnes en åpen sti. -/
theorem dsep_of_dsepPath {Z : Finset V} {x y : V} (h : G.DSeparatedPath Z x y) :
    G.DSeparated Z x y := by
  intro p
  by_contra hp
  obtain ⟨q, hq, _, hqo⟩ := exists_open_path p.length p le_rfl .start hp
  exact hqo (h q hq)

/-- Vandringsbasert og stibasert d-separasjon er ekvivalente. -/
theorem dsepPath_iff_dsep {Z : Finset V} {x y : V} :
    G.DSeparatedPath Z x y ↔ G.DSeparated Z x y :=
  ⟨dsep_of_dsepPath, dsepPath_of_dsep⟩

end DAG
end PearlDoCalculus

namespace WalkPath

open PearlDoCalculus DAG

/-- **Klassisk soundness.** Stibasert d-separasjon gir betinget uavhengighet. -/
theorem dsep_sound_path {V : Type*} [DecidableEq V] [Fintype V] {G : DAG V}
    {α : V → Type*} (M : G.CausalModel α) (Z : Finset V) (x y : V)
    (h : G.DSeparatedPath Z x y) : M.CondIndep {x} {y} Z :=
  DSepSound.dsep_sound M Z x y (dsep_of_dsepPath h)

end WalkPath

#print axioms PearlDoCalculus.DAG.Walk.start_mem_support
#print axioms PearlDoCalculus.DAG.Walk.end_mem_support
#print axioms PearlDoCalculus.DAG.dsepPath_of_dsep
#print axioms PearlDoCalculus.DAG.descend_of_open
#print axioms PearlDoCalculus.DAG.exists_fromLast
#print axioms PearlDoCalculus.DAG.exists_jump
#print axioms PearlDoCalculus.DAG.exists_open_path
#print axioms PearlDoCalculus.DAG.dsep_of_dsepPath
#print axioms PearlDoCalculus.DAG.dsepPath_iff_dsep
#print axioms WalkPath.dsep_sound_path
