/-
  CausalPhys.SimonOrder — fra ligningssystem til kausal modell.

  Simon (1953): en kausal modell er et ligningssystem PLUSS en lesning som sier
  hvilken ligning som bestemmer hvilken variabel (en perfekt matching mellom
  ligninger og endogene variabler). Denne modulen formaliserer det og beviser:

    1. `solves_iff`       Løsningene til den kausale modellen er nøyaktig løsningene
                          til ligningssystemet (med de eksogene variablene satt).
    2. `obs_equiv`        To ulike lesninger av samme system har samme mulige
                          tilstander. Kausal orden er IKKE en egenskap ved løsningsmengden.
    3. `doI_iff`          do(x := c) er det samme som å stryke ligningen som bestemmer x
                          og legge til x = c. Grafkirurgi = ligningskirurgi.
    4. Gass: oppsett A og B fra Physics.lean er to lesninger av ÉN ligning;
       de er observasjonelt like, men svarer ulikt på do(T).
-/
import CausalPhys.Core
import CausalPhys.Physics

set_option linter.unusedSectionVars false

namespace CausalPhys

universe u

/-- En ligning: en relasjon på tilstander, med variablene den nevner. -/
structure Equation (V : Type) (α : Type u) where
  vars   : List V
  holds  : (V → α) → Prop
  local_ : ∀ s t : V → α, (∀ v, v ∈ vars → s v = t v) → (holds s ↔ holds t)

variable {E V : Type} {α : Type u}

/-- `s` oppfyller alle ligningene. -/
def Sat (eqs : E → Equation V α) (s : V → α) : Prop := ∀ e, (eqs e).holds s

/-- En Simon-lesning av et ligningssystem på domenet `D`:
    * `read v = some (e, m)`: ligning `e` bestemmer `v`, løst som mekanismen `m`;
    * `read v = none`: `v` er eksogen;
    * `sound`: på `D` er «ligningen holder» det samme som «v = m(s)»;
    * `cover` og `inj`: hver ligning brukes av nøyaktig én variabel (perfekt matching). -/
structure Reading (eqs : E → Equation V α) (D : (V → α) → Prop) where
  read  : V → Option (E × Mech V α)
  sound : ∀ v e m, read v = some (e, m) → ∀ s, D s → ((eqs e).holds s ↔ s v = m.f s)
  cover : ∀ e, ∃ v m, read v = some (e, m)
  inj   : ∀ v w e m m', read v = some (e, m) → read w = some (e, m') → v = w

namespace Reading

variable {eqs : E → Equation V α} {D : (V → α) → Prop}

/-- Den kausale modellen lesningen gir. -/
def toSCM (R : Reading eqs D) : SCM V α := ⟨fun v => (R.read v).map Prod.snd⟩

theorem mech_some (R : Reading eqs D) {v : V} {e : E} {m : Mech V α}
    (h : R.read v = some (e, m)) : R.toSCM.mech v = some m := by
  simp [toSCM, h]

theorem mech_none (R : Reading eqs D) {v : V} (h : R.read v = none) :
    R.toSCM.mech v = none := by
  simp [toSCM, h]

/-- 1. Kausal modell og ligningssystem har de samme løsningene. -/
theorem solves_iff (R : Reading eqs D) (u s : V → α) (hD : D s) :
    R.toSCM.Solves u s ↔ Sat eqs s ∧ ∀ v, R.read v = none → s v = u v := by
  constructor
  · intro h
    refine ⟨fun e => ?_, fun v hv => ?_⟩
    · obtain ⟨v, m, hv⟩ := R.cover e
      have hs := h v
      rw [R.mech_some hv] at hs
      exact (R.sound v e m hv s hD).2 hs
    · have hs := h v
      rw [R.mech_none hv] at hs
      exact hs
  · rintro ⟨hsat, hexo⟩ v
    cases hr : R.read v with
    | none =>
      rw [R.mech_none hr]
      exact hexo v hr
    | some p =>
      obtain ⟨e, m⟩ := p
      rw [R.mech_some hr]
      exact (R.sound v e m hr s hD).1 (hsat e)

/-- 2. Observasjonell ekvivalens: to lesninger av samme system tillater de samme
    tilstandene. Data alene kan ikke skille dem. -/
theorem obs_equiv (R₁ R₂ : Reading eqs D) (s : V → α) (hD : D s) :
    (∃ u, R₁.toSCM.Solves u s) ↔ (∃ u, R₂.toSCM.Solves u s) := by
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨s, (R₂.solves_iff s s hD).2 ⟨((R₁.solves_iff u s hD).1 hu).1, fun _ _ => rfl⟩⟩
  · rintro ⟨u, hu⟩
    exact ⟨s, (R₁.solves_iff s s hD).2 ⟨((R₂.solves_iff u s hD).1 hu).1, fun _ _ => rfl⟩⟩

variable [DecidableEq V]

/-- 3. do(x := c) = stryk ligningen som bestemmer x, legg til x = c. -/
theorem doI_iff (R : Reading eqs D) (x : V) (c : α) (u s : V → α) (hD : D s) :
    (R.toSCM.doI x c).Solves u s ↔
      s x = c ∧
      (∀ e, (∀ m, R.read x ≠ some (e, m)) → (eqs e).holds s) ∧
      (∀ v, v ≠ x → R.read v = none → s v = u v) := by
  constructor
  · intro h
    refine ⟨SCM.doI_self _ x c u s h, fun e he => ?_, fun v hvx hv => ?_⟩
    · obtain ⟨v, m, hv⟩ := R.cover e
      have hvx : v ≠ x := by
        rintro rfl
        exact he m hv
      have hs := SCM.doI_other R.toSCM c u s m hvx (R.mech_some hv) h
      exact (R.sound v e m hv s hD).2 hs
    · exact SCM.doI_exo R.toSCM c u s hvx (R.mech_none hv) h
  · rintro ⟨hx, heq, hexo⟩ v
    by_cases hvx : v = x
    · subst hvx
      have hm : (R.toSCM.doI v c).mech v = some (SCM.Mech.const c) := by simp [SCM.doI]
      rw [hm]
      exact hx
    · rw [SCM.doI_mech_ne _ c hvx]
      cases hr : R.read v with
      | none =>
        rw [R.mech_none hr]
        exact hexo v hvx hr
      | some p =>
        obtain ⟨e, m⟩ := p
        rw [R.mech_some hr]
        apply (R.sound v e m hr s hD).1
        apply heq
        intro m' hx'
        exact hvx (R.inj v x e m m' hr hx')

end Reading

/-! ## Gass: én ligning, to lesninger -/

/-- Systemet har én ligning: pV = nRT. -/
def gasEqs : Unit → Equation Gas ℝ := fun _ =>
  { vars := [.p, .Vol, .n, .T]
    holds := idealGas
    local_ := by
      intro s t h
      simp only [idealGas]
      rw [h .p (by simp), h .Vol (by simp), h .n (by simp), h .T (by simp)] }

/-- Domenet: trykk og volum er ikke null. -/
def gasDom (s : Gas → ℝ) : Prop := s .Vol ≠ 0 ∧ s .p ≠ 0

/-- Lesning A: ligningen løses for p. -/
noncomputable def readA : Reading gasEqs gasDom where
  read := fun | .p => some ((), mechP) | _ => none
  sound := by
    intro v e m h s hD
    cases v <;> simp at h
    obtain ⟨rfl, rfl⟩ := h
    show s .p * s .Vol = s .n * R * s .T ↔ s .p = s .n * R * s .T / s .Vol
    rw [eq_div_iff hD.1]
  cover := fun e => ⟨.p, mechP, rfl⟩
  inj := by
    intro v w e m m' hv hw
    cases v <;> cases w <;> simp at hv hw ⊢

/-- Lesning B: ligningen løses for V. -/
noncomputable def readB : Reading gasEqs gasDom where
  read := fun | .Vol => some ((), mechV) | _ => none
  sound := by
    intro v e m h s hD
    cases v <;> simp at h
    obtain ⟨rfl, rfl⟩ := h
    show s .p * s .Vol = s .n * R * s .T ↔ s .Vol = s .n * R * s .T / s .p
    rw [eq_div_iff hD.2, mul_comm (s .Vol)]
  cover := fun e => ⟨.Vol, mechV, rfl⟩
  inj := by
    intro v w e m m' hv hw
    cases v <;> cases w <;> simp at hv hw ⊢

/-- Lesningene gir nøyaktig oppsettene fra Physics.lean. -/
theorem readA_eq : readA.toSCM = setupA := by
  simp only [Reading.toSCM, setupA, SCM.mk.injEq]
  funext v
  cases v <;> rfl

theorem readB_eq : readB.toSCM = setupB := by
  simp only [Reading.toSCM, setupB, SCM.mk.injEq]
  funext v
  cases v <;> rfl

/-- Observasjonelt like: hver tilstand som er mulig i A, er mulig i B, og omvendt. -/
theorem gas_obs_equiv (s : Gas → ℝ) (hD : gasDom s) :
    (∃ u, setupA.Solves u s) ↔ (∃ u, setupB.Solves u s) := by
  rw [← readA_eq, ← readB_eq]
  exact readA.obs_equiv readB s hD

/-- … men kausalt ulike: med samme utgangspunkt og samme do(T := 2)
    blir volumet 1 i A og 2 i B. -/
theorem gas_interv_differ : ∃ u s s' : Gas → ℝ,
    (setupA.doI .T 2).Solves u s ∧ (setupB.doI .T 2).Solves u s' ∧ s .Vol ≠ s' .Vol := by
  have hR : R ≠ 0 := R_pos.ne'
  let u : Gas → ℝ := fun | .p => R | _ => 1
  let s : Gas → ℝ := fun | .p => 2 * R | .T => 2 | _ => 1
  let s' : Gas → ℝ := fun | .p => R | .T => 2 | .Vol => 2 | .n => 1
  refine ⟨u, s, s', ?_, ?_, ?_⟩
  · intro v
    cases v <;> simp [SCM.doI, SCM.Mech.const, setupA, mechP, s, u]
    ring
  · intro v
    cases v <;> simp [SCM.doI, SCM.Mech.const, setupB, mechV, s', u]
    field_simp
  · simp [s, s']

end CausalPhys
