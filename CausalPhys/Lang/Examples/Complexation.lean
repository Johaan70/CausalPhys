/-
  Chemistry: stepwise complexation (e.g. Ag⁺ + NH₃), with a closed flask or a
  ligand buffer.

      M + L  ⇌ ML      [ML]  = K₁·[M]·[L]
      ML + L ⇌ ML₂     [ML₂] = K₂·[ML]·[L]
      metal balance    m₀ = [M] + [ML] + [ML₂]
      ligand balance   l₀ = [L] + [ML] + 2·[ML₂]

  Lean computes that the closed flask is one cyclic block of four laws, while
  with a ligand buffer the ligand balance determines l₀ (how much ligand the
  buffer delivered) and the block shrinks to three. Uniqueness in the cyclic
  block is the chemistry (a monotonicity argument from `CausalPhys.Complexation`);
  Le Chatelier is an intervention do(m₀ := more).
-/
import CausalPhys.Lang.Syntax
import CausalPhys.Complexation

open CausalPhys CausalPhys.Lang

namespace CausalPhys.Examples

/-- The two equilibrium constants (fixed at a given temperature). -/
structure Complexation.Consts where
  K1 : ℝ
  K2 : ℝ
  hK1 : 0 < K1
  hK2 : 0 < K2

causal_model Complexation (c : Complexation.Consts) where
  variables M L ML ML2 m0 l0
  domain 0 < M ∧ 0 < L
  law k1 : ML = c.K1 * M * L
    solve ML := c.K1 * M * L
  law k2 : ML2 = c.K2 * ML * L
    solve ML2 := c.K2 * ML * L
  law metal : m0 = M + ML + ML2
    solve M := m0 - ML - ML2
    solve m0 := M + ML + ML2
  law ligand : l0 = L + ML + 2 * ML2
    solve L := l0 - ML - 2 * ML2
    solve l0 := L + ML + 2 * ML2
  setup closed fixes m0 l0        -- closed flask: the amounts added are fixed
  setup buffered fixes m0 L       -- ligand buffer: free ligand held fixed

namespace Complexation

variable (c : Consts)

#causal_order closed c
#causal_order buffered c

/-! ## Computed by Lean -/

theorem closed_one_block : (closed c).block .k1 = [.k1, .k2, .metal, .ligand] := by
  struct_decide
theorem closed_cyclic : ¬ (closed c).Acyclic := by struct_decide

theorem buffered_ligand_determines_l0 : (buffered c).determines .ligand = .l0 := by
  struct_decide
theorem buffered_block : (buffered c).block .k1 = [.k1, .k2, .metal] := by struct_decide
theorem buffered_ligand_alone : (buffered c).block .ligand = [.ligand] := by struct_decide

/-! ## The chemistry, as one domain-specific lemma -/

variable {c}

/-- The amounts added are positive whenever the laws hold. -/
theorem m0_pos {s : V → ℝ} (hD : (model c).dom s) (h : (model c).Sat s) : 0 < s .m0 := by
  have h1 : s .ML = c.K1 * s .M * s .L := h .k1
  have h2 : s .ML2 = c.K2 * s .ML * s .L := h .k2
  have h3 : s .m0 = s .M + s .ML + s .ML2 := h .metal
  have := c.hK1; have := c.hK2; have := hD.1; have := hD.2
  have : 0 < s .ML := by rw [h1]; positivity
  have : 0 < s .ML2 := by rw [h2]; positivity
  linarith

theorem l0_pos {s : V → ℝ} (hD : (model c).dom s) (h : (model c).Sat s) : 0 < s .l0 := by
  have h1 : s .ML = c.K1 * s .M * s .L := h .k1
  have h2 : s .ML2 = c.K2 * s .ML * s .L := h .k2
  have h4 : s .l0 = s .L + s .ML + 2 * s .ML2 := h .ligand
  have := c.hK1; have := c.hK2; have := hD.1; have := hD.2
  have : 0 < s .ML := by rw [h1]; positivity
  have : 0 < s .ML2 := by rw [h2]; positivity
  linarith

/-- The state, seen as an instance of the equilibrium problem. -/
def sysOf (s : V → ℝ) (hD : (model c).dom s) (h : (model c).Sat s) : Complex.Sys :=
  ⟨s .m0, s .l0, c.K1, c.K2, m0_pos hD h, l0_pos hD h, c.hK1, c.hK2⟩

theorem isEq {s : V → ℝ} (hD : (model c).dom s) (h : (model c).Sat s) :
    (sysOf s hD h).IsEq (s .M) (s .L) (s .ML) (s .ML2) :=
  ⟨hD.1, hD.2, h .k1, h .k2, h .metal, h .ligand⟩

/-! ## Closed flask: uniqueness and Le Chatelier -/

/-- The cyclic block has exactly one solution on the physical domain. -/
theorem closed_unique {u s t : V → ℝ} (hDs : (model c).dom s) (hDt : (model c).dom t)
    (hs : (closed c).scm.Solves u s) (ht : (closed c).scm.Solves u t) : s = t := by
  refine (closed c).unique_of_laws ?_ hDs hDt hs ht
  intro s t hDs hDt hss hst hex
  have hm := hex .m0 (by simp [closed])
  have hl := hex .l0 (by simp [closed])
  have h1 := isEq hDs hss
  have h2 : (sysOf s hDs hss).IsEq (t .M) (t .L) (t .ML) (t .ML2) :=
    ⟨hDt.1, hDt.2, hst .k1, hst .k2, hm.trans (hst .metal), hl.trans (hst .ligand)⟩
  have := (sysOf s hDs hss).eq_exists_unique.unique
    (y₁ := (s .M, s .L, s .ML, s .ML2)) (y₂ := (t .M, t .L, t .ML, t .ML2)) h1 h2
  simp only [Prod.mk.injEq] at this
  obtain ⟨e1, e2, e3, e4⟩ := this
  funext v
  cases v <;> assumption

/-- Le Chatelier as an intervention: do(m₀ := more) lowers the free ligand and
    raises the bound ligand. -/
theorem le_chatelier {u s s' : V → ℝ} {m : ℝ} (hm : u .m0 < m)
    (hD : (model c).dom s) (hD' : (model c).dom s')
    (hs : (closed c).scm.Solves u s) (hs' : ((closed c).scm.doI .m0 m).Solves u s') :
    s' .L < s .L ∧ s .ML + 2 * s .ML2 < s' .ML + 2 * s' .ML2 := by
  rw [(closed c).do_exo_iff (by simp [closed])] at hs'
  obtain ⟨hsat, hex⟩ := ((closed c).solves_iff u s hD).1 hs
  obtain ⟨hsat', hex'⟩ := ((closed c).solves_iff _ s' hD').1 hs'
  have hl : s' .l0 = s .l0 := by
    rw [hex' .l0 (by simp [closed]), hex .l0 (by simp [closed])]
    simp
  have hmm : s .m0 < s' .m0 := by
    rw [hex' .m0 (by simp [closed]), hex .m0 (by simp [closed])]
    simpa using hm
  exact Complex.Sys.more_metal_less_free_ligand (sysOf s hD hsat) (sysOf s' hD' hsat')
    hl rfl rfl hmm (isEq hD hsat) (isEq hD' hsat')

/-! ## Buffer -/

/-- With a ligand buffer, the free metal has a closed form, and the ligand
    balance only reports how much ligand the buffer delivered. -/
theorem buffered_solution {u s : V → ℝ} (hD : (model c).dom s)
    (hs : (buffered c).scm.Solves u s) :
    s .M = u .m0 / (1 + c.K1 * u .L + c.K1 * c.K2 * u .L ^ 2) ∧
    s .l0 = s .L + s .ML + 2 * s .ML2 := by
  obtain ⟨hsat, hex⟩ := ((buffered c).solves_iff u s hD).1 hs
  have hL := hex .L (by simp [buffered])
  have hm := hex .m0 (by simp [buffered])
  have key := ((sysOf s hD hsat).buffered_eq (s .L) hD.2 (s .M) (s .ML) (s .ML2)).1
    ⟨hD.1, hsat .k1, hsat .k2, hsat .metal⟩
  refine ⟨?_, hsat .ligand⟩
  rw [key.1, ← hL, ← hm]
  rfl

end Complexation

end CausalPhys.Examples
