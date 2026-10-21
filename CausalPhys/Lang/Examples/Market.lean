/-
  Economics: one market, written once.

      demand    Q_d = a − b·P + c·y                (y: income)
      supply    Q_s = d + e·(P − t) + f·w          (t: tax per unit, w: weather)
      clearing  Q_d = Q_s + Imp                    (Imp: imports)

  Two lab setups, i.e. two economies:

    * closed economy (imports fixed, normally 0) → Lean computes: price and both
      quantities form ONE cyclic block, the market equilibrium. Uniqueness is
      the economics (b + e ≠ 0), plugged into the core's `unique_of_laws`.
    * small open economy (the price is the world price) → Lean computes: the
      model is acyclic; demand gives Q_d, supply gives Q_s, and the clearing
      condition now DETERMINES the imports.

  The same tax increase do(t := t + Δ) then gets two different answers:
    * closed: the price rises by e/(b+e)·Δ (consumers carry part of the tax);
    * open: the price does not move, and imports rise by e·Δ (producers carry
      all of it, domestic production is replaced by imports).
-/
import CausalPhys.Lang.Core
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

namespace CausalPhys.Lang.Market

/-- Slopes and intercepts of demand and supply. -/
structure Params where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  e : ℝ
  f : ℝ
  hb : 0 < b
  he : 0 < e

inductive V | P | Qd | Qs | Imp | t | y | w
deriving DecidableEq, Repr

instance : Inhabited V := ⟨.P⟩

inductive Law | demand | supply | clearing
deriving DecidableEq, Repr

variable (m : Params)

noncomputable section

def model : Model Law V ℝ where
  eqList := [.demand, .supply, .clearing]
  varList := [.P, .Qd, .Qs, .Imp, .t, .y, .w]
  law
    | .demand, s => s .Qd = m.a - m.b * s .P + m.c * s .y
    | .supply, s => s .Qs = m.d + m.e * (s .P - s .t) + m.f * s .w
    | .clearing, s => s .Qd = s .Qs + s .Imp
  solvers
    | .demand => [(.Qd, mech [.P, .y] fun s => m.a - m.b * s .P + m.c * s .y),
                  (.P, mech [.Qd, .y] fun s => (m.a + m.c * s .y - s .Qd) / m.b)]
    | .supply => [(.Qs, mech [.P, .t, .w] fun s => m.d + m.e * (s .P - s .t) + m.f * s .w),
                  (.P, mech [.Qs, .t, .w] fun s => (s .Qs - m.d - m.f * s .w) / m.e + s .t)]
    | .clearing => [(.Qd, mech [.Qs, .Imp] fun s => s .Qs + s .Imp),
                    (.Qs, mech [.Qd, .Imp] fun s => s .Qd - s .Imp),
                    (.Imp, mech [.Qd, .Qs] fun s => s .Qd - s .Qs)]
  sound := by
    have hb := m.hb.ne'
    have he := m.he.ne'
    intro e v mm h s _
    cases e <;> simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Iff.rfl
      · show s .Qd = m.a - m.b * s .P + m.c * s .y ↔ s .P = (m.a + m.c * s .y - s .Qd) / m.b
        rw [eq_div_iff hb]
        constructor <;> intro h <;> linear_combination h
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Iff.rfl
      · show s .Qs = m.d + m.e * (s .P - s .t) + m.f * s .w ↔
          s .P = (s .Qs - m.d - m.f * s .w) / m.e + s .t
        constructor <;> intro h <;> rw [h] <;> field_simp <;> ring
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Iff.rfl
      · show s .Qd = s .Qs + s .Imp ↔ s .Qs = s .Qd - s .Imp
        constructor <;> intro h <;> linarith
      · show s .Qd = s .Qs + s .Imp ↔ s .Imp = s .Qd - s .Qs
        constructor <;> intro h <;> linarith

/-- Closed economy: imports are fixed (normally zero). -/
def closed : Setup (model m) := { exo := [.Imp, .t, .y, .w] }

/-- Small open economy: the price is the world price. -/
def open_ : Setup (model m) := { exo := [.P, .t, .y, .w] }

end

/-! ## Computed by Lean -/

theorem closed_one_block : (closed m).block .demand = [.demand, .supply, .clearing] := by
  struct_decide
theorem closed_cyclic : ¬ (closed m).Acyclic := by struct_decide

theorem open_order :
    (open_ m).determines .demand = .Qd ∧ (open_ m).determines .supply = .Qs ∧
    (open_ m).determines .clearing = .Imp := by struct_decide
theorem open_acyclic : (open_ m).Acyclic := by struct_decide

variable {m}

/-! ## Closed economy: the equilibrium -/

/-- Every state satisfying the laws has the equilibrium price. -/
theorem price_of_laws {s : V → ℝ} (h : (model m).Sat s) :
    s .P = (m.a + m.c * s .y - m.d + m.e * s .t - m.f * s .w - s .Imp) / (m.b + m.e) := by
  have hD : s .Qd = m.a - m.b * s .P + m.c * s .y := h .demand
  have hS : s .Qs = m.d + m.e * (s .P - s .t) + m.f * s .w := h .supply
  have hC : s .Qd = s .Qs + s .Imp := h .clearing
  have hbe : m.b + m.e ≠ 0 := (add_pos m.hb m.he).ne'
  rw [eq_div_iff hbe]
  linear_combination hD - hC - hS

/-- The cyclic block has exactly one solution. -/
theorem closed_unique {u s s' : V → ℝ} (hs : (closed m).scm.Solves u s)
    (hs' : (closed m).scm.Solves u s') : s = s' := by
  refine (closed m).unique_of_laws ?_ trivial trivial hs hs'
  intro s s' _ _ h h' hex
  have hI := hex .Imp (by simp [closed])
  have ht := hex .t (by simp [closed])
  have hy := hex .y (by simp [closed])
  have hw := hex .w (by simp [closed])
  have hP : s .P = s' .P := by rw [price_of_laws h, price_of_laws h', hI, ht, hy, hw]
  have hQd : s .Qd = s' .Qd := by rw [h .demand, h' .demand, hP, hy]
  have hQs : s .Qs = s' .Qs := by rw [h .supply, h' .supply, hP, ht, hw]
  funext v
  cases v <;> assumption

/-- Price in the closed economy, read off a solution. -/
theorem closed_price {u s : V → ℝ} (hs : (closed m).scm.Solves u s) :
    s .P = (m.a + m.c * u .y - m.d + m.e * u .t - m.f * u .w - u .Imp) / (m.b + m.e) := by
  obtain ⟨h, hex⟩ := ((closed m).solves_iff u s trivial).1 hs
  rw [price_of_laws h, hex .Imp (by simp [closed]), hex .t (by simp [closed]),
    hex .y (by simp [closed]), hex .w (by simp [closed])]

/-- Tax incidence in the closed economy: the price rises by e/(b+e)·Δ. -/
theorem closed_tax {u s s' : V → ℝ} (Δ : ℝ) (hs : (closed m).scm.Solves u s)
    (hs' : ((closed m).scm.doI .t (u .t + Δ)).Solves u s') :
    s' .P - s .P = m.e / (m.b + m.e) * Δ := by
  rw [(closed m).do_exo_iff (by simp [closed])] at hs'
  rw [closed_price hs', closed_price hs]
  simp only [Function.update_apply, reduceCtorEq, ↓reduceIte]
  have hbe : m.b + m.e ≠ 0 := (add_pos m.hb m.he).ne'
  field_simp
  ring

/-! ## Small open economy -/

/-- In the open economy the solution is read off the three formulas. -/
theorem open_solution {u s : V → ℝ} (hs : (open_ m).scm.Solves u s) :
    s .P = u .P ∧ s .Qd = m.a - m.b * u .P + m.c * u .y ∧
    s .Qs = m.d + m.e * (u .P - u .t) + m.f * u .w ∧ s .Imp = s .Qd - s .Qs := by
  have hP := (open_ m).exo_eq hs (v := .P) (by simp [open_])
  have ht := (open_ m).exo_eq hs (v := .t) (by simp [open_])
  have hy := (open_ m).exo_eq hs (v := .y) (by simp [open_])
  have hw := (open_ m).exo_eq hs (v := .w) (by simp [open_])
  have hD := (open_ m).mech_eq hs .demand
  have hS := (open_ m).mech_eq hs .supply
  have hC := (open_ m).mech_eq hs .clearing
  obtain ⟨o1, o2, o3⟩ := open_order m
  rw [o1] at hD; rw [o2] at hS; rw [o3] at hC
  simp [Model.mechOf, Model.find, model, mech] at hD hS hC
  refine ⟨hP, ?_, ?_, hC⟩
  · rw [hD, hP, hy]
  · rw [hS, hP, ht, hw]

/-- Tax incidence in the small open economy: the price does not move, and
    imports rise by e·Δ. -/
theorem open_tax {u s s' : V → ℝ} (Δ : ℝ) (hs : (open_ m).scm.Solves u s)
    (hs' : ((open_ m).scm.doI .t (u .t + Δ)).Solves u s') :
    s' .P = s .P ∧ s' .Imp - s .Imp = m.e * Δ := by
  rw [(open_ m).do_exo_iff (by simp [open_])] at hs'
  obtain ⟨p1, d1, q1, i1⟩ := open_solution hs
  obtain ⟨p2, d2, q2, i2⟩ := open_solution hs'
  simp only [Function.update_apply, reduceCtorEq, ↓reduceIte] at p2 d2 q2
  refine ⟨by rw [p1, p2], ?_⟩
  rw [i1, i2, d1, d2, q1, q2]
  ring

/-- Every intervention in the open economy has exactly one outcome. -/
theorem open_do (x : V) (c : ℝ) (u : V → ℝ) : ∃! s, ((open_ m).scm.doI x c).Solves u s :=
  (open_ m).do_existsUnique (open_acyclic m) x c u

end CausalPhys.Lang.Market
