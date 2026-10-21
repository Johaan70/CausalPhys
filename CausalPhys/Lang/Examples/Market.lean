/-
  Economics: one market, in a closed economy or a small open economy.

      demand    Q_d = a − b·P + c·y                (y: income)
      supply    Q_s = d + e·(P − t) + f·w          (t: tax per unit, w: weather)
      clearing  Q_d = Q_s + Imp                    (Imp: imports)

  Lean computes that the closed economy is one cyclic block (the market
  equilibrium), while in the small open economy (world price fixed) the model
  is acyclic and the clearing condition determines the imports. The same tax
  increase then gets two answers: in the closed economy the price rises by
  e/(b+e)·Δ; in the open economy the price stays and imports rise by e·Δ.
-/
import CausalPhys.Lang.Syntax

open CausalPhys CausalPhys.Lang

namespace CausalPhys.Examples

/-- Slopes and intercepts of demand and supply. -/
structure Market.Params where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  e : ℝ
  f : ℝ
  hb : 0 < b
  he : 0 < e

causal_model Market (m : Market.Params) where
  variables P Qd Qs Imp t y w
  law demand : Qd = m.a - m.b * P + m.c * y
    solve Qd := m.a - m.b * P + m.c * y
    solve P := (m.a + m.c * y - Qd) / m.b by have := m.hb.ne'; law_solve
  law supply : Qs = m.d + m.e * (P - t) + m.f * w
    solve Qs := m.d + m.e * (P - t) + m.f * w
    solve P := (Qs - m.d - m.f * w) / m.e + t by have := m.he.ne'; law_solve
  law clearing : Qd = Qs + Imp
    solve Qd := Qs + Imp
    solve Qs := Qd - Imp
    solve Imp := Qd - Qs
  setup closed fixes Imp t y w    -- closed economy: imports fixed (normally 0)
  setup open_ fixes P t y w       -- small open economy: the world price is given

namespace Market

variable (m : Params)

#causal_order closed m
#causal_order open_ m
#causal_check closed m
#causal_check open_ m

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

/-- The closed economy has exactly one equilibrium for every choice of the
    exogenous values. `linear_block` does the linear algebra; what is left,
    1 + e/b ≠ 0, is the economics (demand falls and supply rises with price). -/
theorem closed_existsUnique (u : V → ℝ) : ∃! s, (closed m).scm.Solves u s := by
  linear_block
  have := m.hb; have := m.he; positivity

theorem closed_unique {u s s' : V → ℝ} (hs : (closed m).scm.Solves u s)
    (hs' : (closed m).scm.Solves u s') : s = s' :=
  (closed_existsUnique u).unique hs hs'

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
  read_solution hs
  refine ⟨hs_P, ?_, ?_, hs_Imp⟩
  · rw [hs_Qd, hs_P, hs_y]
  · rw [hs_Qs, hs_P, hs_t, hs_w]

/-- Tax incidence in the small open economy: the price does not move, and
    imports rise by e·Δ. -/
theorem open_tax {u s s' : V → ℝ} (Δ : ℝ) (hs : (open_ m).scm.Solves u s)
    (hs' : ((open_ m).scm.doI .t (u .t + Δ)).Solves u s') :
    s' .P = s .P ∧ s' .Imp - s .Imp = m.e * Δ := by
  read_solution hs
  read_solution hs'
  refine ⟨by rw [hs_P, hs'_P], ?_⟩
  rw [hs_Imp, hs'_Imp, hs_Qd, hs'_Qd, hs_Qs, hs'_Qs, hs_P, hs'_P, hs_y, hs'_y, hs_t, hs'_t,
    hs_w, hs'_w]
  ring

/-- Every intervention in the open economy has exactly one outcome. -/
theorem open_do (x : V) (c : ℝ) (u : V → ℝ) : ∃! s, ((open_ m).scm.doI x c).Solves u s :=
  (open_ m).do_existsUnique (open_acyclic m) x c u

end Market

end CausalPhys.Examples
