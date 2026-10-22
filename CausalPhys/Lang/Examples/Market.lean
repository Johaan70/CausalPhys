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
  units P : NOK/item, Qd : item/yr, Qs : item/yr, Imp : item/yr, t : NOK/item,
    y : NOK/yr, w : 1, m.a : item/yr, m.b : item^2/(NOK*yr), m.c : item/NOK,
    m.d : item/yr, m.e : item^2/(NOK*yr), m.f : item/yr
  law demand : Qd = m.a - m.b * P + m.c * y
  law supply : Qs = m.d + m.e * (P - t) + m.f * w
  law clearing : Qd = Qs + Imp
  witness Qd := m.a, Qs := m.d, Imp := m.a - m.d
  setup closed fixes Imp t y w    -- closed economy: imports fixed (normally 0)
  setup open_ fixes P t y w       -- small open economy: the world price is given

namespace Market

variable (m : Params)

/--
info: demand determines P, reading [Qd, y]
supply determines Qs, reading [P, t, w]
clearing determines Qd, reading [Qs, Imp]
cyclic block: [demand, supply, clearing]
-/
#guard_msgs in
#causal_order closed m
/--
info: demand determines Qd, reading [P, y]
supply determines Qs, reading [P, t, w]
clearing determines Imp, reading [Qd, Qs]
acyclic: every intervention has exactly one outcome of the causal model
-/
#guard_msgs in
#causal_order open_ m
/--
info: cyclic, linear in each block: exactly one outcome of the causal model for every choice of the exogenous values (proved by block_linear)
-/
#guard_msgs in
#causal_check closed m
/--
info: acyclic: every intervention has exactly one outcome of the causal model (Setup.do_existsUnique; it satisfies the laws when it lies in the domain)
-/
#guard_msgs in
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

/-- The market laws themselves (demand, supply, clearing) have exactly one
    solution with the given exogenous values; the domain is everything here. -/
theorem closed_laws (u : V → ℝ) :
    ∃! s, (model m).dom s ∧ (model m).Sat s ∧ ∀ v, v ∈ (closed m).exo → s v = u v :=
  (closed m).laws_existsUnique (closed_existsUnique u) fun _ _ => trivial

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

/-! ## A price ceiling: an intervention inside the equilibrium block

  In the closed economy price and quantities are one block. Holding the price
  fixed can mean two different things, and the language makes the user say
  which law is switched off (the price itself becomes fixed by the lab):

  * Pearl's do(P := c) switches off the law that determines P in the computed
    reading, here demand. Buyers then simply absorb what is supplied.
  * A price ceiling switches off market clearing: buyers still follow demand,
    sellers still follow supply, and the gap is excess demand. -/

section Ceiling

variable (m : Params)

/--
info: demand determines Qd, reading [P, y]
supply determines Qs, reading [P, t, w]
acyclic: every intervention has exactly one outcome of the causal model
-/
#guard_msgs in
#causal_order (closed m).intervene .clearing .P
/--
info: supply determines Qs, reading [P, t, w]
clearing determines Qd, reading [Qs, Imp]
acyclic: every intervention has exactly one outcome of the causal model
-/
#guard_msgs in
#causal_order (closed m).intervene .demand .P

/-- Switching off demand is Pearl's do(P := c) in this setup. -/
theorem demand_reading_is_do (c : ℝ) (u s : V → ℝ) :
    ((closed m).intervene .demand .P).scm.Solves (Function.update u .P c) s ↔
      ((closed m).scm.doI .P c).Solves u s :=
  (closed m).intervene_iff_doI (by struct_decide) c u s trivial

/-- The price ceiling has exactly one outcome. -/
theorem ceiling_existsUnique (u : V → ℝ) :
    ∃! s, ((closed m).intervene .clearing .P).scm.Solves u s :=
  Setup.existsUnique _ (by struct_decide) u

variable {m}

/-- Under a price ceiling at `u .P`, excess demand is (b + e)·(P* − u .P), where
    P* is the equilibrium price: positive when the ceiling binds. -/
theorem ceiling_excess_demand {u s : V → ℝ}
    (hs : ((closed m).intervene .clearing .P).scm.Solves u s) :
    s .Qd - s .Qs - u .Imp =
      (m.b + m.e) * ((m.a + m.c * u .y - m.d + m.e * u .t - m.f * u .w - u .Imp) / (m.b + m.e)
        - u .P) := by
  read_solution hs
  have hbe : m.b + m.e ≠ 0 := (add_pos m.hb m.he).ne'
  rw [hs_Qd, hs_Qs, hs_P, hs_y, hs_t, hs_w]
  field_simp
  ring

/-- Under Pearl's do(P := c) instead, buyers take exactly what is supplied plus
    imports: there is no excess demand, and the demand curve no longer holds. -/
theorem do_reading_no_excess {u s : V → ℝ}
    (hs : ((closed m).intervene .demand .P).scm.Solves u s) :
    s .Qd - s .Qs - u .Imp = 0 := by
  read_solution hs
  rw [hs_Qd, hs_Imp]
  ring

end Ceiling

end Market

end CausalPhys.Examples
