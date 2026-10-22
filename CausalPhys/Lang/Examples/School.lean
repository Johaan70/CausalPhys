/-
  Lower secondary school (10th grade): the laws behind docs/kausal-10.html.

  Each law is written once; each setup says what the experiment holds fixed.
  Lean computes which quantity the law determines (the effect), and the numbers
  for one set of values, so the page's answers are checked here:

    * force and motion: F = m·a, and v = a·t from rest;
    * work, power and the law of energy: W = m·g·h, P·t = W, and
      Ep₀ = Ep + Ek + Q on a slope (Q: heat from friction);
    * electricity: U = R·I, and P = U·I for the lamp.

  The numbers on the page are computed in the browser with the same formulas.
-/
import CausalPhys.Lang.Syntax

open CausalPhys CausalPhys.Lang

namespace CausalPhys.Examples

/-! ## Force and motion -/

causal_model Newton where
  variables F m a
  units F : N, m : kg, a : m/s^2
  domain 0 < m
  law newton : F = m * a
  witness F := 1, m := 1, a := 1
  setup sameForce fixes F m      -- the same pull, different loads: a follows
  setup sameAcc fixes m a        -- the same start, different loads: F is needed

/--
info: newton determines a, reading [F, m]
acyclic: every intervention has exactly one outcome of the causal model
-/
#guard_msgs in
#causal_order Newton.sameForce
/--
info: newton determines F, reading [m, a]
acyclic: every intervention has exactly one outcome of the causal model
-/
#guard_msgs in
#causal_order Newton.sameAcc

-- 10 N on a 2 kg cart gives 5 m/s².
/--
info: F = 10  (fixed)
m = 2  (fixed)
a = 5  (computed)
proved: in the domain, satisfies every law, and is the only outcome of the setup with these fixed values
-/
#guard_msgs in
#causal_eval Newton.sameForce with F := 10, m := 2

causal_model Speed where
  variables v a t
  units v : m/s, a : m/s^2, t : s
  domain 0 < t
  law speed : v = a * t
  witness v := 1, a := 1, t := 1
  setup accelerate fixes a t      -- speeding up for a while: v follows
  setup reach fixes v t           -- reach a speed in a given time: a is needed

/--
info: speed determines a, reading [v, t]
acyclic: every intervention has exactly one outcome of the causal model
-/
#guard_msgs in
#causal_order Speed.reach

/-! ## Work, power and energy -/

causal_model Lift where
  variables m g h W P t
  units m : kg, g : m/s^2, h : m, W : J, P : W, t : s
  domain 0 < t ∧ 0 < P
  law work : W = m * g * h
  law power : P * t = W
  witness m := 1, g := 1, h := 1, W := 1, P := 1, t := 1
  setup sameTime fixes m g h t   -- the same stairs in the same time: W, then P
  setup motor fixes m g h P      -- a motor with fixed power: W, then t

/--
info: work determines W, reading [m, g, h]
power determines P, reading [W, t]
acyclic: every intervention has exactly one outcome of the causal model
-/
#guard_msgs in
#causal_order Lift.sameTime
/--
info: work determines W, reading [m, g, h]
power determines t, reading [W, P]
acyclic: every intervention has exactly one outcome of the causal model
-/
#guard_msgs in
#causal_order Lift.motor

-- A 50 kg pupil climbs 3 m in 6 s (g = 9.8): W = 1470 J, P = 245 W.
/--
info: m = 50  (fixed)
g = 49/5  (fixed)
h = 3  (fixed)
W = 1470  (computed)
P = 245  (computed)
t = 6  (fixed)
proved: in the domain, satisfies every law, and is the only outcome of the setup with these fixed values
-/
#guard_msgs in
#causal_eval Lift.sameTime with m := 50, g := 49/5, h := 3, t := 6

causal_model Slope where
  variables m g h0 h Ep0 Ep Ek Q
  units m : kg, g : m/s^2, h0 : m, h : m, Ep0 : J, Ep : J, Ek : J, Q : J
  law start : Ep0 = m * g * h0
  law height : Ep = m * g * h
  law energy : Ep0 = Ep + Ek + Q
  witness m := 1, g := 1, h0 := 1, Ep0 := 1, Ek := 1
  setup sled fixes m g h0 h Q     -- a sled on the hill: the kinetic energy follows

/--
info: start determines Ep0, reading [m, g, h0]
height determines Ep, reading [m, g, h]
energy determines Ek, reading [Ep0, Ep, Q]
acyclic: every intervention has exactly one outcome of the causal model
-/
#guard_msgs in
#causal_order Slope.sled

-- 30 kg from 5 m down to 1 m with 200 J lost to friction: Ek = 976 J.
/--
info: m = 30  (fixed)
g = 49/5  (fixed)
h0 = 5  (fixed)
h = 1  (fixed)
Ep0 = 1470  (computed)
Ep = 294  (computed)
Ek = 976  (computed)
Q = 200  (fixed)
proved: in the domain, satisfies every law, and is the only outcome of the setup with these fixed values
-/
#guard_msgs in
#causal_eval Slope.sled with m := 30, g := 49/5, h0 := 5, h := 1, Q := 200

/-! ## Electricity -/

causal_model Lamp where
  variables U R I P
  units U : V, R : ohm, I : A, P : W
  domain 0 < R
  law ohm : U = R * I
  law power : P = U * I
  witness U := 1, R := 1, I := 1, P := 1
  setup battery fixes U R         -- a battery holds the voltage: I, then P
  setup supply fixes I R          -- a supply holds the current: U, then P

/--
info: ohm determines I, reading [U, R]
power determines P, reading [U, I]
acyclic: every intervention has exactly one outcome of the causal model
-/
#guard_msgs in
#causal_order Lamp.battery
/--
info: ohm determines U, reading [R, I]
power determines P, reading [U, I]
acyclic: every intervention has exactly one outcome of the causal model
-/
#guard_msgs in
#causal_order Lamp.supply

-- A 4.5 V battery over 9 Ω: 1/2 A and 9/4 W.
/--
info: U = 9/2  (fixed)
R = 9  (fixed)
I = 1/2  (computed)
P = 9/4  (computed)
proved: in the domain, satisfies every law, and is the only outcome of the setup with these fixed values
-/
#guard_msgs in
#causal_eval Lamp.battery with U := 9/2, R := 9

end CausalPhys.Examples
