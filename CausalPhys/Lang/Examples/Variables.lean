/-
  The causal order depends on the variables chosen, not only on the physics.

  A sled slides down a hill (as `School.Slope`): the potential energy at the
  start, the potential energy now, the kinetic energy, and the heat Q lost to
  friction. Written with the natural variables Ep and Ek, the height law
  determines Ep from m, g and h alone, and the energy law determines Ek.

  The same physics written with S = Ep + Ek (the mechanical energy) and
  D = Ep − Ek in place of Ep and Ek has the same solutions: the numbers below
  agree, with S = Ep + Ek and D = Ep − Ek. But the causal order is different.
  Now the energy law determines S, and the height law determines D from S, so
  the friction loss Q is an ancestor of D, a quantity that, read through the
  height law, should depend only on m, g and h.

  The lesson is Simon's (and Iwasaki and Simon's): causal ordering is a
  property of the equations in the variables you measure. Mixing variables
  keeps the physics and changes what causes what. It is the same point as
  `Platonic.rotation_breaks_independence`: agreement up to a change of
  coordinates is not causal agreement.
-/
import CausalPhys.Lang.Syntax

open CausalPhys CausalPhys.Lang

namespace CausalPhys.Examples

-- The sled with the natural variables (as `Slope` in `School`).
causal_model Sled where
  variables m g h0 h Ep0 Ep Ek Q
  units m : kg, g : m/s^2, h0 : m, h : m, Ep0 : J, Ep : J, Ek : J, Q : J
  law start : Ep0 = m * g * h0
  law height : Ep = m * g * h
  law energy : Ep0 = Ep + Ek + Q
  witness m := 1, g := 1, h0 := 1, Ep0 := 1, Ek := 1
  setup sled fixes m g h0 h Q

/--
info: start determines Ep0, reading [m, g, h0]
height determines Ep, reading [m, g, h]
energy determines Ek, reading [Ep0, Ep, Q]
acyclic: every intervention has exactly one outcome of the causal model
-/
#guard_msgs in
#causal_order Sled.sled

-- The same physics with S = Ep + Ek and D = Ep − Ek in place of Ep and Ek.
causal_model SledMixed where
  variables m g h0 h Ep0 S D Q
  units m : kg, g : m/s^2, h0 : m, h : m, Ep0 : J, S : J, D : J, Q : J
  law start : Ep0 = m * g * h0
  law height : (S + D) / 2 = m * g * h
  law energy : Ep0 = S + Q
  witness m := 1, g := 1, h0 := 1, Ep0 := 1, S := 1, D := -1
  setup sled fixes m g h0 h Q

/--
info: start determines Ep0, reading [m, g, h0]
height determines D, reading [S, m, g, h]
energy determines S, reading [Ep0, Q]
acyclic: every intervention has exactly one outcome of the causal model
-/
#guard_msgs in
#causal_order SledMixed.sled

-- Same numbers: 30 kg from 5 m to 1 m, 200 J lost. Ep = 294 J and Ek = 976 J …
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
#causal_eval Sled.sled with m := 30, g := 49/5, h0 := 5, h := 1, Q := 200

-- … and S = 294 + 976 = 1270 J, D = 294 − 976 = −682 J: the same state.
/--
info: m = 30  (fixed)
g = 49/5  (fixed)
h0 = 5  (fixed)
h = 1  (fixed)
Ep0 = 1470  (computed)
S = 1270  (computed)
D = -682  (computed)
Q = 200  (fixed)
proved: in the domain, satisfies every law, and is the only outcome of the setup with these fixed values
-/
#guard_msgs in
#causal_eval SledMixed.sled with m := 30, g := 49/5, h0 := 5, h := 1, Q := 200

end CausalPhys.Examples
