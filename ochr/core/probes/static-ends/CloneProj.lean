import Ochr.Examples.Nat
open Ochr.Test
-- NOT a D90 probe: a fault on main before and after D90 (D81 x D84). `clone(x.0)` runs as the
-- one-arm match `match x { Mk(..) => x.fst }` (the projection, D81) inside `clone`, so the match's
-- static join counts the arm's read of `x.fst` as a move (the clone is outside the match) and
-- drops it: `x` is partly moved afterwards. At an unknown `x` the generic call accepts `CLg`;
-- its closed call `CLrun` is rejected. Expectations below are the current verdicts.
ochr CP uses Nats {
  reject def CL : Nat × Nat := (let x = (Z, Z); let y = clone(x.0); x)
  def CLg (x : Nat × Nat) : Nat × Nat := (let y = clone(x.0); x)
  def CLuse (x : Nat × Nat) : Nat × Nat := CLg(x)
}
ochr CP2 uses Nats, CP {
  reject def CLrun : Nat × Nat := CLg((Z, Z))
}
