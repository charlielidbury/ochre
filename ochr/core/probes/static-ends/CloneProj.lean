import Ochr.Examples.Nat
open Ochr.Test
-- NOT a D90 probe: a fault on main before and after D90 (D81 x D84), fixed by D93. `clone(x.0)`
-- runs as the one-arm match `match x { Mk(..) => x.fst }` (the projection, D81) inside `clone`,
-- and the match's static join counted the arm's read of `x.fst` as a move (the clone is outside
-- the match) and dropped it: `x` was partly moved afterwards (`CL` and the closed call `CLrun`
-- rejected, the generic `CLg` accepted). Since D93 a one-constructor match has no join: all
-- accepted. Asserted in Examples/ReturnedBorrows.lean (block `OneConstructor`).
ochr CP uses Nats {
  def CL : Nat × Nat := (let x = (Z, Z); let y = clone(x.0); x)
  def CLg (x : Nat × Nat) : Nat × Nat := (let y = clone(x.0); x)
  def CLuse (x : Nat × Nat) : Nat × Nat := CLg(x)
}
ochr CP2 uses Nats, CP {
  def CLrun : Nat × Nat := CLg((Z, Z))
}
