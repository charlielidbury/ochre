import Ochr.Examples.Nat
open Ochr.Test

-- a reborrow `s` of a returned borrow `r` outlives `r`: every place `r` was lent stays lent to `s`,
-- the place `r` pointed into included
ochr RB uses Nats {
  def PickP (n : Nat) (x : &(Nat × Nat)) (y : &(Nat × Nat)) : &(Nat × Nat) := (
    match n { Z => x, S _ => y }
  )
  def RB (n : Nat) (a : Nat × Nat) (b : Nat × Nat) : Nat × Nat := (
    let r = PickP(n, &a, &b);
    let s = &(*r).0;
    (let t = &a.0; ());
    (let t = &b.1; ());
    let m = S(Z);
    match m { Z => (let q = *s; Z), S _ => Z };
    let bb = b;
    bb
  )
}
ochr RBRuns uses Nats, RB {
  def RBRun : Nat × Nat := RB(1, (1, 2), (3, 4))
  def RBRun0 : Nat × Nat := RB(0, (1, 2), (3, 4))
}
