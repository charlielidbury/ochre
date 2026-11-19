import Ochr.Examples.Nat
import Ochr.Examples.Fixtures
open Ochr.Test

ochr C3 uses Nats, Fixtures {
  -- a split world re-runs `b`'s fill, which drops `r`'s hole at n = Z; `b` stays lent
  reject def SplitKeeps (n : Nat) (a : Nat) (b : Nat) : Unit := (
    let r = Pick(clone(n), &a, &b);
    match n { Z => (let z = clone(b); *r := 1; ()), S _ => () }
  )
  def SplitKeepsOk (n : Nat) (a : Nat) (b : Nat) : Unit := (
    let r = Pick(clone(n), &a, &b);
    match n { Z => (*r := 1; let z = clone(b); ()), S _ => () }
  )
  -- the same at a closed call: lent whatever n is
  reject def SplitKeeps0 (a : Nat) (b : Nat) : Unit := (
    let n = 0;
    let r = Pick(clone(n), &a, &b);
    match n { Z => (let z = clone(b); *r := 1; ()), S _ => () }
  )
}
