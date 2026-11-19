import Ochr.Examples.Nat
open Ochr.Test

ochr EJProbe uses Nats {
  def PickP (n : Nat) (x : &(Nat × Nat)) (y : &(Nat × Nat)) : &(Nat × Nat) := (
    match n { Z => x, S _ => y }
  )
  -- generic n: reading `a` ends `r`'s borrow early (a's fill holds its hole)
  def EJ (n : Nat) (a : Nat × Nat) (b : Nat × Nat) : Nat × Nat := (
    let r = PickP(n, &a, &b);
    let a1 = a;
    let k = S(Z);
    match k { Z => (let z = (*r).0; Z), S m => Z };
    let bb = b;
    bb
  )
  -- the instance n = 1, written out
  def EJ1 (a : Nat × Nat) (b : Nat × Nat) : Nat × Nat := (
    let r = PickP(S(Z), &a, &b);
    let a1 = a;
    let k = S(Z);
    match k { Z => (let z = (*r).0; Z), S m => Z };
    let bb = b;
    bb
  )
}

ochr EJProbe2 uses Nats, EJProbe {
  -- a closed call of the accepted EJ at n = 1
  def EJRun : Nat × Nat := EJ(1, (2, 3), (4, 5))
  def EJRun0 : Nat × Nat := EJ(0, (2, 3), (4, 5))
}
