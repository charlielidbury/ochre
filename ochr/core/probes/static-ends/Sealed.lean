import Ochr.Examples.Nat
open Ochr.Test

-- a known-constructor match whose dead arm reads a field of a place holding a stuck call's fill
ochr Seal1 uses Nats {
  def PickP (n : Nat) (x : &(Nat × Nat)) (y : &(Nat × Nat)) : &(Nat × Nat) := (
    match n { Z => x, S _ => y }
  )
  reject def SF (n : Nat) (a : Nat × Nat) (b : Nat × Nat) : Unit := (
    let r = PickP(n, &a, &b);
    let k = S(Z);
    match k { Z => (let z = clone(a.0); ()), S _ => () };
    *r := (Z, Z);
    ()
  )
  reject def SF0 (a : Nat × Nat) (b : Nat × Nat) : Unit := (
    let r = PickP(Z, &a, &b);
    let k = S(Z);
    match k { Z => (let z = clone(a.0); ()), S _ => () };
    *r := (Z, Z);
    ()
  )
}
