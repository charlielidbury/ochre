import Ochr.Examples.Nat
open Ochr.Test

ochr FieldsA uses Nats {
  def F1 (x : Nat × Nat) : Unit := (
    let r = &x.1;
    let y = x.0;
    *r := Z;
    ()
  )
  def F2 (x : Nat × Nat) : Unit := (
    let r = &x.1;
    let y = clone(x.0);
    *r := Z;
    ()
  )
  def F3 (x : &(Nat × Nat)) : Unit := (
    let r = &(*x).1;
    let y = clone((*x).0);
    *r := Z;
    ()
  )
  def F4 : Unit := (
    let x = (Z, Z);
    let r = &x.1;
    let y = clone(x.0);
    *r := Z;
    ()
  )
}
