import Ochr.Examples.Nat
open Ochr.Test

ochr EISmall uses Nats {
  def Pick (n : Nat) (x : &Nat) (y : &Nat) : &Nat := ( match n { Z => x, S _ => y } )
  def EI (n : Nat) (a : Nat) (b : Nat) : Unit := (
    let r = Pick(n, &a, &b);
    let a1 = a;
    let T = Id(Unit, (let z = clone(b); ()), ());
    ()
  )
}
ochr EISmall2 uses Nats, EISmall {
  def EIRun : Unit := EI(1, 2, 3)
  def EIRun0 : Unit := EI(0, 2, 3)
}
