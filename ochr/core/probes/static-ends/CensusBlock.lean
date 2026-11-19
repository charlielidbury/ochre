import Ochr.Examples.Nat
open Ochr.Test

ochr CensusC uses Nats {
  -- a stuck block's read-in-place capture ends r at the generic call; the instance's arm does not
  def EIB (k : Nat) (a : Nat) : Unit := (
    let r = &a;
    match k { Z => (let z = clone(a); ()), S _ => () };
    let T = Id(Unit, (let z = clone(a); ()), ());
    ()
  )
  def EJB (k : Nat) (a : Nat × Nat) : Nat × Nat := (
    let r = &a;
    match k { Z => (let z = clone(a); ()), S _ => () };
    let m = S(Z);
    match m { Z => (let z = (*r).0; Z), S _ => Z };
    let aa = a;
    aa
  )
  def MN (z : Nat) : Type := Nat
  reject def GJ (n : Nat) (k : Nat) (h : Eq(Nat, n, Z)) (a : Nat) : Nat := (
    let r = &a;
    let v = J(Nat, n, Z, MN, h, (match k { Z => (a := 1; Z), S _ => Z }));
    *r := 3;
    v
  )
  def GJI (n : Nat) (k : Nat) (h : Eq(Nat, n, Z)) (a : Nat) : Unit := (
    let r = &a;
    let v = J(Nat, n, Z, MN, h, (match k { Z => (let z = clone(a); Z), S _ => Z }));
    let T = Id(Unit, (let z = clone(a); ()), ());
    ()
  )
}
ochr CensusD uses Nats, CensusC {
  def EIBRun : Unit := EIB(1, 0)
  def EJBRun : Nat × Nat := EJB(1, (1, 2))
  reject def GJRun : Nat := GJ(0, 1, refl, 5)
  def GJIRun : Unit := GJI(0, 1, refl, 5)
}
