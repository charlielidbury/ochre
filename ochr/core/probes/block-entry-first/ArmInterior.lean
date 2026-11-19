import Ochr.Examples.Nat
import Ochr.Examples.Fixtures
open Ochr.Test

-- Inside an arm of a stuck block, the generic call now sees the borrows the match's entry ends,
-- as a direct run's arm does (D91)
ochr AI uses Nats, Fixtures {
  def MN (z : Nat) : Type := Nat
  -- an Id side in an arm reads `a`, whose borrower `r` the entry has ended
  def IA (k : Nat) (a : Nat) : Unit := (
    let r = &a;
    match k { Z => (let T = Id(Unit, (let z = clone(a); ()), ()); ()), S _ => () };
    ()
  )
  -- the same with `r` still used after the match: rejected, the entry ends `r`
  reject def IAUse (k : Nat) (a : Nat) : Unit := (
    let r = &a;
    match k { Z => (let T = Id(Unit, (let z = clone(a); ()), ()); ()), S _ => () };
    *r := 1;
    ()
  )
  -- the J form
  def JA (m : Nat) (h : Eq(Nat, m, Z)) (a : Nat) : Nat := (
    let r = &a;
    J(Nat, m, Z, MN, h, (let T = Id(Unit, (let z = clone(a); ()), ()); Z))
  )
  -- an arm that uses a borrow the entry ends: rejected, now inside the arm
  reject def UseEnded (k : Nat) (a : Nat) : Unit := (
    let r = &a;
    match k { Z => (a := 1; ()), S _ => (*r := 2; ()) };
    ()
  )
  -- the entry η-refines the scrutinee itself (its one arm moves a field of it); the arm is then
  -- checked at that refinement
  def EtaScrut (x : Nat × Nat) : Nat := (let v = match x { Mk(a, b) => a, }; v)
  def EtaScrut2 (x : Nat × Nat) : Nat × Nat := (let v = match x { Mk(a, b) => (b, a), }; v)
  -- through a returned borrow: the entry reads `b`, a lender of `r`
  def IAPick (n : Nat) (k : Nat) (a : Nat) (b : Nat) : Unit := (
    let r = Pick(n, &a, &b);
    match k { Z => (let T = Id(Unit, (let z = clone(b); ()), ()); ()), S _ => () };
    ()
  )
}
ochr AIRuns uses Nats, Fixtures, AI {
  def IARun : Unit := IA(0, 5)
  def IARun1 : Unit := IA(1, 5)
  def JARun : Nat := JA(0, refl, 5)
  def IAPickRun : Unit := IAPick(1, 0, 2, 3)
  def EtaScrutRun : Id(Nat, EtaScrut((1, 2)), 1) := refl
  def EtaScrut2Run : Id(Nat × Nat, EtaScrut2((1, 2)), (2, 1)) := refl
}
