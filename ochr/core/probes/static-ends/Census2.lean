import Ochr.Examples.Nat
import Ochr.Examples.Fixtures
import Ochr.Examples.Logic
open Ochr.Test

ochr C2 uses Nats, Fixtures, Logic {
  -- a reborrow of a returned borrow keeps every lender lent (transfer at [End])
  reject def G8 (n : Nat) (a : Nat) (b : Nat) : Unit := (
    let r = Pick(n, &a, &b);
    let s = &*r;
    let z = clone(a);
    *s := 4;
    ()
  )
  reject def G8K (a : Nat) (b : Nat) : Unit := (
    let r = Pick(S(Z), &a, &b);
    let s = &*r;
    let z = clone(a);
    *s := 4;
    ()
  )
  def G8Ok (n : Nat) (a : Nat) (b : Nat) : Unit := (
    let r = Pick(n, &a, &b);
    let s = &*r;
    *s := 4;
    let z = clone(a);
    ()
  )
  -- nested returned borrows: `a` is lent to `s` through `r`
  reject def Nest (n : Nat) (m : Nat) (a : Nat) (b : Nat) (c : Nat) : Unit := (
    let r = Pick(n, &a, &b);
    let s = Pick(m, r, &c);
    let z = clone(a);
    *s := 1;
    ()
  )
  reject def NestK (a : Nat) (b : Nat) (c : Nat) : Unit := (
    let r = Pick(S(Z), &a, &b);
    let s = Pick(Z, r, &c);
    let z = clone(a);
    *s := 1;
    ()
  )
  def NestOk (n : Nat) (m : Nat) (a : Nat) (b : Nat) (c : Nat) : Unit := (
    let r = Pick(n, &a, &b);
    let s = Pick(m, r, &c);
    *s := 1;
    let z = clone(a);
    ()
  )
  -- a function that returns a stuck call's borrow
  def Pick2 (n : Nat) (x : &Nat) (y : &Nat) : &Nat := Pick(n, x, y)
  reject def P2 (n : Nat) (a : Nat) (b : Nat) : Unit := (
    let r = Pick2(n, &a, &b);
    let z = clone(a);
    *r := 1;
    ()
  )
  def P2Ok (n : Nat) (a : Nat) (b : Nat) : Nat := (
    let r = Pick2(n, &a, &b);
    *r := 1;
    let z = clone(a);
    let w = clone(b);
    Add(z, w)
  )
  -- a tail match inside the one arm of a match on a proof is in tail position
  def PT (h : And(True, True)) (k : Nat) (a : Nat) : Unit := (
    let r = &a;
    match h { Intro(x, y) => match k { Z => (a := 1; ()), S _ => (*r := 2; ()) } }
  )
  -- a local returned by a borrow-returning call: an error on every path
  reject def Local (n : Nat) (x : &Nat) : &Nat := (
    let l = 0;
    Pick(n, &l, x)
  )
}
ochr C2Runs uses Nats, Fixtures, Logic, C2 {
  def G8OkRun : Unit := G8Ok(1, 1, 2)
  def NestOkRun : Unit := NestOk(1, 0, 1, 2, 3)
  def P2OkRun : Id(Nat, P2Ok(0, 5, 7), 8) := refl
  def P2OkRun1 : Id(Nat, P2Ok(1, 5, 7), 6) := refl
  def PTRun : Unit := PT(⟨I, I⟩, 1, 0)
}
