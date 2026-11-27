import Ochr.Test
import Ochr.Examples.Nat
import Ochr.Examples.Fixtures
open Ochr.Test

-- THE EXPERIMENT `exp-obs-detach` (checker13): programs aimed at the implementation's own choices
-- (a label lent both below the observing frame and in it, the identity fill under (C) too; a borrow in
-- flight while a later argument forms an `Id`; an `Id` inside a side; a re-pointing into a borrow lent
-- from below), each a plain `def`; checked under the branch's default, (C+).

ochr T13Hunt uses Nats, Fixtures {
  def Ctl : Eq(Nat, Z, S(Z)) := refl
  def G5 (x : &Nat) (e : Id(Unit, *x := 0, *x := 1)) : False := e
  def H (x : &Nat) (e : Id(Unit, *x := 0, *x := 0)) : Unit := ()
  -- a label lent below (the parameter's cell) and in the frame (a): Pick consumes x and borrows a
  def BothF (n : Nat) (x : &Nat) : Unit := (let a = 0; let r = Pick(n, x, &a); let h : Eq(Prop, Id(Unit, *r := 0, *r := 1), False) = refl; ())
  def BothG5 (n : Nat) (x : &Nat) : False := (let a = 0; let r = Pick(n, x, &a); G5(r, refl))
  def BothH (n : Nat) (x : &Nat) : Unit := (let a = 0; let r = Pick(n, x, &a); H(r, refl))
  def BothId (n : Nat) (x : &Nat) : Unit := (let a = 0; let r = Pick(n, x, &a); let h : Id(Unit, *r := 0, *r := 1) = refl; ())
  def UseBothF : Unit := (let c = 3; BothF(Z, &c))
  def UseBothF1 : Unit := (let c = 3; BothF(S(Z), &c))
  def UseBothG5 : False := (let c = 3; BothG5(Z, &c))
  -- a borrow in flight (an earlier argument) while a later argument forms an Id
  def TA (x : &Nat) (u : Unit) : Unit := ()
  def TB (n : Nat) (x : &Nat) : Unit := match n { Z => TA(&*x, (let h : Id(Unit, (), ()) = refl; ())), S(m) => (), }
  def UseTB : Unit := (let a = 0; TB(Z, &a))
  def TC (n : Nat) (x : &Nat) : Unit := match n { Z => TA(&*x, (let h : Id(Unit, *x := 0, *x := 0) = refl; ())), S(m) => (), }
  def UseTC : Unit := (let a = 0; TC(Z, &a))
  def TD (n : Nat) (x : &Nat) : False := match n { Z => (let r = &*x; let y = TA(&*r, ()); G5(r, refl)), S(m) => G5(x, refl), }
  -- an Id inside a side of an Id, over the outer frame's borrow
  def Nested (x : &Nat) : Unit := (let h : Id(Prop, Id(Unit, *x := 0, *x := 1), False) = refl; ())
  def NestedF (x : &Nat) : Unit := (let h : Eq(Prop, Id(Prop, Id(Unit, *x := 0, *x := 1), Id(Unit, *x := 1, *x := 0)), True) = refl; ())
  -- a re-pointed binding into a borrow lent from below
  def RePt (x : &Nat) (y : &Nat) : Unit := (let r = &*x; let h : Id(Unit, (r := &*y; *r := 0), (r := &*y; *r := 1)) = refl; ())
  def RePtSame (x : &Nat) (y : &Nat) : Unit := (let r = &*x; let h : Id(Unit, (r := &*y; *r := 0), (r := &*y; *r := 0)) = refl; ())
}
