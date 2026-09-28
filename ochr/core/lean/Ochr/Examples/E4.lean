import Ochr.Examples.E3

/-! # E4: opaque (abstract) functions -/

open Ochr.Test

ochr E4 {
  def AddM (x : &Nat) (y : Nat) : Unit :=
    match *x { Z => *x := y | S p => AddM(&p, y) }

  def AddMZero (x : &Nat) : Id Unit (AddM(x, 0)) () :=
    match *x { Z => refl | S p => AddMZero(&p) }

  def Twice (f : Π(_ : Unit). Unit) : Unit := f(()); f(())

  -- an f with no borrow argument cannot write anything, so its calls are ()
  def TwiceNoop (f : Π(_ : Unit). Unit) : Id Unit (Twice(f)) () := refl

  def TwiceM (f : Π(_ : &Nat). Unit) (x : &Nat) : Unit := f(&*x); f(&*x)

  -- reborrowing then moving agrees with reborrowing twice (deriver-e346 §E4.2)
  def TwiceMMove (f : Π(_ : &Nat). Unit) (x : &Nat) : Id Unit (TwiceM(f, x)) (f(&*x); f(x)) := refl

  def TwiceMZero (x : &Nat) : Id Unit (TwiceM(λ(z : &Nat) : Unit => AddM(z, 0), x)) () :=
    match *x { Z => refl | S p => TwiceMZero(&p) }

  -- the modular proof (deriver-e346 F8): under P5 citing a lemma no longer
  -- overwrites the borrowed place, so this now checks as written
  def TwiceMZero' (x : &Nat) : Id Unit (TwiceM(λ(z : &Nat) : Unit => AddM(z, 0), x)) () :=
    let h1 = AddMZero(&*x); AddM(&*x, 0); let h2 = AddMZero(&*x); trans h2 h1
}

#eval IO.println (run "E4" E4).show

-- every verdict as expected, and exactly 8 assertions (a truncated file changes the count)
#guard (run "E4" E4).allAsExpected
#guard (run "E4" E4).count == 8
