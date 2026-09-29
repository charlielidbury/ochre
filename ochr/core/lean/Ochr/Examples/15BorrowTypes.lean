import Ochr.Examples.«00Std»

/-! # 15. Borrow types: what may be borrowed, and where `&` may appear

`&A` is a type only when `A` is data: `Nat`, `Unit`, or an inductive type in `Type` at any
parameters, pairs included (D48 (1); a pair is the library's `Pair`, D52). It is never a
borrow of a universe, a proposition, a function type or a type variable. And `&A` may appear
only as the whole declared type of a parameter, a result or an annotated term: never inside
another type, so there are no borrows inside data, and never as the value of a type-level
computation (D48 (2)). These are the core's limits; Rust's iterators of borrows (`IterM`)
are outside it.

Defined in RULES §1 (the scope paragraph) and D48. -/

open Ochr.Test

ochr BorrowTypes uses Std {
  -- Data may be borrowed: an inductive type at any parameter (`Std`'s `List(A)`), a pair ...
  def RefList (A : Type) (xs : &List(A)) : Unit := ()
  def RefPair (p : &(Nat × Unit)) : Unit := *p := (0, ())

  -- ... including a box of propositions (`Std`'s `Box`), which is data even though what it
  -- holds is a type.
  def RefBoxProp (x : &Box(Prop)) : Unit := ()

  -- `&` at the top of a result (`Std`'s `TailM`), an annotation, and the parts of a Π-type.
  def Ann (x : &Nat) : Unit := (
    let r : &Nat = TailM(x);
    *r := 1
  )

  def HO (f : Π(x : &Nat). &Nat) (y : &Nat) : Unit := (
    let r = f(y);
    *r := 2
  )

  -- Not the universe of propositions, not a proposition, not a function type, and not a
  -- type variable, which might stand for any of these.
  reject def PIref (x : &Prop) (h1 : *x) (h2 : *x) : Id (*x) h1 h2 := refl
  reject def RefTrue (x : &True) : Nat := 0
  reject def RefFun (f : &(Π(n : Nat). Nat)) : Nat := 0
  reject def SwapT (A : Type) (x : &A) (y : &A) : Unit := ()

  -- No `&` inside another type: not in a pair, in `Id`'s type, a list, or a field.
  reject def InPair (p : Nat × &Nat) : Nat := 0
  reject def InId (x : &Nat) (h : Id (&Nat) x x) : Nat := 0
  reject def IterM (xs : &List(Nat)) : List(&Nat) := Nil
  reject inductive RefCell := MkRef(r : &Nat)

  -- ## What goes wrong without this rule
  -- A result type that computes to `&Nat` at `n = 0` but is not written `&A`. [Close] reads
  -- the row from the declared result type, so at the generic call `F` returns data, while at
  -- `n = 0` it returns a live borrow. `G` reads `r` twice, which copies data but moves a
  -- borrow, so `UseG` reads a dead borrow when run (switch `refTop`).
  reject def F (n : Nat) (x : &Nat) : match n { Z => &Nat, S _ => Nat } := (
    match n {
      Z => x,
      S _ => 0,
    }
  )

  reject def G (n : Nat) (a : Nat) : Nat := (
    let r = F(n, &a);
    let r2 = r;
    let r3 = r;
    a
  )

  reject def UseG : Nat := G(0, 5)
}

#eval IO.println (run "BorrowTypes" BorrowTypes).show

-- every verdict as expected, and the exact number of declarations (a truncated file changes it)
#guard (run "BorrowTypes" BorrowTypes).allAsExpected
#guard (run "BorrowTypes" BorrowTypes).count == 16
