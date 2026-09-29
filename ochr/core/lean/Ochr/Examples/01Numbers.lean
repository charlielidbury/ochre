import Ochr.Examples.«00Std»

/-! # 1. Numbers, in-place mutation, and the first proofs

Ochr's numbers are Peano naturals: `Z`, `S n`, and numerals. A function can take a
mutable borrow `&Nat` and change, in place, the number it points to. Types are checked by
running programs: `Id A t u` states that the computations `t` and `u` return the same value
and leave the same contents in every place they may write, and `refl` proves it when the
two runs agree.

This file continues the paper's first example, whose definitions are in `Std`: in-place
addition `AddM`, pure addition `Add` defined by running `AddM` on a copy, and the in-place
lemma `AddMZero`. Here are a type that runs a program, the pure theorem that adding zero does
nothing, and how a match names the parts of a number and of a pair.

Defined in RULES §1 (syntax), §3 (the machine: [Read], [Assign], [Match], [Call]) and §7
(examples). -/

open Ochr.Test

ochr Numbers uses Std {
  -- A type can run a program: `Add(2, 3)` evaluates to `5`, so `refl` proves the equation.
  def Add23 : Id Nat (Add(2, 3)) 5 := refl

  -- The pure theorem follows from the in-place one, applied to the predecessor field of `x`.
  -- No congruence step is written: the environment puts the `S` back around `p`.
  def AddZero (x : Nat) : Id Nat (Add(x, 0)) x := (
    match x {
      Z => refl,
      S p => AddMZero(&p),
    }
  )

  -- Or directly, by lending all of `x` to the in-place lemma.
  def AddZero' (x : Nat) : Id Nat (Add(x, 0)) x := AddMZero(&x)

  -- A function's type is formed when it is called, before its body runs. Writing `5` into
  -- `*x` does not make `Id Nat (*x) 5` true of the number `*x` held on entry.
  reject def WriteThenRefl (x : &Nat) : Id Nat (*x) 5 := (
    *x := 5;
    refl
  )

  -- ## Matching on numbers
  -- A match on a number has exactly two arms, `Z` and then `S y`.
  reject def MissingArm (x : Nat) : Nat := (
    match x {
      Z => 0,
    }
  )

  -- The pattern variable `y` in `S y` is not a copy: it names the place `x.1`, the
  -- predecessor inside `x`. After `m := S (S 0)`, reading `y` gives the new predecessor.
  def AliasRead (x : Nat) :
      Id Nat (let m = x; match m { Z => 0, S y => (m := S (S 0); y) }) (match x { Z => 0, S _ => 1 }) := (
    match x {
      Z => refl,
      S _ => refl,
    }
  )

  -- ... and after `x := 0` there is no predecessor, so `y` names nothing.
  reject def AliasDangling (x : Nat) : Nat := (
    match x {
      Z => 0,
      S y => (
        x := 0;
        y
      ),
    }
  )

  -- `x.1` can be written directly, but only where `x` is known to be a successor.
  def Pred (x : Nat) : Nat := (
    match x {
      Z => 0,
      S p => x.1,
    }
  )

  reject def PredOfAbstract (x : Nat) : Nat := x.1

  -- ## Pairs
  -- A pair is data too, and each component is a place: it can be read, assigned and borrowed.
  def PairLocal (n : Nat) : Nat := (
    let p = (n, ());
    p.1
  )

  def PairLocalIs (n : Nat) : Id Nat (PairLocal(n)) n := refl

  def PairWrite (n : Nat) : Nat × Nat := (
    let p = (n, n);
    p.2 := 5;
    p
  )

  def PairWriteIs (n : Nat) : Id (Nat × Nat) (PairWrite(n)) (n, 5) := refl

  def PairBorrow (n : Nat) : Nat := (
    let p = (n, n);
    let r = &p.2;
    *r := 7;
    p.2
  )

  def PairBorrowIs (n : Nat) : Id Nat (PairBorrow(n)) 7 := refl

  -- A number has no second component.
  reject def ProjNat (x : Nat) : Nat := x.2

  -- Not yet expressible: a pair parameter is an abstract value, whose components are not
  -- known, and the rules have neither a match on pairs nor an η rule that would split it.
  reject def SwapPair (p : Nat × Unit) : Unit × Nat := (p.2, p.1)

  -- ## Calls and ascriptions
  -- Calls are saturated: every parameter gets an argument.
  reject def Unsaturated (x : &Nat) : Unit := AddM(x)

  -- An ascription `(t : A)` checks `t` against `A`.
  reject def AscribeWrong : Nat := (() : Nat)
}

#eval IO.println (run "Numbers" Numbers).show

-- every verdict as expected, and the exact number of declarations (a truncated file changes it)
#guard (run "Numbers" Numbers).allAsExpected
#guard (run "Numbers" Numbers).count == 19
