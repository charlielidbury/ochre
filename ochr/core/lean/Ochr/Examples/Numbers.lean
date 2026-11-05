import Ochr.Examples.Nat

/-! # 1. Numbers, in-place mutation, and the first proofs

Ochr's numbers are Peano naturals: `Z`, `S n`, and numerals. A function can take a
mutable borrow `&Nat` and change, in place, the number it points to. Types are checked by
running programs: `Id A t u` states that the computations `t` and `u` return the same value
and leave the same contents in every place they may write, and `refl` proves it when the
two runs agree.

This file continues the paper's first example, whose definitions are in `Nats`: in-place
addition `AddM`, pure addition `Add` defined by running `AddM` on a copy, and the in-place
lemma `AddMZero`. Here are a type that runs a program, the pure theorem that adding zero does
nothing, and how a match names the parts of a number and of a pair.

Defined in RULES §1 (syntax), §3 (the machine: [Read], [Assign], [Match], [Call]) and §7
(examples). -/

open Ochr.Test

ochr Numbers uses Nats {
  -- A type can run a program: `Add(2, 3)` evaluates to `5`, so `refl` proves the equation.
  def Add23 : Id(Nat, Add(2, 3), 5) := refl

  -- The pure theorem follows from the in-place one, applied to the predecessor field of `x`.
  -- No congruence step is written: the environment puts the `S` back around `p`.
  def AddZero (x : Nat) : Id(Nat, Add(x, 0), x) := (
    match x {
      Z => refl,
      S p => AddMZero(&p),
    }
  )

  -- Or directly, by lending all of `x` to the in-place lemma.
  def AddZero' (x : Nat) : Id(Nat, Add(x, 0), x) := AddMZero(&x)

  -- A function's type is formed when it is called, before its body runs. Writing `5` into
  -- `*x` does not make `Id(Nat, *x, 5)` true of the number `*x` held on entry.
  reject def WriteThenRefl (x : &Nat) : Id(Nat, *x, 5) := (
    *x := 5;
    refl
  )

  -- ## Matching on numbers
  -- A match on a number has exactly two arms, `Z` and then `S(y)`.
  reject def MissingArm (x : Nat) : Nat := (
    match x {
      Z => 0,
    }
  )

  -- The pattern variable `y` in `S(y)` is not a copy: it names the place `x.0`, the
  -- predecessor inside `x`. After `m := S(S(0))`, reading `y` gives the new predecessor.
  def AliasRead (x : Nat) :
      Id(Nat, (let m = x; match m { Z => 0, S y => (m := S(S(0)); y) }), (match x { Z => 0, S _ => 1 })) := (
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

  -- `x.0` can be written directly, but only where `x` is known to be a successor (on `Nat`;
  -- `Words`' `Pred` is on `Word`).
  def Pred (x : Nat) : Nat := (
    match x {
      Z => 0,
      S p => x.0,
    }
  )

  reject def PredOfAbstract (x : Nat) : Nat := x.0

  -- ## Pairs
  -- A pair is data too, and each component is a place: it can be read, assigned and borrowed
  -- (`p.0` and `p.1` are its fields).
  def PairLocal (n : Nat) : Nat := (
    let p = (n, ());
    p.0
  )

  def PairLocalIs (n : Nat) : Id(Nat, PairLocal(n), n) := refl

  def PairWrite (n : Nat) : Nat × Nat := (
    let p = (clone(n), n);
    p.1 := 5;
    p
  )

  def PairWriteIs (n : Nat) : Id(Nat × Nat, PairWrite(n), (n, 5)) := refl

  def PairBorrow (n : Nat) : Nat := (
    let p = (clone(n), n);
    let r = &p.1;
    *r := 7;
    p.1
  )

  def PairBorrowIs (n : Nat) : Id(Nat, PairBorrow(n), 7) := refl

  -- A number has no second component.
  reject def ProjNat (x : Nat) : Nat := x.1

  -- A pair is the library inductive `Pair`, whose constructor is `Mk` (D52), so a pair
  -- parameter is taken apart by a match, which splits it like any inductive value ...
  def SwapPair (p : Nat × Unit) : Unit × Nat := (
    match p {
      Mk(a, b) => (b, a),
    }
  )

  -- ... or by projection, which is the same match (D81): `p.i` of a type with one constructor
  -- names that constructor's field `i`, as `let Mk(a, b) = p; b` would, so an abstract pair is
  -- split to read it, as by the match above.
  def SwapPairProj (p : Nat × Unit) : Unit × Nat := (p.1, p.0)

  -- ## Projections (D81)
  -- `t.i` is field `i` of the one constructor of `t`'s type, for every such inductive, `Pair`
  -- being one of them: on a place it is the place that constructor's pattern variable names,
  -- read, written or borrowed in place; on any other term it is `let x = t; x.i`.
  inductive Trip := MkTrip(a : Nat, b : Unit, c : Nat)

  def TripLast (t : Trip) : Nat := t.2
  def TripLastIs (n : Nat) : Id(Nat, TripLast(MkTrip(0, (), n)), n) := refl
  def TermProj (n : Nat) : Id(Nat, MkTrip(0, (), n).2, n) := refl
  def CallProj (n : Nat) : Id(Nat, PairWrite(n).1, 5) := refl

  def TripWrite (n : Nat) : Trip := (
    let t = MkTrip(0, (), n);
    t.2 := 5;
    let r = &t.0;
    *r := 7;
    t
  )

  def TripWriteIs (n : Nat) : Id(Trip, TripWrite(n), MkTrip(7, (), 5)) := refl

  -- the field of a field
  def Nested (n : Nat) : Nat := (
    let p = ((clone(n), ()), n);
    (p.0).0
  )

  def NestedIs (n : Nat) : Id(Nat, Nested(n), n) := refl

  -- an abstract value is split to name its field, as by a match; a field read whole is moved
  -- out of it, and the other fields stay
  def TripBoth (t : Trip) : Nat × Nat := (t.0, t.2)
  def TripBothIs (n : Nat) (m : Nat) : Id(Nat × Nat, TripBoth(MkTrip(n, (), m)), (n, m)) := refl
  reject def TripTwice (t : Trip) : Nat × Nat := (t.0, t.0)

  -- `.i` names a field of a type with exactly one constructor, and an existing one
  inductive LR := OnL(x : Nat) | OnR(y : Nat)
  reject def LRProj (t : LR) : Nat := t.0
  reject def TripOut (t : Trip) : Nat := t.3

  -- `t.i` has `t`'s class: a proof field of data is named by a match
  inductive Tagged := MkTagged(n : Nat, h : Eq(Nat, 0, 0))
  def TaggedData (t : Tagged) : Nat := t.0
  reject def TaggedProof (t : Tagged) : Eq(Nat, 0, 0) := t.1
  def TaggedProofMatch (t : Tagged) : Eq(Nat, 0, 0) := (let MkTagged(n, h) = t; h)

  -- ## Calls and ascriptions
  -- Calls are saturated: every parameter gets an argument.
  reject def Unsaturated (x : &Nat) : Unit := AddM(x)

  -- An ascription `(t : A)` checks `t` against `A`.
  reject def AscribeWrong : Nat := (() : Nat)

  -- ## Built-in names
  -- `Nat`, `Unit`, `Z`, `S` and `refl` are built in, as are the forms `Id`, `Eq`, `cong`, `J`,
  -- `clone`, `trans` and `symm`: no declaration or constructor may take one of these names,
  -- which would shadow the built-in meaning at some uses and not others (reviewer-6's A3: a
  -- `Unit` with two constructors was accepted, and then `Unit` meant it).
  reject inductive Unit := A | B
  reject inductive Nat := Nil0 | Succ0(p : Nat)
  reject inductive Three := Z | One | Two
  reject def refl : Nat := 0
  reject def clone (x : Nat) : Nat := x
  -- the built-in `Unit` is unaffected by the rejected one: `()` is its only value
  def UnitStill (x : Unit) : Eq(Unit, x, ()) := refl
}

