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
  reject def WriteThenRefl (x : &Nat) : Id(Nat, clone(*x), 5) := (
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
      Id(Nat, (let m = clone(x); match m { Z => 0, S y => (m := S(S(0)); y) }), (match x { Z => 0, S _ => 1 })) := (
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

  def PairBorrowIs (n : Nat) : Id(Nat, PairBorrow(clone(n)), 7) := refl

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
  def CallProj (n : Nat) : Id(Nat, PairWrite(clone(n)).1, 5) := refl

  def TripWrite (n : Nat) : Trip := (
    let t = MkTrip(0, (), n);
    t.2 := 5;
    let r = &t.0;
    *r := 7;
    t
  )

  def TripWriteIs (n : Nat) : Id(Trip, TripWrite(clone(n)), MkTrip(7, (), 5)) := refl

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


/-! ## A match on a field place at the end of a body (D145)

A run reads a place with a field step `q.i` by first naming the field with a match on `q`
(D81 [Proj]); the end of a body's check read the scrutinee as it stood, so
`def F1E (b : Box) : Nat := match b.0 { Z => 0, S(m) => 1, }` was rejected ("no such place b.0:
its path does not exist in σ0") while the same match under a `let` (`F1L`) ran. Since D145 the two
share the one step (`projStep`). Each form of scrutinee a run accepts, at the end of a body (`…E`)
and under a `let` (`…L`), now with the same verdict and message: a variable, a field path of one
and of two steps, through a borrow, a field of a known value and of a written one, a field of a
type with several constructors, a field of a value whose other field's type depends on it and the
dependent field itself, a call, a sealed program's field, a proof's field, in an arm, against a
goal that names the match. A proof field of data named by `.1` is rejected by D81 on both paths
(`PdE`, `PdL`), and named by a match it is the field the index write invalidated (`PdM`). -/

ochr FieldScrutinee uses Nats {
  inductive Box := MkBox(v : Nat)
  inductive BB := MkBB(b : Box)
  inductive Tri := TA | TB | TC
  inductive BT := MkBT(v : Tri)
  def F (n : Nat) : Type := match n { Z => Unit, S(m) => Tri, }
  inductive DP := MkDP(n : Nat, x : F(n))
  inductive Ex : Prop := W1(n : Nat) | W2(m : Nat)
  def Id1 (n : Nat) : Nat := n
  def mk (n : Nat) : Box := match n { Z => MkBox(0), S(m) => MkBox(1), }
  -- a variable
  def VarE (n : Nat) : Nat := match n { Z => 0, S(m) => 1, }
  def VarL (n : Nat) : Nat := (let r = match n { Z => 0, S(m) => 1, }; r)
  -- a field path of one step, of two steps
  def F1E (b : Box) : Nat := match b.0 { Z => 0, S(m) => 1, }
  def F1L (b : Box) : Nat := (let r = match b.0 { Z => 0, S(m) => 1, }; r)
  def F1ERun : Eq(Nat, F1E(MkBox(3)), 1) := refl
  def F2E (c : BB) : Nat := match (c.0).0 { Z => 0, S(m) => 1, }
  def F2L (c : BB) : Nat := (let r = match (c.0).0 { Z => 0, S(m) => 1, }; r)
  def F2ERun : Eq(Nat, F2E(MkBB(MkBox(0))), 0) := refl
  -- through a borrow, one and two steps
  def BrE (b : &Box) : Nat := match (*b).0 { Z => 0, S(m) => 1, }
  def BrL (b : &Box) : Nat := (let r = match (*b).0 { Z => 0, S(m) => 1, }; r)
  def Br2E (c : &BB) : Nat := match ((*c).0).0 { Z => 0, S(m) => 1, }
  def Br2L (c : &BB) : Nat := (let r = match ((*c).0).0 { Z => 0, S(m) => 1, }; r)
  def BrERun : Eq(Nat, (let b = MkBox(2); BrE(&b)), 1) := refl
  -- a field of a known value, and of one just written
  def KnE (n : Nat) : Nat := (let b = MkBox(3); match b.0 { Z => 0, S(m) => 1, })
  def KnL (n : Nat) : Nat := (let b = MkBox(3); let r = match b.0 { Z => 0, S(m) => 1, }; r)
  def WrE (b : Box) : Nat := (b.0 := 0; match b.0 { Z => 0, S(m) => 1, })
  def WrL (b : Box) : Nat := (b.0 := 0; let r = match b.0 { Z => 0, S(m) => 1, }; r)
  -- a field of a type with several constructors
  def TrE (b : BT) : Nat := match b.0 { TA => 0, TB => 1, TC => 2, }
  def TrL (b : BT) : Nat := (let r = match b.0 { TA => 0, TB => 1, TC => 2, }; r)
  def TrERun : Eq(Nat, TrE(MkBT(TC)), 2) := refl
  -- a field another field's type depends on; the dependent field, at a stuck type and once known
  def DpE (d : DP) : Nat := match d.0 { Z => 0, S(m) => 1, }
  def DpL (d : DP) : Nat := (let r = match d.0 { Z => 0, S(m) => 1, }; r)
  reject def DxE (d : DP) : Nat := match d.1 { TA => 0, TB => 1, TC => 2, }
  reject def DxL (d : DP) : Nat := (let r = match d.1 { TA => 0, TB => 1, TC => 2, }; r)
  def DxKE (d : DP) : Nat := match d { MkDP(n, x) => match n { Z => 0, S(k) => match d.1 { TA => 0, TB => 1, TC => 2, }, }, }
  def DxKL (d : DP) : Nat := match d { MkDP(n, x) => match n { Z => 0, S(k) => (let r = match d.1 { TA => 0, TB => 1, TC => 2, }; r), }, }
  -- a call; a sealed program's field
  def CaE (n : Nat) : Nat := match Id1(n) { Z => 0, S(m) => 1, }
  def CaL (n : Nat) : Nat := (let r = match Id1(n) { Z => 0, S(m) => 1, }; r)
  def SeE (n : Nat) : Nat := (let b = mk(n); match b.0 { Z => 0, S(m) => 1, })
  def SeL (n : Nat) : Nat := (let b = mk(n); let r = match b.0 { Z => 0, S(m) => 1, }; r)
  def SeEC : Eq(Nat, SeE(0), 0) := refl
  -- a proof's field (And's second component), matched by its type
  def PfE (h : And(True, Ex)) : True := match h.1 { W1(n) => refl, W2(m) => refl, }
  def PfL (h : And(True, Ex)) : True := (let r : True = match h.1 { W1(n) => refl, W2(m) => refl, }; r)
  -- in an arm; against a goal that names the same match
  def ArE (n : Nat) (b : Box) : Nat := match n { Z => match b.0 { Z => 0, S(m) => 1, }, S(k) => 0, }
  def ArL (n : Nat) (b : Box) : Nat := match n { Z => (let r = match b.0 { Z => 0, S(m) => 1, }; r), S(k) => 0, }
  def GoE (b : Box) : Eq(Nat, match b.0 { Z => 0, S(m) => 1, }, F1E(b)) := match b.0 { Z => refl, S(m) => refl, }
  -- a proof field of data: by `.1` (D81) at the end and under a `let`, and by a match
  inductive VP := MkVP(n : Nat, h : Eq(Nat, n, S(Z)))
  reject def PdE (r : &VP) : Unit := ((*r).0 := Z; match (*r).1 {})
  reject def PdL (r : &VP) : Unit := ((*r).0 := Z; let z : Unit = match (*r).1 {}; z)
  reject def PdM (r : &VP) : Unit := ((*r).0 := Z; match *r { MkVP(n, h) => match h {}, })
}

#guard (run "FieldScrutinee" FieldScrutinee).rejectedWith [
  ("DxE", "[Match] on d.x, whose type ⌈F(σ1)⌉ is not an inductive type"),
  ("DxL", "[Match] on d.x, whose type ⌈F(σ1)⌉ is not an inductive type"),
  ("PdE", "[D81] *r.1: field h of VP is a proof and *r is data, and `.1` takes a field of its parent's class: name it with a match, `let MkVP(…) = *r`"),
  ("PdL", "[D81] *r.1: field h of VP is a proof and *r is data, and `.1` takes a field of its parent's class: name it with a match, `let MkVP(…) = *r`"),
  ("PdM", "[Match] on (*r).h, which was moved out")]
