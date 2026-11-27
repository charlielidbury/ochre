import Ochr.Examples.Logic
import Ochr.Examples.Nat
import Ochr.Examples.Fixtures
import Ochr.Examples.Word

/-! # 4. Closing off: what a stuck computation leaves behind

Checking runs programs on abstract values, and a match on an abstract number gets stuck.
A call whose body is stuck is *closed off*: its result, and the final content of each
place it borrowed, are replaced by *sealed programs*, closed source programs that
compute them, such as `⌈let c = σ; AddM(&c, 0); c⌉` (RULES P4, [Close]). A sealed program
runs again when more is known about its inputs ([Seal]).

A match that gets stuck outside tail position (followed by more code, or inside a type)
is closed off the same way (exp-block-text): its sealed program binds the places it uses,
each in a cell, and is then the match itself, `⌈let n = S(σ2); let m = σ1; match m { … }⌉`;
it is not a function, and nothing calls it. It captures as a Rust closure would: a place some arm moves out of is moved in, a place
some arm writes or borrows is borrowed, and any other place it reads is copied ("Stuck
blocks"). This is how a borrow chosen by a branch is handled.

Defined in RULES §3: [Close], [Seal], stuck blocks; [Split] in §5 checks the arms. -/

open Ochr.Test

ochr ClosingOff uses Logic, Nats, Fixtures {
  -- ## A borrow chosen by a branch
  -- The match is not in tail position: its arms are checked, then it is closed off, and the
  -- rest of the body runs once, on the borrow the closed-off block returns.
  def AddToOne (b : Nat) (x1 : &Nat) (x2 : &Nat) (y : Nat) : Unit := (
    let r = match b {
      Z => x1,
      S _ => x2,
    };
    AddM(r, y)
  )

  -- The same program with the continuation copied into each arm ...
  def AddToOne' (b : Nat) (x1 : &Nat) (x2 : &Nat) (y : Nat) : Unit := (
    match b {
      Z => AddM(x1, y),
      S _ => AddM(x2, y),
    }
  )

  -- ... and with the match moved into a function, `Fixtures`' `Pick`.
  def AddToOne'' (b : Nat) (x1 : &Nat) (x2 : &Nat) (y : Nat) : Unit := (
    let r = Pick(b, x1, x2);
    AddM(r, y)
  )

  -- Adding zero through the chosen borrow does nothing, in all three versions. For the
  -- first, the stuck match inside the goal is closed off the same way.
  def AddToOneZero (b : Nat) (x1 : &Nat) (x2 : &Nat) : Id(Unit, AddToOne(clone(b), &*x1, &*x2, 0), ()) := (
    match b {
      Z => AddMZero(x1),
      S _ => AddMZero(x2),
    }
  )

  def AddToOneZero' (b : Nat) (x1 : &Nat) (x2 : &Nat) : Id(Unit, AddToOne'(clone(b), &*x1, &*x2, 0), ()) := (
    match b {
      Z => AddMZero(x1),
      S _ => AddMZero(x2),
    }
  )

  def AddToOneZero'' (b : Nat) (x1 : &Nat) (x2 : &Nat) : Id(Unit, AddToOne''(clone(b), &*x1, &*x2, 0), ()) := (
    match b {
      Z => AddMZero(x1),
      S _ => AddMZero(x2),
    }
  )

  -- The arms of a stuck match must agree on a type, or the match must be annotated.
  reject def ArmTypes (b : Nat) : Nat := (
    let r = match b {
      Z => 0,
      S _ => (),
    };
    0
  )

  def ArmAnnot (b : Nat) : Nat := (
    let r : Nat = match b {
      Z => 0,
      S _ => 1,
    };
    r
  )

  -- ## Stuck matches in statements
  -- Both sides close off into the same sealed program, so `refl` proves the equation.
  def StuckGoal (b : Nat) : Id(Nat, (match b { Z => 0, S _ => 1 }), (match b { Z => 0, S _ => 1 })) := refl

  -- After a case split on `b`, the sealed programs run again, to each arm's value.
  def StuckGoalSplit (b : Nat) : Id(Nat, (match b { Z => 0, S m => S(m) }), b) := (
    match b {
      Z => refl,
      S _ => refl,
    }
  )

  -- A false statement stays unprovable (it fails when `b` is 2 or more).
  reject def StuckGoalWrong (b : Nat) : Id(Nat, (match b { Z => 0, S _ => 1 }), clone(b)) := (
    match b {
      Z => refl,
      S _ => refl,
    }
  )

  -- A recursive call inside a match that is not in tail position is checked in its arm;
  -- the closed-off block then takes the function itself as a value argument.
  def NonTailRec (x : &Nat) : Unit by x := (
    match *x {
      Z => (),
      S p => NonTailRec(&p),
    };
    ()
  )

  -- ## What a stuck match captures
  -- A local the match writes (`c := 1`) is passed to the block by borrow, so the write is
  -- seen after the block.
  def WriteInBlock (b : Nat) :
      Id(Nat, (let c = b; match c { Z => c := 1, S _ => () }; c), (match b { Z => 1, S m => S(m) })) := (
    match b {
      Z => refl,
      S _ => refl,
    }
  )

  -- A borrow the match uses but does not move is reborrowed, so it stays usable afterwards.
  def ReborrowInBlock (b : Nat) (x : &Nat) : Unit := (
    match b {
      Z => AddM(&*x, 1),
      S _ => (),
    };
    AddM(x, 2)
  )

  -- A borrow some arm moves (`x1`, in arm `Z`) is moved into the block, so using it
  -- afterwards is a use after move. If the block only reborrowed it,
  -- `MovedByBlock` would be accepted, although in arm `Z` it uses `x1` after moving it into
  -- `r`.
  reject def AliasAfterBlock (b : Nat) (x1 : &Nat) (x2 : &Nat) : Unit := (
    let r = match b {
      Z => x1,
      S _ => x2,
    };
    AddM(x1, 1);
    AddM(r, 2)
  )

  reject def MovedByBlock (b : Nat) (x1 : &Nat) (x2 : &Nat) : Unit := (
    let r = match b {
      Z => x1,
      S _ => x2,
    };
    AddM(r, 1);
    AddM(x1, 2)
  )

  -- twin of MovedByBlock: `x1` is not used after the block moved it
  def MovedByBlockOk (b : Nat) (x1 : &Nat) (x2 : &Nat) : Unit := (
    let r = match b {
      Z => x1,
      S _ => x2,
    };
    AddM(r, 1)
  )

  -- A closure in an arm captures a copy, so its write `n0 := 0` is to that copy, not a
  -- write by the block: the block copies `n0` in, and the closure can capture it again when
  -- the block re-runs (fuzz-port R2 (i); counted as the block's write, `n0` went in by `&`,
  -- and the re-run closure captured a borrow).
  -- Since D68 the closure captures `n0` by move in a statement too, so the arm's later read of
  -- `n0` is a use after a move.
  reject def LamWriteInBlock (n0 : Nat) :
      Id(Nat, (match n0 { Z => n0, S p2 => (let a5 = (λ(y6 : &Nat) : Unit => n0 := 0); n0) }), n0) := (
    match n0 {
      Z => refl,
      S p => refl,
    }
  )

  -- twin of LamWriteInBlock: the closure writes its own parameter, so it captures nothing and the arm's read of `n0` is fine
  def LamWriteInBlockOk (n0 : Nat) :
      Id(Nat, (match n0 { Z => n0, S p2 => (let a5 = (λ(y6 : &Nat) : Unit => *y6 := 0); n0) }), n0) := (
    match n0 {
      Z => refl,
      S p => refl,
    }
  )

  -- A closure in an arm captures by move what it mentions, in a statement too (D68), so the
  -- block takes `p5` by move on every path, whether or not the run took that arm; the closure
  -- keeps the value it captured before `c` is overwritten. (D63 rejected this: the block took
  -- the place by `&`, and [Fix] captures no borrow.)
  def LamReadInWrittenBlock (q2 : Nat × Nat) :
      Id(Nat, let c = q2; let a0 = match c { Mk(p5, p6) => (let f = (λ(y7 : Nat) : Nat => p5); c := (1, 1); f) }; a0(0), (let d = q2; match d { Mk(p5, p6) => p5 })) := (
    match q2 {
      Mk(a, b) => refl,
    }
  )

  -- ... in a statement, though, a closure captures by move like any code (D68), so the block
  -- takes `n0` by move, not by borrow, and the closure captures the moved value (fuzz-port,
  -- seed 1, case 182, was rejected for capturing a borrow)
  def LamReadOtherArm (n0 : Nat) : Prop :=
    Id(Nat, (match n0 { Z => (n0 := S(n0); 0), S _ => (let f = (λ(y : Nat) : Nat => n0); 0) }), (let m = n0; 0))

  -- Comparing two blocks' functions observed them at a generic argument, where a pattern's
  -- sub-place their arms read may not exist (`q0.0` of the abstract pair `q0`), a type error
  -- (fuzz-port R3; `notes/catch-census.md`), so the true statement was rejected. exp-block-text:
  -- a block is not a function, and two sealed blocks are compared by their texts ([Conv-cong]),
  -- never observed at other values than the ones they captured: accepted.
  def ConvBlocks (q0 : Nat × Nat) : Prop := (
    match q0 {
      Mk(a, b) =>
        Id(Nat × Nat, (match q0 { Mk(p0, p1) => match p0 { Z => q0, S p7 => (q0 := Mk(clone(p1), p1); q0) } }), (match q0 { Mk(p15, p16) => match p16 { Z => (p16 := 0; (1, 0)), S _ => q0 } })),
    }
  )

  -- ## How a stuck call returns: the row of [Close]
  -- A stuck call returns a borrow with a hole when its declared result type is written
  -- `&T` (`ReturnedBorrows`), and otherwise its sealed program, which at a declared `Unit` is
  -- `()` (η for `Unit`, D59, D80). `G`'s declared result type `UU(n)` reads as `Unit` for every
  -- `n`, since both arms of `UU` are `Unit` (D80: read from `UU`'s body, never computed), so
  -- `RowUnit` and `RowI` both hold by `refl` and the induction of `RowIInd` is not needed.
  -- Without η, a call written to return `Unit` returned `()`, `G`'s returned a sealed program,
  -- and `RowI` failed.
  def UU (n : Nat) : Type := (
    match n {
      Z => Unit,
      S _ => Unit,
    }
  )

  def AddU (x : &Nat) : Unit by x := (
    match *x {
      Z => (),
      S p => AddU(&p),
    }
  )

  def G (x : &Nat) (n : Nat) : UU(n) by x := (
    match n {
      Z => match *x {
        Z => (),
        S p => G(&p, n),
      },
      S _ => AddU(x),
    }
  )

  def RowUnit (x : &Nat) : Id(Unit, let c = clone(*x); AddU(&c), ()) := refl
  def RowI (x : &Nat) : Id(Unit, let c = clone(*x); G(&c, Z), ()) := refl

  def RowIInd (x : &Nat) : Id(Unit, let c = clone(*x); G(&c, Z), ()) by x := (
    match *x {
      Z => refl,
      S p => RowIInd(&p),
    }
  )

  -- η for `Unit` (D59, refined; D80): values are in η-normal form where their declared type
  -- reads as `Unit`. A parameter `u : Unit` (or `UU(Z)`) is `()`, and a call whose declared
  -- result type reads as `Unit` returns `()`; a stuck one's effects are in its borrowed places'
  -- fills. `Eq` at `Unit` and comparing functions into `Unit` then need no rule of their own:
  -- both sides are `()`.
  def UnitEta (u : Unit) (v : Unit) : Eq(Unit, u, v) := refl
  def UnitEtaUU (u : UU(Z)) (v : UU(Z)) : Eq(UU(Z), u, v) := refl
  def UnitNotConv (u : Unit) (P : Unit → Prop) (h : P(u)) : P(()) := h
  def StuckResult (x : &Nat) (P : Unit → Prop) (h : P(let c = *x; AddM(&c, 0))) : P(let d = *x; AddM(&d, Add(0, 0))) := h
  -- prop-checker's gap (`Scratch/D59ConvGap.lean`): with the result a sealed program, these
  -- true statements were rejected
  def StuckResultUnit (x : &Nat) (P : Unit → Prop) (h : P(())) : P(let c = *x; AddM(&c, 0)) := h
  def StuckResultArgs (x : &Nat) (P : Unit → Prop) (h : P(let c = *x; AddM(&c, 0))) : P(let c = *x; AddM(&c, 1)) := h
  def ConvUnitRes : Eq(Π(x : &Nat). Unit, (λ(x : &Nat) : Unit => ()), (λ(x : &Nat) : Unit => (let c = clone(*x); G(&c, Z)))) := refl
  def ConvUnitWritten :
      Eq(Π(x : &Nat). UU(Z), (λ(x : &Nat) : UU(Z) => ()), (λ(x : &Nat) : UU(Z) => (let c = clone(*x); G(&c, Z)))) := (
    refl
  )

  -- D80: η reads the declared result type, never the computed one, so `G(&c, n)` is `()` at an
  -- unknown `n` as at `Z`: `UU(n)` reads as `Unit` because both arms of `UU` do. `NeutralKept`
  -- was rejected while η read the computed type, which is the neutral `UU(n)` there; it is true
  -- (both arguments of `P` are `()`). A type that is `Unit` only at some arguments is not read
  -- as `Unit` (`DeclaredReadings.ComputedMix`).
  def ComputedUnit (x : &Nat) (P : Unit → Prop) (h : P(())) : P(let c = *x; G(&c, Z)) := h
  def NeutralKept (x : &Nat) (n : Nat) (P : UU(n) → Prop) (h : P(let c = *x; G(&c, n))) : P(let c = S(*x); G(&c, n)) := h
  def NeutralKeptZ (x : &Nat) (P : UU(Z) → Prop) (h : P(let c = *x; G(&c, Z))) : P(let c = S(*x); G(&c, Z)) := h

  -- ## Typing a sealed program
  -- A sealed program is typed by running its program, typed. A value embedded in it with no
  -- type of its own is typed by where it sits: a proof argument, `⋆`, by its parameter's
  -- declared type, and a place lent out by its borrow's content. Here `y` is the sealed
  -- `H(σ, ⋆)`, and both a split on a decision about it and a closure capturing it type it
  -- (arrays-library) ... The order is on `Nat` here, not `Words`' on `Word`; `Dec` is
  -- `Logic`'s.
  def Le (a : Nat) (b : Nat) : Prop by a := (
    match a {
      Z => ⊤,
      S a' => match b {
        Z => False,
        S b' => Le(a', b'),
      },
    }
  )

  def Lt (a : Nat) (b : Nat) : Prop := Le(S(a), b)

  def LeDec (a : Nat) (b : Nat) : Dec(Le(a, b), Lt(b, a)) by a := (
    match a {
      Z => Yes(refl),
      S a' => match b {
        Z => No(refl),
        S b' => LeDec(a', b'),
      },
    }
  )

  def H (x : Nat) (h : ⊤) : Nat by x := (
    match x {
      Z => Z,
      S p => H(p, h),
    }
  )

  def UseDec (x : Nat) : Nat := (
    let y = H(clone(x), refl);
    let d = LeDec(y, x);
    match d {
      Yes(h) => 0,
      No(k) => 1,
    }
  )

  def Apply (f : Π(u : Unit). Nat) : Nat := f(())

  def UseApply (x : Nat) : Nat := (
    let y = H(x, refl);
    Apply(λ(u : Unit) : Nat => clone(y))
  )

  -- ... and the `Id` in the stuck match's `Z` arm observes the match's cell for `*x0`, which
  -- the block's re-run at `*x0 := 0` has lent out (fuzz-port).
  def IdInBlock (x0 : &Nat) : Id(Prop, (match *x0 { Z => Id(Unit, (), *x0 := 0), S _ => ⊤ }), ⊤) := (
    match *x0 {
      Z => refl,
      S _ => refl,
    }
  )

  -- ## What goes wrong without these rules
  -- The closed-off block of `Clear` writes through the pattern variable `p`, which names
  -- `(*x).0`: a write to `*x` (D32). If the block did not see that write, it would copy `*x` instead of borrowing it, the write would be
  -- lost, and `Boom5` would prove `1 = 2`.
  reject def Clear (x : &Nat) : Id(Unit, (match *x { Z => (), S p => p := Z }), ()) := refl

  -- twin of Clear: the right-hand side is the same write, not `()`
  def ClearOk (x : &Nat) : Id(Unit, (match *x { Z => (), S p => p := Z }), (match *x { Z => (), S p => p := Z })) := refl

  reject def Boom5 : Eq(Nat, S(Z), S(S(Z))) := (
    let c = S(S(Z));
    Clear(&c)
  )

  -- twin of Boom5: the claim is the true `1 = 1`, with the write to `c` seen
  def Boom5Ok : Eq(Nat, S(Z), S(Z)) := (
    let c = S(S(Z));
    ClearOk(&c)
  )

  -- A sealed program whose head is a call of an abstract function stays as it is when it is
  -- normalised (D39): it is not closed off again, which would loop. `P1` only has to be
  -- checked without looping.
  def P1 (h : Π(x : &Nat) (y : &Nat). &Nat) : Prop := (
    Id(Nat, let a = Z; let b = Z; (let r = h(&a, &b); ()); a, Z)
  )

  -- An earlier version joined a match that is not in tail position by taking the refined
  -- types from its arms, so after `match b` the hypothesis `h : Id(Nat, b, 0)` could get the
  -- `S` arm's type, `False`. Closing the match off instead continues from the state before
  -- the split, where `h` still says `Id(Nat, b, 0)` (D15).
  reject def Bad (b : Nat) (h : Id(Nat, clone(b), 0)) : False := (
    match b {
      Z => (),
      S _ => (),
    };
    h
  )

  -- Seed 10 case 8706. A stuck block takes a place by move if any arm moves it, so the block
  -- over `n2` takes `n1` by move (arm `Z` moves it into `*x0`), and arm `S`'s `&n1` would return
  -- a borrow of the block's own parameter, which dies where the arm returns. Until D87 the
  -- block's [Return] let that borrow out: `MoveBorrowBlk` was accepted, and only the split
  -- (`MoveBorrowSplit`) or a direct run at `n2 = 1` met the [Join] drop of `n1` (D84). D87
  -- rejects it where the block forms, with the same message as the direct path, so both paths
  -- agree; `MoveBorrowCode` is its runtime-code twin
  reject def MoveBorrowBlk (x0 : &Nat) (n1 : Nat) (n2 : Nat) : Prop :=
    Id(Unit, (let r = match n2 { Z => (*x0 := n1; &*x0), S _ => &n1 }; ()), (let m = n1; ()))
  reject def MoveBorrowSplit (x0 : &Nat) (n1 : Nat) (n2 : Nat) (h : MoveBorrowBlk(x0, n1, n2)) : Unit :=
    match n2 { Z => (), S _ => () }
  reject def MoveBorrowCode (x0 : &Nat) (n1 : Nat) (n2 : Nat) : Unit := (
    let m = clone(n2);
    let r = match m { Z => (*x0 := n1; &*x0), S _ => &n1 };
    match n2 { Z => (), S _ => () }
  )
}


/-! ## Borrow ends agree on every path

`Fixtures`' `Pick` returns a borrow, so it lends that borrow both `a` and `b`, as Rust's
`fn pick<'a>(n: u32, x: &'a mut u32, y: &'a mut u32) -> &'a mut u32` does, whatever `n` is:
at an abstract `n`, where the call is stuck and each place holds a sealed program with the
borrow's hole, and at each concrete `n`, where the call runs and the borrow points into one of
them (D90). Reading `b` ends it, and the write through `r` in arm `Z` fails, at every `n`. So
`PickEarly` is rejected, and so is its instance `PickEarly0` at `n = 0`, which was accepted
until D90 (the symbolic run then agreed with the concrete ones only up to which borrows had
ended, and an accepted definition could fail when called: `StaticEnds` in
`ReturnedBorrows.lean`). Rust rejects both. -/

ochr Naturality uses Fixtures {
  reject def PickEarly (n : Nat) (a : Nat) (b : Nat) : Unit := (
    let r = Pick(clone(n), &a, &b);
    let z = b;
    match n {
      Z => *r := 5,
      S _ => (),
    }
  )

  -- twin of PickEarly: `b` is not read before the write through `r`
  def PickEarlyOk (n : Nat) (a : Nat) (b : Nat) : Unit := (
    let r = Pick(clone(n), &a, &b);
    match n {
      Z => *r := 5,
      S _ => (),
    }
  )

  -- D90: `b` is lent to `r` though `Pick(0, …)` points into `a`, so reading `b` ends `r` and
  -- the write through it fails, as at an abstract `n` (accepted before D90)
  reject def PickEarly0 (a : Nat) (b : Nat) : Unit := (
    let n = 0;
    let r = Pick(clone(n), &a, &b);
    let z = b;
    match n {
      Z => *r := 5,
      S _ => (),
    }
  )

  -- at `n = 1` arm `Z` does not run, so the ended borrow is never used
  def PickEarly1 (a : Nat) (b : Nat) : Unit := (
    let n = 1;
    let r = Pick(clone(n), &a, &b);
    let z = b;
    match n {
      Z => *r := 5,
      S _ => (),
    }
  )
}

#guard (run "Naturality" Naturality).rejectedWith [
  ("PickEarly", "no such place *r: its path does not exist in ⊥"),
  ("PickEarly0", "no such place *r: its path does not exist in ⊥")]


/-! ## A stuck block's captures over-approximate every arm (notes/erasure-model.md, K1)

A stuck block takes each outer place by the largest effect any arm has on it (copy ⊑ `&` ⊑
move), at the granularity of the place an arm moves, net of an arm's own refills. So the code
after the block sees, at the generic call, at least every effect the direct match has at any
instance: a field an arm moves is gone after the block, a field an arm moves and refills is
not, a field one arm lends while the other moves its sibling stays readable, and a statement
inside an arm (run on its own private copy) affects nothing outside it. -/

ochr BlockCaptures uses Nats, Fixtures {
  def K (y : &Nat) : Unit := ()

  -- an arm moves a field; the code after the block reads it (the direct path at `n = 0`
  -- reads a moved field)
  reject def MovedField (n : Nat) (q : Nat × Nat) : Nat := (
    match q { Mk(a, b) => (match n { Z => (let t = a; ()), S _ => () }; a) }
  )

  -- twin of MovedField: the arm refills the field it moved, so its net effect is a write
  def RefilledField (n : Nat) (q : Nat × Nat) : Nat := (
    match q { Mk(a, b) => (match n { Z => (let t = a; a := Z; ()), S _ => () }; a) }
  )

  -- one arm lends a field to a call while the other moves its sibling: the lent field is
  -- readable after the block
  def LentSibling (n : Nat) (q : Nat × Nat) : Nat := (
    match q { Mk(a, b) => (match n { Z => K(&a), S _ => (let t = b; ()) }; a) }
  )

  -- twin of LentSibling, reading the moved sibling instead
  reject def MovedSibling (n : Nat) (q : Nat × Nat) : Nat := (
    match q { Mk(a, b) => (match n { Z => K(&a), S _ => (let t = b; ()) }; b) }
  )

  -- a statement inside an arm reads `x` on its own private copy: `x` is unchanged after
  def StmtInArm (n : Nat) (x : Nat) :
      Id(Nat, (match n { Z => (let h : Eq(Nat, x, x) = refl; ()), S _ => () }; x), x) := refl

  -- a proof inside an arm lends `x` to a lemma: in place, but within the proof's own copy
  def TrueOf (x : &Nat) : True := I
  def ProofLendsInArm (n : Nat) (x : Nat) : Nat := (
    match n { Z => (let h : True = TrueOf(&x); ()), S _ => () };
    x
  )
}


/-! ## Closing off computes what the call would have (notes/closeoff-model.md, (C))

A closed-off call's sealed programs are the call delayed: run again once a refinement decides
what the call was stuck on, each computes exactly what the call would have produced at those
arguments, its result and the final content of each place it borrowed. A returned borrow's
final content is a parameter of every fill (its hole), filled when the borrow ends. Each pair
below is a true statement that needs this to hold, and the same statement made false at one
instance, which must be rejected: the hole sitting in two fills (`Pick`), the last of two
writes through a returned borrow, a reborrow through it passed to another stuck call, the
returned borrow moved into a second call, the hole met as an inert loan by a re-run that a
later split triggers, a closed-off call generalised by a split and derived again (refined
once and twice), and a stuck block whose arms close off calls or return a borrow. -/

ochr CloseOffModel uses Nats, Fixtures {
  def CoPick (n : Nat) (a : &Nat) (b : &Nat) :
      Id(Unit, (let r = Pick(clone(n), &*a, &*b); *r := 5), (match n { Z => *a := 5, S _ => *b := 5, })) :=
    match n { Z => refl, S _ => refl, }
  reject def CoPickOnlyA (n : Nat) (a : &Nat) (b : &Nat) : Id(Unit, (let r = Pick(clone(n), &*a, &*b); *r := 5), *a := 5) :=
    match n { Z => refl, S _ => refl, }
  reject def CoPickBoth (n : Nat) (a : &Nat) (b : &Nat) : Id(Unit, (let r = Pick(clone(n), &*a, &*b); *r := 5), (*a := 5; *b := 5)) :=
    match n { Z => refl, S _ => refl, }
  reject def CoPickRefl (n : Nat) (a : &Nat) (b : &Nat) : Id(Unit, (let r = Pick(clone(n), &*a, &*b); *r := 5), *a := 5) := refl

  def CoTwice (x : &Nat) : Id(Unit, (let t = TailM(x); *t := 1; *t := 2), AddM(x, 2)) by x :=
    match *x { Z => refl, S p => CoTwice(&p), }
  reject def CoTwiceFirst (x : &Nat) : Id(Unit, (let t = TailM(x); *t := 1; *t := 2), AddM(x, 1)) by x :=
    match *x { Z => refl, S p => CoTwiceFirst(&p), }

  def CoReborrow (x : &Nat) (y : Nat) : Id(Unit, (let t = TailM(x); AddM(&*t, y)), AddM(x, y)) by x :=
    match *x { Z => refl, S p => CoReborrow(&p, y), }
  reject def CoReborrowOff (x : &Nat) (y : Nat) : Id(Unit, (let t = TailM(x); AddM(&*t, y)), AddM(x, S(y))) by x :=
    match *x { Z => refl, S p => CoReborrowOff(&p, y), }

  def CoMoved (x : &Nat) : Id(Unit, (let t = TailM(x); let u = TailM(t); *u := 3), AddM(x, 3)) by x :=
    match *x { Z => refl, S p => CoMoved(&p), }
  reject def CoMovedOff (x : &Nat) : Id(Unit, (let t = TailM(x); let u = TailM(t); *u := 3), AddM(x, 2)) by x :=
    match *x { Z => refl, S p => CoMovedOff(&p), }

  def CoInert (n : Nat) : Unit := (
    let c = clone(n);
    let t = TailM(&c);
    match n {
      Z => (*t := 7; (let u = t; ()); let h : Id(Nat, clone(c), 7) = refl; ()),
      S m => (),
    }
  )
  reject def CoInertOff (n : Nat) : Unit := (
    let c = clone(n);
    let t = TailM(&c);
    match n {
      Z => (*t := 7; (let u = t; ()); let h : Id(Nat, clone(c), 8) = refl; ()),
      S m => (),
    }
  )
  def CoWrittenFirst (n : Nat) : Unit := (
    let c = clone(n);
    let t = TailM(&c);
    *t := 7;
    (let u = t; ());
    match n {
      Z => (let h : Id(Nat, clone(c), 7) = refl; ()),
      S m => match m { Z => (let h : Id(Nat, clone(c), S(7)) = refl; ()), S k => (), },
    }
  )
  reject def CoWrittenFirstOff (n : Nat) : Unit := (
    let c = clone(n);
    let t = TailM(&c);
    *t := 7;
    (let u = t; ());
    match n {
      Z => (let h : Id(Nat, clone(c), 7) = refl; ()),
      S m => match m { Z => (let h : Id(Nat, clone(c), 7) = refl; ()), S k => (), },
    }
  )
  def CoPerArm (n : Nat) : Unit := (
    let c = clone(n);
    let t = TailM(&c);
    match n {
      Z => (*t := 1; (let u = t; ()); let h : Id(Nat, clone(c), 1) = refl; ()),
      S m => match m { Z => (*t := 2; (let u = t; ()); let h : Id(Nat, clone(c), S(2)) = refl; ()), S k => (), },
    }
  )
  reject def CoPerArmOff (n : Nat) : Unit := (
    let c = clone(n);
    let t = TailM(&c);
    match n {
      Z => (*t := 1; (let u = t; ()); let h : Id(Nat, clone(c), 1) = refl; ()),
      S m => match m { Z => (*t := 2; (let u = t; ()); let h : Id(Nat, clone(c), S(1)) = refl; ()), S k => (), },
    }
  )

  def CoGen (x : Nat) : Unit := (
    let a = Add(clone(x), 0);
    match a {
      Z => (let h : Id(Nat, Add(clone(x), 0), Z) = refl; ()),
      S q => (let h : Id(Nat, Add(clone(x), 0), S(clone(q))) = refl; ()),
    }
  )
  reject def CoGenOff (x : Nat) : Unit := (
    let a = Add(clone(x), 0);
    match a {
      Z => (),
      S q => (let h : Id(Nat, Add(clone(x), 0), Z) = refl; ()),
    }
  )
  def CoGenTwice (x : Nat) : Unit := (
    let a = Add(clone(x), 1);
    match a {
      Z => (),
      S q => match q {
        Z => (let h : Id(Nat, Add(clone(x), 1), S(Z)) = refl; ()),
        S r => (let h : Id(Nat, Add(clone(x), 1), S(S(clone(r)))) = refl; ()),
      },
    }
  )
  reject def CoGenTwiceOff (x : Nat) : Unit := (
    let a = Add(clone(x), 1);
    match a {
      Z => (),
      S q => match q {
        Z => (let h : Id(Nat, Add(clone(x), 1), Z) = refl; ()),
        S r => (),
      },
    }
  )

  def CoBlockCalls (n : Nat) (x : &Nat) : Unit := (
    let old = clone(*x);
    match n { Z => AddM(&*x, 1), S _ => AddM(&*x, 2), };
    match n {
      Z => (let h : Id(Nat, clone(*x), Add(clone(old), 1)) = refl; ()),
      S _ => (let h : Id(Nat, clone(*x), Add(clone(old), 2)) = refl; ()),
    }
  )
  reject def CoBlockCallsOff (n : Nat) (x : &Nat) : Unit := (
    let old = clone(*x);
    match n { Z => AddM(&*x, 1), S _ => AddM(&*x, 2), };
    match n {
      Z => (let h : Id(Nat, clone(*x), Add(clone(old), 2)) = refl; ()),
      S _ => (),
    }
  )
  def CoBlockBorrow (n : Nat) (m : Nat) (a : &Nat) (b : &Nat) : Unit := (
    let r = match m { Z => Pick(clone(n), &*a, &*b), S _ => Pick(clone(n), &*b, &*a), };
    *r := 9;
    (let u = r; ());
    match m {
      Z => match n { Z => (let h : Id(Nat, clone(*a), 9) = refl; ()), S _ => (let h : Id(Nat, clone(*b), 9) = refl; ()), },
      S _ => match n { Z => (let h : Id(Nat, clone(*b), 9) = refl; ()), S _ => (let h : Id(Nat, clone(*a), 9) = refl; ()), },
    }
  )
  reject def CoBlockBorrowOff (n : Nat) (m : Nat) (a : &Nat) (b : &Nat) : Unit := (
    let r = match m { Z => Pick(clone(n), &*a, &*b), S _ => Pick(clone(n), &*b, &*a), };
    *r := 9;
    (let u = r; ());
    match m {
      Z => match n { Z => (let h : Id(Nat, clone(*b), 9) = refl; ()), S _ => (), },
      S _ => (),
    }
  )
}


/-! ## Copy or move, and η at `Unit`, read from declared types (D80)

A read copies exactly when the place's declared type reads as a copy type, and a value is `()`
exactly where its declared type reads as `Unit`: a parameter, a call's result, the fill of a
lent place. Both are read by the one reader of declared types (D77's, which reads a type
function's body and the arguments of a call as written), never from a value or a computed type,
so a definition's generic call and each of its instances decide them alike. As in Rust, a type
parameter is never a copy type, whatever an instance substitutes for it; and a type that is
`Unit` only at some arguments, by computation, is not normalised. Each test has its twin. -/

ochr DeclaredReadings uses Nats, Words, Fixtures {
  -- R1, copy or move. `x : A` moves on every path, at `A := Word` as at the generic call
  def IdF (A : Type) (x : A) : A := x
  reject def Dup (A : Type) (x : A) : Pair(A, A) := Mk(x, x)
  -- twin of Dup: `clone` copies, whatever the type
  def DupC (A : Type) (x : A) : Pair(A, A) := Mk(clone(x), x)
  def DupCAt (w : Word) : Id(Pair(Word, Word), DupC(Word, w), Mk(w, w)) := refl
  -- a call's declared result type, with its type arguments as written: `IdF(Word, w)` is a `Word`
  def LetW (w : Word) : Pair(Word, Word) := (let y = IdF(Word, w); Mk(y, y))
  -- twin of LetW: at a type parameter it is not a copy type
  reject def LetA (A : Type) (a : A) : Pair(A, A) := (let y = IdF(A, a); Mk(y, y))
  -- a type function's call is a copy type when every arm of its body is one
  def MixT (n : Nat) : Type := match n { Z => Unit, S _ => Nat }
  def CopyT (n : Nat) : Type := match n { Z => Unit, S _ => Word }
  reject def ReadMix (n : Nat) (u : MixT(n)) : Pair(MixT(n), MixT(n)) := Mk(u, u)
  -- twin of ReadMix: both arms of `CopyT` are copy types
  def ReadCopy (n : Nat) (u : CopyT(n)) : Pair(CopyT(n), CopyT(n)) := Mk(u, u)

  -- R2, η at `Unit`. A type function every arm of whose body is `Unit` reads as `Unit`, so its
  -- values are `()`, at an unknown argument too
  def SameT (n : Nat) : Type := match n { Z => Unit, S _ => Unit }
  def SameEta (n : Nat) (u : SameT(n)) (v : SameT(n)) : Eq(SameT(n), u, v) := refl
  -- twin of SameEta: `MixT(n)` is `Unit` only at `Z`, so its values are not normalised
  reject def MixEta (n : Nat) (u : MixT(n)) (v : MixT(n)) : Eq(MixT(n), u, v) := refl
  -- a call whose declared result type reads as `Unit` returns `()`, stuck or not
  def GS (x : &Nat) (n : Nat) : SameT(n) by x := (
    match n {
      Z => match *x { Z => (), S p => GS(&p, n) },
      S _ => (),
    }
  )
  def DeclaredUnit (x : &Nat) : Id(SameT(Z), let c = clone(*x); GS(&c, Z), ()) := refl
  -- twin of DeclaredUnit: `MixT(Z)` computes to `Unit`, but `GM`'s declared result type
  -- `MixT(n)` does not read as `Unit`, so its stuck call keeps its sealed program. True, and
  -- rejected: no decision reads the computed type (D80); `ComputedMixInd` proves it by induction
  def GM (x : &Nat) (n : Nat) : MixT(n) by x := (
    match n {
      Z => match *x { Z => (), S p => GM(&p, n) },
      S _ => Z,
    }
  )
  reject def ComputedMix (x : &Nat) : Id(MixT(Z), let c = clone(*x); GM(&c, Z), ()) := refl
  def ComputedMixInd (x : &Nat) : Id(MixT(Z), let c = clone(*x); GM(&c, Z), ()) by x := (
    match *x {
      Z => refl,
      S p => ComputedMixInd(&p),
    }
  )

  -- R3, [Close]'s fill. `TouchA` is stuck on `n`, so `ExA` closes it off and fills `c`. `c` is
  -- declared `A` (it is `x`), so its fill is the sealed program at every instance, `A := Unit`
  -- with `x := ()` included, as at the generic call: never `()` because the content happens to
  -- be `()`. The instance's fill is the generic call's at `x := ()` (the reason below)
  def TouchA (A : Type) (a : &A) (n : Nat) : Unit := match n { Z => (), S(m) => () }
  def ExA (A : Type) (x : A) (n : Nat) : Pair(A, Nat) := (let c = x; TouchA(A, &c, n); Mk(c, Z))
  reject def ExAAt (n : Nat) : Id(Pair(Unit, Nat), ExA(Unit, (), clone(n)), Mk((), Z)) := refl
  -- twin of ExAAt: a place declared `Unit` is filled with `()`, at an instance and at the
  -- generic call alike
  def TouchU (a : &Unit) (n : Nat) : Unit := match n { Z => (), S(m) => () }
  def ExU (x : Unit) (n : Nat) : Pair(Unit, Nat) := (let c = x; TouchU(&c, n); Mk(c, Z))
  def ExUAt (n : Nat) : Id(Pair(Unit, Nat), ExU((), clone(n)), Mk((), Z)) := refl
  def ExUGen (x : Unit) (n : Nat) : Id(Pair(Unit, Nat), ExU(x, clone(n)), Mk(x, Z)) := refl
}

#guard (run "DeclaredReadings" DeclaredReadings).rejectedWith [
  ("Dup", "[Read] x was moved out"),
  ("LetA", "[Read] y was moved out"),
  ("ReadMix", "[Read] u was moved out"),
  ("MixEta", "the body of MixEta has type ⊤, but the goal is Eq(⌈MixT(σ0)⌉, σ1, σ2)"),
  ("ComputedMix", "the body of ComputedMix has type ⊤, but the goal is Eq(Unit, ⌈let c1 = σ0; GM(&c1, 0)⌉, ())"),
  ("ExAAt", "the body of ExAAt has type ⊤, but the goal is Eq(Unit, ⌈let c1 = (); TouchA(Unit, &c1, σ0); c1⌉, ())")]

/-! ## [Close]'s fill at a place declared `Unit`: `()` only when the call returns data (D137)

A call that closes off fills each place it borrowed with a sealed program. When the call returns
data and the place is declared `Unit`, the fill is `()` (η at `Unit`, D80; `ExU` above). When the
call returns a borrow, the fill keeps the returned borrow's hole `loan_k` at a `Unit` place too:
`()` would leave the hole in no place, so what is written through the returned borrow would be
observed nowhere and an `Id` over two different writes through it would hold. `QU` would then
refute `Π(u : &Unit). &Nat`, as `Q` would refute `Π(n : Nat). &Nat` without D44
(`ReturnedBorrows`): safe Rust inhabits both with a leaked borrow. Until D137 the paper and RULES
said `()` in both rows; the checker has always kept the hole (docs/18, "Resolved determination").
Each rejected row has its twin. -/

ochr UnitFill uses Nats, Fixtures {
  def G5 (x : &Nat) (e : Id(Unit, *x := 0, *x := 1)) : False := e
  def H5 (x : &Nat) (e : Id(Unit, *x := 0, *x := 0)) : Unit := ()
  -- the fill of `u` keeps the hole, so the statement observes the writes through `g(&u)`: `False`
  reject def QU (g : Π(u : &Unit). &Nat) : False := (let u = (); G5(g(&u), refl))
  -- twin of QU: the true statement, through the same call, by `refl`
  def QUOk (g : Π(u : &Unit). &Nat) : Unit := (let u = (); H5(g(&u), refl))
  -- the same at two `Unit` places, at a borrow parameter declared `&Unit`, at an annotated `let`,
  -- at a `Unit` value parameter, at a type function every arm of which is `Unit`, at a field
  reject def QU2 (g : Π(u : &Unit) (v : &Unit). &Nat) : False := (let u = (); let v = (); G5(g(&u, &v), refl))
  reject def QU3 (g : Π(u : &Unit). &Nat) (u : &Unit) : False := G5(g(u), refl)
  reject def QU4 (g : Π(u : &Unit). &Nat) : False := (let u : Unit = (); G5(g(&u), refl))
  reject def QU5 (g : Π(u : &Unit). &Nat) (w : Unit) : False := (let u = w; G5(g(&u), refl))
  def UU (n : Nat) : Type := match n { Z => Unit, S(m) => Unit, }
  reject def QU6 (g : Π(u : &UU(Z)). &Nat) (w : UU(Z)) : False := (let u = w; G5(g(&u), refl))
  reject def QUp (g : Π(u : &Unit). &Nat) : False := (let p : Pair(Nat, Unit) = Mk(0, ()); G5(g(&p.1), refl))
  -- the two rows at the `Unit` place itself. A call returning data: the fill is `()`
  def QD (g : Π(u : &Unit). Nat) : Id(Unit, (let u = (); g(&u); u), ()) := refl
  -- twin of QD, a call returning a borrow: the fill, its hole filled when `r` ends, is not `()`.
  -- True (`u` has one value), and rejected: the price of keeping the hole
  reject def QB (g : Π(u : &Unit). &Nat) : Id(Unit, (let u = (); let r = g(&u); u), ()) := refl
}

#guard (run "UnitFill" UnitFill).rejectedWith [
  ("QU", "argument 2 (e) has type ⊤, expected Eq(Unit, ⌈let c1 = (); let r = σ0(&c1); *r := 0; c1⌉, ⌈let c1 = (); let r = σ0(&c1); *r := 1; c1⌉)"),
  ("QU2", "argument 2 (e) has type ⊤, expected Eq(Unit, ⌈let c1 = (); let c2 = (); let r = σ0(&c1, &c2); *r := 0; c1⌉, ⌈let c1 = (); let c2 = (); let r = σ0(&c1, &c2); *r := 1; c1⌉) ∧ Eq(Unit, ⌈let c1 = (); let c2 = (); let r = σ0(&c1, &c2); *r := 0; c2⌉, ⌈let c1 = (); let c2 = (); let r = σ0(&c1, &c2); *r := 1; c2⌉)"),
  ("QU3", "argument 2 (e) has type ⊤, expected Eq(Unit, ⌈let c1 = (); let r = σ0(&c1); *r := 0; c1⌉, ⌈let c1 = (); let r = σ0(&c1); *r := 1; c1⌉)"),
  ("QU4", "argument 2 (e) has type ⊤, expected Eq(Unit, ⌈let c1 = (); let r = σ0(&c1); *r := 0; c1⌉, ⌈let c1 = (); let r = σ0(&c1); *r := 1; c1⌉)"),
  ("QU5", "argument 2 (e) has type ⊤, expected Eq(Unit, ⌈let c1 = (); let r = σ0(&c1); *r := 0; c1⌉, ⌈let c1 = (); let r = σ0(&c1); *r := 1; c1⌉)"),
  ("QU6", "argument 2 (e) has type ⊤, expected Eq(Unit, ⌈let c1 = (); let r = σ0(&c1); *r := 0; c1⌉, ⌈let c1 = (); let r = σ0(&c1); *r := 1; c1⌉)"),
  ("QUp", "argument 2 (e) has type ⊤, expected Eq(Unit, ⌈let c1 = (); let r = σ0(&c1); *r := 0; c1⌉, ⌈let c1 = (); let r = σ0(&c1); *r := 1; c1⌉)"),
  ("QB", "the body of QB has type ⊤, but the goal is Eq(Unit, ⌈let c1 = (); let r = σ0(&c1); *r := ⌈let c1 = (); let r = σ0(&c1); *r⌉; c1⌉, ())")]


/-! ## Blocks as text (exp-block-text)

A sealed block binds what it captured, each in a cell (a place taken by `&` reached through a
borrow of its cell), and is then the match itself. A function under check that the match calls
is named by its global, never held as a cell; a block is checked at the values it captured only,
and its text says nothing about other values. The four faults the consistency proof found (docs/31
D232–D234) are pinned here: the text of `MB0e`'s block mentions `MB0e` only as the head of a call,
and the text of `NTe`'s reads the predecessor of `n` only under the cell that holds `S(σ2)`. -/

ochr BlockText uses Nats, Fixtures {
  inductive BB := TT | FF
  def MB0r (m : Nat) (n : Nat) : Nat by n := (let r = (match m { Z => Z, S(p) => match n { Z => Z, S(k) => MB0r(p, k), }, }); r)
  def NTr (n : Nat) (m : Nat) : Nat := match n { Z => Z, S(p) => (let r = (match m { Z => clone(n), S(q) => clone(p), }); r), }
  -- the texts, shown by an equation the checker cannot decide
  reject def MB0e (m : Nat) (n : Nat) : Nat by n := (let r = (match m { Z => Z, S(p) => match n { Z => Z, S(k) => MB0e(p, k), }, }); let h : Eq(Nat, clone(r), Z) = refl; r)
  reject def NTe (n : Nat) (m : Nat) : Nat := match n { Z => Z, S(p) => (let r = (match m { Z => clone(n), S(q) => clone(p), }); let h : Eq(Nat, clone(r), Z) = refl; r), }
  -- a block returning a borrow, written through, then split
  def BR (b : BB) (x : &Nat) (y : &Nat) : Nat := (let r = (match b { TT => &*x, FF => &*y, }); *r := Z; match b { TT => Z, FF => Z, })
  -- a block re-run after a later split refines what it captured; one whose arm ends stuck again
  def RR (n : Nat) : Eq(Nat, (let r = (match n { Z => Z, S(p) => clone(p), }); match n { Z => r, S(q) => Z, }), Z) := match n { Z => refl, S(q) => refl, }
  def BS (n : Nat) (m : Nat) : Nat := (let r = (match n { Z => Z, S(p) => match m { Z => Z, S(q) => S(q), }, }); match n { Z => r, S(p) => r, })
  -- two J blocks with convertible motives of different code are convertible (compared by text)
  def EqJ (a : Nat) (b : Nat) (h : Eq(Nat, a, b)) : Eq(Nat, J(Nat, a, b, λ(z : Nat) : Type => Nat, h, Z), J(Nat, a, b, λ(z : Nat) : Type => (let w = Nat; w), h, Z)) := refl
  -- two blocks with different texts are not
  reject def EqDiff (n : Nat) : Eq(Nat, (let r = (match n { Z => Z, S(p) => S(Z), }); r), (let r = (match n { Z => Z, S(p) => clone(p), }); r)) := refl
}

#guard (run "BlockText" BlockText).rejectedWith [
  ("MB0e", "the ascribed term has type ⊤, expected Eq(Nat, ⌈let m = σ0; let n = σ1; match m { Z => 0, S _ => match n { Z => 0, S _ => MB0e(m.0, n.0) } }⌉, 0)"),
  ("NTe", "the ascribed term has type ⊤, expected Eq(Nat, ⌈let n = S(σ2); let m = σ1; match m { Z => clone(n), S _ => clone(n.0) }⌉, 0)"),
  ("EqDiff", "the body of EqDiff has type ⊤, but the goal is Eq(Nat, ⌈let n = σ0; match n { Z => 0, S _ => (fix _ (n : Nat) : Nat := S(n))(0) }⌉, ⌈let n = σ0; match n { Z => 0, S _ => clone(n.0) }⌉)")]
