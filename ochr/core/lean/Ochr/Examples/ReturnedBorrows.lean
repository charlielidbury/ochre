import Ochr.Examples.Nat
import Ochr.Examples.Fixtures
import Ochr.Examples.Word
import Ochr.Examples.List

/-! # 3. Functions that return a borrow

A function may return a borrow into one of its borrow arguments, like Rust's
`fn tail(x: &mut Nat) -> &mut Nat`. `TailM(x)` returns a borrow of the `Z` at the bottom of
`*x`, and writing through it changes `*x`. When such a call gets stuck on an abstract
number, both what it returns and what it leaves in `*x` become sealed programs, with a
hole where the returned borrow's contents will go (RULES §3 [Close], its `&T` row).

A returned borrow always comes from a borrow argument: a function type that returns `&T`
must take a borrow (D44). This is Rust's lifetime-elision rule; Ochr has no `'static`
borrows.

Defined in RULES §1 (D44), §3 [Close] and §7. -/

open Ochr.Test

ochr ReturnedBorrows uses Nats, Fixtures {
  -- `Nats`' `TailM(x)` returns a borrow of the final `Z` of `*x`. Addition by writing
  -- through it ...
  def AddM' (x : &Nat) (y : Nat) : Unit := (
    let t = TailM(x);
    *t := y
  )

  -- ... is the same as `AddM`, in its result and in what it leaves in `*x`. The proof is the
  -- same bare recursion as `AddMZero`'s.
  def AddMEq (x : &Nat) (y : Nat) : Id(Unit, AddM(x, y), AddM'(x, y)) by x := (
    match *x {
      Z => refl,
      S p => AddMEq(&p, y),
    }
  )

  def AddMEqOwned (x : Nat) : Id(Unit, AddM(&x, 0), AddM'(&x, 0)) := AddMEq(&x, 0)

  -- Reading through the returned borrow, and not using it at all.
  def AddM1 (x : &Nat) : Id(Unit, AddM(x, 1), let t = TailM(x); *t := S(*t)) by x := (
    match *x {
      Z => refl,
      S p => AddM1(&p),
    }
  )

  def TailNoop (x : &Nat) : Id(Unit, let t = TailM(&*x); (), ()) by x := (
    match *x {
      Z => refl,
      S p => TailNoop(&p),
    }
  )

  -- A returned borrow into a local would outlive the local.
  reject def DanglingTail (n : Nat) : &Nat := (
    let z = n;
    TailM(&z)
  )

  -- A function type that returns a borrow must have a borrow parameter for it to come from.
  def Keep (x : &Nat) (n : Nat) : &Nat := x
  def KeepT : Type := Π(x : &Nat) (n : Nat). &Nat
  reject def LeakT : Type := Π(n : Nat). &Nat
  -- twin of LeakT: a borrow parameter added, which the returned borrow can come from
  def LeakTOk : Type := Π(n : Nat) (x : &Nat). &Nat

  -- Every function of type `Π(x : &Nat). &Nat` returns a borrow into `*x`, so writing
  -- different numbers through its result leaves different numbers in `*x`.
  def L (x : &Nat) (e : Id(Unit, *x := 0, *x := 1)) : False := e

  def Inj (g : Π(x : &Nat). &Nat) (x : &Nat) (e : Id(Unit, let r = g(x); *r := 0, let r = g(x); *r := 1)) :
      False := (
    let r = g(x);
    L(r, e)
  )

  -- ## What goes wrong without these rules
  -- Without D44 a function type could return a borrow that comes from nowhere. Closing off
  -- `g(5)` would give a borrow whose hole is in no place at all, so an `Id` about writes
  -- through it would observe nothing and be trivially true. `Q` would then refute
  -- `Π(n : Nat). &Nat`, which Rust inhabits with `Box::leak`: given such a function as an
  -- opaque `leak`, `Boom` is a closed proof of `Empty`.
  def M (n : Nat) : Type := (
    match n {
      Z => Unit,
      S _ => Empty,
    }
  )

  def P (x : &Nat) (e : Id(Unit, *x := 0, *x := 1)) : Empty := J(Nat, 0, 1, M, e, ())
  reject def Q (g : Π(n : Nat). &Nat) : Empty := P(g(5), refl)
  -- twin of Q: `g` takes a borrow, and the hypothesis is the `Id` about writes through its result, not `refl`
  def QOk (g : Π(x : &Nat). &Nat) (x : &Nat) (e : Id(Unit, let r = g(x); *r := 0, let r = g(x); *r := 1)) : Empty := (
    let r = g(x);
    P(r, e)
  )
  reject def Boom (leak : Π(n : Nat). &Nat) : Empty := Q(leak)
  -- twin of Boom: `leak` takes a borrow, so it is a borrow into `*x` and the contradiction needs the `Id` hypothesis
  def BoomOk (leak : Π(x : &Nat). &Nat) (x : &Nat) (e : Id(Unit, let r = leak(x); *r := 0, let r = leak(x); *r := 1)) : Empty :=
    QOk(leak, x, e)
  -- the same with the library's `False`
  def PF (x : &Nat) (e : Id(Unit, *x := 0, *x := 1)) : False := e
  reject def QF (g : Π(n : Nat). &Nat) : False := PF(g(5), refl)
  -- twin of QF: `g` takes a borrow, and the hypothesis is the `Id` about writes through its result, not `refl`
  def QFOk (g : Π(x : &Nat). &Nat) (x : &Nat) (e : Id(Unit, let r = g(x); *r := 0, let r = g(x); *r := 1)) : False := (
    let r = g(x);
    PF(r, e)
  )

  -- Matching on a place ends every borrow whose hole is inside the sealed program the
  -- place holds (D29). Here `*x` holds `TailM`'s sealed program, with the hole of `t` inside
  -- it, so `match *x` ends `t`, as the concrete run does when `*x` is `Z`. Without that
  --, `Bad` is accepted, and `Main(0)` writes through an ended
  -- borrow when run.
  reject def Bad (x : &Nat) : Unit := (
    let t = TailM(&*x);
    match *x {
      Z => (
        *t := S(Z);
        let h : Id(Nat, clone(*x), Z) = refl;
        ()
      ),
      S _ => (),
    }
  )

  -- twin of Bad: `t` is not written through after `match *x` has ended it
  def BadOk (x : &Nat) : Unit := (
    let t = TailM(&*x);
    match *x {
      Z => (
        let h : Id(Nat, clone(*x), Z) = refl;
        ()
      ),
      S _ => (),
    }
  )

  reject def Main (n : Nat) : Nat := (
    let c = n;
    Bad(&c);
    c
  )

  -- twin of Main: calls `BadOk`
  def MainOk (n : Nat) : Nat := (
    let c = n;
    BadOk(&c);
    c
  )

  reject def Main0 : Nat := Main(0)
}


/-! ## Moving a borrow down: reborrow and replace (D67)

`x := &(*x).f` moves the cursor `x` down into what it borrows. Before an assignment to `x`,
[Access] ends only the loans in the part of `content(x)` that `x` owns. The new borrow's loan
sits *behind* the borrow `x` held, so it survives: [Drop] of the old borrow carries it back to
its owner, where it stays live. Rust allows the same, since a reborrow of `*x` lives as long
as the reference `x` held, not the variable `x`. Reads, moves and borrows of `x` still end every
loan inside, so a borrow passed to a call carries no live loan ([Close]'s precondition). -/

ochr Reborrows uses WordType, Lists, Fixtures {
  -- meta-order's `Trav`: step down one `S`, then write there
  def Trav (x : &Nat) : Unit := (
    match *x {
      Z => (),
      S p => (
        x := &p;
        *x := 0
      ),
    }
  )
  def TravRun : Id(Nat, let a = 5; Trav(&a); a, 1) := refl
  reject def TravRunWrong : Id(Nat, let a = 5; Trav(&a); a, 0) := refl

  -- a list cursor walks to the last node and writes there
  def WriteLast (x : &List(Word)) (v : Word) : Unit by x := (
    match *x {
      Nil => (),
      Cons(h, t) => match t {
        Nil => h := v,
        Cons(h2, t2) => (
          x := &t;
          WriteLast(x, v)
        ),
      },
    }
  )
  def WriteLastRun : Id(List(Word), 
      let l = Cons(Zero, Cons(Succ(Zero), Cons(Succ(Succ(Zero)), Nil)));
      WriteLast(&l, Zero);
      l, Cons(Zero, Cons(Succ(Zero), Cons(Zero, Nil)))) := refl

  -- Rust allows this: `y` reborrows behind `x`'s borrow, and `x` is then pointed elsewhere
  def ReplaceKeep (x : &Nat) (other : &Nat) : Unit := (
    match *x {
      Z => (),
      S p => (
        let y = &p;
        x := other;
        *y := 0
      ),
    }
  )
  def ReplaceKeepRun : Id(Nat × Nat, let a = 3; let b = 7; ReplaceKeep(&a, &b); (a, b), (1, 7)) := refl

  -- a neutral behind the held borrow travels back with it: which of `*x` and `*b` the cursor
  -- ends up at is not known at an abstract `n`
  def PickMove (n : Nat) (x : &Nat) (b : &Nat) : Unit := (
    x := Pick(n, &*x, &*b);
    *x := 0
  )
  def PickMoveRun0 : Id(Nat × Nat, let a = 3; let c = 7; PickMove(0, &a, &c); (a, c), (0, 7)) := refl
  def PickMoveRun1 : Id(Nat × Nat, let a = 3; let c = 7; PickMove(1, &a, &c); (a, c), (3, 0)) := refl

  -- still rejected: `x` used after it was moved
  reject def UseMoved (x : &Nat) : Unit := (
    match *x {
      Z => (),
      S p => (
        x := &p;
        let z = x;
        *x := 0
      ),
    }
  )
  -- still rejected: `x` passed to a call while a reborrow behind it is still wanted (reading
  -- `x` ends every loan inside it, conservatively)
  def Nop (x : &Nat) : Unit := ()
  reject def PassWhileReborrowed (x : &Nat) : Unit := (
    match *x {
      Z => (),
      S p => (
        let y = &p;
        Nop(x);
        *y := 0
      ),
    }
  )

  -- twin of PassWhileReborrowed: `x` is not passed to a call while `y` is still wanted
  def PassWhileReborrowedOk (x : &Nat) : Unit := (
    match *x {
      Z => (),
      S p => (
        let y = &p;
        *y := 0
      ),
    }
  )
}

#guard (run "Reborrows" Reborrows).rejectedWith [
  ("TravRunWrong", "the body of TravRunWrong has type ⊤, but the goal is False"),
  ("UseMoved", "no such place *x: its path does not exist in ⊥"),
  ("PassWhileReborrowed", "no such place *y: its path does not exist in ⊥")]

/-! ## Borrow ends are static

When a borrow ends is decided as Rust decides it, from the program and the declared types, never
from where a run leaves it pointing, so a definition's generic call and every closed call of it
have the same borrows live at every point. A call that returns a borrow lends it every place its
borrow arguments lend, whether the call runs or closes off (rule 1: `Fixtures`' `Pick(Z, &a, &b)`
lends `a` and `b`, as Rust's `fn pick<'a>(n, x: &'a mut T, y: &'a mut T) -> &'a mut T` does). A
match that is not in tail position ends and lends as the stuck block it closes off as on an
unknown scrutinee, whichever arm runs (rule 2), and so does `J`'s transported term. Before this,
the generic call ended a borrow wherever a stuck call's hole or a stuck block's capture said it
might, and a closed call only where its run said it did, so an accepted definition could fail
when called: `EI`, `EJ`, `EIB`, `EJB`, `EJJ` and `GJI` below were accepted and their closed calls
rejected. -/

ochr StaticEnds uses Nats, Fixtures {
  def PickP (n : Nat) (x : &(Nat × Nat)) (y : &(Nat × Nat)) : &(Nat × Nat) := (
    match n { Z => x, S _ => y }
  )
  def MN (z : Nat) : Type := Nat

  -- A stuck call's hole: at an unknown `n`, reading `a` ends `r`, so the `Id`'s side ends
  -- nothing; at `n = 1` it ends `r` too, as `a` is lent to it whatever `n` is
  def EI (n : Nat) (a : Nat) (b : Nat) : Unit := (
    let r = Pick(n, &a, &b);
    let a1 = a;
    let T = Id(Unit, (let z = clone(b); ()), ());
    ()
  )
  -- ... and the join of a match on a known constructor drops nothing through the dead `r`
  -- (its arm `Z` does not run), at an unknown `n` and at every `n`
  def EJ (n : Nat) (a : Nat × Nat) (b : Nat × Nat) : Nat × Nat := (
    let r = PickP(n, &a, &b);
    let a1 = a;
    let k = S(Z);
    match k { Z => (let z = (*r).0; Z), S m => Z };
    let bb = b;
    bb
  )
  -- the arm that runs ends the borrow (reading `a`), before the join drops through it
  def EJ2 (n : Nat) (a : Nat × Nat) (b : Nat × Nat) : Nat × Nat := (
    let r = PickP(n, &a, &b);
    let k = S(Z);
    match k { Z => (let z = (*r).0; Z), S m => (let a2 = clone(a); Z) };
    let bb = b;
    bb
  )
  -- A stuck block's captures: the block over `k` reads `a`, ending `r`; the arm that runs at
  -- `k = 1` does not read it, but the match ends what the block would
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
  -- The same through `J`: at an unknown `m` the `J` closes off as a block that reads `a`; at
  -- `m = 0` it is its transported term, which ends what the block would
  def GJI (m : Nat) (k : Nat) (h : Eq(Nat, m, Z)) (a : Nat) : Unit := (
    let r = &a;
    let v = J(Nat, m, Z, MN, h, (match k { Z => (let z = clone(a); Z), S _ => Z }));
    let T = Id(Unit, (let z = clone(a); ()), ());
    ()
  )
  def EJJ (m : Nat) (h : Eq(Nat, m, Z)) (k : Nat) (a : Nat × Nat) : Nat × Nat := (
    let r = &a;
    let v = J(Nat, m, Z, MN, h, (match k { Z => (let z = clone(a); Z), S _ => Z }));
    let j = S(Z);
    match j { Z => (let z = (*r).0; Z), S _ => Z };
    let aa = a;
    aa
  )
  -- A computed call lends every place its borrow arguments lend: `Pick(Z, &a, &b)` points
  -- into `a`, and reading `b` ends it, as in Rust
  reject def PickZ (a : Nat) (b : Nat) : Unit := (
    let r = Pick(Z, &a, &b);
    let z = clone(b);
    *r := 5;
    ()
  )
  -- twin of PickZ: `b` is read after the write through `r`
  def PickZOk (a : Nat) (b : Nat) : Unit := (
    let r = Pick(Z, &a, &b);
    *r := 5;
    let z = clone(b);
    ()
  )
  -- A stuck block's by-move capture of `a.0` reaches `a`'s content, which holds `r`'s hole,
  -- by ending `r`, as the arm that moves it does. Before, it generalised the content and lost
  -- the hole: `G1` was accepted and `G1(0, 1, (1, 2), (3, 4))` rejected
  reject def G1 (n : Nat) (k : Nat) (a : Nat × Nat) (b : Nat × Nat) : Unit := (
    let r = PickP(n, &a, &b);
    match k { Z => (let z = a.0; ()), S _ => () };
    *r := (Z, Z);
    ()
  )
  -- twin of G1: the write through `r` comes before the match
  def G1Ok (n : Nat) (k : Nat) (a : Nat × Nat) (b : Nat × Nat) : Unit := (
    let r = PickP(n, &a, &b);
    *r := (Z, Z);
    match k { Z => (let z = a.0; ()), S _ => () };
    ()
  )
  -- A match in tail position is split at the generic call, not closed off, so the arm that
  -- runs uses `r` though the other ends it (Rust accepts this too)
  def G4 (k : Nat) (a : Nat) : Unit := (
    let r = &a;
    match k { Z => (a := 1; ()), S _ => (*r := 2; ()) }
  )
  -- not in tail position, the match ends what its block would: `a`'s borrower `r`
  reject def G5 (k : Nat) (a : Nat) : Unit := (
    let r = &a;
    match k { Z => (a := 1; ()), S _ => (*r := 2; ()) };
    ()
  )
  -- A match that returns a borrow lends it what its block's result would be: `a` and `b`
  reject def G3 (k : Nat) (a : Nat) (b : Nat) : Unit := (
    let r = match k { Z => &a, S _ => &b };
    let z = clone(a);
    *r := 5;
    ()
  )
  -- twin of G3: neither lender is read before the write
  def G3Ok (k : Nat) (a : Nat) (b : Nat) : Unit := (
    let r = match k { Z => &a, S _ => &b };
    *r := 5;
    let z = clone(a);
    ()
  )
  -- A stuck block accesses all its captures before it takes any, as a direct run's entry does:
  -- here `c`'s access ends `b`, through which arm `S` reads. Taking the read of `*b` first would
  -- let the block's arm read a copy that the direct run at `k = 1`, which reads `*b` after the
  -- entry, cannot (on main, without the entry, both were accepted; Rust accepts `EK`, its arms
  -- being separate paths)
  reject def EK (k : Nat) (a : Nat) : Unit := (
    let b = &a;
    let c = 5;
    b := &c;
    match k { Z => (c := 1; ()), S _ => (let z = clone(*b); ()) };
    ()
  )
  -- ... at a known constructor too
  reject def G3K (a : Nat) (b : Nat) : Unit := (
    let k = S(Z);
    let r = match k { Z => &a, S _ => &b };
    let z = clone(a);
    *r := 5;
    ()
  )
}

-- Closed calls of the definitions above: each is accepted, as its definition is
ochr StaticEndsRuns uses Nats, Fixtures, StaticEnds {
  def EIRun : Unit := EI(1, 2, 3)
  def EIRun0 : Unit := EI(0, 2, 3)
  def EJRun : Nat × Nat := EJ(1, (2, 3), (4, 5))
  def EJRun0 : Nat × Nat := EJ(0, (2, 3), (4, 5))
  def EJ2Run : Nat × Nat := EJ2(1, (2, 3), (4, 5))
  def EJ2Run0 : Nat × Nat := EJ2(0, (2, 3), (4, 5))
  def EIBRun : Unit := EIB(1, 0)
  def EJBRun : Nat × Nat := EJB(1, (1, 2))
  def GJIRun : Unit := GJI(0, 1, refl, 5)
  def EJJRun : Nat × Nat := EJJ(0, refl, 1, (1, 2))
  def G1OkRun : Unit := G1Ok(0, 1, (1, 2), (3, 4))
  def G4Run : Unit := G4(1, 0)
  def G4Run0 : Unit := G4(0, 0)
  def G3OkRun : Unit := G3Ok(1, 0, 0)
}

#guard (run "StaticEnds" StaticEnds).rejectedWith [
  ("PickZ", "no such place *r: its path does not exist in ⊥"),
  ("G1", "no such place *r: its path does not exist in ⊥"),
  ("G5", "no such place *r: its path does not exist in ⊥"),
  ("G3", "no such place *r: its path does not exist in ⊥"),
  ("G3K", "no such place *r: its path does not exist in ⊥"),
  ("EK", "no such place *b: its path does not exist in ⊥")]
