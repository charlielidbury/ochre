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
  -- the closed call of the rejected G1 (accepted on main, where G1 was, and rejected there by
  -- its run: the fault)
  reject def G1Run : Unit := G1(0, 1, (1, 2), (3, 4))
  def G4Run : Unit := G4(1, 0)
  def G4Run0 : Unit := G4(0, 0)
  def G3OkRun : Unit := G3Ok(1, 0, 0)
}

#guard (run "StaticEndsRuns" StaticEndsRuns).rejectedWith [("G1Run", "unknown constant G1")]

#guard (run "StaticEnds" StaticEnds).rejectedWith [
  ("PickZ", "no such place *r: its path does not exist in ⊥"),
  ("G1", "no such place *r: its path does not exist in ⊥"),
  ("G5", "no such place *r: its path does not exist in ⊥"),
  ("G3", "no such place *r: its path does not exist in ⊥"),
  ("G3K", "no such place *r: its path does not exist in ⊥"),
  ("EK", "no such place *b: its path does not exist in ⊥")]

/-! ## A stuck block's arms are checked after its entry (D91)

A stuck block computes its captures from syntax and declared types, accesses them all, and only
then checks its arms, from the state a direct run's arm starts from (D90's entry). Before D91 it
checked its arms first, in a state where the borrows its entry would end were still live, so the
generic call was stricter inside an arm than every instance: `IA`, `JA` and `IAPick` were
rejected by [Id-typestate]'s no-ending clause (the `Id`'s side ends `r`), while at each instance
the entry had already ended `r`. -/

ochr BlockEntry uses Nats, Fixtures, StaticEnds {
  -- an `Id` side in an arm reads `a`, whose borrower `r` the block's entry has ended
  def IA (k : Nat) (a : Nat) : Unit := (
    let r = &a;
    match k { Z => (let T = Id(Unit, (let z = clone(a); ()), ()); ()), S _ => () };
    ()
  )
  -- twin of IA: `r` is used after the match, which the entry has ended
  reject def IAUse (k : Nat) (a : Nat) : Unit := (
    let r = &a;
    match k { Z => (let T = Id(Unit, (let z = clone(a); ()), ()); ()), S _ => () };
    *r := 1;
    ()
  )
  -- the `J` form: [T-J-stuck]'s block
  def JA (m : Nat) (h : Eq(Nat, m, Z)) (a : Nat) : Nat := (
    let r = &a;
    J(Nat, m, Z, MN, h, (let T = Id(Unit, (let z = clone(a); ()), ()); Z))
  )
  -- an arm that uses a borrow the entry ends is rejected, now inside the arm
  reject def ArmUsesEnded (k : Nat) (a : Nat) : Unit := (
    let r = &a;
    match k { Z => (a := 1; ()), S _ => (*r := 2; ()) };
    ()
  )
  -- through a returned borrow: the entry reads `b`, a place lent to `r`
  def IAPick (n : Nat) (k : Nat) (a : Nat) (b : Nat) : Unit := (
    let r = Pick(n, &a, &b);
    match k { Z => (let T = Id(Unit, (let z = clone(b); ()), ()); ()), S _ => () };
    ()
  )
  -- the entry η-refines the scrutinee itself (its one arm moves a field of it), and the arm is
  -- checked at that refinement
  def EtaScrut (x : Nat × Nat) : Nat := (let v = match x { Mk(a, b) => a, }; v)
  def EtaScrut2 (x : Nat × Nat) : Nat × Nat := (let v = match x { Mk(a, b) => (b, a), }; v)
}

-- Closed calls: each is accepted, as its definition is
ochr BlockEntryRuns uses Nats, Fixtures, StaticEnds, BlockEntry {
  def IARun : Unit := IA(0, 5)
  def IARun1 : Unit := IA(1, 5)
  def JARun : Nat := JA(0, refl, 5)
  def IAPickRun : Unit := IAPick(1, 0, 2, 3)
  def EtaScrutRun : Id(Nat, EtaScrut((1, 2)), 1) := refl
  def EtaScrut2Run : Id(Nat × Nat, EtaScrut2((1, 2)), (2, 1)) := refl
}

#guard (run "BlockEntry" BlockEntry).rejectedWith [
  ("IAUse", "no such place *r: its path does not exist in ⊥"),
  ("ArmUsesEnded", "no such place *r: its path does not exist in ⊥")]

/-! ## A match on a value of a one-constructor type never closes off (D93)

A projection `x.i` (D81), a destructuring `let` and an explicit one-arm match are matches on a
value of a type with one constructor. In a typed run an unknown scrutinee is refined in place to
that constructor (a sealed one is generalised first), and the one arm runs, as at an instance:
such a match is never a stuck block. With one arm there is no other path to agree with, so it has
no entry (D90's rule 2) and no join (D84) on any path. Before D93 the generic call closed it off
when it was not in tail position, and its entry read the whole value: `&x.1; x.0` ended the
borrow of `x.1` (D90's known gap F4: `F1`–`F4`, which Rust accepts), and `clone(x.0)`'s join
counted the clone's read as a move (`CL`, `CLrun`: `x` partly moved afterwards). A stuck block
whose arm borrows a field of a captured place reached an internal error ("stuck escaped to the
top"): the block's call took `&c.0` at an unrefined `c`. A block's captures are now refined in
place before its arms (`SB` and its variants). -/

ochr OneConstructor uses Nats, Fixtures, StaticEnds {
  def Whole (x : &(Nat × Nat)) : &(Nat × Nat) := x
  def IdN (x : &Nat) : &Nat := x
  -- disjoint fields (D90's gap F4; Rust accepts all four)
  def F1 (x : Nat × Nat) : Unit := (let r = &x.1; let y = x.0; *r := Z; ())
  def F2 (x : Nat × Nat) : Unit := (let r = &x.1; let y = clone(x.0); *r := Z; ())
  def F3 (x : &(Nat × Nat)) : Unit := (let r = &(*x).1; let y = clone((*x).0); *r := Z; ())
  def F4 : Unit := (let x = (Z, Z); let r = &x.1; let y = clone(x.0); *r := Z; ())
  -- two borrows of disjoint fields, live together (Rust accepts)
  def TwoBorrows (c : Nat × Nat) : Unit := (let a = &c.0; let b = &c.1; *a := Z; *b := Z; ())
  def TwoBorrowsRun : Unit := (let c = (Z, Z); let a = &c.0; let b = &c.1; *a := Z; *b := Z; ())
  -- control: the same field twice; the second borrow ends the first (Rust rejects too)
  reject def SameField (c : Nat × Nat) : Unit := (let a = &c.0; let b = &c.0; *a := Z; *b := Z; ())
  -- `clone` of a projection copies, and leaves the value whole (CloneProj)
  def CL : Nat × Nat := (let x = (Z, Z); let y = clone(x.0); x)
  def CLg (x : Nat × Nat) : Nat × Nat := (let y = clone(x.0); x)
  -- control: a read of a projection moves the field, so the value is partly moved
  reject def MoveProj (x : Nat × Nat) : Nat × Nat := (let y = x.0; x)
  -- a stuck block whose arm borrows a field of a captured place (an internal error before)
  def SB (k : Nat) (c : Nat × Nat) : Nat := (match k { Z => (let t = &c.0; ()), S _ => () }; 0)
  def SBRet1 (k : Nat) (c : Nat × Nat) : Nat := (let s = match k { Z => &c.0, S _ => &c.0 }; 0)
  def SBRet2 (k : Nat) (c : Nat × Nat) : Nat := (let s = match k { Z => &c.0, S _ => &c.1 }; 0)
  def SBRetMix (k : Nat) (c : Nat × Nat) (d : Nat) : Nat := (let s = match k { Z => &c.0, S _ => &d }; 0)
  def SBDeref (k : Nat) (c : Nat × Nat) : Nat := (let r = &c; let s = match k { Z => &(*r).0, S _ => &(*r).1 }; 0)
  def SBParam (k : Nat) (r : &(Nat × Nat)) : Nat := (let s = match k { Z => &(*r).0, S _ => &(*r).1 }; 0)
  def SBInBlock (k : Nat) (c : Nat × Nat) : Nat := (let s = (let r = Whole(&c); match k { Z => &(*r).0, S _ => &(*r).1 }); 0)
  -- ... and through `J`'s transported term at an unknown endpoint ([T-J-stuck]'s block)
  def SJ (m : Nat) (h : Eq(Nat, m, Z)) (c : Nat × Nat) : Nat × Nat := (
    let r = Whole(&c);
    let v = J(Nat, m, Z, MN, h, (let t = IdN(&(*r).0); *t := 1; Z));
    let d = c; d)
  -- a captured field under a fill over a live borrow: the block's entry ends the borrow first
  -- (D90), then the capture is refined (a fill is never generalised with its hole, D90's `G1`)
  def SFB (n : Nat) (k : Nat) (a : Nat × Nat) (b : Nat × Nat) : Unit := (
    let r = PickP(n, &a, &b); match k { Z => (let t = &a.0; ()), S _ => () }; ())
  reject def SFBUse (n : Nat) (k : Nat) (a : Nat × Nat) (b : Nat × Nat) : Unit := (
    let r = PickP(n, &a, &b); match k { Z => (let t = &a.0; ()), S _ => () }; *r := (Z, Z); ())
  -- a field of the place a returned borrow points to, borrowed in a block's arm
  def SFR (n : Nat) (k : Nat) (a : Nat × Nat) (b : Nat × Nat) : Unit := (
    let r = PickP(n, &a, &b); match k { Z => (let t = &(*r).0; ()), S _ => () }; *r := (Z, Z); ())
  -- the borrow a block returns of one field is still live after it, the other field free
  def SBUse (k : Nat) (c : Nat × Nat) : Nat × Nat := (let s = match k { Z => &c.0, S _ => &c.0 }; *s := 1; let d = c; d)
  reject def SBUseAfter (k : Nat) (c : Nat × Nat) : Nat × Nat := (let s = match k { Z => &c.0, S _ => &c.0 }; let d = c; *s := 1; d)
}

ochr OneConstructorRuns uses Nats, Fixtures, StaticEnds, OneConstructor {
  def F1Run : Unit := F1((Z, Z))
  def F2Run : Unit := F2((Z, Z))
  def F3Run : Unit := (let x = (Z, Z); F3(&x))
  def TwoBorrowsCall : Unit := TwoBorrows((Z, Z))
  def CLrun : Nat × Nat := CLg((Z, Z))
  def SBRun : Nat := SB(0, (Z, Z))
  def SBRet2Run : Nat := SBRet2(1, (Z, Z))
  def SBParamRun : Nat := (let c = (Z, Z); SBParam(0, &c))
  def SJRun : Nat × Nat := SJ(0, refl, (Z, Z))
  def SBUseRun : Nat × Nat := SBUse(1, (Z, Z))
  def SFBRun : Unit := SFB(0, 0, (Z, Z), (Z, Z))
  def SFRRun : Unit := SFR(0, 0, (Z, Z), (Z, Z))
  -- `SFBUse` at known values: the match on `k` runs directly, its entry ends `r` as the block's did
  reject def SFBUseRun : Unit := (
    let a = (Z, Z); let b = (Z, Z); let r = PickP(0, &a, &b); let k = 0;
    match k { Z => (let t = &a.0; ()), S _ => () }; *r := (Z, Z); ())
}

#guard (run "OneConstructor" OneConstructor).rejectedWith [
  ("SameField", "no such place *a"),
  ("MoveProj", "[Read] x was partly moved out (D53)"),
  ("SBUseAfter", "no such place *s"),
  ("SFBUse", "no such place *r")]

#guard (run "OneConstructorRuns" OneConstructorRuns).rejectedWith [
  ("SFBUseRun", "no such place *r")]

/-! ## The join's places exist, or the definition is rejected (D94)

A match on a known constructor runs one arm; the others are read for their moves (D84,
`Decide.jdMoves`) but never checked, so a place there can be ill-typed: a field its constructor
does not have (`(c.0).5`), or `*` of something that is not a borrow. Before D94 the join re-rooted
such a place to its longest existing prefix and dropped that whole (`c.0`), so `BadIdx` was
accepted and `BadIdxRead` rejected for reading the dropped `c.0`. The join's place is now dropped
when it exists, whatever made it exist; nothing is dropped when its longest existing prefix holds
`⊥` or `⋆`; and otherwise the definition is rejected where the match is, naming the place (found
by the meaning spine, docs/31 D41: `Regress/UnrunArmPlace.lean`, `ReRootExists.lean`). Since D101
a move through `*` of a place not declared a borrow is rejected before any run, from declared
types (`Decide.jdGrain`), so `BadDerefRead` is rejected statically. -/

ochr JoinPlaces uses Nats, Lists {
  inductive In := MkIn(a : List(Nat), b : List(Nat))
  inductive Out := MkOut(i : In, z : List(Nat))
  def Whole (x : &Out) : &Out := x
  -- an arm that is not run moves a field `In` does not have
  reject def BadIdx (xs : List(Nat)) (ys : List(Nat)) (zs : List(Nat)) : Unit := (
    let k = Z; let c = MkOut(MkIn(xs, ys), zs);
    match k { Z => (), S m => (let a = (c.0).5; ()) }; ())
  reject def BadIdxRead (xs : List(Nat)) (ys : List(Nat)) (zs : List(Nat)) : List(Nat) := (
    let k = Z; let c = MkOut(MkIn(xs, ys), zs);
    match k { Z => (), S m => (let a = (c.0).5; ()) }; (c.0).1)
  -- ... and `*` of a place that is not a borrow
  reject def BadDerefRead (xs : List(Nat)) (ys : List(Nat)) (zs : List(Nat)) : List(Nat) := (
    let k = Z; let c = MkOut(MkIn(xs, ys), zs);
    match k { Z => (), S m => (let a = (*(c.0)).0; ()) }; (c.0).1)
  -- control: a well-typed move of `(c.0).0` drops only it
  def GoodIdxRead (xs : List(Nat)) (ys : List(Nat)) (zs : List(Nat)) : List(Nat) := (
    let k = Z; let c = MkOut(MkIn(xs, ys), zs);
    match k { Z => (), S m => (let a = (c.0).0; ()) }; (c.0).1)
  -- at an unknown: the join's place through refined unknowns
  def GoodIdxGen (k : Nat) (c : Out) : List(Nat) := (match k { Z => (), S m => (let a = (c.0).0; ()) }; (c.0).1)
  -- a place under a value lent whole, in tail position (no entry): the join's access ends the
  -- lending, and the place itself is dropped (the ReRootExists shape; not observable here, since
  -- nothing follows the join)
  def LentTail (xs : List(Nat)) (ys : List(Nat)) (zs : List(Nat)) : Unit := (
    let k = Z; let c = MkOut(MkIn(xs, ys), zs); let rr = Whole(&c);
    match k { Z => (), S m => (let a = (c.0).0; ()) })
  -- the arm that lends `c` uses it whole: the join moves `c` whole (D84's grain)
  reject def LentRead (xs : List(Nat)) (ys : List(Nat)) (zs : List(Nat)) (us : List(Nat)) (vs : List(Nat)) (ws : List(Nat)) : List(Nat) := (
    let k = Z; let c = MkOut(MkIn(xs, ys), zs); let e = MkOut(MkIn(us, vs), ws); let rr = Whole(&e);
    match k { Z => (rr := Whole(&c); ()), S m => (let a = (c.0).0; ()) };
    (c.0).1)
  def NotLentRead (xs : List(Nat)) (ys : List(Nat)) (zs : List(Nat)) (us : List(Nat)) (vs : List(Nat)) (ws : List(Nat)) : List(Nat) := (
    let k = Z; let c = MkOut(MkIn(xs, ys), zs); let e = MkOut(MkIn(us, vs), ws); let rr = Whole(&e);
    match k { Z => (rr := Whole(&e); ()), S m => (let a = (c.0).0; ()) };
    (c.0).1)
}

#guard (run "JoinPlaces" JoinPlaces).rejectedWith [
  ("BadIdx", "[Join] an arm of the match moves c.0.5, which does not exist: c.0 holds a constructor value without that field"),
  ("BadIdxRead", "[Join] an arm of the match moves c.0.5, which does not exist: c.0 holds a constructor value without that field"),
  ("BadDerefRead", "[Join] an arm of the match moves a place through * of a place not declared a borrow"),
  ("LentRead", "[Match] on c, which was moved out")]

/-! ### A move through `*` in an arm that is not run (D101)

The join's moves through `*` must go through a place declared a borrow (`&T`), decided from
declared types before any run, as Rust type-checks every arm. `*h` of a proof (`DP1`) and of a
proof field (`DP2` to `DP4`, the last two under a place lent to a returned borrow, where the
checker read through the borrow's mark and the model could not follow), or of a number
(`DData`), in an arm the run never takes, used to be accepted or caught only at run time. A
borrow read through a match (`ViaMatchLive`), returned by a call (`RetDead`) or a parameter
(`ParamDead`) is declared one. Moving through it in a dead arm is a move like any other: unless
it is refilled (`ParamDeadRefill`) or copied (`ParamDeadClone`), the borrow ends with its content
moved out ([D53]). A borrow variable moved earlier (`MovedBefore`, `MovedByArm`) and a reborrow
(`RebDead`) are still fine. A type function cannot compute a borrow type (`&` is only ever
written, D48), so no place is a borrow only through one. -/

ochr JoinDeref uses Nats {
  reject def DP1 (h : Eq(Nat, Z, Z)) : Unit := (
    let k = Z;
    match k { Z => (), S m => (let a = *h; ()) })
  inductive Tg := MkTg(n : Nat, h : Eq(Nat, 0, 0))
  def Get (s : &Tg) : &Nat := &(*s).0
  reject def DP2 (x : Tg) : Unit := (
    let r = Get(&x);
    let k = Z;
    match k { Z => (), S m => (let a = *(x.1); ()) })
  reject def DP3 : Unit := (
    let x = MkTg(0, refl);
    let r = Get(&x);
    let k = Z;
    match k { Z => (), S m => (let a = *(x.1); ()) })
  reject def DP4 (n : Nat) : Unit := (
    let x = MkTg(n, refl);
    let r = Get(&x);
    let k = Z;
    match k { Z => (), S m => (let a = *(x.1); ()) })
  reject def DData (x : Nat) : Unit := (let k = Z; match k { Z => (), S m => (let a = *x; ()) })
  def IdB (x : &Nat) : &Nat := x
  def Take (x : &Nat) : Unit := ()
  def ViaMatchLive (b : Nat) (x : Nat) (y : Nat) : Nat := (let r = match b { Z => &x, S _ => &y }; *r := 5; 0)
  def ViaMatchDead (b : Nat) (x : Nat) (y : Nat) : Unit := (let r = match b { Z => &x, S _ => &y }; let k = Z; match k { Z => (), S m => (let a = clone(*r); ()) })
  def RetDead (x : Nat) : Unit := (let r = IdB(&x); let k = Z; match k { Z => (), S m => (let a = clone(*r); ()) })
  reject def ParamDead (r : &Nat) : Unit := (let k = Z; match k { Z => (), S m => (let a = *r; ()) })
  def ParamDeadClone (r : &Nat) : Unit := (let k = Z; match k { Z => (), S m => (let a = clone(*r); ()) })
  def ParamDeadRefill (r : &Nat) : Unit := (let k = Z; match k { Z => (), S m => (let a = *r; *r := a; ()) })
  def MovedBefore (x : Nat) : Unit := (let r = &x; let s = r; let k = Z; match k { Z => (), S m => (let a = *r; ()) })
  def MovedByArm (k : Nat) (x : Nat) : Unit := (let r = &x; match k { Z => Take(r), S m => () }; let j = Z; match j { Z => (), S m => (let a = *r; ()) })
  def RebDead (x : Nat) : Unit := (let r = &x; let k = Z; match k { Z => (), S m => (let w = &*r; ()) })
}

#guard (run "JoinDeref" JoinDeref).rejectedWith [
  ("DP1", "[Join] an arm of the match moves a place through * of a place not declared a borrow"),
  ("DP2", "[Join] an arm of the match moves a place through * of a place not declared a borrow"),
  ("DP3", "[Join] an arm of the match moves a place through * of a place not declared a borrow"),
  ("DP4", "[Join] an arm of the match moves a place through * of a place not declared a borrow"),
  ("DData", "[Join] an arm of the match moves a place through * of a place not declared a borrow"),
  ("ParamDead", "[D53] a borrow ends while its content is partly moved out (⊥)")]

/-! ## A sealed program whose text holds a loan is not run (D97)

A fill (what a stuck call or block leaves at a place it lends to a returned borrow) holds the
borrow's hole in its text. Running it would write the hole (`*r := loan_k`) in a nested state
that does not hold the borrow, and what it computed could not be observed anyway: the place is
lent, and an access ends the borrow first. So such a program is left sealed, and runs when its last
hole is filled. These programs hit each site that substitutes into a sealed program while a hole
is in its text: [Close] (its fills, and a second stuck call over a returned borrow), a split's
refinement and re-normalisation, [End] with a reborrow that outlives its borrow, and a neutral's
generalisation. They also try to observe a lent place without ending its borrow, through `Id`,
`Eq` and a call. Every verdict is the one main gave before D97. -/

ochr HoleSites uses Nats, Fixtures, StaticEnds {
  def IdN (x : &Nat) : &Nat := x
  def AddTo (x : &Nat) (k : Nat) : Unit := match k { Z => (), S _ => (*x := 7; ()) }
  -- endBorrow: a reborrow of *r outlives r (the content substituted holds a live loan)
  def Reb (n : Nat) (a : Nat) (b : Nat) : Nat := (
    let s = (let r = Pick(clone(n), &a, &b); &*r);
    *s := 3;
    let d = a; d)
  def RebRun : Nat := Reb(0, 1, 2)
  -- a split after a stuck borrow-returning call (refine's substitution and renormAll, with fills)
  def SplitAfter (n : Nat) (a : Nat) (b : Nat) : Nat := (
    let r = Pick(clone(n), &a, &b);
    let z = match n { Z => 0, S m => 1 };
    *r := z;
    let d = a; d)
  def SplitAfterRun0 : Nat := SplitAfter(0, 1, 2)
  def SplitAfterRun1 : Nat := SplitAfter(1, 1, 2)
  -- the same in tail position (the split's arms run to the return)
  def SplitTail (n : Nat) (a : Nat) (b : Nat) : Nat := (
    let r = Pick(clone(n), &a, &b);
    match n { Z => (*r := 5; let d = a; d), S m => (*r := 6; let d = b; d) })
  -- a second stuck call over a returned borrow (closeCall's &T row puts a new hole in old fills)
  def Second (n : Nat) (m : Nat) (a : Nat) (b : Nat) (c : Nat) : Nat := (
    let r = Pick(clone(n), &a, &b);
    let s = Pick(clone(m), r, &c);
    *s := 4;
    let d = a; d)
  def SecondRun : Nat := Second(0, 0, 1, 2, 3)
  def SecondSplit (n : Nat) (m : Nat) (a : Nat) (b : Nat) (c : Nat) : Nat := (
    let r = Pick(clone(n), &a, &b);
    let s = Pick(clone(m), r, &c);
    let z = match m { Z => 0, S k => 1 };
    *s := z;
    let d = c; d)
  -- a neutral substitution into a fill: a stuck call's result generalised by a later match,
  -- while a fill over a live borrow mentions the same program
  def NeutralIn (n : Nat) (a : Nat) (b : Nat) : Nat := (
    let r = Pick(clone(n), &a, &b);
    let k = Add(clone(n), 0);
    let z = match k { Z => 0, S m => 1 };
    *r := z;
    let d = a; d)
  -- reading a lent place without ending its borrow: an Id over the lender in a split world
  reject def ObsLent (n : Nat) (a : Nat) (b : Nat) : Prop := (
    let r = Pick(clone(n), &a, &b);
    match n { Z => Id(Nat, clone(a), 1), S m => True })
  -- ... and an Eq, and a stuck call given the lent place (both end the borrow first)
  def EqLent (n : Nat) (a : Nat) (b : Nat) : Prop := (
    let r = Pick(clone(n), &a, &b);
    let z = match n { Z => 0, S m => 1 };
    Eq(Nat, clone(a), z))
  def CallLent (n : Nat) (k : Nat) (a : Nat) (b : Nat) : Nat := (
    let r = Pick(clone(n), &a, &b);
    AddTo(&a, k);
    let d = a; d)
  reject def CallLentUse (n : Nat) (k : Nat) (a : Nat) (b : Nat) : Nat := (
    let r = Pick(clone(n), &a, &b);
    AddTo(&a, k);
    *r := 1;
    let d = a; d)
}

#guard (run "HoleSites" HoleSites).rejectedWith [
  ("ObsLent", "[Id-typestate] a side of Id ends the borrow r"),
  ("CallLentUse", "no such place *r")]

/-! ## A borrow never ends over a moved-out content, in an observation as anywhere (D98)

Observing a side of `Id` ends every borrow ([Obs]). A side that leaves a borrow's content moved
out (`let z = *r; ()`) is rejected there, as the same code is when it runs (`RunAfterCall`):
[End] requires the content to be whole (D53). Until D98 an observation read such a part as `⊥`
instead; the semantic model cannot follow that through a borrow a call returned, whose backward
function is defined only on whole contents (`ObsBorrowThrough`, found by the proof). Copying with
`clone`, as runtime code must, or refilling the place, is accepted. A statement that ends no
borrow (a side of `Eq`) is unaffected: its moves are undone with its copy. -/

ochr ObsMoved uses Nats, Lists {
  def IdL (x : &List(Nat)) : &List(Nat) := &*x
  -- the witness: both sides reborrow through a borrow a call returned, then move its content out
  reject def ObsBorrowThrough (y : List(Nat)) : Unit := (let r = IdL(&y); let p : Id(Unit, (let w = &*r; let z = *r; ()), (let w = &*r; let z = *r; ())) = refl; ())
  -- its neighbours, changed alike: without the reborrow, after a plain borrow, through a parameter
  reject def ObsAfterCall (y : List(Nat)) : Unit := (let r = IdL(&y); let p : Id(Unit, (let z = *r; ()), (let z = *r; ())) = refl; ())
  reject def ObsAfterBorrow (y : List(Nat)) : Unit := (let r = &y; let p : Id(Unit, (let z = *r; ()), (let z = *r; ())) = refl; ())
  reject def ObsR (r : &List(Nat)) : Id(Unit, (let z = *r; ()), (let z = *r; ())) := refl
  -- ... a result that carries the content out, a field, a side split on an unknown, a nested Id
  reject def TakeBoth (r : &List(Nat)) : Id(List(Nat), *r, *r) := refl
  reject def FieldOpen (r : &Pair(List(Nat), Nat)) : Id(Unit, (let z = (*r).0; ()), (let z = (*r).0; ())) := refl
  reject def SplitSide (n : Nat) (y : List(Nat)) : Unit := (let r = IdL(&y); let p : Id(Unit, match clone(n) { Z => (let z = *r; ()), S m => (let z = *r; ()) }, (let z = *r; ())) = refl; ())
  reject def Nested (r : &List(Nat)) : Id(Prop, Id(Unit, (let z = *r; ()), (let z = *r; ())), True) := refl
  -- unchanged: sides that differ are told apart by the type-state first; a borrow that ends
  -- inside a side, and the same code run rather than observed, were always rejected
  reject def ObsAfterCallCtl (y : List(Nat)) : Unit := (let r = IdL(&y); let p : Id(Unit, (let z = *r; ()), ()) = refl; ())
  reject def ObsInSide (y : List(Nat)) : Id(Unit, (let r = IdL(&y); let z = *r; ()), (let r = IdL(&y); let z = *r; ())) := refl
  reject def ThroughW (y : List(Nat)) : Unit := (let r = IdL(&y); let p : Id(Unit, (let w = &*r; let z = *w; ()), (let w = &*r; let z = *w; ())) = refl; ())
  reject def RunAfterCall (y : List(Nat)) : Unit := (let r = IdL(&y); let z = *r; ())
  -- the rewrites: copy (D68's idiom) or refill
  def ObsBorrowThroughClone (y : List(Nat)) : Unit := (let r = IdL(&y); let p : Id(Unit, (let w = &*r; let z = clone(*r); ()), (let w = &*r; let z = clone(*r); ())) = refl; ())
  def ObsAfterCallClone (y : List(Nat)) : Unit := (let r = IdL(&y); let p : Id(Unit, (let z = clone(*r); ()), (let z = clone(*r); ())) = refl; ())
  def ObsAfterCallRefill (y : List(Nat)) : Unit := (let r = IdL(&y); let p : Id(Unit, (let z = *r; *r := z; ()), (let z = *r; *r := z; ())) = refl; ())
  def ObsRRefill (r : &List(Nat)) : Id(Unit, (let z = *r; *r := Cons(0, z); ()), (let z = *r; *r := Cons(0, z); ())) := refl
  def TakeBothClone (r : &List(Nat)) : Id(List(Nat), clone(*r), clone(*r)) := refl
  def FieldRefill (r : &Pair(List(Nat), Nat)) : Id(Unit, (let z = (*r).0; (*r).0 := z; ()), (let z = (*r).0; (*r).0 := z; ())) := refl
  -- a side of Eq ends no borrow: its move is undone with its copy
  def EqSideVal (r : &List(Nat)) : Eq(List(Nat), *r, *r) := refl
  -- a partial move refilled, another variable read in between (the proof's check 2)
  def PartMove (p : Pair(List(Nat), Nat)) (q : Nat) : Nat := (let r = &p; let z = (*r).0; let w = q; (*r).0 := z; w)
}

#guard (run "ObsMoved" ObsMoved).rejectedWith [
  ("ObsBorrowThrough", "[D53] a borrow ends while its content is partly moved out (⊥)"),
  ("ObsAfterCall", "[D53] a borrow ends while its content is partly moved out (⊥)"),
  ("ObsAfterBorrow", "[D53] a borrow ends while its content is partly moved out (⊥)"),
  ("ObsR", "[D53] a borrow ends while its content is partly moved out (⊥)"),
  ("TakeBoth", "[D53] a borrow ends while its content is partly moved out (⊥)"),
  ("FieldOpen", "[D53] a borrow ends while its content is partly moved out ((⊥, σ"),
  ("SplitSide", "[D53] a borrow ends while its content is partly moved out (⊥)"),
  ("Nested", "[D53] a borrow ends while its content is partly moved out (⊥)"),
  ("ObsAfterCallCtl", "[Id-typestate] the left side of Id leaves moved, through a borrow, *r, the right side does not"),
  ("ObsInSide", "[D53] a borrow ends while its content is partly moved out (⊥)"),
  ("ThroughW", "[D53] a borrow ends while its content is partly moved out (⊥)"),
  ("RunAfterCall", "[D53] a borrow ends while its content is partly moved out (⊥)")]

/-! ## A call's returned borrow is always fresh (D99)

A call whose declared result is a borrow returns the label it reserves for [Lend], whether its
body runs or it closes off. The borrow the body returned is ended into that label: its loans and
marks become the label's. That borrow may be a borrow argument, made before the call (`IdP`, a
`let` of one in `LetP`), a reborrow made in the call (`Reb`), one of several (`PickN`), or the
result of an inner call (`Via`, `IdP(IdP(&y))`). So after the call no label made before it is the
result's, on every path, as in the call's meaning. Before D99 a call that ran returned the
argument's own label, and one that closed off a fresh one (found by the proof:
`Meaning/Regress/ReturnParam.lean`). A renaming of labels changes no value. -/

ochr FreshResult uses Nats {
  def IdP (x : &Nat) : &Nat := x
  def Reb (x : &Nat) : &Nat := &*x
  def LetP (x : &Nat) : &Nat := (let z = x; z)
  def Via (x : &Nat) : &Nat := IdP(x)
  def PickN (n : Nat) (x : &Nat) (y : &Nat) : &Nat := match n { Z => x, S _ => y }
  -- the proof's witness: the callee returns its borrow parameter
  def UseIdP (u : Unit) : Nat := (let y = 2; let r = IdP(&y); *r := 5; y)
  def UseIdP5 : Eq(Nat, UseIdP(()), 5) := refl
  reject def UseIdP2 : Eq(Nat, UseIdP(()), 2) := refl
  -- a reborrow, a `let` of the parameter, through two calls, through a call in the body
  def UseReb : Eq(Nat, (let y = 2; let r = Reb(&y); *r := 5; y), 5) := refl
  def UseLetP : Eq(Nat, (let y = 2; let r = LetP(&y); *r := 5; y), 5) := refl
  def UseTwice : Eq(Nat, (let y = 2; let r = IdP(IdP(&y)); *r := 5; y), 5) := refl
  def UseVia : Eq(Nat, (let y = 2; let r = Via(&y); *r := 5; y), 5) := refl
  -- one of several, computed: both places are lent to the result
  def UsePick (n : Nat) : Nat := (let a = 1; let b = 2; let r = PickN(n, &a, &b); *r := 5; Add(a, b))
  def UsePick0 : Eq(Nat, UsePick(0), 7) := refl
  def UsePick1 : Eq(Nat, UsePick(1), 6) := refl
  reject def UsePickWrong : Eq(Nat, UsePick(0), 6) := refl
  -- the generic call closes `PickN(n, …)` off; a split on `n` refines it, and it runs
  def Pk (n : Nat) : Nat := match n { Z => 7, S _ => 6 }
  def UsePickSplit (n : Nat) : Eq(Nat, UsePick(n), Pk(n)) := match n { Z => refl, S m => refl }
}

#guard (run "FreshResult" FreshResult).rejectedWith [
  ("UseIdP2", "the body of UseIdP2 has type ⊤, but the goal is False"),
  ("UsePickWrong", "the body of UsePickWrong has type ⊤, but the goal is False")]

-- The property itself, read off the checker's state at a hole after the call: `&y` makes the
-- label 0, the call reserves 1, and the result is 1, not 0 (before D99: `lent_0 loan_0`,
-- `borrow_0 2`). Through two calls the result is the outer call's label 2; a reborrow made in
-- the callee (label 2) is ended into the call's label 1.
#guard_msgs (drop warning) in
ochr FreshResultAt uses Nats {
  def IdP (x : &Nat) : &Nat := x
  def Reb (x : &Nat) : &Nat := &*x
  def At1 (u : Unit) : Nat := (let y = 2; let r = IdP(&y); ?)
  def At2 (u : Unit) : Nat := (let y = 2; let r = IdP(IdP(&y)); ?)
  def At3 (u : Unit) : Nat := (let y = 2; let r = Reb(&y); ?)
}

/-- The values of the state at the first hole of `name` (`FreshResultAt`). -/
def freshResultAt (name : String) : List String :=
  let r := runWith (some Prelude) "FreshResultAt" FreshResultAt (located := true)
  match r.rows.find? (·.name == name) with
  | some row => (row.trace.toList.filterMap fun
      | .note _ _ (.hole _ Ω) => some (Ω.map (·.2.2.pp)) | _ => none).headD []
  | none => []

#guard freshResultAt "At1" == ["()", "lent_1 loan_1", "borrow_1 2"]
#guard freshResultAt "At2" == ["()", "lent_2 loan_2", "borrow_2 2"]
#guard freshResultAt "At3" == ["()", "lent_1 loan_1", "borrow_1 2"]
