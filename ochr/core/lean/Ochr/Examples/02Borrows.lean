import Ochr.Examples.«00Std»

/-! # 2. Borrows: moving, copying, reborrowing, and the borrow checker

`&p` borrows the place `p`, and `*r` is the place a borrow `r` points to. Reading a place
moves what it holds out, and the place is dead afterwards, unless its type is a copy type
(`Unit`, `Bool`, a `Word`, a pair of copies; not `Nat`), which a read copies. `clone(p)`
copies anything. A term that is erased (a type, a proof, a statement) reads without moving,
and still sees what was moved (D53). A borrow is always moved (RULES P3). `&*x` reborrows: it lends `*x` for a while
and leaves `x` usable afterwards. Before a place is used, every borrow that might still
reach it is ended ([Access]); using an ended borrow is an error, and so is dropping a
local that something still borrows ([Drop]). This is the whole borrow checker.

Defined in RULES §3: [Read], [Borrow], [Assign], [Access], [End], [Drop], [Call]. -/

open Ochr.Test

ochr Borrows uses Std {
  -- Passing `x` moves the borrow into the call, so the second call reads a dead place.
  reject def UseMoved (x : &Nat) : Unit := (
    AddM(x, 0);
    AddM(x, 0)
  )

  -- Reborrowing `&*x` for the first call leaves `x` usable for the second.
  def UseReborrowed (x : &Nat) : Unit := (
    AddM(&*x, 0);
    AddM(x, 0)
  )

  -- A statement is erased, and its reads copy, so `Add(x, x)` reads `x` twice, and
  -- `x + x = x` is a well-formed statement (a false one).
  def AddXX (x : Nat) : Prop := Id Nat (Add(x, x)) x

  -- A borrow of a local writes to the local: after `*y := 2` through `y = &x`, `x` is `2`.
  def LetZ (x : Nat) : Nat := (
    let z = (let y = &x; *y := 2; x);
    let h : Id Nat z 2 = refl;
    z
  )

  -- Returning a borrow of a local: the local is dropped at the end of the call while the
  -- returned borrow still points to it.
  reject def DanglingLocal (u : Unit) : &Nat := (
    let z = 0;
    &z
  )

  reject def DanglingReborrow (z : Nat) : &Nat := (
    let r = &z;
    &*r
  )

  -- Arguments are evaluated left to right, each into a temporary that later arguments can
  -- see. Reading `x` for the second argument ends the borrow `&x` made for the first, so
  -- the callee would receive a dead borrow.
  reject def Dead (f : Π(a : &Nat) (b : Nat). Unit) (x : Nat) : Unit := f(&x, x)
  reject def DeadTwice (f : Π(a : &Nat) (b : &Nat). Unit) (x : Nat) : Unit := f(&x, &x)

  -- The other way round is fine when `x` is a copy (a `Word`, D53): it is copied first, then
  -- borrowed. A `Nat` is moved by the first argument, so it needs `clone(x)` there.
  def NotDead (f : Π(a : Word) (b : &Word). Unit) (x : Word) : Unit := f(x, &x)

  -- A statement about two separate borrows ...
  def g (x : &Nat) (y : &Nat) : Id Nat (*x := 0; *y := 1; *x) (*x := 0; *y := 1; 0) := refl

  -- ... cannot be used on two borrows of the same place: passing `z` ends the reborrow `a`,
  -- in whichever order the two are passed (D19).
  reject def attack (z : &Nat) : Id Nat 1 0 := (
    let a = &*z;
    g(z, a)
  )

  reject def attack' (z : &Nat) : Id Nat 1 0 := (
    let a = &*z;
    g(a, z)
  )

  -- ## What goes wrong without these rules
  -- Without the check that no argument is dead (switch `argNotBot`), `Dead` is accepted: an
  -- opaque callee receives a dead borrow, and a concrete run goes wrong as soon as it writes
  -- through it.

  -- [Access] ends every borrow of a place inside the content being passed, not only borrows
  -- of the place itself (D19). Here `r` borrows the predecessor inside `*b`; passing `b` to
  -- `G1` must end `r` first. Without that (switch `accessInside`), the call's stuck result
  -- would keep `r`'s loan inside `a`, and the later write through `r` would go to a place
  -- that no longer exists. (Since η for `Unit`, D59, the stuck call's result is its sealed
  -- program, which carries the loan too, and discarding it is a [Drop] error: `BadA1` is
  -- rejected even with the switch off.)
  def G1 (x : &Nat) (n : Nat) : Unit := (
    match n {
      Z => (),
      S _ => *x := 0,
    }
  )

  reject def BadA1 (n : Nat) : Nat := (
    let a = S Z;
    (let b = &a; let r = &(*b).1; G1(b, n); *r := S Z);
    a
  )

  -- D19's witnesses since then (fuzz-port, `--diff --switch D19`). In `V` a stuck block
  -- returns a borrow of `n0`, so `n0` holds a sealed program with that borrow's loan inside
  -- it; reading `n0` must end the borrow, and the write through `a0` then has no place.
  -- Without D19, `V` is accepted and `V(0)` goes wrong: the block runs, the read of `n0`
  -- ends `a0`, and the write is to nothing.
  reject def V (n0 : Nat) : Unit := (let a0 = match n0 { Z => &n0, S _ => &n0 }; *a0 := n0)
  reject def VRun : Unit := V(0)

  -- [Close]'s precondition (a stuck call's arguments hold no live loans): `&a` holds `r`'s
  -- loan inside, [Close] would seal it into `out`, and the write through `r` would be
  -- accepted; at `n = 1` the call runs and overwrites `a` while `r` borrows inside it. The
  -- result goes to `out`, declared before `r`, so `r` dies first and [Drop] never sees the
  -- loan in it (bound after `r`, as in `BadA1`, [Drop] catches it even without D19).
  def G2 (x : &Nat) (n : Nat) : Nat := (match n { Z => 0, S _ => *x := 0; 0 })
  reject def W (n : Nat) : Nat := (let a = S Z; let out = 0; (let r = &a.1; out := G2(&a, n); *r := S Z); out)
  reject def WRun : Nat := W(1)
}

#eval IO.println (run "Borrows" Borrows).show

-- every verdict as expected, and the exact number of declarations (a truncated file changes it)
#guard (run "Borrows" Borrows).allAsExpected
#guard (run "Borrows" Borrows).count == 19

/-! ## Moves and copies (D53)

D53 is checked in this block only, until its acceptance run passes (`Ochr.Test.d53Blocks`);
the rest of the tour reads by copying, as before D53, and its `clone`s are harmless there. -/

ochr Moves uses Std {
  -- Reading a `Nat` moves it: after `let m = n`, `n` is gone ...
  def MoveNat (n : Nat) : Nat := (
    let m = n;
    m
  )

  reject def UseAfterMove (n : Nat) : Nat := (
    let m = n;
    n
  )

  -- ... unless it is cloned. A `Word` is declared `copy`, so every read copies it.
  def CloneNat (n : Nat) : Nat × Nat := (clone(n), n)
  reject def TwiceNat (n : Nat) : Nat × Nat := (n, n)
  def TwiceWord (w : Word) : Word × Word := (w, w)

  -- A type is a copy type when it is declared `copy` (its fields must be copies) or when it
  -- is not recursive and its fields are copies.
  copy inductive Pt := MkPt(x : Word, y : Word)
  reject copy inductive NatBox := MkNatBox(n : Nat)
  def TwicePt (p : Pt) : Pt × Pt := (p, p)

  -- A statement reads without moving, and sees what was moved (its ghost), in any order.
  def GhostRead (n : Nat) : Nat := (
    let m = n;
    let h : Id Nat n m = refl;
    m
  )

  -- Moving out through a borrow is allowed when the place is whole again by the time the
  -- borrow ends ...
  def TakeAndRestore (x : &Nat) : Nat := (
    let v = *x;
    *x := Z;
    v
  )

  -- ... and an error otherwise, as is returning a borrow of what was moved out.
  reject def TakeFromBorrow (x : &Nat) : Nat := *x

  reject def ReturnMovedBorrow (x : &Nat) (y : &Nat) : &Nat := (
    let v = *y;
    y
  )

  -- A call does not consume the function it calls, so a function can be called twice. A
  -- closure may run again, so its body may not move out of what it captured: returning a
  -- captured `Nat` needs `clone`. A closure whose captures are copies is a copy itself;
  -- otherwise reading it moves it.
  def CallTwice (f : Π(x : Nat). Nat) (x : Nat) : Nat := f(f(x))

  reject def ClosureMovesCapture (n : Nat) : Nat × Nat := (
    let f = (λ(u : Unit) : Nat => n);
    (f(()), f(()))
  )

  def ClosureClones (n : Nat) : Nat × Nat := (
    let f = (λ(u : Unit) : Nat => clone(n));
    (f(()), f(()))
  )

  def ClosureCopy (w : Word) : Word × Word := (
    let f = (λ(u : Unit) : Word => w);
    let g = f;
    (f(()), g(()))
  )

  reject def ClosureMoved (n : Nat) : Nat := (
    let f = (λ(u : Unit) : Nat => clone(n));
    let g = f;
    f(())
  )

  -- A match that moves out of a borrowed place in one arm leaves the borrow partly moved
  -- when it ends. Closed off, the same program is re-run for its result and for what it
  -- leaves in `*x0`, and each re-run moves again: the re-runs have runtime semantics, and
  -- only the final read of the result is an observation (fuzz-port shape (b)).
  reject def MoveInArm (x0 : &Nat) : Nat := (
    match *x0 {
      Z => *x0,
      S p3 => 0,
    }
  )

  -- A stuck match reads its scrutinee in place, so closing it off does not move a `Nat` it
  -- only reads ...
  def BlockReads (n0 : Nat) : Nat := (
    let l = match n0 {
      Z => 0,
      S _ => 1,
    };
    n0
  )

  -- ... and moves in only the part an arm moves out, `q1.1`, so `q1.2` is still there
  -- (fuzz-port shape (a)).
  def BlockMovesField (q1 : Nat × Nat) : Nat := (
    let a = match q1 {
      Mk(p7, p8) => p7,
    };
    match q1 {
      Mk(p9, p10) => p10,
    }
  )

  -- A function that moves out of `*y10` and returns `y10` hands back a borrow of a moved
  -- place, an error as when a borrow ends partly moved. Compared by their results only
  -- through a fresh value written into them (D38), it looked equal to the one that just
  -- returns `y10` (fuzz-port shape (c)).
  reject def RetMoved : Eq (Π(y9 : &Nat) (y10 : &Nat). &Nat)
      (λ(y9 : &Nat) (y10 : &Nat) : &Nat => (*y10; y10)) (λ(y9 : &Nat) (y10 : &Nat) : &Nat => y10) := refl

  -- A stuck match's effect on what it captures is the direct path's, moves included, at
  -- every granularity (fuzz-port's execution oracle: each of these was accepted and went
  -- wrong when run). M1: an arm moves a field its pattern exposed, so `q0` (and `n0`) is
  -- partly moved afterwards; a pair is refined to its one constructor to say which part.
  reject def A1 (q0 : Nat × Nat) : Nat × Nat := (let a = match q0 { Mk(p, _) => p }; q0)
  reject def A2 (n0 : Nat) : Nat := (let a = match n0 { Z => 0, S p => p }; n0)
  def A3 (q0 : Nat × Nat) : Nat := (let a = match q0 { Mk(p, _) => p }; a)
  -- M2: an arm moves a captured place that is not a whole variable (`*x0`, `*x1`), so the
  -- block moves it in and the borrow ends partly moved
  reject def B1 (x0 : &Nat) (n1 : Nat) : Nat := (let a = match n1 { Z => 0, S _ => *x0 }; a)
  reject def B2 (q0 : Nat × Nat) (x1 : &Nat) : Nat := S (match q0 { Mk(_, _) => *x1 })
  reject def B3 (x0 : &Nat) (x1 : &Nat) : &Nat := (match *x1 { Z => (), S _ => *x1 := *x0 }; x0)
  -- M2b: one arm moves the borrow into the block, another moves out through it, and the
  -- block's frame ends the borrow partly moved
  reject def B4 (x0 : &Nat) : Nat := S (match *x0 { Z => x0; 0, S _ => *x0 })
  -- M3: erased positions read without moving, whichever path runs them: `J`'s endpoints and
  -- motive (as run by a call, untyped), and an `Id` side on its private copy
  def J1 (n : Nat) (h : Eq Nat n 1) : Nat := (let m = n; J(Nat, n, 1, λ(z : Nat) : Type => Nat, h, m))
  def J1Run : Nat := J1(1, refl)
  def I1 (n1 : Nat) : Nat := (let m = n1; let a0 = Id Unit () (n1 := 0); 0)
  def I1Run : Nat := I1(0)
  -- A block's effect on its captures is read from its arms' moves and assignments, by place
  -- (not by comparing values, which are abstract or sealed), so it composes through nested
  -- blocks (N1), sees a borrow moved in whole by an inner block's capture (N2), and gives
  -- each part of a captured place its own mode: `q1.1` moved, `q1.2` lent (N3). A move that
  -- the arm restores, or that goes through a local borrow, counts as the owner's.
  reject def N1 (x0 : &(Nat × Nat)) (n1 : Nat) : Nat := (
    let a = match n1 { Z => match *x0 { Mk(p, _) => p }, S _ => 0 }; a)
  reject def N2 (x0 : &Nat) : Nat := (
    let a = match *x0 { Z => match *x0 { Z => 0, S _ => x0; 0 }, S _ => *x0 }; a)
  reject def N3 (q1 : Nat × Nat) : Nat × Nat := (
    let a = match q1 { Mk(p1, p2) => match p2 { Z => p1; &p2, S _ => &p2 } }; q1)
  def N3Other (q1 : Nat × Nat) : Nat := (
    let a = match q1 { Mk(p1, p2) => match p2 { Z => p1; &p2, S _ => &p2 } }; 0)
  def MoveRestore (x0 : &Nat) (n1 : Nat) : Nat := (
    let a = match n1 { Z => 0, S _ => (let v = *x0; *x0 := 0; v) }; a)
  reject def ThroughLocal (q0 : Nat × Nat) (n1 : Nat) : Nat × Nat := (
    let a = match n1 { Z => 0, S _ => (let r = &q0; match *r { Mk(u, _) => u }) }; q0)

  -- RN: a split in a data function re-normalises its hypotheses' types, as types (reads copy)
  def DataSplit (n : Nat) (h : Id (Nat × Nat) (match n { Z => (n, n), S p => (p, p) })
      (match n { Z => (0, 0), S p => (p, p) })) : Nat := (
    match n { Z => 0, S _ => 1 })
}

#eval IO.println (run "Moves" Moves).show

#guard (run "Moves" Moves).allAsExpected
#guard (run "Moves" Moves).count == 39
