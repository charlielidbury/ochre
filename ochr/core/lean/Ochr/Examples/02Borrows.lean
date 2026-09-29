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

  -- ## Moves and copies (D53)
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
}

#eval IO.println (run "Borrows" Borrows).show

-- every verdict as expected, and the exact number of declarations (a truncated file changes it)
#guard (run "Borrows" Borrows).allAsExpected
#guard (run "Borrows" Borrows).count == 32
