import Ochr.Examples.«00Std»

/-! # 2. Borrows: moving, copying, reborrowing, and the borrow checker

`&p` borrows the place `p`, and `*r` is the place a borrow `r` points to. Reading a place
that holds data copies it; reading a place that holds a borrow moves the borrow out, and
the place it was read from is dead (RULES P3). `&*x` reborrows: it lends `*x` for a while
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

  -- Reading a number copies it, so `Add(x, x)` reads `x` twice, and `x + x = x` is a
  -- well-formed statement (a false one).
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

  -- The other way round is fine: `x` is copied first, then borrowed.
  def NotDead (f : Π(a : Nat) (b : &Nat). Unit) (x : Nat) : Unit := f(clone(x), &x)

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
  -- that no longer exists.
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
#guard (run "Borrows" Borrows).count == 14
