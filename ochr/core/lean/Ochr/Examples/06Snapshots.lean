import Ochr.Test

/-! # 6. Types and closures are formed once

A type is evaluated once, where it is written, on a private copy of the environment. It
captures the values it mentions, so it is a closed statement: a later mutation does not
change what it says (RULES P2; D2, D13). A function's type is formed when the function is
called, before its body runs.

Closures (`λ`) and Π-types capture in the same way. Forming one reads each variable it
mentions, as a use of that variable: the value is copied into the closure, a live borrow of
the variable ends ([Access]), and a variable that holds a borrow, or nothing because its
borrow was moved out, cannot be captured (closures capture no borrows, RULES §1). A captured
value keeps its declared type, even when it is a sealed program or a proof (D51).

Defined in RULES P2, §1 (closures capture no borrows) and §5 [Call-type]; the checker's
`capture` (Machine.lean). -/

open Ochr.Test

ochr Snapshots {
  def AddM (x : &Nat) (y : Nat) : Unit by x := (
    match *x {
      Z => *x := y,
      S p => AddM(&p, y),
    }
  )

  -- ## Types are formed once
  -- The result type is formed on entry, so writing `5` first does not prove it; ascribing
  -- the type again after the write does not help, since the goal is still the entry one.
  reject def WriteThenRefl' (x : &Nat) : Id Nat (*x) 5 := (
    *x := 5;
    (refl : Id Nat (*x) 5)
  )

  -- A proof formed before a mutation is still about the value it saw: `h` says `x = x` for
  -- the old `x`, which is still a true statement after `x := S x`.
  def Snapshot (x : Nat) : Id Nat x x := (
    let h = (refl : Id Nat x x);
    x := S x;
    h
  )

  -- So it cannot be re-read as a statement about the new value.
  reject def SnapshotLie (x : Nat) : False := (
    match x {
      Z => (
        let h = (refl : Id Nat x 0);
        x := S x;
        (h : Id Nat x 0)
      ),
      S _ => Snapshot(0),
    }
  )

  -- A closure's type is formed at its generic call, before its body writes.
  reject def LamWrite : (Π(x : &Nat). Id Nat (*x) 5) := λ(x : &Nat) : Id Nat (*x) 5 => (*x := 5; refl)

  -- ## What a closure captures
  -- A closure captures the value of `n` when it is formed ...
  def Cap (n : Nat) : Id Nat ((λ(u : Unit) : Nat => S n)(())) (S n) := refl

  -- ... so a closure formed before `a := 1` still returns the old value ...
  def CapSnap : Id Nat (let a = 0; let f = (λ(y : Nat) : Nat => a); a := 1; f(0)) 0 := refl

  -- ... and not the new one.
  reject def CapSnapNew : Id Nat (let a = 0; let f = (λ(y : Nat) : Nat => a); a := 1; f(0)) 1 := refl

  -- The same at an abstract number.
  def CapMut (n : Nat) : Id Nat (let m = n; let f = (λ(u : Unit) : Nat => m); m := S m; f(())) n := refl

  -- A closure may not capture a borrow: a closure is a value, and values hold no borrows
  -- (RULES §1).
  reject def CapBorrow (x : &Nat) : Nat := (
    let f = (λ(y : Nat) : Nat => *x);
    f(0)
  )

  -- Copying the number out first is fine ...
  def CapCopy (x : &Nat) : Nat := (
    let n = *x;
    let f = (λ(y : Nat) : Nat => n);
    f(0)
  )

  -- ... also when the copy is a sealed program (after `AddM(&*x, 1)`, `*x` is one): the
  -- captured value keeps its type, so the closure can be typed.
  def CapS (x : &Nat) : Nat := (
    AddM(&*x, 1);
    let n = *x;
    let f = (λ(y : Nat) : Nat => n);
    f(0)
  )

  def CapSId (x : &Nat) : Nat := (
    AddM(&*x, 1);
    let n = *x;
    let f = (λ(y : Nat) : Id Nat n n => refl);
    0
  )

  -- A Π-type is a closure too: the same rule, and the same way round it.
  reject def PiBorrow (x : &Nat) : Prop := Π(n : Nat). Id Nat n (*x)

  def PiCopy (x : &Nat) : Prop := (
    let m = *x;
    Π(n : Nat). Id Nat n m
  )

  def CapPi (x : &Nat) : Prop := (
    AddM(&*x, 1);
    let n = *x;
    Π(y : Nat). Id Nat n y
  )

  -- Capturing `a` reads it, which ends the borrow `r` of `a`, so the later write through `r`
  -- is a use of an ended borrow ...
  reject def CapEndsBorrow (a : Nat) : Nat := (
    let r = &a;
    let f = (λ(y : Nat) : Nat => a);
    *r := 1;
    f(0)
  )

  -- ... while writing through `r` before the closure is formed is fine, and the closure sees
  -- the write.
  def CapAfterBorrow :
      Id Nat (let a = 0; let r = &a; *r := 1; let f = (λ(y : Nat) : Nat => a); f(0)) 1 := refl

  -- A borrow variable whose borrow was moved out holds nothing to capture.
  reject def CapMoved (x : &Nat) : Nat := (
    let y = x;
    let f = (λ(z : Nat) : Nat => *x);
    0
  )

  -- A captured proof keeps its type too.
  def CapP (h : Eq Nat Z Z) : Nat := (
    let f = (λ(x : Nat) : Eq Nat Z Z => h);
    0
  )

  def CapP2 (h : Eq Nat Z Z) : Eq Nat Z Z := (
    let f = (λ(x : Nat) : Eq Nat Z Z => h);
    f(0)
  )

  -- ## What goes wrong without these rules
  -- If a Π-type were read again at each call, `h(())` here would say `Id Nat (S x) 0`,
  -- which is `False`. It captured `x` when it was formed, so it still says `Id Nat x 0`
  -- about the `x` on entry (D13).
  reject def Oops2 (x : Nat) (h : Π(_ : Unit). Id Nat x 0) : False := (
    x := S x;
    h(())
  )
}

#eval IO.println (run "Snapshots" Snapshots).show

-- every verdict as expected, and the exact number of declarations (a truncated file changes it)
#guard (run "Snapshots" Snapshots).allAsExpected
#guard (run "Snapshots" Snapshots).count == 22
