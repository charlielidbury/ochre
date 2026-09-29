import Ochr.Test

/-! # 6. Types and closures are formed once

A type is evaluated once, where it is written, on a private copy of the environment. It
captures the values it mentions, so it is a closed statement: a later mutation does not
change what it says (RULES P2; D2, D13). A function's type is formed when the function is
called, before its body runs. Closures (`λ`) and Π-types capture values in the same way,
and never borrows; a captured value keeps its declared type, even when it is a sealed
program or a proof (D51).

Defined in RULES P2, §1 (closures capture no borrows) and §5 [Call-type]. -/

open Ochr.Test

ochr Snapshots {
  def AddM (x : &Nat) (y : Nat) : Unit by x := {
    match *x {
      | Z => *x := y
      | S p => AddM(&p, y)
    }
  }

  -- The result type is formed on entry, so writing `5` first does not prove it; ascribing
  -- the type again after the write does not help, since the goal is still the entry one.
  reject def WriteThenRefl' (x : &Nat) : Id Nat (*x) 5 := {
    *x := 5;
    (refl : Id Nat (*x) 5)
  }

  -- A proof formed before a mutation is still about the value it saw: `h` says `x = x` for
  -- the old `x`, which is still a true statement after `x := S x`.
  def Snapshot (x : Nat) : Id Nat x x := {
    let h = (refl : Id Nat x x);
    x := S x;
    h
  }

  -- So it cannot be re-read as a statement about the new value.
  reject def SnapshotLie (x : Nat) : False := {
    match x {
      | Z =>
        let h = (refl : Id Nat x 0);
        x := S x;
        (h : Id Nat x 0)
      | S _ => Snapshot(0)
    }
  }

  -- A closure's type is formed at its generic call, before its body writes.
  reject def LamWrite : (Π(x : &Nat). Id Nat (*x) 5) := λ(x : &Nat) : Id Nat (*x) 5 => (*x := 5; refl)

  -- A closure captures the value of `n` when it is formed ...
  def Cap (n : Nat) : Id Nat ((λ(u : Unit) : Nat => S n)(())) (S n) := refl

  -- ... so a later write to `m` does not change what `f` returns.
  def CapMut (n : Nat) : Id Nat (let m = n; let f = (λ(u : Unit) : Nat => m); m := S m; f(())) n := refl

  -- A captured sealed program keeps its type: after `AddM(&*x, 1)`, `*x` is a sealed
  -- program, and a closure or Π-type that captures it can still be typed.
  def CapS (x : &Nat) : Nat := {
    AddM(&*x, 1);
    let n = *x;
    let f = (λ(y : Nat) : Nat => n);
    f(0)
  }

  def CapSId (x : &Nat) : Nat := {
    AddM(&*x, 1);
    let n = *x;
    let f = (λ(y : Nat) : Id Nat n n => refl);
    0
  }

  def CapPi (x : &Nat) : Prop := {
    AddM(&*x, 1);
    let n = *x;
    Π(y : Nat). Id Nat n y
  }

  -- A captured proof keeps its type too.
  def CapP (h : Eq Nat Z Z) : Nat := {
    let f = (λ(x : Nat) : Eq Nat Z Z => h);
    0
  }

  def CapP2 (h : Eq Nat Z Z) : Eq Nat Z Z := {
    let f = (λ(x : Nat) : Eq Nat Z Z => h);
    f(0)
  }

  -- ## What goes wrong without these rules
  -- If a Π-type were read again at each call, `h(())` here would say `Id Nat (S x) 0`,
  -- which is `False`. It captured `x` when it was formed, so it still says `Id Nat x 0`
  -- about the `x` on entry (D13).
  reject def Oops2 (x : Nat) (h : Π(_ : Unit). Id Nat x 0) : False := {
    x := S x;
    h(())
  }
}

#eval IO.println (run "Snapshots" Snapshots).show

-- every verdict as expected, and the exact number of declarations (a truncated file changes it)
#guard (run "Snapshots" Snapshots).allAsExpected
#guard (run "Snapshots" Snapshots).count == 13
