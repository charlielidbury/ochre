import Ochr.Examples.«00Std»
open Ochr Ochr.Test
/-! Reviewer 9 (cold review of `notes/typed-fragment-proof.typ`, 2026-09-30): probes for the
findings in `notes/reviewer-9.md`. Each verdict below is the one the checker gives; the
comments say what it shows. -/

/-! ## Early ends inside F (F5 respected): no accepted program found that fails at a ground
instance. -/
ochr R9Early uses Std, Fixtures {
  -- a borrow in flight (a let-block's result) outlives the block's local `a`: the symbolic
  -- path rejects it too, since `a`'s fill holds the live hole
  reject def E1 (n : Nat) (b : Nat) : Unit := (
    let q = (
      let a = 0;
      Pick(n, &a, &b)
    );
    ()
  )
  -- reading the other owner ends `r` symbolically only; `r` is dropped before `a` anyway
  def E2 (n : Nat) (b : Nat) : Unit := (
    let a = 0;
    let r = Pick(n, &a, &b);
    let z = b;
    ()
  )
  def E2g0 : Unit := E2(0, 5)
  def E2g1 : Unit := E2(1, 5)
  -- a match on a fill ends every loan inside it (one owner): symbolic early end, ground not
  def E3 (x : &Nat) : Unit := (
    let r = TailM(&*x);
    match *x {
      Z => (),
      S p => (),
    }
  )
  def E3g : Unit := (
    let c = 2;
    E3(&c)
  )
  -- an early end, then the borrow parameter is returned
  def E4 (n : Nat) (x : &Nat) : &Nat := (
    let a = 0;
    let r = Pick(n, &a, &*x);
    let z = clone(*x);
    x
  )
  def E4g0 : Unit := (
    let c = 2;
    let q = E4(0, &c);
    ()
  )
  def E4g1 : Unit := (
    let c = 2;
    let q = E4(1, &c);
    ()
  )
}
#eval IO.println (run "R9Early" R9Early).show
#guard (run "R9Early" R9Early).allAsExpected
#guard (run "R9Early" R9Early).count == 9

/-! ## Ghosts inside borrows: resolution is undefined at reachable states of F, and calls are
made at non-ground instances. -/
ochr R9Ghost uses Std, Fixtures {
  -- accepted: after `let v = *x`, x's content is a ghost until `*x := S v`
  def Replace (x : &Nat) : Unit := (
    let v = *x;
    *x := S v
  )
  -- at that state, ending every borrow (what an observation, and the proof's ρ, do) fails
  reject def ReplaceObs (x : &Nat) : Unit := (
    let v = *x;
    let h : Id Unit () () = refl;
    *x := S v
  )
  -- a call whose borrow argument holds a ghost: not a ground instance of `W`
  def W (y : &Nat) : Unit := *y := 0
  def G (x : &Nat) : Unit := (
    let v = *x;
    W(x)
  )
  def Gg : Nat := (
    let c = 3;
    G(&c);
    c
  )
  -- the same with a recursive callee (recursive on another argument)
  def WR (y : &Nat) (n : Nat) : Unit by n := (
    match n {
      Z => *y := 0,
      S m => WR(y, m),
    }
  )
  def GR (x : &Nat) : Unit := (
    let v = *x;
    WR(x, 2)
  )
  -- matching a moved-out place is rejected on the symbolic path (as at runtime)
  reject def GhostMatch (n : Nat) : Nat := (
    let m = n;
    match n {
      Z => m,
      S _ => m,
    }
  )
}
#eval IO.println (run "R9Ghost" R9Ghost).show
#guard (run "R9Ghost" R9Ghost).allAsExpected
#guard (run "R9Ghost" R9Ghost).count == 8

/-! ## `clone` of a borrow variable: the appendix's [Clone] would duplicate it; the checker
moves it, and rejects a clone of ⊥. -/
ochr R9Clone uses Std, Fixtures {
  def CloneB1 (x : &Nat) : Unit := (
    let y = clone(x);
    ()
  )
  -- after `clone(x)`, x is ⊥
  reject def CloneB2 (x : &Nat) : Unit := (
    let y = clone(x);
    *x := 1
  )
  reject def CloneBot (a : Nat) : Unit := (
    let r = &a;
    let s = r;
    let z = clone(r);
    ()
  )
  -- outside F (it assigns a borrow): a whole-variable assignment over ⊥ is not an error,
  -- so a statement can mention a borrow variable that the symbolic path has ended
  def AssignBot (n : Nat) (a : Nat) (b : Nat) (c : Nat) : Unit := (
    let x = Pick(n, &a, &b);
    let z = clone(b);
    let h : Id Unit (x := &c; *x := 5) (x := &c; *x := 5) = refl;
    ()
  )
}
#eval IO.println (run "R9Clone" R9Clone).show
#guard (run "R9Clone" R9Clone).allAsExpected
#guard (run "R9Clone" R9Clone).count == 4

/-! ## `Id`'s sides run with copying reads; the same code at runtime moves. -/
ochr R9Copy uses Std, Fixtures {
  def IdCopies (a : Nat) : Id Nat (let z = a; a) a := refl
  reject def RunTwice (a : Nat) : Nat := (
    let z = a;
    a
  )
}
#eval IO.println (run "R9Copy" R9Copy).show
#guard (run "R9Copy" R9Copy).allAsExpected
#guard (run "R9Copy" R9Copy).count == 2

/-! ## Lemma 7 (b) checked: a footprint conjunct that exists only at an abstract `n` becomes ⊤
once `n` is refined (FootprintProbe says so in a comment; here it is a verdict). -/
ochr R9Foot uses Std, Fixtures {
  -- in arm Z the hypothesis is `False ∧ ⊤`, and its second conjunct is used as `True`
  def FPZ (n : Nat) (a : Nat) (b : Nat)
      (h : Id Unit (let r = Pick(n, &a, &b); *r := 0) (let r = Pick(n, &a, &b); *r := 1)) : Eq Nat n n := (
    match n {
      Z => (
        let w : True = (match h { Intro(l, k) => k });
        refl
      ),
      S _ => refl,
    }
  )
  -- the rejection message shows arm S's type, `⊤ ∧ False`
  reject def FPZshow (n : Nat) (a : Nat) (b : Nat)
      (h : Id Unit (let r = Pick(n, &a, &b); *r := 0) (let r = Pick(n, &a, &b); *r := 1)) : Eq Nat n (S n) := (
    match n {
      Z => h,
      S _ => h,
    }
  )
}
#eval IO.println (run "R9Foot" R9Foot).show
#guard (run "R9Foot" R9Foot).allAsExpected
#guard (run "R9Foot" R9Foot).count == 2
