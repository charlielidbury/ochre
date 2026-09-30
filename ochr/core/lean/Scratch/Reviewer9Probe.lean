import Ochr.Examples.«00Std»
open Ochr Ochr.Test
/-! Reviewer 9 (cold review of `notes/typed-fragment-proof.typ`, 2026-09-30): probes for the
findings in `notes/reviewer-9.md` (review of the proof at c0e3b665). Each verdict below is the one the checker gives; the
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

/-! ## The planned ghost-borrow fix (proof §"Naturality fails without F5") covers the
several-owner channel (`Pick`'s hole in two fills). A second channel has one owner: a match on
a place whose content is a sealed fill ends every loan inside it (D29), because the loan's
position inside the neutral is unknown; on the ground the loan sits deeper and survives the
match. Outside F (it assigns a borrow into an older variable, against F5), the same [Drop]
failure as `Bad2` follows. -/
ochr R9Bad4 uses Std, Fixtures {
  def Bad4 (x : &Nat) (a : Nat) : Unit := (
    x := TailM(&a);
    match a {
      Z => (),
      S _ => (),
    }
  )
  -- at a = 1, TailM returns a borrow of a.1; the match on a (head S) ends nothing, and a is
  -- dropped while x still borrows it
  reject def RunBad4S : Unit := (
    let c = 0;
    Bad4(&c, 1)
  )
  -- at a = 0, TailM returns &a itself, and the match ends x on the ground too
  def RunBad4Z : Unit := (
    let c = 0;
    Bad4(&c, 0)
  )
  -- the same with a local borrow declared before the owner
  def Bad5 (a : Nat) : Unit := (
    let c = 1;
    let x = &c;
    let b = a;
    x := TailM(&b);
    match b {
      Z => (),
      S _ => (),
    }
  )
  reject def RunBad5S : Unit := Bad5(1)
}
#eval IO.println (run "R9Bad4" R9Bad4).show
#guard (run "R9Bad4" R9Bad4).allAsExpected
#guard (run "R9Bad4" R9Bad4 { d53 := false }).allAsExpected
#guard (run "R9Bad4" R9Bad4).count == 5

/-! ## D65 ([Drop] ends the borrows of a dying place; DECISIONS 37500b5b) is not implemented
yet; these verdicts are today's, where the drop errs. Under D65 as written (a scratch
implementation: a dying owned value ends every borrower of its live loans, repeating as
[Access] does), `Blk`, `G` and `UseG` are accepted and each `Run…0` goes wrong: a stuck
block's arm evaluates to an ended borrow (⊥ at `&Nat`), [Split] discards arm values, and
[Close]'s `&T` row gives the closed-off block a fresh live borrow. The ground run takes the
arm directly and gets ⊥. [Def]'s result check does not see it (`G`'s generic result is the
block's live borrow). `RetLocal` is accepted under D65 unless [Def] checks its result, and
the suite has no such witness: its dangling returns have no borrow parameter, so D44 rejects
them first. The variant that ends only borrowers held in bindings, and errs when the
borrower is a value in flight, rejects all four and still runs `Bad2`–`Bad5` and
`DropVariants` (reviewer-9.md, finding 16). -/
ochr R9D65 uses Std, Fixtures {
  -- under D65: accepted; `RunBlk0` fails ("no such place *r: its path does not exist in ⊥")
  reject def Blk (n : Nat) (b : Nat) : Unit := (
    let r : &Nat = match n {
      Z => (
        let q = 0;
        &q
      ),
      S _ => &b,
    };
    *r := 5
  )
  -- under D65: accepted, though at n = 0 it returns an ended borrow
  reject def G (n : Nat) (b : &Nat) : &Nat := (
    let r : &Nat = match n {
      Z => (
        let q = 0;
        &q
      ),
      S _ => &*b,
    };
    r
  )
  -- under D65 (with `G` accepted): accepted at the generic call, where `G` closes off to a
  -- live borrow; `UseG(0, 1)` reads an ended borrow
  reject def UseG (n : Nat) (c : Nat) : Unit := (
    let r = G(n, &c);
    *r := 7
  )
  -- under D65 without a result check in [Def]: accepted
  reject def RetLocal (x : &Nat) : &Nat := (
    let a = 0;
    &a
  )
  -- inside F once F5 is removed (typed-fragment proof revision 2.1): a tail match whose arm
  -- returns a borrow of an arm-local. Under D65 without a result check in [Def], `FR` is
  -- accepted, and so is `UseFR(n, c) := let r = FR(n, &c); *r := 1`, since `FR`'s call closes
  -- off to a live borrow; `UseFR(0, 1)` then writes through an ended borrow (scratch D65 run,
  -- reviewer-9.md, re-check of revision 2.1). The variant rejects `FR`.
  reject def FR (n : Nat) (x : &Nat) : &Nat := (
    match n {
      Z => (
        let a = 0;
        &a
      ),
      S _ => x,
    }
  )
}
#eval IO.println (run "R9D65" R9D65).show
#guard (run "R9D65" R9D65).allAsExpected
#guard (run "R9D65" R9D65).count == 5

/-! ## Re-check of the typed-fragment proof, revision 2.2: an assignment's own [Access] can
end its new value on the symbolic path only. `Pick`'s hole sits in `x`'s content (through
the reborrow `&*x`) and in `b`'s, so the [Access] on `x` ends the new borrow symbolically; at
`n = 1` the ground borrow points into `b` and survives. Harmless (the symbolic path ends
more), but it contradicts revision 2.2's "ended on both paths alike". -/
ochr R9AS uses Std, Fixtures {
  def AS (n : Nat) (b : Nat) (x : &Nat) : Unit := (
    x := Pick(n, &*x, &b)
  )
  -- after the assignment x is ⊥ symbolically
  reject def AS2 (n : Nat) (b : Nat) (x : &Nat) : Unit := (
    x := Pick(n, &*x, &b);
    *x := 5
  )
  -- at n = 1 the ground run writes through the same assignment's result without error
  def AS2g1 : Unit := (
    let b = 3;
    let c = 0;
    let q = &c;
    q := Pick(1, &*q, &b);
    *q := 5
  )
}
#eval IO.println (run "R9AS" R9AS).show
#guard (run "R9AS" R9AS).allAsExpected
#guard (run "R9AS" R9AS).count == 3
