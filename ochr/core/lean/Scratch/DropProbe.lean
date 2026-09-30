import Ochr.Examples.«00Std»
open Ochr Ochr.Test
/-! Soundness lead (meta-order, 2026-09-30): an accepted data function goes wrong at a ground
instance. Found while writing the naturality step of the typed-fragment proof.

At an abstract `n`, `Pick(n, &a, &b)` closes off and its hole `loan_k` sits in the fills of both
`a` and `b`. Reading `b` ends `x`'s borrow `k` ([Access] ends every loan inside the content,
sealed programs included), so `x` is ⊥ and `a` holds data when `a` goes out of scope: `Bad2` is
accepted. At `n = 0`, `Pick` returns a borrow of `a`, `b` holds no loan, reading `b` ends
nothing, and `a` goes out of scope while `x` still borrows it: [Drop] fails. The symbolic path
ended the borrow earlier than the ground path (F3's over-approximation), and an early end makes
a later [Drop] succeed. Independent of D53 (the same with `d53 := false`). `x` needs to outlive
`a`, which takes an assignment of a borrow into an existing variable (a parameter here, or a
`let` declared before `a`, `Bad3`).

Fixed by amended D65 (d65-lane): `a`'s drop ends `x`, a borrower held in a binding, instead of
erring, so the ground runs complete. The tour's `Drops` block (02Borrows) holds these. -/
ochr DropProbe uses Fixtures {
  def Bad2 (n : Nat) (b : Nat) (x : &Nat) : Unit := (
    let a = 0;
    x := Pick(n, &a, &b);
    let z = b;
    ()
  )
  -- accepted, as `Bad2` is: it is `Bad2` at a ground instance
  def RunBad0 : Unit := (
    let y = 7;
    Bad2(0, 5, &y)
  )
  def RunBad1 : Unit := (
    let y = 7;
    Bad2(1, 5, &y)
  )
  -- the same with a local borrow declared before `a`
  def Bad3 (n : Nat) (b : Nat) : Unit := (
    let c = 1;
    let x = &c;
    let a = 0;
    x := Pick(n, &a, &b);
    let z = b;
    ()
  )
  def RunBad3 : Unit := Bad3(0, 5)
}
#eval IO.println (run "DropProbe" DropProbe).show
#guard (run "DropProbe" DropProbe).allAsExpected
#guard (run "DropProbe" DropProbe {}).allAsExpected
#guard (run "DropProbe" DropProbe).count == 5
