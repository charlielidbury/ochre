import Ochr.Examples.«00Std»

/-! # 12. Proofs about the current state

A type may mention the current contents of a place, and a proof passed to a function may
be about a place that was just changed. `SubM(x, y, h)` subtracts `y` from `*x` in place and
needs `h : Le(y, *x)` about the current `*x`. `AddSub` builds that proof from a copy of `*x`
taken before `AddM` changed it: in-place and pure addition close off into the same sealed
program, so `Le(old, Add(old, y))` is a statement about the new `*x`.

Defined in RULES §7 (the E5 example); `match h {}` on a refined type is RULES §8 (D49). -/

open Ochr.Test

ochr CurrentState uses Std {
  -- A function that returns a proposition.
  def Le (a : Nat) (b : Nat) : Prop by a := (
    match a {
      Z => ⊤,
      S a' => match b {
        Z => False,
        S b' => Le(a', b'),
      },
    }
  )

  -- A lemma about the pure `Add`.
  def LeAdd (n : Nat) (m : Nat) : Le(n, Add(n, m)) by n := (
    match n {
      Z => refl,
      S n' => LeAdd(n', m),
    }
  )

  -- Take `y` successors off the top of `*x`. The precondition survives `*x := p`, and where
  -- `*x` is `Z` but `y` is not, the split has refined `h`'s type to `Le(S(q), Z)`, which
  -- computes to `False`, so the arm is `match h {}`.
  def SubM (x : &Nat) (y : Nat) (h : Le(y, *x)) : Unit by y := (
    match y {
      Z => (),
      S q => match *x {
        Z => match h {},
        S p => (
          *x := p;
          SubM(x, q, h)
        ),
      },
    }
  )

  -- A proof made from the copy `old`, about the changed `*x`.
  def AddSub (x : &Nat) (y : Nat) : Unit := (
    let old = clone(*x);
    AddM(&*x, y);
    SubM(x, old, LeAdd(old, y))
  )

  -- Adding `y` and then subtracting the old `*x` leaves `y` in `*x`. The induction hypothesis
  -- is about a copy of the predecessor.
  def AddSubId (x : &Nat) (y : Nat) : Id(Unit, AddSub(x, y), *x := y) by x := (
    match *x {
      Z => refl,
      S p => (
        let c = p;
        AddSubId(&c, y)
      ),
    }
  )

  -- The precondition really is about the current state: after `*x := Z` it no longer holds
  -- ...
  reject def AddSubStale (x : &Nat) (y : Nat) : Unit := (
    let old = clone(*x);
    AddM(&*x, y);
    *x := Z;
    SubM(x, old, LeAdd(old, y))
  )

  -- `LeAdd` is also the idiom for a postcondition (paper §2): what an in-place function
  -- leaves behind is stated by running it on a copy inside the statement ...
  def PostCopy (x : &Nat) (y : Nat) : Le(*x, (let c = *x; AddM(&c, y); c)) := LeAdd(*x, y)

  -- ... since a type is formed before the body runs: here `Le(*x, *x)` is about the entry
  -- value, and the proof about the value `AddM` leaves does not match it.
  reject def PostInBody (x : &Nat) (y : Nat) : Le(*x, *x) := (
    let old = clone(*x);
    AddM(&*x, y);
    LeAdd(old, y)
  )

  -- ... it is not about `S(old)` ...
  reject def AddSubWrong (x : &Nat) (y : Nat) : Unit := (
    let old = clone(*x);
    AddM(&*x, y);
    SubM(x, S(old), LeAdd(old, y))
  )

  -- The induction hypothesis may also be about the predecessor in place (a borrow into
  -- `*x`): it is then an equation between two successors, while `SubM` has already removed
  -- the `S` from the goal, and `Eq` takes the successors apart (injectivity, D52).
  def AddSubIdReborrow (x : &Nat) (y : Nat) : Id(Unit, AddSub(x, y), *x := y) by x := (
    match *x {
      Z => refl,
      S p => AddSubId(&p, y),
    }
  )

  -- `match h {}` needs `h`'s type to compute to an inductive type with no constructors; a
  -- type that is still stuck (`Le(a, b)` for abstract `a`) is an error (D49).
  reject def Neutral (a : Nat) (b : Nat) (h : Le(a, b)) : Nat := match h {}

  -- Every proof is `⋆` at a definition's generic call, so sealed programs that differ only
  -- in the proof they carry are equal (D27).
  def LeId (a : Nat) (b : Nat) (h : Le(a, b)) : Le(a, b) := h

  def ProofIrr (x : &Nat) (y : Nat) (h : Le(y, *x)) :
      Id(Unit, SubM(x, y, h), let h2 = LeId(y, *x, h); SubM(x, y, h2)) := refl

  -- A proof argument may read the state that an earlier argument has lent out, because
  -- proofs run on a private copy (like Rust's two-phase borrows) ...
  def LeZero (b : Nat) : Le(0, b) := refl
  def TwoPhase (x : &Nat) : Unit := SubM(&*x, 0, LeZero(*x))

  -- ... but not after the borrow was moved into the call.
  reject def TwoPhaseMoved (x : &Nat) : Unit := SubM(x, 0, LeZero(*x))
}

-- the exact number of declarations (a truncated file changes it)
#guard CurrentState.decls.length == 16
