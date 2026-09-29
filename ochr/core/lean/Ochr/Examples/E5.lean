import Ochr.Examples.E4

/-! # E5: dependent types flowing through mutation (RULES v1.4 §7, notes/deriver-e5.md)

A precondition proof about the *current, mutated* `*x` is built from a snapshot with the
pure `Add`: in-place `AddM` and pure `Add` close off into the same sealed program. -/

open Ochr.Test

ochr E5 {
  def AddM (x : &Nat) (y : Nat) : Unit by x := match *x { Z => *x := y | S p => AddM(&p, y) }
  def Add (x : Nat) (y : Nat) : Nat := AddM(&x, y); x

  -- a Prop-valued function (v2.0: False is the library's empty inductive; before, Eq Nat Z (S Z))
  def Le (a : Nat) (b : Nat) : Prop by a :=
    match a { Z => ⊤ | S a' => match b { Z => False | S b' => Le(a', b') } }

  -- a lemma about the pure Add
  def LeAdd (n : Nat) (m : Nat) : Le(n, Add(n, m)) by n :=
    match n { Z => refl | S n' => LeAdd(n', m) }

  -- peel y successors off the top of *x; the precondition survives *x := p, and where *x
  -- is Z but y is not, h : Le(S q, Z) computes to False (v2.0: the paper's version)
  def SubM (x : &Nat) (y : Nat) (h : Le(y, *x)) : Unit by y :=
    match y { Z => () | S q => match *x { Z => match h {} | S p => *x := p; SubM(x, q, h) } }

  -- a proof from the snapshot old, about the mutated *x
  def AddSub (x : &Nat) (y : Nat) : Unit :=
    let old = *x; AddM(&*x, y); SubM(x, old, LeAdd(old, y))

  -- the theorem; the IH is about a copy of the tail (deriver-e5 Q5)
  def AddSubId (x : &Nat) (y : Nat) : Id Unit (AddSub(x, y)) (*x := y) by x :=
    match *x { Z => refl | S p => let c = p; AddSubId(&c, y) }

  -- rejections (deriver-e5 §E5.6): the requirement really is about the current state
  reject def AddSubStale (x : &Nat) (y : Nat) : Unit :=
    let old = *x; AddM(&*x, y); *x := Z; SubM(x, old, LeAdd(old, y))
  reject def AddSubWrong (x : &Nat) (y : Nat) : Unit :=
    let old = *x; AddM(&*x, y); SubM(x, S old, LeAdd(old, y))
  reject def AddSubIdReborrow (x : &Nat) (y : Nat) : Id Unit (AddSub(x, y)) (*x := y) by x :=
    match *x { Z => refl | S p => AddSubId(&p, y) }

  -- deriver-e5 §E5.7 (Q1): proofs are ⋆ at the generic call, so sealed programs that
  -- differ only in the proof they embed are equal (v1.4, D27)
  def LeId (a : Nat) (b : Nat) (h : Le(a, b)) : Le(a, b) := h
  def ProofIrr (x : &Nat) (y : Nat) (h : Le(y, *x)) :
      Id Unit (SubM(x, y, h)) (let h2 = LeId(y, *x, h); SubM(x, y, h2)) := refl

  -- deriver-e5 §E5.8: ex falso into Prop with J (explicit endpoints) and a Prop-valued motive.
  -- (v2.0: h's type computes to False by D47, and `match h {}` does the same job, Logic.absurdP.)
  def ExFalso (G : Prop) (h : Eq Nat Z (S Z)) : G :=
    J(Nat, Z, S Z, λ(n : Nat) : Prop => match n { Z => ⊤ | S _ => G }, h, refl)

  -- deriver-e5 §E5.9 (Q6): a proof argument may read the state an earlier argument
  -- reserved, because it runs on a private copy (two-phase-borrow-like)
  def LeZero (b : Nat) : Le(0, b) := refl
  def TwoPhase (x : &Nat) : Unit := SubM(&*x, 0, LeZero(*x))
  reject def TwoPhaseMoved (x : &Nat) : Unit := SubM(x, 0, LeZero(*x))
}

#eval IO.println (run "E5" E5).show

-- every verdict as expected, and exactly 16 assertions (a truncated file changes the count)
#guard (run "E5" E5).allAsExpected
#guard (run "E5" E5).count == 16
