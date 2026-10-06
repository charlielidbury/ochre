import Ochr.Examples.«00Std»
open Ochr Ochr.Test
/-! A2 (reviewer-6): conversion compares Π-types at the generic call, where a borrow
parameter borrows one fresh place, but an argument such as `Pick(n, &a, &b)` has two possible
owners, so the codomain at it is a conjunction over both. Can two Π-types that are
convertible generically be told apart at an instance, in a way that proves `False` or lets a
program go wrong? These are the attempts. -/
ochr A2Probe uses Std, Fixtures {
  -- reviewer-6's programs
  def CP (h : Π(x : &Nat). False) : (Π(x : &Nat). Id(Unit, *x := 0, *x := 1)) := h
  reject def CPuse (h : Π(x : &Nat). Id(Unit, *x := 0, *x := 1)) (n : Nat) (a : Nat) (b : Nat) : False := (
    let r = Pick(n, &a, &b); h(r))
  def CPuse2 (h : Π(x : &Nat). False) (n : Nat) (a : Nat) (b : Nat) : False := (
    let r = Pick(n, &a, &b); h(r))

  -- The other direction: a codomain that is ⊤ generically (both sides leave the one owner
  -- at 1) but, at a two-owner argument, a conjunction of equations between different sealed
  -- programs. It is provable, so an exploit would have to refute that conjunction without
  -- splitting `n`.
  def TopGen : (Π(x : &Nat). Id(Unit, *x := 0; *x := 1, *x := 1)) :=
    λ(x : &Nat) : Id(Unit, *x := 0; *x := 1, *x := 1) => refl
  def TopConv (h : Π(x : &Nat). ⊤) : (Π(x : &Nat). Id(Unit, *x := 0; *x := 1, *x := 1)) := h
  -- the instance normalises to ⊤ even at an abstract `n` (the overwritten write drops out) ...
  def TopAtPick (n : Nat) (a : Nat) (b : Nat) : ⊤ := (let r = Pick(n, &a, &b); TopGen(r))
  -- ... so there is nothing to refute: the instance is ⊤ as a type
  reject def RefuteL (n : Nat) (a : Nat) (b : Nat) : False := (
    let r = Pick(n, &a, &b);
    let h = TopGen(r); match h { Intro(l, k) => l })
  def TopAt0 (a : Nat) (b : Nat) : ⊤ := (let r = Pick(0, &a, &b); TopGen(r))

  -- A codomain proved by recursion (`AddMZero`) stays a stuck conjunction at a two-owner
  -- argument: one equation per owner, between sealed programs.
  def G5 : (Π(x : &Nat). Id(Unit, AddM(x, 0), ())) := λ(x : &Nat) : Id(Unit, AddM(x, 0), ()) => AddMZero(x)
  reject def G5Top (n : Nat) (a : Nat) (b : Nat) : ⊤ := (let r = Pick(n, &a, &b); G5(r))
  -- Neither conjunct can be refuted: its sides are sealed programs, with no constructor for
  -- disjointness (D47) or injectivity (D52), so a zero-arm match on it is stuck (D58).
  reject def G5RefuteL (n : Nat) (a : Nat) (b : Nat) : False := (
    let r = Pick(n, &a, &b);
    let h = G5(r); match h { Intro(l, k) => match l {} })
  reject def G5RefuteR (n : Nat) (a : Nat) (b : Nat) : False := (
    let r = Pick(n, &a, &b);
    let h = G5(r); match h { Intro(l, k) => match k {} })
  -- At a ground `n` the instance is the generic codomain at the real owner (the other owner
  -- is untouched on both sides, so its conjunct is ⊤ and drops out).
  def G5At0 (a : Nat) (b : Nat) : Id(Unit, AddM(&a, 0), ()) := (let r = Pick(0, &a, &b); G5(r))
  def G5At1 (a : Nat) (b : Nat) : Id(Unit, AddM(&b, 0), ()) := (let r = Pick(1, &a, &b); G5(r))

  -- Constructor heads: writes of whole pairs versus field by field agree generically; at a
  -- two-owner argument each owner's content is again a sealed program, with no head.
  def PickP (n : Nat) (x : &(Nat × Nat)) (y : &(Nat × Nat)) : &(Nat × Nat) := match n { Z => x, S _ => y }
  def PairGen : (Π(x : &(Nat × Nat)). Id(Unit, *x := (0, 0), *x := (0, 1); *x := (0, 0))) :=
    λ(x : &(Nat × Nat)) : Id(Unit, *x := (0, 0), *x := (0, 1); *x := (0, 0)) => refl
  reject def PairRefute (n : Nat) (a : Nat × Nat) (b : Nat × Nat) : False := (
    let r = PickP(n, &a, &b);
    let h = PairGen(r); match h { Intro(l, k) => l })
  -- A read through the argument: generically the result is the one owner's value; at a
  -- two-owner argument it is a sealed read.
  def ReadGen : (Π(x : &Nat). Id(Nat, *x := 3; clone(*x), *x := 3; 3)) :=
    λ(x : &Nat) : Id(Nat, *x := 3; clone(*x), *x := 3; 3) => refl
  def ReadAt (n : Nat) (a : Nat) (b : Nat) : Nat := (let r = Pick(n, &a, &b); let h = ReadGen(r); 0)
  reject def ReadRefute (n : Nat) (a : Nat) (b : Nat) : False := (
    let r = Pick(n, &a, &b);
    let h = ReadGen(r); match h { Intro(l, k) => l })
}
#eval IO.println (run "A2Probe" A2Probe).show
#guard (run "A2Probe" A2Probe).allAsExpected
#guard (run "A2Probe" A2Probe).count == 20
