import Ochr.Examples.E4

/-! # E6: programs and proofs that must be rejected (RULES-v0 §8), with their accepted repairs

`Eq Nat 0 1` plays the role of `⊥` (v1 has no empty proposition; a closed proof of
it is what an unsoundness looks like). -/

open Ochr.Test

ochr E6 {
  def AddM (x : &Nat) (y : Nat) : Unit by x :=
    match *x { Z => *x := y | S p => AddM(&p, y) }

  -- (a) use of a moved borrow
  reject def UseMoved (x : &Nat) : Unit := AddM(x, 0); AddM(x, 0)
  def UseReborrowed (x : &Nat) : Unit := AddM(&*x, 0); AddM(x, 0)
  -- v1.3 (P2, D26): a proof, argument evaluation included, runs on a private copy,
  -- so citing a lemma on x does not move x (under v1 this was rejected)
  def AddMZero (x : &Nat) : Id Unit (AddM(x, 0)) () by x :=
    match *x { Z => refl | S p => AddMZero(&p) }
  def LemmaMoves (x : &Nat) : Unit := let h = AddMZero(x); AddM(x, 0)

  -- (b) a proof formed after a mutation, checked against the entry goal
  reject def WriteThenRefl (x : &Nat) : Id Nat (*x) 5 := *x := 5; refl
  reject def WriteThenRefl' (x : &Nat) : Id Nat (*x) 5 := *x := 5; (refl : Id Nat (*x) 5)

  -- (c) Id Nat Z (S Z) has no proof
  reject def ZeroIsOne : Id Nat 0 1 := refl

  -- (d) adding 0 and adding 1 in place are different
  reject def Add01 (x : Nat) : Id Unit (AddM(&x, 0)) (AddM(&x, 1)) by x :=
    match x { Z => refl | S p => Add01(p) }

  -- the negation is provable, by the same induction (deriver-e346 §E6.4); the S arm
  -- needs Nat injectivity, which v1 dropped (D16), so we state it on the successor
  -- and use a borrow so that the environment does the congruence
  def NotAdd01 (x : &Nat) (h : Id Unit (AddM(x, 0)) (AddM(x, 1))) : Eq Nat 0 1 by x :=
    match *x { Z => h | S p => NotAdd01(&p, h) }

  -- a type formed before a mutation is still about the value it saw (E6.5, D2)
  def Snapshot (x : Nat) : Id Nat x x := let h = (refl : Id Nat x x); x := S x; h
  reject def SnapshotLie (x : Nat) : Eq Nat 0 1 :=
    match x { Z => let h = (refl : Id Nat x 0); x := S x; (h : Id Nat x 0) | S _ => Snapshot(0) }

  -- (E6.6) returning a borrow of a local
  reject def DanglingLocal (u : Unit) : &Nat := let z = 0; &z
  def TailM (x : &Nat) : &Nat by x := match *x { Z => x | S p => TailM(&p) }
  reject def DanglingTail (n : Nat) : &Nat := let z = n; TailM(&z)
  reject def DanglingReborrow (z : Nat) : &Nat := let r = &z; &*r
}

#eval IO.println (run "E6" E6).show

-- every verdict as expected, and exactly 16 assertions (a truncated file changes the count)
#guard (run "E6" E6).allAsExpected
#guard (run "E6" E6).count == 16
