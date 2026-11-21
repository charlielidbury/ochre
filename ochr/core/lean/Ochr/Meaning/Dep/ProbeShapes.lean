-- The five shapes D112 rejects, each with its rewrite (self-contained, uses Nats). Verdicts re-checked on
-- main 59e9bee7 (D112 landed); every one, rejected shape and rewrite, was accepted on main before D112.
-- Not imported by any library root.
import Ochr.Examples.Nat
open Ochr.Test

-- 1. Reading a leaf after its index changed. Rewrite: take the leaf out first.
ochr Shape1 uses Nats {
  inductive Bit := B0 | B1
  def Payload (b : Bit) : Type := match b { B0 => Nat, B1 => Unit, }
  inductive Tagged := MkT(b : Bit, x : Payload(b))
  reject def ReadAfter (p : &Tagged) : Nat := match *p { MkT(b, x) => match b { B0 => (b := B1; let old = x; x := (); old), B1 => 0, }, }
  def TakeFirst (p : &Tagged) : Nat := match *p { MkT(b, x) => match b { B0 => (let old = x; b := B1; x := (); old), B1 => 0, }, }
}
-- 2. Writing a leaf before its index. Rewrite: write the index first.
ochr Shape2 uses Nats {
  inductive Bit := B0 | B1
  def Payload (b : Bit) : Type := match b { B0 => Nat, B1 => Unit, }
  inductive Tagged := MkT(b : Bit, x : Payload(b))
  reject def PayloadFirst (p : &Tagged) : Unit := match *p { MkT(b, x) => (x := (); b := B1), }
  def TagFirst (p : &Tagged) : Unit := match *p { MkT(b, x) => (b := B1; x := ()), }
}
-- 3. A borrow of a leaf used after its index changed. Rewrite: use the borrow first.
ochr Shape3 uses Nats {
  inductive Bit := B0 | B1
  def Payload (b : Bit) : Type := match b { B0 => Nat, B1 => Unit, }
  inductive Tagged := MkT(b : Bit, x : Payload(b))
  reject def UseAfter (p : &Tagged) : Unit := match *p { MkT(b, x) => match b { B0 => (let r = &x; b := B1; *r := 5; x := ()), B1 => (), }, }
  def UseBefore (p : &Tagged) : Unit := match *p { MkT(b, x) => match b { B0 => (let r = &x; *r := 5; b := B1; x := ()), B1 => (), }, }
}
-- 4. A number parked in a field whose type is a data type at every instance. Rewrite: leave it moved out.
ochr Shape4 uses Nats {
  inductive Void : Type
  inductive One := O
  def Fin1 (n : Nat) : Type := match n { Z => Void, S(m) => One, }
  inductive V := MkV(n : Nat, x : Fin1(n))
  reject def Park (v : &V) : Unit := match *v { MkV(n, x) => (let old = x; x := 5; x := old), }
  def NoPark (v : &V) : Unit := match *v { MkV(n, x) => (let old = x; x := old), }
}
-- 5. A proof read after a match one of whose arms writes its index. Rewrite: read it before.
ochr Shape5 uses Nats {
  inductive PosN := MkPosN(n : Nat, h : Eq(Nat, n, 1))
  reject def ReadProofAfter (c0 : PosN) : Unit := (let c = c0; match c { MkPosN(n, h) => (match S(Z) { Z => (n := n; ()), S(m) => (), }; let h2 = h; ()), }; ())
  def ReadProofBefore (c0 : PosN) : Unit := (let c = c0; match c { MkPosN(n, h) => (let h2 = h; match S(Z) { Z => (n := n; ()), S(m) => (), }; ()), }; ())
}
def showShapes : IO Unit := do
  let blocks : List (String × Ochr.Surface.Block) := [("Shape1", Shape1), ("Shape2", Shape2), ("Shape3", Shape3), ("Shape4", Shape4), ("Shape5", Shape5)]
  for (n, b) in blocks do
    for r in (run n b).rows do
      match r.verdict with
      | Ochr.Verdict.rejected m _ => IO.println s!"{n}.{r.name}: rejected: {m}"
      | Ochr.Verdict.accepted => IO.println s!"{n}.{r.name}: accepted"
      | Ochr.Verdict.undecided m => IO.println s!"{n}.{r.name}: undecided {m}"
#eval showShapes
