import Ochr.Examples.DependentFields
open Ochr.Test

-- dependent fields around a block whose entry now comes before its arms (D91)
ochr DFP uses DepFields {
  -- the entry ends `r`, a borrow of the index field through which a lie was written; the lie
  -- is still caught where `*v` must be whole again
  reject def LieThenBlock (k : Nat) (v : &V) : Unit := (
    let r = match *v { MkV(n, x) => &n, };
    *r := Zero;
    match k { Z => (let z = clone(*v); ()), S _ => () };
    ()
  )
  -- twin: a borrow of the dependent field, written nothing
  def LieThenBlockOk (k : Nat) (v : &V) : Unit := (
    let r = match *v { MkV(n, x) => &x, };
    match k { Z => (let z = clone(*v); ()), S _ => () };
    ()
  )
  -- an arm's lie, as D72's LieSeq, behind a borrow the entry ends
  reject def LieArm (k : Nat) (v : &V) : Unit := (
    let r = &*v;
    match k { Z => (match *v { MkV(n, x) => n := Zero, }; ()), S _ => () };
    ()
  )
  -- the J form of the arm's lie
  def MN (z : Nat) : Type := Unit
  reject def LieJ (m : Nat) (h : Eq(Nat, m, Z)) (v : &V) : Unit := (
    let r = &*v;
    J(Nat, m, Z, MN, h, (match *v { MkV(n, x) => n := Zero, }; ()))
  )
}
