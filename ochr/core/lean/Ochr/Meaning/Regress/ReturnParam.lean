import Ochr.Meaning.Steps.Records
import Ochr.Examples.Nat

/-!
# A callee that returns its borrow parameter: the result is a fresh label (docs/31 D69, main's D99)

`IdP (x : &Nat) : &Nat := x` and `let y = 2; let r = IdP(&y); *r := 5; y` are accepted. Before main's
D99 the checker's result after the call was the borrow `0` the argument `&y` made BEFORE the call
(`y ↦ lent_0 loan_0`, `r ↦ borrow_0 2`), while the reference's `callOf` returns a fresh label
(`Steps.callOfL_ref_label`), so any renaming relating the two states sent `0` to a label that did not
exist before the call, against part (a)'s renaming condition (`result_not_old`). D99 (decided by the
lead): a borrow-returning call returns the fresh borrow it reserves, the body's returned borrow ended
into it. Now the checker holds `y ↦ lent_1 loan_1`, `r ↦ borrow_1 2`: the result is the reserved
label `1` and the argument's `0` occurs nowhere, as in `callOf` and in the reference's in-place
mirror (`CallRef.runCallRef`).

A second record: `Pick2 (a : &Nat) (b : &Nat) : &Nat := &*a` lends its result at `b`'s lender too
(the reserved label's marks at every borrow argument's lender): reading `y` ends `r`.
-/

open Ochr.Test

ochr ReturnParam uses Nats {
  def IdP (x : &Nat) : &Nat := x
  def UseIdP (u : Unit) : Nat := (let y = 2; let r = IdP(&y); *r := 5; y)
}

-- A callee whose result reborrows one of two borrow arguments: the result is lent at both lenders
-- (the checker's marks `lent_g` at every borrow argument's lender, handed to the result), so reading
-- `y` ends `r` though `r` points into `x` (`UsePick2Read`, rejected)
ochr ReturnPick uses Nats {
  def Pick2 (a : &Nat) (b : &Nat) : &Nat := &*a
  def UsePick2 (u : Unit) : Nat := (let x = 1; let y = 2; let r = Pick2(&x, &y); *r := 5; x)
  reject def UsePick2Read (u : Unit) : Nat := (let x = 1; let y = 2; let r = Pick2(&x, &y); let z = clone(y); *r := 5; x)
}

#guard_msgs (drop warning) in
ochr ReturnParamAt uses Nats {
  def IdP (x : &Nat) : &Nat := x
  def UseIdPAt (u : Unit) : Nat := (let y = 2; let r = IdP(&y); ?)
  def Pick2 (a : &Nat) (b : &Nat) : &Nat := &*a
  def UsePick2At (u : Unit) : Nat := (let x = 1; let y = 2; let r = Pick2(&x, &y); ?)
}

namespace Ochr.Meaning.Regress.ReturnParam
open Ochr Ochr.Meaning

def atHole (name : String) : List Value :=
  let r := Ochr.Test.runWith (some Prelude) "ReturnParamAt" ReturnParamAt (located := true)
  match r.rows.find? (·.name == name) with
  | some row => (row.trace.toList.filterMap fun
      | .note _ _ (.hole _ Ω) => some (Ω.map (·.2.2)) | _ => none).headD []
  | none => []

-- The checker's state after the call (D99): `r` holds the reserved label `1`; `&y`'s `0` is gone.
#guard (atHole "UseIdPAt").map Value.pp == ["()", "lent_1 loan_1", "borrow_1 2"]

-- After `Pick2(&x, &y)` (D99): `r`'s borrow is the reserved `2` (the body's reborrow `3` ended into
-- it), lent at `x` and, by the mark, at `y`. The reference's in-place run lends its result every
-- place a borrow argument lent before the call (`CallRef.runCallRef`), as `callOf` does.
#guard (atHole "UsePick2At").map Value.pp == ["()", "lent_2 loan_2", "lent_2 2", "borrow_2 1"]

/-- **No renaming that agrees before the call relates the result** (the reference's side): the
result of `callOf`'s `.ref` row is a label no state before the call had issued, so it is not the
image of the checker's result label `0` under a renaming that keeps `0`'s image from before the call,
which is below the reference's counter (`Rel.fresh`). -/
theorem result_not_old.{u} (Lv : Lvl.{u}) {C : Type u} (t : Tel Lv.Code PUnit C) (fv : Sem) (args : List Res)
    {s s' : SState} {res : Res} (h : callOfL Lv t fv args s = some (res, s'))
    {U : Type u} {c : Lv.Code U} {fwd : U} {back : U → List Sem}
    (happ : applyFnL Lv t fv (args.map (·.1)) = some (.ref U c fwd back))
    (π : Nat → Nat) (l : Nat) (hl : π l < s.nextLoan) : res.2.label ≠ some (π l) := by
  rw [Steps.callOfL_ref_label Lv t fv args h happ]
  intro he
  injection he with he
  omega

end Ochr.Meaning.Regress.ReturnParam
