import Ochr.Examples.Nat
import Ochr.Examples.List

/-!
# The lead's checks 2 and 3 for D66 (checker verdicts, asserted by the build)

* Check 2's program: a content partly moved out through a borrow and refilled, a read of another
  variable in between (`PartMove`): accepted. At the read of `q` the reference's closed future fixes
  `r`'s label to a partly moved pair, which is not a typed future; `q`'s read does not depend on that
  label (docs/31 D66, check 2).
* Check 3: an `Id` whose sides move the content out through a borrow a call returned
  (`ObsAfterCall`): accepted, beside the rejected control `ObsAfterCallCtl` (the sides' type-states
  differ) and the plain-borrow twin `ObsAfterBorrow` (accepted); moving through the returned borrow
  inside a side and ending it there is rejected (`ObsInSide`, [D53]). A side that only reads through
  `r` leaves the lender out of the footprint (D68), so neither model observes it; a side that also
  borrows through `r` puts it in (`ObsBorrowThrough`, accepted): the checker's observation reads the
  lender's raw value `lent_k loan_k`, whose meaning at the observation's closed future is the moved
  content, where the reference's `callOf` reads it decoded, `err` (docs/31 D66, check 3).
-/

open Ochr.Test

ochr ObsReturned uses Nats, Lists {
  def IdL (x : &List(Nat)) : &List(Nat) := &*x
  def PartMove (p : Pair(List(Nat), Nat)) (q : Nat) : Nat := (let r = &p; let z = (*r).0; let w = q; (*r).0 := z; w)
  def ObsR (r : &List(Nat)) : Id(Unit, (let z = *r; ()), (let z = *r; ())) := refl
  def ObsAfterCall (y : List(Nat)) : Unit := (let r = IdL(&y); let p : Id(Unit, (let z = *r; ()), (let z = *r; ())) = refl; ())
  reject def ObsAfterCallCtl (y : List(Nat)) : Unit := (let r = IdL(&y); let p : Id(Unit, (let z = *r; ()), ()) = refl; ())
  def ObsAfterBorrow (y : List(Nat)) : Unit := (let r = &y; let p : Id(Unit, (let z = *r; ()), (let z = *r; ())) = refl; ())
  def ObsBorrowThrough (y : List(Nat)) : Unit := (let r = IdL(&y); let p : Id(Unit, (let w = &*r; let z = *r; ()), (let w = &*r; let z = *r; ())) = refl; ())
  reject def ObsInSide (y : List(Nat)) : Id(Unit, (let r = IdL(&y); let z = *r; ()), (let r = IdL(&y); let z = *r; ())) := refl
}
