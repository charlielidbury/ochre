import Ochr.Examples.Nat
import Ochr.Examples.List

/-!
# The lead's checks 2 and 3 for D66 (checker verdicts, asserted by the build)

* Check 2's program: a content partly moved out through a borrow and refilled, a read of another
  variable in between (`PartMove`): accepted. At the read of `q` the closed future fixed `r`'s label
  to a partly moved pair, which is not a typed future (docs/31 D66, check 2); since D68 the read is
  at the typed future, which gives the label its record, `p`'s pair (`PartMoveRead`, kernel-checked).
* Check 3: an `Id` whose sides move the content out through a borrow and leave it moved when the
  observation ends the borrow. Accepted until main's D98, which removed the observation's exception
  to [End]'s wholeness check ([D53]: a borrow never ends over a moved-out content, in an
  observation's final ends as anywhere); all four are now rejected: through a borrow parameter
  (`ObsR`), a borrow a call returned (`ObsAfterCall`), a plain borrow (`ObsAfterBorrow`), and a side
  that also borrows through the returned borrow (`ObsBorrowThrough`, the witness of D66's check 3:
  the checker's observation read the lender's raw value `lent_k loan_k` as the moved content, where
  the reference's `callOf` reads it decoded, `err`). The control whose sides' type-states differ
  (`ObsAfterCallCtl`) and the move-and-end inside a side (`ObsInSide`) were rejected before and
  still are. So the observation step needs no hypothesis of its own: the observation's ends are
  [End]'s, with its wholeness check.
-/

open Ochr.Test

ochr ObsReturned uses Nats, Lists {
  def IdL (x : &List(Nat)) : &List(Nat) := &*x
  def PartMove (p : Pair(List(Nat), Nat)) (q : Nat) : Nat := (let r = &p; let z = (*r).0; let w = q; (*r).0 := z; w)
  reject def ObsR (r : &List(Nat)) : Id(Unit, (let z = *r; ()), (let z = *r; ())) := refl
  reject def ObsAfterCall (y : List(Nat)) : Unit := (let r = IdL(&y); let p : Id(Unit, (let z = *r; ()), (let z = *r; ())) = refl; ())
  reject def ObsAfterCallCtl (y : List(Nat)) : Unit := (let r = IdL(&y); let p : Id(Unit, (let z = *r; ()), ()) = refl; ())
  reject def ObsAfterBorrow (y : List(Nat)) : Unit := (let r = &y; let p : Id(Unit, (let z = *r; ()), (let z = *r; ())) = refl; ())
  reject def ObsBorrowThrough (y : List(Nat)) : Unit := (let r = IdL(&y); let p : Id(Unit, (let w = &*r; let z = *r; ()), (let w = &*r; let z = *r; ())) = refl; ())
  reject def ObsInSide (y : List(Nat)) : Id(Unit, (let r = IdL(&y); let z = *r; ()), (let r = IdL(&y); let z = *r; ())) := refl
}
