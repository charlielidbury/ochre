import Ochr.Meaning.Run
import Ochr.Examples.Nat

/-!
# The drop at the join of a borrow variable ends its borrow and nothing it lends (built)

docs/31 D28 (fourth lead, 2026-11-19; found while proving the drop at the join). `Machine.dropAtJoin`
drops a place holding a borrow by ending that borrow: nothing inside its content is accessed, so a
reborrow of part of the content stays live. The reference's `joinDrop` accessed every dropped
place first, observing a borrow variable's whole content, so it ended every borrow that content
lends, the reborrow included. Then a write through the reborrow after the match was lost, and the
model made false a proposition the checker proves.

* `RJ` (accepted): `s` reborrows `(*r).0`; the match on the known `S(Z)` takes the arm that leaves
  `r` alone, and its other arm moves `r`, so the join drops `r`; then `*s := 7` writes through the
  reborrow, `x.0` is read, and `Id(Nat, clone(w), 7)` is proved by `refl`. In the reference as
  first written the join ended `s` when it dropped `r`, the write was lost, and `w` meant `a`.
* `RJRead` (rejected, the control): the arm taken reads `r` whole, which ends `s` ([Access] of
  `r`'s content), and the write through `s` is an error.
* `RJGen` (rejected): at an unknown scrutinee the match is a stuck block taking `r` by move, as a
  read; the write through `s` is an error there too.

Kernel-checked: a position reading a label directly makes the old access of it depend on that
label (`old_access_depends`); `joinAccess`, the fix, accesses nothing at a root holding a borrow
(`joinAccess_borrow_root`).
-/

open Ochr.Test

ochr JoinBorrowRoot uses Nats {
  def RJ (a : Nat) (b : Nat) : Nat := (
    let x = (a, b);
    let r = &x;
    let s = &(*r).0;
    let k = S(Z);
    match k { Z => (let u = r; Z), S m => Z };
    *s := 7;
    let w = x.0;
    let h : Id(Nat, clone(w), 7) = refl;
    w
  )
  reject def RJRead (a : Nat) (b : Nat) : Nat := (
    let x = (a, b);
    let r = &x;
    let s = &(*r).0;
    let k = Z;
    match k { Z => (let u = r; Z), S m => Z };
    *s := 7;
    let w = x.0;
    w
  )
  reject def RJGen (a : Nat) (b : Nat) (k : Nat) : Nat := (
    let x = (a, b);
    let r = &x;
    let s = &(*r).0;
    match k { Z => (let u = r; Z), S m => Z };
    *s := 7;
    let w = x.0;
    w
  )
}

namespace Ochr.Meaning.Regress.JoinBorrowRoot
open Ochr Ochr.Meaning

variable (K : RunCtx)

/-- The access as first written, at a root position whose meaning reads the label `l` (as a
borrow variable's content does where it holds a reborrow's loan), depends on `l`. -/
theorem old_access_depends (s : SState) (pos : Pos) (l : Nat) (hv : s.valAt pos = fun ψ => ψ l) :
    s.obsDep pos (obsAt K (s.tyAt pos).m [] wholeOb) l := by
  refine ⟨fun _ => .proof, .moved, ?_⟩
  simp only [hv, obsAt, Sem.follow, wholeOb, Future.upd_same]
  intro h
  injection h with _ _ h
  injection h with h
  cases h

/-- The fix: at a root holding a borrow, the drop accesses nothing. -/
theorem joinAccess_borrow_root (s : SState) (pos : Pos) (l : Nat) (hs : s.shape pos = some l) :
    joinAccess K s pos [] = s := by
  simp [joinAccess, hs]

end Ochr.Meaning.Regress.JoinBorrowRoot
