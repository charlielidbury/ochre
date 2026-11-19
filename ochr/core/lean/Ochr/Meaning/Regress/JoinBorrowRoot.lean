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

Kernel-checked: the drop at a root holding a borrow ends that borrow and accesses nothing it lends
(`dropAt_borrow_root`).
-/

open Ochr.Test

ochr JoinBorrowRoot uses Nats {
  -- REJECTED since main's D90: the match is not in tail position, and its entry accesses what the
  -- stuck block would capture, `r` by move (arm `Z` reads it whole), which ends `s` before the
  -- arm runs, on every path (D90's known gap `EK` against Rust). The finding it carried stands:
  -- the join's drop of a borrow root ends that borrow only (`dropAt_borrow_root`).
  reject def RJ (a : Nat) (b : Nat) : Nat := (
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

variable (K : RunCtx) (φ : Future)

/-- The fix, in the static form (docs/31 D29): at a root holding a borrow, the drop ends that
borrow and accesses nothing it lends, as `Machine.dropAtJoin` does. (The first form of the fix,
`joinAccess`, skipped the reference's access by dependence at such a root; the access by
dependence went with the early ends, and with it the record `old_access_depends` that the old
access of a root reading a reborrow's label depended on that label.) -/
theorem dropAt_borrow_root (q : Place) (s : SState) (pos : Pos) (l : Nat) (hs : s.shape pos = some l)
    (v : Sem) (T : TyS) (hv : v ≠ .proof ∧ v ≠ .moved)
    (hf : Sem.follow K.dm K.Γ (s.tyAt pos) (s.valAt pos (s.closedFuture φ)) [] = some (v, T)) :
    dropAt K φ q pos [] s = s.endLabel l := by
  unfold dropAt
  rw [hf]
  rcases hv with ⟨h1, h2⟩
  cases v <;> simp_all

end Ochr.Meaning.Regress.JoinBorrowRoot
