import Ochr.Meaning.Steps.Statements
import Ochr.Examples.Nat

/-!
# The read of a place: pins (lead26, 2026-11-22; docs/31 D181)

**A borrow whose content is partly moved out is read (moved) by the checker** (FINDING, ruling asked). `MB2`
moves `x`'s first field out through `r` (D53 (h): allowed if the content is whole again when the borrow ends),
then reads `r` whole (`let r2 = r`, a move of the borrow), then makes the content whole through `r2`: ACCEPTED.
`readPlace`'s borrow branch moves a borrow before its `hasHole` check, which every other value meets ("[Read] …
was partly moved out", D53). The reference reads a borrow as its content (`meanV`'s `.borrow` clause), and its
`readPlace` returns nothing for a value that is not whole (`Sem.whole`: a record with a `moved` field is not), so
its run of `MB2`'s body fails at `r`: the typed place step is FALSE as the two stand (by reading the reference,
which is not computable; the checker's verdicts are pinned here). `MB1` (the content restored through `r` itself)
and `MB3` (the borrow ends partly moved: rejected) are the controls.
-/

open Ochr.Test

ochr PlaceMB uses Nats {
  inductive Box := MkBox(n : Nat)
  def MB1 (a : Nat) (b : Nat) : Unit := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; *r := (MkBox(Z), Z); ())
  def MB2 (a : Nat) (b : Nat) : Unit := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; let r2 = r; *r2 := (MkBox(Z), Z); ())
  reject def MB3 (a : Nat) (b : Nat) : Unit := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; let r2 = r; ())
}

-- TODAY: `MB2` is accepted (the pin flips if the checker rejects reading a partly moved borrow)
#guard (Ochr.Test.runWith (some Prelude) "PlaceMB" PlaceMB {} (located := false)).allAsExpected
