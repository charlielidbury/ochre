import Ochr.Examples.Nat
import Ochr.Examples.Logic

/-!
# A read into a dependent field of an open value, made open by a write (built; the checker's verdicts)

docs/31 D32 (fifth lead, 2026-11-20). With `WP := MkWP(n : Nat, x : Pk(n))` and
`Pk(n) := MkPk(a : Fin1N(n), b : Nat)` as in `PartialMoveDep`:

* `OWK` (ACCEPTED): `w = MkWP(S(w0), y)`; the index is rewritten whole, `w.0 := S(S(Z))`, so `w`
  is open (D64): `w.1` holds a `Pk(S(w0))` while its type from the earlier fields is `Pk(2)`; then
  `(w.1).1` is read. The checker types `w.1` by its content.
* `OW`, `OWM` (rejected, the controls): the same at an unknown `w` (a stuck match the arm returns
  open, [Repack]).

The reference decodes `w.1` at the hint its declaration gives at the current earlier fields,
`Pk(2)`, where the value was packed at `Pk(S(w0))`: at `w0 ≠ 1` the two parameter lists differ,
and decoding through equal carriers is not provably the value's own. So reading into an open
value's dependent field is beyond decoding by the position's type, whatever the join does: (WF13)
as restricted to fields after whole earlier fields is FALSE here (the earlier field is whole, the
data disagrees), and tightening the join's drop (D32 option (d)) does not reach this case.
-/

open Ochr.Test

ochr OpenWriteDep uses Nats, Logic {
  inductive One := O
  def Fin1N (n : Nat) : Type := match n { Z => Void, S m => One }
  inductive Pk (n : Nat) := MkPk(a : Fin1N(n), b : Nat)
  inductive WP := MkWP(n : Nat, x : Pk(n))
  def OWK (w0 : Nat) (y : Pk(S(w0))) : Nat := (let w = MkWP(S(w0), y); w.0 := S(S(Z)); let c = (w.1).1; c)
  reject def OW (w : WP) : Nat := (w.0 := S(S(Z)); let c = (w.1).1; c)
  reject def OWM (w : WP) : Nat := (w.0 := S(S(Z)); match w.1 { MkPk(a, b) => b })
}
