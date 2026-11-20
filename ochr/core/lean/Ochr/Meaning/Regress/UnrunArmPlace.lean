import Ochr.Examples.Nat
import Ochr.Examples.List

/-!
# An ill-typed place in an arm the checker does not run is dropped at its parent (built)

docs/31 D41 (fifth lead, 2026-11-21). A match on a known constructor runs only its arm; the other
arms are read for their moves (`Decide.jdMoves`) but never checked. A place there can be ill-typed:
a field index its constructor does not have (`(c.0).5`, `In` has two fields), or `*` of a place that
is not a borrow (`*(c.0)`). `jdMoves` keeps it (`jdGrain` checks only that a field step is through
a type with one constructor), and at the join `Machine.movedPlace` re-roots it to its parent `c.0`,
which holds a constructor value: the join drops `c.0` whole. The reference's drop of a place that
does not exist does nothing (`Run.dropAt`). So the drop's statement (`joinDrop_step_stmt`) is false
on `BadIdx`'s join with the grain as first stated, and the grain as restated in D41 (a field index
the constructor has, `*` through a borrow type, `Steps.GrainOk`) is not what `jdMoves` provides.

The checker is the more conservative side (it drops more), so nothing is accepted that should not
be: `BadIdxRead` and `BadDerefRead` are rejected because `c.0` was dropped, where `GoodIdxRead` (a
well-typed move of `(c.0).0`) is accepted.
-/

open Ochr.Test

ochr UnrunArmPlace uses Nats, Lists {
  inductive In := MkIn(a : List(Nat), b : List(Nat))
  inductive Out := MkOut(i : In, z : List(Nat))
  -- accepted: the join drops `c.0` for `(c.0).5`, which nothing reads afterwards
  def BadIdx (xs : List(Nat)) (ys : List(Nat)) (zs : List(Nat)) : Unit := (
    let k = Z;
    let c = MkOut(MkIn(xs, ys), zs);
    match k { Z => (), S m => (let a = (c.0).5; ()) };
    ())
  reject def BadIdxRead (xs : List(Nat)) (ys : List(Nat)) (zs : List(Nat)) : List(Nat) := (
    let k = Z;
    let c = MkOut(MkIn(xs, ys), zs);
    match k { Z => (), S m => (let a = (c.0).5; ()) };
    (c.0).1)
  reject def BadDerefRead (xs : List(Nat)) (ys : List(Nat)) (zs : List(Nat)) : List(Nat) := (
    let k = Z;
    let c = MkOut(MkIn(xs, ys), zs);
    match k { Z => (), S m => (let a = (*(c.0)).0; ()) };
    (c.0).1)
  -- control: a well-typed move of `(c.0).0` drops only it
  def GoodIdxRead (xs : List(Nat)) (ys : List(Nat)) (zs : List(Nat)) : List(Nat) := (
    let k = Z;
    let c = MkOut(MkIn(xs, ys), zs);
    match k { Z => (), S m => (let a = (c.0).0; ()) };
    (c.0).1)
}
