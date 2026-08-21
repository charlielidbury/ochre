import Dllbc.Program
import Dllbc.ProgMacro
import Dllbc.Boundary
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.Tests.Diff

/-!
# `Dllbc.Tests.AuditFold`

Tests the exit audit re-typing a dependent pack whose array component has been
carved into segments. A `&mut` to a `Σ0 (a : Array n T). P a` pack is
destructured, the array is carved, every borrow is returned, and the pack is
rebuilt from the entry proof. Nothing was written, so the audit must accept —
which requires it to see through the segment node (segments deliberately do not
auto-collapse, so the borrow machinery can see carves) and instantiate the
dependent tail at the array the segments concatenate back to.
-/

open Dllbc
open Dllbc.StdLemmas (LeAddRaw SortedA)

namespace Dllbc.Tests.AuditFold

/-! ## (i) The pack, and the fn that carves it

    `Σ0 (a : Array n Nat). SortedA n a`: a runtime array with an erased
    invariant in the tail. `SortedA` is an `arrRec`, so on a symbolic array it is
    a stuck neutral, which makes the tail asymmetric and the test honest — a
    predicate that converts with itself regardless of argument would pass with
    no fold at all. -/

/-- The identity on the invariant, so the repack's tail is an application (a
    ⇝-position) rather than a bare comptime binder, which the erasure fence
    refuses to ⇒-move. -/
def SortedAId : Term := prog defer_check {
  λ (N : Nat). λ (A : Array N Nat). λ (H : SortedA N A). H }

/-- The acceptance test: carve the pack's array three ways, return every
    borrow, repack inline from the entry clause. No callee, no write. -/
def packCarveRepack : Term := prog{
  fn Touch (n : Nat, i : Nat, r : Nat, hd : Id Nat n (Add i (S r)),
            self : &mut (Σ0 (a : Array n Nat). SortedA n a)) -> Unit {
    let Pair(arr, HS) = *self;
    let SL0 = arr;
    let sb = &m arr;
    let pre = &m (*sb)[Z ; i ; S r | LeAddRaw i (S r) | hd];
    let cell = &m (*sb)[i ; 1 ; r];
    let hic = &m (*sb)[S i ; r];
    *self := Pair(arr, SortedAId n SL0 HS);
    () };
  () }

example : progOk packCarveRepack = true := by native_decide

/-- The baseline: the same round-trip with no carve, to isolate that the case
    under test is about the carve and not about packs in general. -/
def packRepackNoCarve : Term := prog{
  fn Touch (n : Nat, self : &mut (Σ0 (a : Array n Nat). SortedA n a)) -> Unit {
    let Pair(arr, HS) = *self;
    let SL0 = arr;
    *self := Pair(arr, SortedAId n SL0 HS);
    () };
  () }
example : progOk packRepackNoCarve = true := by native_decide

/-! ## (ii) The control: the equation is definitional

    Over a local owned array. The carve's own `refineSym` rewrites the leaf's
    array to the `arrCat` spine of its pieces, so "the whole is the composition
    of its segments" is not a lemma here — it is the same term, definitionally.
    This isolates the audit's bridge-taking as the thing under test, rather than
    the equation itself. -/

def carveRejoinEq : Term := prog{
  fn Touch (n : Nat, i : Nat, r : Nat, hd : Id Nat n (Add i (S r)),
            a : Array n Nat) -> Unit {
    let SL0 = a;
    let sb = &m a;
    let pre = &m (*sb)[Z ; i ; S r | LeAddRaw i (S r) | hd];
    let cell = &m (*sb)[i ; 1 ; r];
    let hic = &m (*sb)[S i ; r];
    let L0 = *pre;
    let C0 = *cell;
    let H0 = *hic;
    let Heq = (Refl : Id (Array n Nat) SL0 (arrCat i (S r) L0 (arrCat 1 r C0 H0)));
    () };
  () }
example : progOk carveRejoinEq = true := by native_decide

/-! ## (iii) The negative controls — what the fold must still refuse

    Two ways for the same program to be wrong, failing at two different places.
    `packCarveHole` takes a segment's value away and never puts it back: the
    carve does not rejoin, the fold cannot close it, and the hole hunt catches
    it. `packCarveWrite` rejoins perfectly — the fold succeeds — but the audit
    refuses anyway, because the array it folds to is not the one the entry
    clause is about. Together they confirm the fold only widens acceptance for
    the true no-op case, not more. -/

/-- A genuinely un-rejoined hole: the middle segment is moved out and not
    refilled. -/
def packCarveHole : Term := prog defer_check {
  fn Touch (n : Nat, i : Nat, r : Nat, hd : Id Nat n (Add i (S r)),
            self : &mut (Σ0 (a : Array n Nat). SortedA n a)) -> Unit {
    let Pair(arr, HS) = *self;
    let SL0 = arr;
    let sb = &m arr;
    let pre = &m (*sb)[Z ; i ; S r | LeAddRaw i (S r) | hd];
    let cell = &m (*sb)[i ; 1 ; r];
    let hic = &m (*sb)[S i ; r];
    let stolen = *cell;
    *self := Pair(arr, SortedAId n SL0 HS);
    () };
  () }
example : progRejects packCarveHole
  "holds a hole (⊥) at return, in a leaf it still owns" = true := by native_decide

/-- The carve rejoins and the fold succeeds, yet the pack is still refused,
    because a `7` was written into the cell and the entry clause is about the
    array that was there before. Confirms the fold only lets the audit *state*
    what the array is — it does not make the audit vacuous. -/
def packCarveWrite : Term := prog defer_check {
  fn Touch (n : Nat, i : Nat, r : Nat, hd : Id Nat n (Add i (S r)),
            self : &mut (Σ0 (a : Array n Nat). SortedA n a)) -> Unit {
    let Pair(arr, HS) = *self;
    let SL0 = arr;
    let sb = &m arr;
    let pre = &m (*sb)[Z ; i ; S r | LeAddRaw i (S r) | hd];
    let cell = &m (*sb)[i ; 1 ; r];
    let hic = &m (*sb)[S i ; r];
    *cell := Arr(7);
    *self := Pair(arr, SortedAId n SL0 HS);
    () };
  () }
example : progRejects packCarveWrite "does not have its owed type" = true := by native_decide

/-! ## (iv) The fence, at the value level

    Asserted directly on `subsKnowledge` rather than through a program: a
    segment list whose bodies are all owned contributes its `arrCat` spine, and
    one with a live loan in it still contributes `@stateComponent`. The
    loan case is deliberately not fixed here — it needs the opaque-fill rule,
    not a fold. -/

/-- A rejoined two-way carve: both bodies are owned values, so the fold
    closes. -/
def segsRejoined : Val :=
  .node "§segs" [Val.segNode (Term.nat 1) (Val.sym 0), Val.segNode (Term.nat 2) (Val.sym 1)]

/-- The same carve with one segment still out on loan. -/
def segsSuspended : Val :=
  .node "§segs" [Val.segNode (Term.nat 1) (Val.sym 0), Val.segNode (Term.nat 2) (.loanM 0)]

example : Term.beq (subsKnowledge segsRejoined)
  prog defer_check { arrCat 1 2 %(Term.sym 0) %(Term.sym 1) } = true := by native_decide

example : Term.beq (subsKnowledge segsSuspended) (.const "@stateComponent") = true := by
  native_decide

/-- The store is untouched by the projection: `subsKnowledge` is a typing-time
    view only, and `Val.ctor`'s refusal to collapse a `§segs` node is what the
    borrow machinery depends on. Asserted directly, since a fix that instead
    folded the carve in the value representation would pass every test above. -/
example : Val.beq (Val.ctor "§segs" [Val.segNode (Term.nat 1) (Val.sym 0),
                                     Val.segNode (Term.nat 2) (Val.sym 1)])
                  segsRejoined = true := by native_decide

end Dllbc.Tests.AuditFold
