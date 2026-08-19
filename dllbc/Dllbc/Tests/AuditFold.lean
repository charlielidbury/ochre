import Dllbc.Program
import Dllbc.ProgMacro
import Dllbc.Boundary
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.Tests.Diff

/-!
# `Dllbc.Tests.AuditFold` — re-typing a dependent pack whose array is SEGMENTED

Gap A of `docs/14-packed-borrows.md`, in the smallest program that shows it.

A `&mut` to a pack `Σ0 (a : Array n T). P a` is destructured, its array is CARVED
into three segments, every borrow is returned, and the pack is rebuilt inline from
the entry proof. Nothing is written; the array's value is exactly what it was.
The exit audit must re-type the payload against the pack type, and to do that it
must instantiate the dependent tail `P a` at what the array component *is*.

The array component is a `§segs` node — `Val.ctor` deliberately refuses to
collapse one, so that the borrow machinery can see a carve (M32 R1) — and
`subsKnowledge`, the projection that says what a component contributes to a type,
had no reading for it: it fell to `@stateComponent`, "a name that converts with
nothing". So the tail was demanded at `P @stateComponent` while the entry proof
inhabits `P σ_entry`, and the audit rejected a pack that had never changed.

The equation itself was never in doubt — §(ii)'s control asserts, with an ascribed
`Refl`, that the entry array IS definitionally the `arrCat` of its segments (the
carve's own `refineSym` makes it so). What was missing was the audit taking the ⇝
bridge (`Val.arrFoldDeep`) to get there.
-/

open Dllbc
open Dllbc.StdLemmas (LeAdd SortedA)

namespace Dllbc.Tests.AuditFold

/-! ## (i) The pack, and the fn that carves it

    `Σ0 (a : Array n Nat). SortedA n a` is the flagship's `HashMap` in miniature:
    a runtime array with an erased invariant over it in the tail. `SortedA` is an
    `arrRec`, so on a σ it is a stuck neutral — which is what makes the tail
    ASYMMETRIC and the test honest. A predicate that converted with itself
    regardless of its argument (`Id T a a`, say) would pass with no fold at all. -/

/-- The identity on the invariant, so that the repack's tail is an APPLICATION
    (a ⇝-position) rather than a bare comptime binder, which the erasure fence
    refuses to ⇒-move. This is `MkInv` in miniature: the flagship rebuilds its
    invariant from projections typed at the ENTRY array, and this rebuilds it from
    the entry clause itself, which is the same claim with none of the arithmetic. -/
def SortedAId : Term := prog{
  λ (N : Nat). λ (A : Array N Nat). λ (H : SortedA N A). H }

/-- **THE ACCEPTANCE TEST** (was `s1P2a` on `hm-flagship-fable`, over the real
    `HMInvT`): carve the pack's array three ways, return every borrow, repack
    INLINE from the entry clause. No callee, no write. -/
def packCarveRepack : Term := prog{
  fn Touch (n : Nat, i : Nat, r : Nat, hd : Id Nat n (Add i (S r)),
            self : &mut (Σ0 (a : Array n Nat). SortedA n a)) -> Unit {
    let Pair(arr, HS) = *self;
    let SL0 = arr;
    let sb = &m arr;
    let pre = &m (*sb)[Z ; i ; S r | LeAdd i (S r) | hd];
    let cell = &m (*sb)[i ; 1 ; r];
    let hic = &m (*sb)[S i ; r];
    *self := Pair(arr, SortedAId n SL0 HS);
    () };
  () }

example : progOk packCarveRepack = true := by native_decide

/-- **THE BASELINE**: the same round-trip with NO carve — s1P1's shape. Green
    before the fix and after it, which is what says the fix is about the carve and
    not about packs. -/
def packRepackNoCarve : Term := prog{
  fn Touch (n : Nat, self : &mut (Σ0 (a : Array n Nat). SortedA n a)) -> Unit {
    let Pair(arr, HS) = *self;
    let SL0 = arr;
    *self := Pair(arr, SortedAId n SL0 HS);
    () };
  () }
example : progOk packRepackNoCarve = true := by native_decide

/-! ## (ii) The control: the equation was always definitional

    s1P2c, over a LOCAL owned array. The carve's own `refineSym` rewrites the
    leaf's σ to the `arrCat` spine of its pieces, so "the whole is the composition
    of its segments" is not a lemma here — it is the same term. This was green
    before the fix and is green after it, which is what pins the diagnosis: the gap
    was never the equation, it was the audit not folding its way to it. -/

def carveRejoinEq : Term := prog{
  fn Touch (n : Nat, i : Nat, r : Nat, hd : Id Nat n (Add i (S r)),
            a : Array n Nat) -> Unit {
    let SL0 = a;
    let sb = &m a;
    let pre = &m (*sb)[Z ; i ; S r | LeAdd i (S r) | hd];
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

    Two ways for the same program to be wrong, and they fail at the two different
    places they should. `packCarveHole` takes a segment's value away and never puts
    it back: the carve does not rejoin, the fold cannot close it, and the hole hunt
    says so. `packCarveWrite` rejoins perfectly — the fold SUCCEEDS — and the audit
    refuses anyway, because the array it folds to is not the one the entry clause
    is about. Between them they say the fix widened what can be typed by exactly
    the no-op case and turned the audit into a rubber stamp for nothing. -/

/-- A genuinely un-rejoined hole: the middle segment is moved out and not
    refilled. Red before the fix and after it, at the hole hunt. -/
def packCarveHole : Term := prog defer_check {
  fn Touch (n : Nat, i : Nat, r : Nat, hd : Id Nat n (Add i (S r)),
            self : &mut (Σ0 (a : Array n Nat). SortedA n a)) -> Unit {
    let Pair(arr, HS) = *self;
    let SL0 = arr;
    let sb = &m arr;
    let pre = &m (*sb)[Z ; i ; S r | LeAdd i (S r) | hd];
    let cell = &m (*sb)[i ; 1 ; r];
    let hic = &m (*sb)[S i ; r];
    let stolen = *cell;
    *self := Pair(arr, SortedAId n SL0 HS);
    () };
  () }
example : progRejects packCarveHole
  "holds a hole (⊥) at return, in a leaf it still owns" = true := by native_decide

/-- The carve REJOINS and the fold succeeds — and the pack is still refused,
    because a `7` was written into the cell and the entry clause is about the
    array that was there before. This is the assertion that the fold did not make
    the audit vacuous: the only thing it added is the ability to SAY what the
    array is, and saying it is what exposes the change. -/
def packCarveWrite : Term := prog defer_check {
  fn Touch (n : Nat, i : Nat, r : Nat, hd : Id Nat n (Add i (S r)),
            self : &mut (Σ0 (a : Array n Nat). SortedA n a)) -> Unit {
    let Pair(arr, HS) = *self;
    let SL0 = arr;
    let sb = &m arr;
    let pre = &m (*sb)[Z ; i ; S r | LeAdd i (S r) | hd];
    let cell = &m (*sb)[i ; 1 ; r];
    let hic = &m (*sb)[S i ; r];
    *cell := Arr(7);
    *self := Pair(arr, SortedAId n SL0 HS);
    () };
  () }
example : progRejects packCarveWrite "does not have its owed type" = true := by native_decide

/-! ## (iv) The fence, at the value level

    The scope of the fix, asserted directly on `subsKnowledge` rather than through
    a program: a segment list whose bodies are all OWNED contributes its `arrCat`
    spine, and one with a live loan in it still contributes `@stateComponent`. The
    second is `14-packed-borrows.md`'s Gap B — an escaping borrow leaves a live
    loan inside the pack at the callee's own exit — and it is deliberately NOT
    moved here: that case needs the opaque-fill rule, not a fold. -/

/-- A rejoined two-way carve: both bodies are σ's, so the fold closes. -/
def segsRejoined : Val :=
  .node "§segs" [Val.segNode (Term.nat 1) (Val.sym 0), Val.segNode (Term.nat 2) (Val.sym 1)]

/-- The same carve with one segment still out on loan. -/
def segsSuspended : Val :=
  .node "§segs" [Val.segNode (Term.nat 1) (Val.sym 0), Val.segNode (Term.nat 2) (.loanM 0)]

example : Term.beq (subsKnowledge segsRejoined)
  prog{ arrCat %(Term.nat 1) %(Term.nat 2) %(Term.sym 0) %(Term.sym 1) } = true := by native_decide

example : Term.beq (subsKnowledge segsSuspended) (.const "@stateComponent") = true := by
  native_decide

/-- The store is UNTOUCHED by the projection: `subsKnowledge` is a typing-time
    view, and `Val.ctor`'s refusal to collapse a `§segs` (M32 R1) is what the
    borrow machinery depends on. Asserted rather than assumed, because a fix that
    folded the carve in Ω instead would pass every test above. -/
example : Val.beq (Val.ctor "§segs" [Val.segNode (Term.nat 1) (Val.sym 0),
                                     Val.segNode (Term.nat 2) (Val.sym 1)])
                  segsRejoined = true := by native_decide

end Dllbc.Tests.AuditFold
