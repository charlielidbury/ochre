import Dllbc.Program
import Dllbc.ProgMacro
import Dllbc.Boundary
import Dllbc.Std
import Dllbc.StdChain
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

§i-ii's accepted programs consume the standard chain (docs/20): the pack's
`SortedA` and the carve's `LeAdd i (S r)` bound are cited by NAME from a
`prog (Dllbc.std) { … }` seed, rather than spliced whole from the old lemma
library. §iii's two negative controls are structural mutations of that shape —
an extra statement, a missing one — not a single value swapped at a fixed
site, so they stay unseeded fragments checked with `progRejectsFrom`, citing
the chain's raw `Dllbc.StdChainRaw.SortedA` directly (only the seeded module
form resolves an imported name by name at elaboration; an unseeded block's
identifier resolution falls to the Lean constant it names, same as any other
file-local `Term` splice). The file has no dependency on the old splice-based
lemma library.
-/

open Dllbc

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
def SortedAId : Term := prog_parse {
  λ (N : Nat). λ (A : Array N Nat). λ (H : Dllbc.StdChainRaw.SortedA N A). H }

/-- The acceptance test: carve the pack's array three ways, return every
    borrow, repack inline from the entry clause. No callee, no write. A seeded
    golden — the `Checked` def elaborating IS the definition-site check, and
    `LeAdd`'s bound is call-and-bind: `let h1 = LeAdd(i, S r)` binds an opaque σ
    at `Le i (Add i (S r))` and the carve's evidence slot consumes it by TYPE,
    where the old spelling spliced the raw `LeAddRaw i (S r)` as an inline
    reducible spine. -/
def packCarveRepack : Checked := prog (Dllbc.std) {
  fn Touch (n : Nat, i : Nat, r : Nat, hd : Id Nat n (Add i (S r)),
            self : &mut (Σ0 (a : Array n Nat). SortedA n a)) -> Unit {
    let Pair(arr, HS) = *self;
    let SL0 = arr;
    let sb = &m arr;
    let h1 = LeAdd(i, S r);
    let pre = &m (*sb)[Z ; i ; S r | h1 | hd];
    let cell = &m (*sb)[i ; 1 ; r];
    let hic = &m (*sb)[S i ; r];
    *self := Pair(arr, SortedAId n SL0 HS);
    () };
  () }

/-- The greens are asserted twice over (docs/20's consumer migration playbook):
    the golden `def` above elaborating is the definition-site check, and
    `progOkFrom` re-checks the persisted term with the closing `endScope` and
    the `Unit` return audit — the module walk runs NEITHER (bindings must
    persist), so this does NOT collapse into the elaboration and stays as its
    own assertion. -/
example : progOkFrom Dllbc.std packCarveRepack.term = true := by native_decide

/-- The baseline: the same round-trip with no carve, to isolate that the case
    under test is about the carve and not about packs in general. No `LeAdd`
    citation, so no call-and-bind needed — only the pack's `SortedA` is seeded. -/
def packRepackNoCarve : Checked := prog (Dllbc.std) {
  fn Touch (n : Nat, self : &mut (Σ0 (a : Array n Nat). SortedA n a)) -> Unit {
    let Pair(arr, HS) = *self;
    let SL0 = arr;
    *self := Pair(arr, SortedAId n SL0 HS);
    () };
  () }
example : progOkFrom Dllbc.std packRepackNoCarve.term = true := by native_decide

/-! ## (ii) The control: the equation is definitional

    Over a local owned array. The carve's own `refineSym` rewrites the leaf's
    array to the `arrCat` spine of its pieces, so "the whole is the composition
    of its segments" is not a lemma here — it is the same term, definitionally.
    This isolates the audit's bridge-taking as the thing under test, rather than
    the equation itself. -/

/-- No pack, so no `SortedA` citation — but the carve still needs `LeAdd`'s
    bound, so this is seeded for that alone. -/
def carveRejoinEq : Checked := prog (Dllbc.std) {
  fn Touch (n : Nat, i : Nat, r : Nat, hd : Id Nat n (Add i (S r)),
            a : Array n Nat) -> Unit {
    let SL0 = a;
    let sb = &m a;
    let h1 = LeAdd(i, S r);
    let pre = &m (*sb)[Z ; i ; S r | h1 | hd];
    let cell = &m (*sb)[i ; 1 ; r];
    let hic = &m (*sb)[S i ; r];
    let L0 = *pre;
    let C0 = *cell;
    let H0 = *hic;
    let Heq = (Refl : Id (Array n Nat) SL0 (arrCat i (S r) L0 (arrCat 1 r C0 H0)));
    () };
  () }
example : progOkFrom Dllbc.std carveRejoinEq.term = true := by native_decide

/-! ## (iii) The negative controls — what the fold must still refuse

    Two ways for the same program to be wrong, failing at two different places.
    `packCarveHole` takes a segment's value away and never puts it back: the
    carve does not rejoin, the fold cannot close it, and the hole hunt catches
    it. `packCarveWrite` rejoins perfectly — the fold succeeds — but the audit
    refuses anyway, because the array it folds to is not the one the entry
    clause is about. Together they confirm the fold only widens acceptance for
    the true no-op case, not more.

    Neither is a value-level mutation of `packCarveRepack` at one fixed site —
    one inserts an extra statement (`let stolen = *cell`), the other omits the
    final rebind — so both stay `prog_parse` fragments checked from the seed by
    `progRejectsFrom` rather than marked twins minted from the golden's term
    (docs/20's consumer migration playbook, "not a mutation of any golden"
    fallback). `LeAddRaw i (S r)` still becomes call-and-bind, and the pack's
    `SortedA` is cited via the chain's raw constant directly — an unseeded
    block's identifier resolution has no seed to look names up against, so it
    falls to the same Lean-constant splice any file-local `Term` uses. -/

/-- A genuinely un-rejoined hole: the middle segment is moved out and not
    refilled. -/
def packCarveHole : Term := prog_parse {
  fn Touch (n : Nat, i : Nat, r : Nat, hd : Id Nat n (Add i (S r)),
            self : &mut (Σ0 (a : Array n Nat). Dllbc.StdChainRaw.SortedA n a)) -> Unit {
    let Pair(arr, HS) = *self;
    let SL0 = arr;
    let sb = &m arr;
    let h1 = LeAdd(i, S r);
    let pre = &m (*sb)[Z ; i ; S r | h1 | hd];
    let cell = &m (*sb)[i ; 1 ; r];
    let hic = &m (*sb)[S i ; r];
    let stolen = *cell;
    *self := Pair(arr, SortedAId n SL0 HS);
    () };
  () }
example : progRejectsFrom Dllbc.std packCarveHole
  "holds a hole (⊥) at return, in a leaf it still owns" = true := by native_decide

/-- The carve rejoins and the fold succeeds, yet the pack is still refused,
    because a `7` was written into the cell and the entry clause is about the
    array that was there before. Confirms the fold only lets the audit *state*
    what the array is — it does not make the audit vacuous. -/
def packCarveWrite : Term := prog_parse {
  fn Touch (n : Nat, i : Nat, r : Nat, hd : Id Nat n (Add i (S r)),
            self : &mut (Σ0 (a : Array n Nat). Dllbc.StdChainRaw.SortedA n a)) -> Unit {
    let Pair(arr, HS) = *self;
    let SL0 = arr;
    let sb = &m arr;
    let h1 = LeAdd(i, S r);
    let pre = &m (*sb)[Z ; i ; S r | h1 | hd];
    let cell = &m (*sb)[i ; 1 ; r];
    let hic = &m (*sb)[S i ; r];
    *cell := Arr(7);
    *self := Pair(arr, SortedAId n SL0 HS);
    () };
  () }
example : progRejectsFrom Dllbc.std packCarveWrite "does not have its owed type" = true := by native_decide

/-! ## (iv) The fence, at the value level

    Asserted directly on `subsKnowledge` rather than through a program: a
    segment list whose bodies are all owned contributes its `arrCat` spine, and
    one with a live loan in it still contributes `@stateComponent`. The
    loan case is deliberately not fixed here — it needs the opaque-fill rule,
    not a fold. No library citation, so no seeding change. -/

/-- A rejoined two-way carve: both bodies are owned values, so the fold
    closes. -/
def segsRejoined : Val :=
  .node "§segs" [Val.segNode (Term.nat 1) (Val.sym 0), Val.segNode (Term.nat 2) (Val.sym 1)]

/-- The same carve with one segment still out on loan. -/
def segsSuspended : Val :=
  .node "§segs" [Val.segNode (Term.nat 1) (Val.sym 0), Val.segNode (Term.nat 2) (.loanM 0)]

example : Term.beq (subsKnowledge segsRejoined)
  prog_parse { arrCat 1 2 %(Term.sym 0) %(Term.sym 1) } = true := by native_decide

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
