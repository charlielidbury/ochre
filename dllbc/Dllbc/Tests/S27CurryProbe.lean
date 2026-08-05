import Dllbc.Program
import Dllbc.Macro
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.PureMacro
import Dllbc.DeclMacro
import Dllbc.ProgMacro
import Dllbc.FnMacro
import Dllbc.Tests.S9Diff

/-!
# §27 — CURRIED RUNTIME APPLICATION, probed by deleting saturation

`combining-fns.md` §12 decision 4 makes runtime application **saturated**: a
partial application is unwritable, because "a partial application at runtime is
precisely a closure holding its arguments — including, in general, borrows —
while it waits". M26 unified λ and Π but kept two application disciplines
either side of that line: ⇝ is curried, ⇒ is spine-saturated.

The justification predates measurement. The sigprobe measured borrow-containing
values **stored** across statements and **returned** through
`collectResultBorrows` as clean in both machines, their suspended loans reachable
by the demand-end rule. This file tests the hypothesis that follows: a partial
application `f a ⟨borrow⟩` is *structurally that same object* — a spine value
carrying a suspended loan — so saturation can be deleted.

It is probed by **actually deleting it** (branch `curryprobe`, `Machine.lean`),
because every question past the first is otherwise answered by the same arity
check. Three rejection sites went; five loan-graph walkers gained an `.app`
case; **one new notion** was forced — *a value carrying a loan is linear* — at
the two sites that read such a value, the call (§B4) and the slot read (§G1).
Everything else was plumbing or free.

## The verdict, up front

| question | verdict |
|---|---|
| 1. partial-as-value, data only | **GO.** The unary step rule was already written — `applyR` collects the spine and appends, so what saturation withheld was the *constructor*, never the eliminator. The arity errors are subsumed by ordinary typing (§A). |
| 2. partial holding a borrow | **GO, and the §7 objection is empirically false.** The loan suspends in the spine, every demand site collapses it, the completion writes through, both machines agree, negative controls fire (§B). One new rule is forced: a linear callee must be MOVED, not located (§B.4). |
| 3. returned partial | **GO**, and the §10 capture wall is genuinely a different object, refused independently by the rule that already exists (§C). |
| 4. ensures / exit snapshots | **FAILS, with diagnosis, and it is a machine DIVERGENCE** — the checker refuses what the executing machine happily runs (§D). The premise needs correcting first: the audit does not fire at the call at all (§D0). |
| 5. the deletion sketch | **NO-GO as stated; GO for a bounded version** that curries application and keeps the call event atomic (§E) — and its cost line now includes teaching `indexKindV` about `fsig`, which is a PREREQUISITE and not an optional fix (§G3). |

## The finding that dominates

§D. The two disciplines are not an asymmetry between λ and Π, and after §B they
are not about borrows either. They are an asymmetry between **application** and
**the call event**. Everything M26 made a value — pure λ, runtime λ, `ih`, and
now a partial — curries fine. What cannot curry is `callDeclC`: one
`processArgs` over the whole telescope, ONE loan group tying captured loans to
issued borrows, and `borrowParamIds`/`markExit` keying the exit snapshots by
telescope index. Arrive one argument at a time and there is no moment before the
last at which a group can be minted — and the captured loan, which for a `.rfn`
partial sits *in the value* where §B's demand-end rule reaches it, for a sealed
callee is recorded in a `Group` instead, where nothing reaches it.

So the residual asymmetry the challenge names is real, and it is NOT the calling
convention: it is that a **sealed** function's call is an indivisible event, and
the whole M23 corpus is written against that event.

§F1 then decides how much that costs, and it is more than §D alone suggests. The
wall is not the ensures convention — it is `fsig`. A sealed runtime λ with no
borrows and no contract is behind it too, because `sealMint` files every runtime
λ's signature there and `.callV` sends every `fsig` callee to `callDeclC`. Since
§8 makes a program a term and §7 makes `fn` a macro over a sealed binding, every
function a program *declares* is a sealed runtime λ. **Currying works for local
and anonymous functions, and not for declared ones** — which is a coherent
language, but not the "one application form everywhere" the deletion was for.

Three defects were found, two of them silent wrong answers rather than
rejections; the ledger is §F3. §G then folds M27-P3's read-rule finding
(`a41980f2`, `S26Rec` §M) and generalizes it: the divergence is not about `ih`
but about **any σ whose Π is borrow-moded**, since such a σ has no `Val` and so
lives in `fsig` alone — no recursor required — and on one such program both
machines ACCEPT while the simulation relation fails, which is a worse class than
§M's conservative refusal. That is the prerequisite the bounded design must buy.
-/

open Dllbc
open Dllbc.StdLemmas (le_refl le_trans len Le)

namespace Dllbc.Tests.S27CurryProbe

/-! ## Helpers

    Rejections are asserted on the message, never on a Bool (S26Seal's rule,
    kept): `hasType` returns `false` for "does not have this type" and the audit
    turns that into an error, so a helper collapsing error and false would let a
    *stuckness* pass for a *typing* rejection. -/

def ok (d : Decl) (table : List Decl := [d]) : Bool :=
  match checkFn table d with | .ok _ => true | .error _ => false

def rejects (d : Decl) (needle : String) (table : List Decl := [d]) : Bool :=
  match checkFn table d with | .ok _ => false | .error e => strContains e needle

/-- One slot of the concrete final Ω, pretty-printed. The owner's final value is
    the observable every borrow question in this file turns on, and naming the
    slot keeps the assertion about that rather than about Ω's layout. -/
def slotOf (t : Term) (name : String) (table : List Decl := []) : String :=
  match runProgram t table with
  | .ok e => match e.find? (fun p => p.1 == name) with
             | some p => p.2.pretty
             | none => "<absent>"
  | .error err => "ERR: " ++ err

/-- The concrete final Ω is a σ-instance of some accepted symbolic path's. -/
def progDiff (t : Term) (table : List Decl := []) : Bool :=
  match runProgram t table with
  | .error _ => false
  | .ok concEnv => (programEnvs t table).any (fun r => match r with
      | .ok se => Tests.S9Diff.instanceOfC se concEnv
      | .error _ => false)

/-! ## §A. PARTIAL-AS-VALUE, data only

    `let g = f(a)`, then `g(b)` completing later, at each of the three callee
    kinds. All three work, and the reason they were never far away is §A.4. -/

-- A1. A **runtime λ** (`.rfn`) — the site BOTH machines share, so it is the one
-- that decides whether execution can curry at all. It can.
def a1rfn : Term := prog{
  let f = λ(a, b){ Cons(a, Cons(b, Nil)) };
  let g = f(S(Z));
  let r = g(S(S(Z)));
  () }
example : progOk a1rfn = true := by native_decide
example : progDiff a1rfn = true := by native_decide
example : slotOf a1rfn "r" = "Cons (S Z) (Cons (S (S Z)) Nil)" := by native_decide

-- A2. A **pure λ** — `applyLam`'s residual. Both machines.
def a2lam : Term := prog{
  let f = λ (a : Nat). λ (b : Nat). a;
  let g = f(S(Z));
  let r = g(S(S(Z)));
  () }
example : progOk a2lam = true := by native_decide
example : progDiff a2lam = true := by native_decide

-- A3. A **sealed σ : Π** — `callVValue`'s `instantiatePi` residual, checking
-- only by construction (no concrete run has a σ in a slot).
def a3seal : Term := prog{
  let f = seal(λ (a : Nat). λ (b : Nat). a, Π (a : Nat) → Π (b : Nat) → Nat);
  let g = f(S(Z));
  let r = g(S(S(Z)));
  () }
example : progOk a3seal = true := by native_decide

/-! ### A4. Why this was one line: the eliminator was already written

    `applyR` opens with `collectSpine f` and `sargs ++ args` — it has ALWAYS
    consumed a partial spine correctly, because that is how ι hands an arm the
    predecessor, the recursor at the predecessor, and everything the caller still
    owed. Saturation withheld the **constructor** and kept the eliminator. The
    same holds one level up: the σ case's residual is what `instantiatePi`
    already computes, and minting a σ at it is the rule the saturated case
    takes anyway.

    So `f(a)(b)` and `f(a, b)` agree — asserted, not assumed. -/

def a4curried : Term := prog{
  let f = λ(a, b){ Cons(a, Cons(b, Nil)) };
  let g = f(S(Z));
  let r = g(S(S(Z)));
  () }
def a4spine : Term := prog{
  let f = λ(a, b){ Cons(a, Cons(b, Nil)) };
  let r = f(S(Z), S(S(Z)));
  () }
example : slotOf a4curried "r" = slotOf a4spine "r" := by native_decide
example : slotOf a4spine "r" = "Cons (S Z) (Cons (S (S Z)) Nil)" := by native_decide

/-! ### A5. The arity errors are SUBSUMED, not lost

    §12 decision 4's rejections do double duty today: they catch a genuine
    mistake (a body that under-applies and returns the residual where a `Nat`
    was promised) *and* they refuse a legitimate partial. Deleting them keeps the
    first, because the residual has a function type and the audit reads it: the
    S26Seal test that pinned the arity error still fails, one rule over.

    This is the deletion's main dividend — a rejection stops being an arity
    class and becomes the ordinary typing it always was. -/

def a5bad : Decl :=
  decl{ fn apply1bad (g : Π (x : Nat) → Π (y : Nat) → Nat, n : Nat) -> Nat { g(n) } }
example : rejects a5bad "does not have return type" = true := by native_decide

-- The honest twin: promise the function type and the same body is accepted.
def a5ok : Decl :=
  decl{ fn apply1ok (g : Π (x : Nat) → Π (y : Nat) → Nat, n : Nat)
        -> Π (y : Nat) → Nat { g(n) } }
example : ok a5ok = true := by native_decide

/-! ## §B. A PARTIAL HOLDING A BORROW

    The §7-cost-3 objection, stated as a fact about the world: "`(natRec … fuel)
    ⟨borrow⟩` is a partial application *holding a borrow* while awaiting the next
    argument". It is — and the sigprobe's stored/returned evidence says that
    object is governed. §B measures it directly. -/

/-! ### B1. The loan suspends in the spine, and the completion writes through it

    Both machines, with the owner's final value asserted rather than inspected:
    the write inside the completing call lands in `x`, which is only true if the
    borrow that travelled inside the residual is the same borrow. -/

def b1 : Term := prog{
  let f = λ(v, n){ *v := Cons(n, Nil); () };
  let x = Nil;
  let g = f(&mut x);
  let r = g(S(Z));
  let y = x;
  () }
example : progOk b1 = true := by native_decide
example : progDiff b1 = true := by native_decide
example : slotOf b1 "y" = "Cons (S Z) Nil" := by native_decide
-- …and the residual really was consumed on completion (§B4), not left aliasing.
example : slotOf b1 "g" = "⊥" := by native_decide

/-! ### B2. The negative control — the demand-end rule reaches INSIDE the spine

    Read the owner before the partial is completed and the loan is demanded out
    from under it; the completion then finds a hole. Both machines, same message
    — which is what makes B1 a statement about the demand-end rule rather than
    about nothing happening. This is the sigprobe's §B2 verbatim, one former
    over: `Pair(Z, &mut x)` there, `f(&mut x)` here. -/

def b2 : Term := prog{
  let f = λ(v, n){ *v := Cons(n, Nil); () };
  let x = Nil;
  let g = f(&mut x);
  let y = x;
  let r = g(S(Z));
  () }
example : progRejects b2 "cannot peel a vacant slot" = true := by native_decide
example : progRunErr b2 "cannot peel a vacant slot" = true := by native_decide

/-! ### B3. THE FIRST DEFECT — five loan-graph walkers stopped at `.ctor`

    `findBorrowPayload`, `replaceLoanMarker`, `replaceBorrowWithBot`,
    `containsLoan` and `firstLoanMarker` all descend `.ctor` and `.borrowM` and
    stop. A partial application is an `.app` spine, so a borrow inside one was
    invisible: `killBorrowInΩ` could not find it and reported "its other end is
    in flight — cannot end", which is the rejection for a self-reborrow, not for
    this.

    Exactly the sigprobe's §A4 defect one former over (there: a borrow inside a
    `Pair`, `collapseArg` matching by slot shape). The fix is the same shape too
    — one `.app` case each — and B1/B2 are its differential. -/

/-! ### B4. THE SECOND DEFECT, and the one real NEW RULE currying forces

    `.callV` **locates** its callee rather than consuming it — "a slot can be
    called twice", and reading a function to call it is a place read. Under
    saturation that is unconditionally right: every callee is a closed function
    value with no owned content.

    A partial application is not one. Its spine holds the actuals already
    supplied, so locating it **duplicates** them: after `applyRFn` binds the
    spine's borrow into the frame's slot there are two `borrowM ℓ` nodes for one
    loan, `killBorrowInΩ`'s `findSome?` reaches the stale one, and the write is
    written back over. That is a silent wrong ANSWER, not a rejection — B1
    printed `y = Nil` — and it is the kind of thing constraint 6 exists to catch.

    The rule: a callee carrying a loan is **linear** and is moved out of its slot
    on the call. Discriminated on the value, not on a flag, so `ih` (a
    `.const`-headed closed recursor spine) stays locatable and M26-C's recursion
    is untouched. The consequence is asserted below: completing a partial twice
    is use-after-move, in both machines.

    Note the doc comment at `.callV` had it exactly backwards — it says stating
    the rule as location "keeps the rule true of the borrow-capturing closures §7
    defers, which are NOT copyable". Location is precisely what is UNSOUND for a
    non-copyable callee. -/

def b4twice : Term := prog{
  let f = λ(v, n){ *v := Cons(n, Nil); () };
  let x = Nil;
  let g = f(&mut x);
  let r = g(S(Z));
  let s = g(S(S(Z)));
  () }
example : progRejects b4twice "use-after-move" = true := by native_decide
example : progRunErr b4twice "use-after-move" = true := by native_decide

-- …and the control that says B4 did not just break calling twice in general: a
-- CLOSED function value in a slot is still located, and still callable twice.
def b4closed : Term := prog{
  let f = λ(a, b){ Cons(a, Cons(b, Nil)) };
  let r = f(S(Z), S(Z));
  let s = f(S(Z), S(S(Z)));
  () }
example : progOk b4closed = true := by native_decide
example : progDiff b4closed = true := by native_decide

/-! ### B6. The other demand sites, and the abandoned partial

    B2 is the READ. The write and the reborrow are the other two ways a program
    can demand the owner while a partial holds it, and both take the same rule in
    both machines: the loan ends, the partial is left holding a dead borrow, and
    the completion says so.

    The DROP is the interesting one. A partial that is never completed is not an
    error — the owner comes back at its ENTRY value, because the write inside the
    unrun body never happened, and the loan is returned by the demand-end at the
    read of `x`. Nothing needs to know that the partial was abandoned. -/

-- B6a. WRITE to the owner while the partial lives.
def b6write : Term := prog{
  let f = λ(v, n){ *v := Cons(n, Nil); () };
  let x = Nil;
  let g = f(&mut x);
  x := Cons(Z, Nil);
  let r = g(S(Z));
  () }
example : progRejects b6write "cannot peel a vacant slot" = true := by native_decide
example : progRunErr b6write "cannot peel a vacant slot" = true := by native_decide

-- B6b. RE-BORROW the owner while the partial lives.
def b6reborrow : Term := prog{
  let f = λ(v, n){ *v := Cons(n, Nil); () };
  let x = Nil;
  let g = f(&mut x);
  let b = &mut x;
  let r = g(S(Z));
  () }
example : progRejects b6reborrow "cannot peel a vacant slot" = true := by native_decide
example : progRunErr b6reborrow "cannot peel a vacant slot" = true := by native_decide

-- B6c. DROP: the partial is never completed, and the owner comes back at its
-- entry value. Compare B1, where the same program completes and `y` is the
-- written list — the difference between them is the whole of what the partial
-- was holding.
def b6drop : Term := prog{
  let f = λ(v, n){ *v := Cons(n, Nil); () };
  let x = Nil;
  let g = f(&mut x);
  let y = x;
  () }
example : progOk b6drop = true := by native_decide
example : progDiff b6drop = true := by native_decide
example : slotOf b6drop "y" = "Nil" := by native_decide
example : slotOf b1 "y" = "Cons (S Z) Nil" := by native_decide

/-! ### B5. The group/audit story of a completed partial matches the spine call's

    The same function, the same borrow, the same write — reached once by
    `f(&mut x, n)` and once by `f(&mut x)` then `g(n)`. The owner's final value
    is identical, which is the observable the ensures convention is about. -/

def b5spine : Term := prog{
  let f = λ(v, n){ *v := Cons(n, Nil); () };
  let x = Nil;
  let r = f(&mut x, S(Z));
  let y = x;
  () }
example : slotOf b1 "y" = slotOf b5spine "y" := by native_decide
example : progOk b5spine = true := by native_decide
example : progDiff b5spine = true := by native_decide

/-! ## §C. THE RETURNED PARTIAL — and which wall is which

    §7 cost 2 admits closed function values; §10 defers environment capture. A
    returned partial could be either, and the probe's job is to say which. The
    answer is that they are genuinely different objects and the machinery already
    tells them apart, with no new rule. -/

/-! ### C1. A spine of applied ACTUALS, returned out of a frame — WORKS

    `mk` takes a borrow, hands it to `f`, and returns the partial. The reborrow
    travels out of `mk`'s frame inside the residual, survives to the completion,
    and the write lands in the original owner. Both machines. -/

def c1 : Term := prog{
  let f = λ(v, n){ *v := Cons(n, Nil); () };
  let mk = λ(w){ f(&mut *w) };
  let x = Nil;
  let g = mk(&mut x);
  let r = g(S(Z));
  let y = x;
  () }
example : progOk c1 = true := by native_decide
example : progDiff c1 = true := by native_decide
example : slotOf c1 "y" = "Cons (S Z) Nil" := by native_decide

/-! ### C2. A λ CAPTURING a local — refused, by the rule that already exists

    The §10 item, and it is not reached through currying at all: the inner λ's
    body names `w`, which is a borrow rather than a function, so the closedness
    check at `.lamR` refuses it in both machines with the rejection M26-C wrote.
    Nothing here is a currying question — which is the diagnosis §C was asked
    for. -/

def c2capture : Term := prog{
  let mk = λ(w){ λ(n){ *w := Cons(n, Nil); () } };
  let x = Nil;
  let g = mk(&mut x);
  () }
example : progRejects c2capture "environment capture stays deferred" = true := by native_decide
example : progRunErr c2capture "environment capture stays deferred" = true := by native_decide

/-! ## §D. THE WALL — the ensures/exit-snapshot interaction

    ### D0. First, the question's premise needs correcting.

    "A sealed function's audit fires at the call — with currying, WHEN?" The
    audit does **not** fire at the call. `sealFn` runs `checkRFnBody` at the
    `.seal` node, once, when the binding is evaluated; §12 decision 1 is what
    made that true, and currying does not touch it. D1 pins it: a sealed function
    with a body that violates its ascription is rejected *without ever being
    called*.

    So there is no audit-timing question. What fires at the CALL is the
    **contract instantiation** — `buildResult` at the actuals, the exit-snapshot
    σs, and the loan group — and that is where currying breaks. -/

def d1neverCalled : Term := prog{
  let f = seal(λ(v, n){ *v := Nil; () },
               Π (v : &mut List Nat) → Π (n : Nat) → Id (List Nat) (*v) (Cons n Nil));
  () }
example : progRejects d1neverCalled "does not have return type" = true := by native_decide

/-! ### D2. The saturated ensures call, so the wall is about currying

    A real exit-snapshot contract — `Id (List Nat) (*v) (Cons n Nil)` — sealed,
    called with its whole telescope, checked and run. -/

def d2sat : Term := prog{
  let f = seal(λ(v, n){ *v := Cons(n, Nil); Refl },
               Π (v : &mut List Nat) → Π (n : Nat) → Id (List Nat) (*v) (Cons n Nil));
  let x = Nil;
  let r = f(&mut x, S(Z));
  () }
example : progOk d2sat = true := by native_decide
example : progDiff d2sat = true := by native_decide

/-! ### D3. THE SAME CALL, CURRIED — and the machines DIVERGE

    The checker refuses with `processArgs`' arity mismatch. The executing machine
    runs it, correctly, to the same answer as D2.

    The divergence is structural rather than incidental: the two machines
    represent a sealed function differently. Executing, a seal evaluates to its
    own term, so `g` holds the `.rfn` and `applyR` curries it by §A's rule.
    Checking, the seal mints a σ whose signature lives in `fsig`, so `.callV`
    dispatches to `callDeclC` — and `callDeclC` takes `List Term` against a whole
    `decl.telescope`, with no prefix case and nowhere to put one.

    **This is the FAILS, and it is asserted rather than described**: `progRejects`
    and a successful `runProgram` on the same term, which is the shape constraint
    6 names ("a checking-vs-executing divergence"). Note which way it points —
    the computation is fine and the *contract* cannot follow it. -/

def d3curried : Term := prog{
  let f = seal(λ(v, n){ *v := Cons(n, Nil); Refl },
               Π (v : &mut List Nat) → Π (n : Nat) → Id (List Nat) (*v) (Cons n Nil));
  let x = Nil;
  let g = f(&mut x);
  let r = g(S(Z));
  () }
example : progRejects d3curried "arity mismatch (arguments vs telescope)" = true := by native_decide
-- The executing machine runs the very same program, to D2's answer.
example : slotOf d3curried "x" = "Cons (S Z) Nil" := by native_decide
example : slotOf d3curried "r" = "Refl" := by native_decide
-- …which is D2's answer, reached by the machine that has no contract to check.
example : slotOf d3curried "x" = slotOf d2sat "x" := by native_decide

/-! ### D4. Why it cannot be closed by more seeding code

    `callDeclC` has three coupled outputs and only the last argument can produce
    them:

      1. `processArgs` returns `captured` (one loan per borrow argument, with its
         owed type) and `inst` (parameter → actual). A prefix gives a partial
         `inst`, and a later parameter's type may mention an earlier one — the
         telescope is dependent, which is the whole of §5.2.
      2. `buildResult`/`markExit` key the exit snapshots by `borrowParamIds
         decl.telescope` — a *telescope index*. Half a telescope indexes into
         nothing.
      3. The **loan group** ties `captured` to `issued` and is minted once. Before
         the last argument there are captured loans and no issued borrows, so
         there is no group — and a captured loan with no group has nothing that
         can release it.

    Point 3 is the sharp one, and it is exactly the contrast §B draws. For a
    `.rfn` partial the suspended loan sits IN THE VALUE, where the demand-end
    rule finds it (B2 is that measurement). For a sealed callee the captured loan
    is recorded in a `Group` in the state instead — so currying `callDeclC`
    needs the residual to carry a partial group, which is a new value form AND a
    new release rule, not a missing case. -/

/-! ## §E. THE DELETION SKETCH, itemized

    **What went, to get §A–§C:** three rejection sites — `applyR`'s
    under-application (the one both machines share), `applyLam`'s residual, and
    `callVValue`'s σ residual. Each was a `throwErr` replaced by the value it
    was declining to build, and one of the three (the σ case) was a pure
    deletion: `instantiatePi` had already computed the residual type and the
    saturated branch below it already minted a σ at whatever it returned.

    A fourth site was NOT touched and would need thought: `piPeel`'s arity
    agreement at the seal, which checks a runtime λ's binder count against its
    ascription. A curried calculus wants it to peel a prefix and ascribe the
    residual, which is a real change rather than a deletion.

    The unary step rule needed no code at all: `applyR` already collects the
    spine and appends (§A4).

    **What arrived:**

      * five `.app` cases on the loan-graph walkers (§B3) — mechanical, and the
        same gap the sigprobe closed for Σ-packages;
      * ONE new rule (§B4): a callee carrying a loan is linear and is moved, not
        located. This is real semantics, not plumbing, and it is the honest cost
        of the deletion.

    **What the corpus said.** Flip-validated on the whole corpus, the M23
    flagship included. Exactly **seven declarations in three files** changed, and
    every one of them asserts saturation itself:

    | file | cases | what they become |
    |---|---|---|
    | `S26Seal` | `c4`, `c5` | correct acceptances |
    | `S26Seal` | `apply1bad` | still rejected, by typing (§A5) |
    | `S26Modes` | `g1`, `g2`, `g3` | correct acceptances |
    | `S26Rec` | `a5` | correct acceptance (`a6`, over-application, is untouched) |

    Nothing else in the repo depends on saturation. That is a stronger statement
    than §12 decision 4's own "it cost nothing" — that was about not NEEDING
    partials, this is about nothing breaking when they exist.

    Two of those tests are worth quoting back. `S26Modes` g2 is pinned in its own
    comment as "the LIMITATION it is: `mk` means to be the constant function at
    1, and is refused" — under the probe it simply is that function. And the
    paragraph above `S26Modes` g1 files the exact decision this probe takes ("a
    residual telescope with no borrow-moded binder could be curried soundly …
    left filed"), while assuming the borrow case was the hard part. §B is the
    measurement that says it is not.

    **Can checking and executing share one rule?** For application, yes — they
    already do, `applyR` is one function and §A–§C's differentials are all green.
    For the CALL EVENT, no, and §D3 is the measurement: they do not share a rule
    today (`applyR` vs `callDeclC`), and saturation is what kept that difference
    unobservable.

    **The bounded design that IS available**, and the probe's recommendation:
    curry *application* and keep the *call event* atomic — a partial of a sealed
    function accumulates its arguments in the residual and fires `callDeclC` once
    the count reaches the telescope length. §D's three coupled outputs are then
    produced at one moment, as today, and §B says the borrow is safe in the
    residual meanwhile. The cost is one new value form (a residual carrying
    already-evaluated actuals, since `callDeclC` takes `List Term` and a borrow
    argument must take its loan when it is written, not when the call completes)
    — which is more than this probe's budget and less than a partial group. -/

/-! ## §F. TWO MEASUREMENTS THAT CHANGE THE VERDICT'S SHAPE

    ### F1. The wall is not the ensures convention — it is `fsig`

    §D reached the wall through a contract, so it is natural to read it as being
    about `*v`/`old *v`. It is not. A sealed runtime λ with **no borrows and no
    contract at all** is behind the same wall, for the same reason: `sealMint`
    files a runtime λ's signature in `fsig`, and `.callV` sends every `fsig`
    callee to `callDeclC`.

    That widens the blast radius considerably, and it is the fact that decides
    question 5. Currying works for values reached by `applyR`/`applyLam` — an
    unsealed runtime λ (§A/§B), a partial spine, `ih`, and a sealed PURE λ (A3).
    It fails for every sealed RUNTIME λ. And since §8 makes a program a term and
    §7 makes `fn` a macro over a sealed binding, **every function a program
    declares is a sealed runtime λ**. So the honest summary is: currying works
    for local and anonymous functions, and not for declared ones. -/

def f1noContract : Term := prog{
  let f = seal(λ(a, b){ Cons(a, Cons(b, Nil)) },
               Π (a : Nat) → Π (b : Nat) → List Nat);
  let g = f(S(Z));
  let r = g(S(S(Z)));
  () }
example : progRejects f1noContract "arity mismatch (arguments vs telescope)" = true := by native_decide
example : slotOf f1noContract "r" = "Cons (S Z) (Cons (S (S Z)) Nil)" := by native_decide
-- The sealed-PURE-λ twin, which is on the other side of the same line (A3's
-- shape, restated here so the two sit together).
example : progOk a3seal = true := by native_decide

/-! ### F2. THE THIRD DEFECT — binder modes were read from the wrong end

    `valBinderModes` computes the callee's spine and then, in the `.rfn` case,
    ignored it: the modes owed were taken from the START of the binder list.
    Saturation made that correct by making the spine always empty. Curried, the
    (k+1)-th argument was routed by the FIRST binder's mode — so a capital binder
    anywhere past the first silently **consumed** its argument, which is R16 back
    at full strength and arriving as a wrong answer rather than a rejection.

    Fixed by dropping the already-applied count. The three cases below are the
    differential that found it and the one that confirms the fix: the mode-
    sensitive binder first (which was always right), the same binder second
    (which was wrong), and the saturated control that says it is about
    currying. -/

-- F2a. Capital binder FIRST, curried: the caller keeps its argument (was always
-- correct — the offset is zero).
def f2first : Term := prog{
  let f = λ(Ha, b){ b };
  let y = Cons(Z, Nil);
  let g = f(y);
  let z = y;
  let r = g(S(Z));
  () }
example : progOk f2first = true := by native_decide
example : slotOf f2first "z" = "Cons Z Nil" := by native_decide

-- F2b. Capital binder SECOND, curried: this is the case that was broken.
def f2second : Term := prog{
  let f = λ(a, Hb){ a };
  let x = S(Z);
  let y = Cons(Z, Nil);
  let g = f(x);
  let r = g(y);
  let z = y;
  () }
example : progOk f2second = true := by native_decide
example : progDiff f2second = true := by native_decide
example : slotOf f2second "z" = "Cons Z Nil" := by native_decide

-- F2c. The SATURATED control: same function, same arguments, one spine. The
-- curried and saturated answers agree, which is what "the mode survives" means.
def f2sat : Term := prog{
  let f = λ(a, Hb){ a };
  let x = S(Z);
  let y = Cons(Z, Nil);
  let r = f(x, y);
  let z = y;
  () }
example : progOk f2sat = true := by native_decide
example : slotOf f2second "z" = slotOf f2sat "z" := by native_decide

/-! ### F3. The defect ledger, since three is the number that matters

    Every one of the three was found by running a program, and two of the three
    were silent WRONG ANSWERS rather than rejections — which is the class the
    polarity doctrine and constraint 6 exist for, and the reason "delete the rule
    and see" was the right instrument.

    | # | defect | class | found by |
    |---|---|---|---|
    | 1 | five loan-graph walkers stop at `.ctor`, so a borrow inside an `.app` spine is invisible (§B3) | rejection, with a misleading message | B2's negative control |
    | 2 | `.callV` LOCATES a linear callee, duplicating the actuals it holds (§B4) | **silent wrong answer** — the write was written back over | B1's owner assertion |
    | 3 | `valBinderModes` reads modes from the start of the binder list (§F2) | **silent wrong answer** — a capital binder consumed its argument | F2b vs F2c |

    Defect 2 is the only one that is semantics rather than plumbing, and it is
    the single rule the deletion actually adds. -/

/-! ## §G. THE READ RULE — folded from M27-P3, and it is a PREREQUISITE

    M27-P3 (`a41980f2`, `S26Rec` §M) pinned that `let g = ih` inside an arm is
    REJECTED when checking and RUNS when executing, because checking-side `ih` is
    a σ whose signature lives in `St.fsig` while `indexKindV`'s `.sym` case
    consults `sctx` only, so it takes the move default. Its four assertions are
    the evidence and are not re-derived here. §G adds three things currying
    forced, and re-prices question 5 accordingly.

    ### G1. Currying needs the read rule changed at a DIFFERENT case — and that
    part is free

    A partial application is an `.app` spine, and `indexKindV` classified `.app`
    unconditionally as index-kind ("a pure-former spine (proof/type)"). That was
    right while the only inhabitant was a proof or a type. Currying adds a
    second, and a partial carrying a loan is linear — copying it is wrong for
    exactly the reason §B4 gives at the callee position.

    So the rule is ONE notion at two sites: **a value carrying a loan is
    linear**, checked at the call (§B4) and at the read (here). The read half is
    free — the whole corpus stays green — and with it a partial can be moved
    between slots, stored in a constructor, and completed from wherever it ended
    up (§G2). -/

-- G1a. Moved to another slot and completed FROM THERE: the borrow travels with
-- the value, which is what "a borrow the value carries is relocated as-is on a
-- move" means once partials exist.
def g1move : Term := prog{
  let f = λ(v, n){ *v := Cons(n, Nil); () };
  let x = Nil;
  let g = f(&mut x);
  let h = g;
  let r = h(S(Z));
  let y = x;
  () }
example : progOk g1move = true := by native_decide
example : progDiff g1move = true := by native_decide
example : slotOf g1move "y" = "Cons (S Z) Nil" := by native_decide

-- G1b. …and the source slot really was moved out of, so it is a move and not a
-- copy. Without the read-rule change BOTH slots stayed live and the loan was
-- reachable twice.
def g1both : Term := prog{
  let f = λ(v, n){ *v := Cons(n, Nil); () };
  let x = Nil;
  let g = f(&mut x);
  let h = g;
  let r = g(S(Z));
  () }
example : progRejects g1both "use-after-move" = true := by native_decide
example : progRunErr g1both "use-after-move" = true := by native_decide

-- G1c. The DATA-only partial is still copied, which is what says the rule keys
-- on the loan and not on the shape: no loan, two live copies, both complete.
def g1data : Term := prog{
  let f = λ(a, b){ Cons(a, Cons(b, Nil)) };
  let g = f(S(Z));
  let h = g;
  let r = g(S(S(Z)));
  let s = h(S(S(S(Z))));
  () }
example : progOk g1data = true := by native_decide
example : progDiff g1data = true := by native_decide

/-! ### G2. Stored in a constructor and completed after a match

    The sigprobe's stored direction, one level up: a `Pair` holding a partial
    that holds a borrow. Matched out and completed, and the write lands. -/

def g2stored : Term := prog{
  let f = λ(v, n){ *v := Cons(n, Nil); () };
  let x = Nil;
  let g = f(&mut x);
  let p = Pair(Z, g);
  match p { Pair(k, q) => { let r = q(S(Z)); () } };
  let y = x;
  () }
example : progOk g2stored = true := by native_decide
example : progDiff g2stored = true := by native_decide
example : slotOf g2stored "y" = "Cons (S Z) Nil" := by native_decide

/-! ### G3. THE fsig HALF IS NOT FREE, and it is worse than §M priced it

    §M's cause generalizes past `ih`, and the generalization is what makes it a
    prerequisite rather than a curiosity. The trigger is not "a function-typed σ
    in a slot" — H1 below is one and copies fine, because a borrow-FREE Π has a
    `Val` and lands in `sctx` too. The trigger is a σ whose **Π is borrow-moded**:
    it has no `Val` (M26-C's founding fact), so it exists in `fsig` ALONE, and
    `indexKindV` finds nothing.

    Two consequences beyond §M:

      1. **No recursor is needed.** An ordinary sealed borrow-taking function
         bound to a slot has the divergence (`i1`/`i3`). §M reached it through
         `ih`; it is a property of sealed borrow-moded functions as such.
      2. **It is NOT only in the safe direction.** §M's case was reject-vs-run.
         `i1` is a program BOTH machines accept whose final Ωs do not correspond
         — `f = ⊥` checking, `f = λr(…)` executing — so `progDiff` is FALSE. That
         is a simulation break on an accepted program, which is a different and
         worse class than a conservative refusal.

    **The pricing.** For the deletion as probed, this is not hit: an unsealed
    runtime λ's partial is an `.app`/`.rfn` spine and takes §G1's case. But §E's
    recommended bounded design accumulates arguments for a SEALED callee, so its
    residual is exactly the object that must be bound to a slot and read back —
    and every sealed borrow-moded function is behind this blindness today. So
    teaching `indexKindV` about `fsig` **is a prerequisite of the bounded
    design**, and §M is right that it changes the read rule for every σ and does
    not belong in a deletion phase. Question 5's cost line gains it. -/

-- G3a. Borrow-FREE sealed function: copies on both sides, no divergence. This
-- is the control that locates the boundary.
def g3free : Term := prog{
  let f = seal(λ(a, b){ Cons(a, Cons(b, Nil)) },
               Π (a : Nat) → Π (b : Nat) → List Nat);
  let h = f;
  let r = h(S(Z), S(S(Z)));
  () }
example : progOk g3free = true := by native_decide
example : progDiff g3free = true := by native_decide

-- G3b. BORROW-MODED sealed function: both machines accept, and the simulation
-- relation FAILS. No recursor involved.
def g3moded : Term := prog{
  let f = seal(λ(v, n){ *v := Cons(n, Nil); () },
               Π (v : &mut List Nat) → Π (n : Nat) → Unit);
  let h = f;
  let x = Nil;
  let r = h(&mut x, S(Z));
  let y = x;
  () }
example : progOk g3moded = true := by native_decide
example : progDiff g3moded = false := by native_decide

-- G3c. The sharp form: use the source slot again and the checker refuses what
-- the executing machine runs — §M's shape, reached without a recursor.
def g3sharp : Term := prog{
  let f = seal(λ(v, n){ *v := Cons(n, Nil); () },
               Π (v : &mut List Nat) → Π (n : Nat) → Unit);
  let h = f;
  let x = Nil;
  let y = Nil;
  let r = h(&mut x, S(Z));
  let s = f(&mut y, S(Z));
  () }
example : progRejects g3sharp "use-after-move" = true := by native_decide
example : slotOf g3sharp "x" = "Cons (S Z) Nil" := by native_decide
example : slotOf g3sharp "y" = "Cons (S Z) Nil" := by native_decide

-- G3d. The no-`let` twin, so G3b/G3c are about the READ and not the shape.
def g3nolet : Term := prog{
  let f = seal(λ(v, n){ *v := Cons(n, Nil); () },
               Π (v : &mut List Nat) → Π (n : Nat) → Unit);
  let x = Nil;
  let r = f(&mut x, S(Z));
  let y = x;
  () }
example : progOk g3nolet = true := by native_decide
example : progDiff g3nolet = true := by native_decide

end Dllbc.Tests.S27CurryProbe
