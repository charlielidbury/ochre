# Packed invariants under escaping borrows — problem statement

**The problem.** A container with its invariant packed in the type (`HashMap := Σ (cap). … Σ0 (slots : Array cap Bucket). HMInv …`) cannot have a `GetMut`: an op that returns a `&mut` into the pack leaves a live loan inside `slots` at its own exit, and the exit audit must then re-type the pack — including the Σ0 invariant — around that loan. Today it cannot, so `GetMut`/`GetMutOrInsert` execute correctly but are unwritable in checked code. Pinned on branch `hm-flagship-fable` as `gmProbe1/2/3` (inline carve / callee boundary / index place, all red) with `packNav` as the control (the identical shape over a slots-independent tail passes). This became visible when the audit's per-parameter exemption was fixed to per-place (main `6c46db1c`) — the old behavior was unsound, so this is a genuine capability gap, not a regression.

Written 2026-08-18 as the mandate for an overnight campaign (user directive: fix it on a branch; sub-agents do the major work; a review guide if something lands). **Design priorities, fixed by the user: keep the theory simple, keep the user experience good.**

## The three moments

1. **Callee exit.** `GetMut` returns `&m` into a value cell. Its `self` payload at exit = the pack with a segmented array and one in-flight loan. The audit must accept this. (Prerequisite, separate lane: re-typing across a *rejoined* segmentation is already broken even with no live loan — `s1P2a` — though the composition equation is definitional — `s1P2c`. That fix is mechanical and dispatched independently: fold segments through the existing ⇝ bridge at typing time.)
2. **The caller's write.** `*r := v` through the returned borrow changes a cell the packed invariant quantifies over. Nothing re-checks the invariant here, by design (writes are only audited at boundaries).
3. **Group end.** The owner recovers a fresh σ at the owed type — the packed type — which *asserts* the post-write invariant. For that to be sound, the system must know no write through the issued borrow could have broken it.

## The thesis: opaque-fill for escaping borrows

One rule: **when the audit re-types a payload containing an ESCAPING mutable borrow (one issued into the result), the lent place is filled with a FRESH σ, not its current value.** If the pack types with the cell opaque, the stored invariant holds for *every* value the caller could write — the fresh σ is the checker's native universal quantifier — and moment 3's re-mint becomes sound rather than optimistic. Non-escaping in-flight places keep the actual-payload fill (the audit-fix lane's measured stage-5 finding; escaping is exactly the case its `trivialOwed` caveat excluded).

Why this should work on the real invariant: `HMInv`'s clauses (hashing, counts, ledger, per-bucket no-dup) fold over *keys and structure* and never inspect *values*, so `HMInv … (slots[cell := σ])` normalizes to the same type as with the concrete cell, and the stored proof still inhabits it. Where it fails, it should: a borrow into a *key* cell makes the abstracted invariant stuck/uninhabited, and the op is refused — which is correct, since a key write really would break hashing. UX: `GetMut` over value cells just works, no annotations; the failure mode names the invariant clause that blocked it. Theory: no new syntax, no new judgment forms — one fill-mode distinction inside the existing audit, using existing σ machinery.

**What would refute the thesis** (the viability probe's job to try): (a) the convertibility claim fails on the machine — `HMInv` with an abstracted value cell does not in fact convert, e.g. because a fold gets stuck on the σ in a way key-independence doesn't rescue; (b) the escaping-loan set is not identifiable at the fill site (it should be — `collectResultBorrows`/`resultLoans` already computes it); (c) a soundness counterexample — a pack whose *runtime* components depend on the lent cell (`Σ (x : Nat). Σ0 (H : Id Nat x y)…`) must be refused by the same rule, and the probe must confirm the abstraction catches every such dependence, not just Σ0 tails; (d) the caller-side group end needs more than the current opaque re-mint (Fable's gmProbe2 note: "the group-end re-mint orphans the packed proof" — characterize exactly what that means before trusting moment 3).

## Alternatives, and why not first

- **Loan-attached debts** (`12-design-borrow-refounding.md`): the full answer, and the only one that also buys *functional* caller-side facts (find-after-write). Heavier: new mint sites, pins, a 12–14-session milestone awaiting user review. The opaque-fill rule is that design's safety floor extracted: debts would still land later for precision, and nothing here forecloses them.
- **Unpack the invariant** (extrinsic `Hinv` parameters, Nth-style): works today, but trades away the design win the flagship exists to demonstrate (a map that cannot exist broken), and worsens UX at every call site. Fallback only.

## Acceptance

`gmProbe1/2/3` flip green (borrow into a value cell, all three routes); a NEW negative control is added and stays red (borrow into a *key* cell — refused because the abstracted invariant does not type); `packNav` and the whole existing suite show zero verdict changes beyond the pinned flips; the fable flagship's `GetMut`/`GetMutOrInsert` chain checks on a demonstration branch. Campaign result lands on branch `packed-borrows` with a review guide (what changed, the soundness argument, what to check, test flips) — NOT merged to main; the morning review gates it.
