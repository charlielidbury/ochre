# examples-tour's queue (maintained by team-lead; re-read before starting each item)

Last updated 2026-10-01 by team-lead. Your current item is 6, erased moves.

1. (REASSIGNED 2026-09-30 to d65-lane: revert the ghost borrows and land amended D65. Do NOT do this item.)
2. (DONE) **D66** (ochr/docs/08): `Prop : Type₁`; `&A` iff `A : Type₀`.
3. (DONE at 042a06f7) **Delete the old copy system**.
4. **A2.** After item 6, if not already done.
5. **Nat/Unit redeclaration.** After item 6, if not already done.
6. **CURRENT: one mental model, "using a variable consumes it".** The user approved this on 2026-10-01. Part A (Eq sides apart) is DONE at 9c406bf5. Part B is on branch `erased-moves` (d4c9a24d):
   - Reads inside statements move.
   - A move doesn't count as an outer-place effect under D41.
   - Every argument of a type- or proof-returning call runs on its own copy, so Eq and Id are ordinary instances.
   - No exception for an Id side moving out through a borrow: migrate those sites to `clone(*x)`.
   - The Fn rule isn't applied to statement-position bodies.
   - Delete ghosts. Id observes only places written or borrowed.
   - Make it the default and add a ledger row.
   - Update DECISIONS, RULES, the paper and OCHR_BOOK (§5 rule 1, §7 copy idiom). The book's rule: "using a variable consumes it; a statement, and each argument of a statement, runs on its own copy of the state".
   - **Landing condition:**
     - all builds and tests are green, with the default config rerun;
     - every residual flip is intended or migrated, and any unexplained flip is reported before landing;
     - fuzz statuses are unchanged (at most 6 workers, taskset 0-14);
     - every paper-printed program checks, and the page count is unchanged.
   - Land by FF-CAS, rebasing over callform if it lands first.

7. **Follow through `&E` (D66) in the arrays library, after item 6.** User request, 2026-10-01: "make sure to follow through all the consequences of that &E".
   - **Generic `GetMut`.** Make `GetMut(E, n, s, i, h) : &E` and its lemmas (`GetMutSet`, …) generic. Delete `GetMutB` and point its callers at `GetMut(List(Entry), …)`.
   - **Remove `Read`.** The user's reason: "copying elements should be left to the caller so they are aware they are doing a copy". Callers write `let r = GetMut(E, n, s, i, h); clone(*r)`, or `*r` for a copy type such as `Word`. Restate every `Read` lemma and test through `GetMut`, or delete it where it only tested `Read`. Sites: 16Arrays (14), 18DependentFields (2), the bench GUIDE.md and sandbox.py, OCHR_BOOK §9, and the paper (impl.typ's list of primitives, and anything printed).
   - **`Swap` without copies.** Split the view with `WithSplit`, borrow element `i` of the left piece and element 0 of the right piece with `GetMut`, and swap through the two borrows by moves (`let t = *a; *a := *b; *b := t`). Case on `i < j`, `j < i`, `i = j`. The lead checked this at i < j against ochr-core 297dff47 (`SwapLt`, plus a concrete run). See /home/charlielidbury/.claude/jobs/16809284/tmp/book/TG.lean, which also shows that two `GetMut`s on one view are rejected. Keep `SwapIsSwapS` (`Swap` equals writing `SwapS`): prove it if `refl` no longer does, and report if it can't be proved.
   - **`Set`.** If its lemmas still go through, make it an ordinary function written with `GetMut` (`let r = GetMut(…); *r := x`) instead of a native. That leaves six natives: AsSlice, GetMut, WithSplit, empty, push, pop. If it gets awkward, keep it native and report why.
   - **Notes.** Rewrite the K1 note at the top of 16Arrays and the header's clone count. If `&Cells(E, n)` at an unknown `n` is now well formed too, say whether the `SliceOf` wrapping of cell tails can go, but don't change the representation without asking.
   - **Landing condition** as item 6: green builds and tests, fuzz statuses unchanged, every paper-printed program checks, page count unchanged.
8. **Generic `V` in the Ochr hashmap benchmark packages, after item 7.** `ochr/bench/hashmap/SPEC.md` says the `ochr` and `ochr-2p` packages stay word-valued "pending D66"; D66 has landed. Move both to the generic API that SPEC §3 describes:
   - `Bucket(V)`;
   - `contains(&m, k) : Bool`;
   - `get(&m, k, h : Contains(*m, k)) : &V`;
   - `get_mut → &V`;
   - `SlotMut` replaced by the generic `GetMut`;
   - the H rows split into their `contains` and value parts.
   Update the SPEC rows that say "Pending D66". The acceptance is the package's own: the reference solution passes `grade.sh`, the skeleton's holes are named, and the sandbox builds. This item may be reassigned to a fresh agent if you're still busy.

Not yours: M2 and the `Nat` match stored-type check (rule-audit, done on rule-tags); `armRecords` witness search (30 min max, then a ledger note).
