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

Not yours: M2 and the `Nat` match stored-type check (rule-audit, done on rule-tags); `armRecords` witness search (30 min max, then a ledger note).
