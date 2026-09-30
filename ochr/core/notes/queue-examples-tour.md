# examples-tour's queue (maintained by team-lead; re-read before starting each item)

Last updated 2026-09-30 by team-lead.

1. **Revert the ghost borrows and apply amended D65.**
   - `git revert` the ghost-borrow commits (8d918c9c).
   - Apply `Scratch/Reviewer9D65Amended.patch` (58a11a55). The rule: at a drop, a borrower held in a binding is ended, and a borrower still in flight is an error.
   - Replace the GhostBorrows block with a `Drops` block:
     - accepted and running: Bad2, Bad3, Bad4, D1–D4, AssignBot;
     - rejected: RetLocal, FR, Blk, G, UseG, FPZ.
   - Add the ledger row `dropEndsBound` (class soundness), and add `Naturality.PickEarly` to `accessInside`.
   - Tell prop-paper the block name. Acceptance is fuzz-port's `--drop 100`: 0 exec, 0 verdict, 0 renorm.
2. **D66** (ochr/docs/08). `Prop : Type₁`; `&A` iff `A : Type₀`, replacing the data-only check.
   - Function borrows and `&V` become accepted.
   - Borrows of proofs, propositions and types, and `Box(Prop)`, are rejected by the universe check.
   - Tell fuzz-port the new `--rules` expectations.
3. **Delete the old copy system**: `Config.d53`, `preD53`, runtime copy paths, the `moves` switch, the "cost" ledger row. Tell fuzz-port and prop-paper.
4. **A2.**
5. **Nat/Unit redeclaration.**

Not yours: M2 and the `Nat` match stored-type check (rule-audit, done on rule-tags); `armRecords` witness search (30 min max, then a ledger note).
