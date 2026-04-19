import Och.Macro
import Och.SubCheckVal
import Och.TyCheck
import Och.Std.Vec
import Och.Std.Array
import Och.Eval
open NbE

/-! # Performance probe & root-cause findings

## Root cause (H1, confirmed)

`Val.beq` walks the Val DAG as a *tree*: shared sub-Vals are
re-traversed at each reference. With `unfBound = 32` (NbE.lean:83),
the self-applying `(dsucc m)` in `dsucc`'s `P`-domain creates a
32-deep `.lam` tower, and each level's closure env references the
predecessor numeral. Tree-size at `unf=32`:

| numeral | tree-size | NbE.subCheck@200 (pre-fix) |
|---------|-----------|----------------------------|
| dzero   |        75 |                       2 ms |
| done_   |    13,982 |                     447 ms |
| dtwo    |   472,913 |                  10,004 ms |
| dthree  |15,617,636 |                 322,175 ms |

The DAG itself is tiny (`eval` is 1–3 ms; the tree-walk to compute
the size above is 2 s). With 488 `subCheckVal` calls (constant
across done_..dthree — same call tree, just bigger Vals) each doing
~2 + 2·|seen| `Val.beq` guards, the cost compounds to ~5 min.

## Fix: `@[implemented_by Val.beqFast]` with `ptrEq` fast-path

Shared sub-structure is detected by pointer equality (Lean has no
copying GC, so identity = address). The proof-side `Val.beq` is
unchanged, so `LawfulBEq Val` and `subCheckVal_subV` compile
unmodified.

| numeral | post-fix |
|---------|----------|
| done_   |   305 ms |
| dtwo    |   306 ms |
| dthree  |   308 ms |
| dfour   |   329 ms |
| dfive   |   330 ms |

**Flat across numerals and fuel** — the tree-traversal is now
O(unf-depth × calls), independent of numeral level.

## Build-time impact

- `Och.Std.DNat`: ~300 s → 3 s (100×)
- Full clean `lake build`: 580 s → 261 s (2.2×)
- `subCheckVal_subV`: compiles unchanged (8 SoundnessProof sorries)

## H3 (codegen): ruled out

`grep WellFounded SubCheckVal.c` → 0. The `termination_by (fuel,
tag)` lex compiles to direct recursion.

## Residual (261 s): legacy `subCheck` in Vec/Array

`Och.Std.Vec` (181 s) and `Och.Std.Array` (43 s) dominate the
post-fix build. Both use the *legacy* Expr-domain `subCheck`
(Eval.lean's `subCheckNF` via `absEval`) for several tests:

| test                                    | legacy | NbE |
|-----------------------------------------|--------|-----|
| `subCheck 5000 appendVec (λT. Vec T→…)` | 9.8 s  | 8 ms|
| `subCheck 5000 appendArrays (…)`        | 9.4 s  | —   |
| `NbE.typeCheck 5000 appendVec (…)`      |   —    |32 ms|
| `NbE.subCheck 400 vecResult (Vec Nat_)` |   —    |47 ms|

The legacy checker is substitution-based (`absEval` does
`body.subst 0 arg` at every β), copying the Expr tree per step.
That is the known limitation NbE was introduced to address; it is
not fixable without making `absEval` closure-based — i.e., turning
it into NbE. Migrating these tests to `NbE.subCheck` (the canonical
checker; agreement covered by `divergenceSweep_onlyA6`) is the
correct change, not a workaround. (Done in a separate commit.)

## Coordinator's question: repeated work in `typeCheck`

Each `tyCheck`/`tyInfer` call to `subCheckVal` starts with empty
`seen`, so there is no cross-call memoization. For `appendVec` this
is several dozen `subCheckVal` calls, several of which re-derive
e.g. `dNat ⊑ dNat`. Post-fix, each such re-derivation hits the
`a == b` ptrEq guard in O(1), so the repeated work is cheap:
`NbE.typeCheck 5000 appendVec` is 32 ms total. A cross-call
memo-table would save a few ms but is not load-bearing.
-/

-- Verify NbE.subCheck agrees with legacy on the tests being
-- migrated. The `testArr*`/`testVec*` cases are `private` in
-- their modules, so verified there directly; the public ones:
section Agreement
open Std
example : NbE.subCheck 1000 unit_ (och{ Array_ done_ Nat_ }) = .ok false := by native_decide
example : NbE.subCheck 1000 (och{ Vec Nat_ }) Nat_ = .ok false := by native_decide
example : NbE.subCheck 1000 zero_ (och{ Vec Nat_ }) = .ok false := by native_decide
example : NbE.subCheck 5000 appendVec (och{ λT:Type. Vec T → Vec T → Vec T })
  = .ok true := by native_decide
-- `appendArrays`: NbE.subCheck AND NbE.typeCheck return
-- `.ok false` while legacy `subCheck` returns `.ok true`.
-- This is an NbE incompleteness *outside* the divergence
-- sweep's 26-term corpus (hence not in
-- `a6KnownIncompleteness`). Array:175 must stay on the
-- legacy checker. (Out of scope for this perf fix; flagged
-- for the parent.)
example : NbE.subCheck 5000 appendArrays
    (och{ λT:Type. λn1:dNat. λn2:dNat.
         Array_ n1 T → Array_ n2 T → Array_ (dadd n1 n2) T })
  = .ok false := by native_decide
end Agreement
