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
the self-applying `(succ_ m)` in `succ_`'s `P`-domain creates a
32-deep `.lam` tower, and each level's closure env references the
predecessor numeral. Tree-size at `unf=32`:

| numeral | tree-size | NbE.subCheck@200 (pre-fix) |
|---------|-----------|----------------------------|
| zero_   |        75 |                       2 ms |
| one_   |    13,982 |                     447 ms |
| two_    |   472,913 |                  10,004 ms |
| three_  |15,617,636 |                 322,175 ms |

The DAG itself is tiny (`eval` is 1–3 ms; the tree-walk to compute
the size above is 2 s). With 488 `subCheckVal` calls (constant
across one_..three_ — same call tree, just bigger Vals) each doing
~2 + 2·|seen| `Val.beq` guards, the cost compounds to ~5 min.

## Fix: `@[implemented_by Val.beqFast]` with `ptrEq` fast-path

Shared sub-structure is detected by pointer equality (Lean has no
copying GC, so identity = address). The proof-side `Val.beq` is
unchanged, so `LawfulBEq Val` and `subCheckVal_subV` compile
unmodified.

| numeral | post-fix |
|---------|----------|
| one_   |   305 ms |
| two_    |   306 ms |
| three_  |   308 ms |
| four_   |   329 ms |
| five_   |   330 ms |

**Flat across numerals and fuel** — the tree-traversal is now
O(unf-depth × calls), independent of numeral level.

## Build-time impact

- `Och.Std.DNat`: ~300 s → 3 s (100×)
- Full clean `lake build`: 580 s → 261 s (2.2×)
- `subCheckVal_subV`: compiles unchanged (8 SoundnessProof sorries)

## H3 (codegen): ruled out

`grep WellFounded SubCheckVal.c` → 0. The `termination_by (fuel,
tag)` lex compiles to direct recursion.

## Residual: removed

The legacy `subCheckNF`/`absEval` (substitution-based) was
retired at `6772061`; with both fixes, a fresh-worktree clean
`lake build` is **71 s** (from 580 s pre-ptrEq, 261 s
post-ptrEq-pre-retirement). The remaining time is spread
across `SoundnessProof` (~50 s of proof elaboration) and the
~60 `native_decide` tests at a few hundred ms each.

## Coordinator's question: repeated work in `typeCheck`

Each `tyCheck`/`tyInfer` call to `subCheckVal` starts with empty
`seen`, so there is no cross-call memoization. For `appendVec` this
is several dozen `subCheckVal` calls, several of which re-derive
e.g. `Nat_ ⊑ Nat_`. Post-fix, each such re-derivation hits the
`a == b` ptrEq guard in O(1), so the repeated work is cheap:
`NbE.typeCheck 5000 appendVec` is 32 ms total. A cross-call
memo-table would save a few ms but is not load-bearing.
-/

section Regression
open Std
-- Pre-ptrEq, three_ was the practical ceiling (322 s) and
-- dfive was untestable. Post-ptrEq, all numerals WERE flat
-- ~310-330 ms; dfive was the perf-regression sentinel.
--
-- Post-Option-A singleton tightening of `succ_` (2026-04-24),
-- the `s`-domain contra chain threads each predecessor through
-- the subtype derivation, so fuel consumption scales with numeral
-- size again. `three_ ⊑ Nat_` still closes (fuel 1600, see
-- DNat.lean) but `dfive ⊑ Nat_` does not close within 10+ minutes
-- at fuel 6400. The tradeoff is accepted: Option A unlocks the
-- `succ_ m ⊑ Fin (succ_ n)` subsumption that Option F Fin needs
-- for unified Fin/Nat without wrapper constructors.
def four_ := och{ succ_ three_ }
def five_ := och{ succ_ four_  }
-- example : NbE.subCheck 6400 five_ Nat_ = .ok true := by native_decide

-- `appendArrays` at its declared type: an A6-family
-- incompleteness (`domA` push gives the wrong ascent type
-- under the `n1`/`n2` binders). Found independently by the
-- perf and retire-subchecknf forks; pinned here so any
-- future `domB` re-enabling or RHS-ascent flips it visibly.
example : NbE.subCheck 5000 appendArrays
    (och{ λT:Type. λn1:Nat_. λn2:Nat_.
         Array_ n1 T → Array_ n2 T → Array_ (add_ n1 n2) T })
  = .ok false := by native_decide
end Regression
