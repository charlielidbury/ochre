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
e.g. `dNat ⊑ dNat`. Post-fix, each such re-derivation hits the
`a == b` ptrEq guard in O(1), so the repeated work is cheap:
`NbE.typeCheck 5000 appendVec` is 32 ms total. A cross-call
memo-table would save a few ms but is not load-bearing.
-/

section Regression
open Std
-- Pre-ptrEq, dthree was the practical ceiling (322 s) and
-- dfive was untestable. Post-ptrEq, all numerals are flat
-- ~310-330 ms; dfive is the perf-regression sentinel.
def dfour := och{ dsucc dthree }
def dfive := och{ dsucc dfour  }
example : NbE.subCheck 800 dfive dNat = .ok true := by native_decide

-- `appendArrays` at its declared type: an A6-family
-- incompleteness (`domA` push gives the wrong ascent type
-- under the `n1`/`n2` binders). Found independently by the
-- perf and retire-subchecknf forks; pinned here so any
-- future `domB` re-enabling or RHS-ascent flips it visibly.
example : NbE.subCheck 5000 appendArrays
    (och{ λT:Type. λn1:dNat. λn2:dNat.
         Array_ n1 T → Array_ n2 T → Array_ (dadd n1 n2) T })
  = .ok false := by native_decide
end Regression
