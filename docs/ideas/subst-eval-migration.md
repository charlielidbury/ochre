# Substitution-based eval — production migration

**Date**: 2026-04-26 (continued from `eval-subst-vs-env-benchmark.md`)
**Status**: phase 1 (production-grade module) + phases 2-3 (typed
wrapper + regressed-test uncomment) shipped on
branch `subst-eval-primary`.
**Predecessor doc**: `docs/ideas/eval-subst-vs-env-benchmark.md`
covers the benchmark that motivated this work (substitution-based
subCheck ~1100x faster than env-based NbE on Och's heaviest workload,
`three_ ⊑ Nat_`: 14.5 s → 13 ms).

## What landed

### Phase 1 — `EvalSubst.lean` as a production module

The original `lean/Och/EvalSubst.lean` was a benchmark-only port,
explicitly described in its docstring as "soundness-untested" and using
a `partial def` for everything. The refactor:

- Rewrote the top-level docstring: this is now Och's primary
  substitution-based evaluation pipeline, with the level-bvar trick
  documented as a deliberate single-namespace encoding of
  locally-nameless on top of `Expr` (no AST change). Trade-offs and
  verdict-parity-with-NbE (16/16 BeqBench) explicitly noted.
- Removed dead code (`liftToLevels`, `isStuckRec`, `spineArgs`).
- Added `@[inline] def isLevelIdx` for readability — replaces raw
  `k >= levelOffset` checks throughout.
- Added `subCheckT` — the typed entry point analogous to
  `NbE.subCheckT`. Tries `NbE.typeCheck` first (fast on positive
  cases via the syntactic-bidirectional walk), falls back to
  substitution-based `subCheck` on rejection or fuel exhaustion.
- Threaded `Och.TyCheck` import for `NbE.typeCheck` access.

Termination story:
- `evalSubst`, `substL`, `shiftL`: non-`partial def`. Lean accepts
  the recursion via implicit `(fuel, unf)` lex measure on
  `evalSubst`; the helpers are structurally recursive on the input
  `Expr`.
- `subCheckSubst` mutual block: remains `partial def`. The recursion
  interleaves WHNF re-evaluation with structural descent through
  binders, and a `decreasing_by` clause matching the NbE-domain
  `subCheckVal`'s `(fuel, _)` lex measure would require non-trivial
  termination work. The fuel parameter guarantees runtime
  termination. **Documented as a pending proof obligation in the
  module docstring.** No new sorries.

LOC: ~440 lines (~50 LOC bigger than legacy due to docstring rewrite +
typed wrapper; algorithm body unchanged structurally).

### Phase 2 — typed wrapper as primary path

`SubstEval.subCheckT` mirrors `NbE.subCheckT`'s strategy:

```
def subCheckT (fuel : Nat) (a τ : Expr) : Outcome Bool :=
  match NbE.typeCheck fuel a τ with
  | .ok true => .ok true
  | _ => subCheck fuel a τ
```

For positive cases that `typeCheck` accepts, both wrappers are
identically fast (typeCheck doesn't depend on the eval engine). For
positive cases that need conversion fallback, `SubstEval.subCheckT` is
~1000x faster than `NbE.subCheckT` on the singleton-Nat tower. For
negatives, `SubstEval.subCheckT` is similarly faster — `three_ ⊄ Fin
two_` drops from ~16 s (NbE) to ~37 ms (subst).

Both `NbE.subCheckT` and `SubstEval.subCheckT` are public; existing
tests calling `NbE.subCheckT` continue to work unchanged.

### Phase 3 — uncomment regressed tests

Tests that were commented out in `lean/Och/Std/*` due to env-based
subCheck timeouts have been uncommented and now pass:

| File | Test | Prior status | Now |
| --- | --- | --- | --- |
| `Std/DNat.lean` | `concEval … add_ zero_ two_ = two_` | "multiple minutes" | passes (~12 ms) |
| `Std/DNat.lean` | `concEval … add_ one_ one_ = two_` | "multiple minutes" | passes (~6 ms) |
| `Std/DNat.lean` | `concEval … add_ one_ two_ = three_` | "multiple minutes" | passes (~22 ms) |
| `Std/DNat.lean` | `concEval … double_ zero_ = zero_` | "multiple minutes" | passes (~1 ms) |
| `Std/DNat.lean` | `concEval … double_ one_ = two_` | "multiple minutes" | passes (~7 ms) |
| `Std/DNat.lean` | `three_ ⊑ Nat_` (subCheckT) | not in panel | passes (~0 ms via typeCheck fast-path) |
| `Std/DNat.lean` | `four_ ⊑ Nat_` (subCheckT) | not in panel | passes (~0 ms via typeCheck fast-path) |
| `Std/DNat.lean` | `five_ ⊑ Nat_` (subCheckT) | not in panel | passes (~0 ms via typeCheck fast-path) |
| `Std/DFin.lean` | `two_ ⊑ Fin three_` (subCheckT, fuel 16000) | "doesn't terminate quickly" | passes (~35 ms via SubstEval) |
| `Std/DFin.lean` | `two_ ⊄ Fin two_` (subCheckT, fuel 16000) | commented | passes (~15 ms via SubstEval) |
| `Std/DFin.lean` | `three_ ⊄ Fin two_` (subCheckT, fuel 16000) | commented | passes (~37 ms via SubstEval) |

**Two findings worth noting:**

1. **The `add_ … = …` "multiple minutes" comment was wrong.** Both
   `concEval` (existing) and `SubstEval.evalSubst` (new) close
   `add_ one_ two_ = three_` in ~22 ms. The comment likely reflected
   an earlier dNat-style Nat_ encoding where each succ was much more
   expensive; the current encoding is significantly cheaper. Pure
   eval (not subCheck) was never the bottleneck here.

2. **`subCheckT`'s typeCheck fast-path makes `four_/five_ ⊑ Nat_`
   tractable for *both* engines.** The path that exposes the 1000x
   speedup is the conversion fallback in `subCheckT` — and that
   triggers only for negative tests or for positive tests where
   typeCheck is incomplete. Most positive tests of literal numerals
   close via typeCheck without ever invoking subCheckVal/subCheckSubst.
   The 1000x bench number on `three_ ⊑ Nat_` was measured against
   bare `NbE.subCheck`, not `NbE.subCheckT`.

The headline value of `SubstEval.subCheckT` is therefore concentrated
on:
- **Negative subtype tests** at higher numerals (e.g. `three_ ⊄ Fin
  two_`): NbE 16 s → subst 37 ms.
- **Cases where typeCheck is incomplete** (the conversion fallback
  fires) — currently rare in the test corpus but matters for any
  future test that exercises non-bidirectional subtyping.
- **Bare `subCheck`** (no typeCheck wrapper): when the kernel calls
  the conversion check directly, e.g. `Subtype'`-derivation sanity or
  any consumer that doesn't have a bidirectional fast-path. Here the
  full 1000x speedup applies.

## Verification

- `lake build` passes on the full project (35 modules).
- `AxiomCheck` output unchanged: same 4 declaration-level sorries
  (`Soundness.soundness`, `Soundness.typeCheck_sound`,
  `Soundness.eval_quote_equiv_closed`, plus the typed-NbE in-progress
  family). Soundness boundary preserved.
- `lake exe eval_bench` shows verdict parity 16/16 on the BeqBench
  panel (NbE.subCheck vs SubstEval.subCheck).
- The new `runImpossibleSection` (§6 of the bench) verifies parity
  between `NbE.subCheckT` and `SubstEval.subCheckT` on the
  previously-impossible cases — both engines return the same
  verdicts.

## What did NOT land

Per the task ground rules ("No new sorries"; partial def OK if
documented), the following deliberate gaps exist:

1. **`subCheckSubst` mutual block remains `partial def`.** A
   non-partial form would need a `decreasing_by` clause matching the
   `(fuel, _)` lex measure that NbE-domain `subCheckVal` uses. The
   substitution-domain version interleaves WHNF re-evaluation with
   the recursion (the WHNF call uses `fuel + 1`, which doesn't
   trivially compose with the structural descent), making the
   termination measure harder to express. Keeping `partial def` here
   matches the semi-conservative status of `NbE.subCheckVal` (which
   *is* non-partial but uses a delicate measure that took several
   passes to land). Future work.

2. **Soundness against `subCheckVal` is empirical only.** The
   benchmark verifies 16/16 verdict agreement on BeqBench; the
   uncommented tests verify on a further 8 cases. There is no
   `theorem` of the form `subCheckSubst-sound : … → SubV …`. The
   user's instructions explicitly note this: "the existing Och gets
   the perf win regardless of whether the rewrite lands ... build it
   well anyway." A formal soundness proof would parallel the
   `subCheckVal_subV` chain in `SoundnessProof.lean` — a multi-week
   undertaking beyond this pass.

3. **The level-bvar trick is preserved** rather than replaced with a
   true locally-nameless representation (separate `fvar`
   constructor). Replacing it would require modifying `Expr` itself,
   which would touch ~6000 lines of soundness proofs. The trick is
   documented as a deliberate choice; future kernel rewrites
   (Novus/Agda track) would naturally drop it.

## How to use

For new tests in `Std/*.lean`:
- If `typeCheck` accepts (positive case where the term's principal
  type matches): `NbE.subCheckT` and `SubstEval.subCheckT` are
  equivalent. Pick either.
- If the test is a positive case where `typeCheck` rejects (rare),
  or any negative case at higher numerals: prefer
  `SubstEval.subCheckT` for fuel-budget tractability.
- For computation tests (`concEval` / `evalSubst`), the existing
  `concEval` is fine for small inputs; for `succ_`-tower-heavy
  computations, prefer `SubstEval.evalSubst` (an order of magnitude
  smaller HNFs).

For kernel internals:
- The "primary path" for the benchmark-validated speed win is bare
  `SubstEval.subCheck` (no typeCheck wrapper). Code that previously
  called `NbE.subCheck` directly should consider migrating.
- `SubstEval.subCheck` produces verdicts that match `NbE.subCheck`
  on all tested cases (verified by the bench's §2 parity panel).

## Files touched

- `lean/Och/EvalSubst.lean` — production refactor + `subCheckT` (~440 LOC)
- `lean/Och/EvalBench.lean` — added §6 (impossible-tests) and §6.5 (arith)
- `lean/Och/Std/DNat.lean` — uncommented arith tests; added 4_/5_ defs and
  3_/4_/5_ ⊑ Nat_ tests under both engines
- `lean/Och/Std/DFin.lean` — uncommented 2_⊑Fin3_, 2_⊄Fin2_, 3_⊄Fin2_
  tests under SubstEval.subCheckT
- `lean/Och/PerfProbe.lean` — removed local `four_`/`five_` defs (now
  in Std), updated regression doc

## Branch

`subst-eval-primary` (off `main`).
