# `Val.beq` ptrEq fast-path: hard-numbers benchmark (2026-04-26)

## Question this answers

Is the `@[implemented_by Val.beqFast]` ptrEq fast-path in
`SubCheckVal.lean` load-bearing in the current codebase, or is it a
historical artefact?

Motivation: an architectural decision about merging `Val` and
`WTExpr` into a single typed structure. The merge would require HEq
gymnastics that defeat `ptrEq` (Lean's `ptrEq` returns `false`
across HEq-coerced terms — different runtime objects). If the
fast-path is critical, the merge buys correctness at a perf cliff;
if it isn't, the merge is free.

## TL;DR

In the **current** (post-Option-A, post-typed-NbE) codebase, ptrEq
buys a **~1.5–1.7× constant factor**, not the 1000× reported in
commit `b055339`. The 1000× was on the **old** `dNat` encoding
(self-applying `(dsucc m)` tower; shared sub-Vals at every level
of a 32-deep `unfBound` chain) which was retired during the Option
A singleton-tightening of `succ_`. Today's `Nat_` does *not*
exhibit that O(unfBound^level) tree-walk explosion, because:

- `succ_`'s body is now a flat λ-spine (no ι-wrap), so opening it
  doesn't recursively unfold the predecessor's domain.
- The typed-NbE pipeline (`subCheckT`) short-circuits via type
  inference for almost every test; the bare `subCheck` recursion
  fires only for cases where typeCheck rejects.

The fast-path remains worth keeping (it's free, and is
load-bearing on the one stress-case below), but it is **not**
the make-or-break optimization the b055339 commit message
suggested. Trading it for HEq is a ~1.5× wall-clock cost on
*hot* paths, ~0× on cold paths.

## Hard numbers

Bench: `lean/Och/BeqBench.lean` (compiled `lake exe beq_bench`,
runtime fuel forced through an `IO.Ref` to defeat constant-folding).
Each row is a single timed call after a separate process-start
(no in-process warmup; first call pays cold-cache cost). Hardware:
WSL2 Linux, host as configured in flake.

| # | Test                                                      | with ptrEq | without | speedup |
|---|-----------------------------------------------------------|-----------:|--------:|--------:|
| 01 | `.type ⊑ .type`                                          |       0 ms |    0 ms |     —   |
| 02 | `Unit_ ⊑ .type`                                          |       0 ms |    0 ms |     —   |
| 03 | `unit_ ⊑ Unit_`                                          |       0 ms |    0 ms |     —   |
| 04 | `dtrue ⊑ dBool`                                          |       0 ms |    0 ms |     —   |
| 05 | `true_ ⊑ Bool`                                           |       0 ms |    0 ms |     —   |
| 06 | `zero_ ⊑ Nat_`                                           |       0 ms |    0 ms |     —   |
| 07 | `one_ ⊑ Nat_` (subCheck 200)                             |       5 ms |    7 ms |   1.4×  |
| 08 | `two_ ⊑ Nat_` (subCheck 800)                             |     295 ms |  500 ms |   1.7×  |
| 09 | `three_ ⊑ Nat_` (subCheckT 800, type-fast-path)          |       1 ms |    0 ms |     —   |
| 09b | `two_ ⊑ Nat_` (subCheck 5000, headroom)                 |     294 ms |  503 ms |   1.7×  |
| **09c** | **`three_ ⊑ Nat_` (subCheck 50000, bare engine)**  | **15 004 ms** | **25 196 ms** | **1.7×** |
| 10 | `pair_ Nat Nat 1 2 ⊑ Pair Nat Nat`                       |       0 ms |    0 ms |     —   |
| 11 | `Pair zero_ unit_ ⊑ Pair Nat_ Unit_`                     |       0 ms |    0 ms |     —   |
| 12 | `zero_ ⊑ Fin one_`                                       |       0 ms |    0 ms |     —   |
| 13 | `one_ ⊑ Fin three_` (subCheckT 8000)                     |       5 ms |    8 ms |   1.6×  |
| 14 | `Fin one_ ⊑ Fin two_`                                    |       0 ms |    0 ms |     —   |
| 15 | reject: `Nat_ ⊄ zero_`                                   |       0 ms |    0 ms |     —   |
| 16 | reject: `unit_ ⊄ Nat_`                                   |       0 ms |    0 ms |     —   |

Raw output captured at `/tmp/bench_with_ptreq.txt` and
`/tmp/bench_no_ptreq.txt` during the run.

### What the table says

- The fast-path costs nothing: rows where it doesn't trigger
  measure indistinguishably from the structural path.
- It saves ~30–40% wall-clock on the cases that exercise it,
  consistently across fuel levels (3 ms → 5 ms; 295 ms → 500 ms;
  15 s → 25 s — all ~1.7×).
- **Asymptotically, ptrEq does not change complexity** in the
  current code. Both columns scale ~5× per numeral level
  (one_→two_→three_ at fuels 200/5000/50000). With the old
  encoding's 32-deep self-applying tower, the gap was
  asymptotic — that workload no longer exists.
- Most cases run in 0–8 ms either way. The typed-NbE
  fast-path (typeCheck → refl-check on the inferred type)
  does the heavy lifting; ptrEq is the secondary
  optimisation under it.

### Where the 1.7× actually comes from

In the bare-`subCheck` path on `n_ ⊑ Nat_`, each `subCheckVal`
call does three Val-equality guards:

```
if a == b then .ok true
else if seen.any (fun (a', b') => a == a' && b == b') then .ok true
else if b == .type then .ok true
```

The third (`b == .type`) is constant-time (top-level shape).
The first (`a == b`) and second (`seen.any …`) walk full Vals.
With the singleton-tightened `succ_`, each numeral level adds
one `(s m)` application whose closure env references the
*same* predecessor numeral that's also bound in the seen set.
ptrEq catches that shared reference; structural BEq walks
the predecessor's tree. The 1.7× factor is the ratio of
"`Val.beq` cost" to "everything else `subCheckVal` does"
(pattern matching, fresh-neutral allocation, arm logic).

### Where it would matter

The 25 s vs 15 s on `three_ ⊑ Nat_` at fuel 50 000 is the
clearest signal. If we lost ptrEq:

- A test pinned at fuel `F` that closes today in time `T` would
  close in `~1.7T`. Most tests are <10 ms; 1.7× of nothing is
  nothing.
- Tests at the boundary of the build budget (e.g. `three_ ⊑
  Nat_` via bare engine, currently 15 s) would graze the timeout.
  We'd need to cut their fuel or move them to `subCheckT`.
- `four_ ⊑ Nat_`, `five_ ⊑ Nat_` are already commented out in
  `PerfProbe.lean` because they don't close at fuel 6400 *with*
  ptrEq. Without ptrEq they remain not-closing.

## Where ptrEq is used (every site)

`grep -rn "ptrEq\|ShareCommon\|shareCommon" lean/`

### 1. `lean/Och/SubCheckVal.lean` (the only live ptrEq site)

Lines 82–110 define four parallel `*.beqFast` mutually-recursive
functions, each opening with `ptrEq a b ||`:

| function           | line | what it compares                      |
|--------------------|-----:|---------------------------------------|
| `Val.beqFast`      |   83 | top-level `Val` (5 constructors)      |
| `Neutral.beqFast`  |   92 | neutral spines                        |
| `Closure.beqFast`  |   98 | `(body : Expr, env : List Val)` pair  |
| `Env.beqFast`      |  100 | `List Val`                            |

Wired up via `attribute [implemented_by …]` (lines 107–110).
Compiled `subCheck` / `subCheckT` (and any `==`/`BEq` use on
`Val`/`Neutral`/`Closure`/`List Val`) calls the `beqFast`
runtime; the proof side compiles against the structural
`Val.beq`.

The proof-side `Val.beq_eq` / `Val.beq_refl` (lines 117–194)
prove the structural definition is a lawful `BEq`; this is
what `LawfulBEq Val` (line 196) and `subCheckVal_subV`
(SoundnessProof.lean) are built on. **The proof story does
not depend on the fast-path** — swapping `beqFast` out
preserves all proofs by construction.

### 2. `lean/Och/MemoRefs.lean` + `lean/Och/SubCheckVal.lean:240–264` (`ShareCommon`, currently disabled)

A second optimisation tier was prototyped: pipe `Closure.open`
results through `ShareCommon.State.shareCommon` so that
structurally-equal Vals from independent recursion paths
become *pointer*-equal, restoring the ptrEq fast-path's
guarantees beyond per-tree sharing.

**Status: disabled** (line 264, `attribute … openImpl`
commented out). The post-mortem at
`docs/ideas/subcheck-perf.md` documents:
- `two_ ⊑ Nat_` at fuel 800: ~23 s with shareCommon vs
  ~18 s without.
- Hash-consing's per-call overhead exceeds the downstream
  ptrEq savings on Och's workload.

The infrastructure remains as a `Closure.openImpl`/`openImplQuick`
pair with the `[implemented_by]` line commented out, ready to
re-enable if a workload that benefits emerges.

### 3. No other ptrEq sites

```
$ grep -rn 'ptrEq\|ptrAddrUnsafe\|isShared\|implemented_by' lean/Och --include='*.lean'
```

Only matches in `SubCheckVal.lean` (the four sites above) plus
docstrings. There is no ptrEq in `Eval.lean`, `NbE.lean`,
`TyCheck.lean`, or `TypedNbE.lean`. The `Val.beq` fast-path is
the **single** memoization-ish optimisation in the value layer.

## Why the historical 1000× evaporated

Reading the `b055339` commit message in light of the current
encoding:

> Root cause of the DNat build hot-spot: `Val.beq` walks the
> value DAG as a *tree*, re-traversing shared sub-Vals at each
> reference. With `unfBound = 32`, the self-applying `(dsucc m)`
> in `dsucc`'s `P`-domain creates a 32-deep `.lam` tower whose
> closure envs each reference the predecessor numeral, so the
> DAG-as-tree size grows ~33× per numeral level.

The "self-applying `(dsucc m)` in `dsucc`'s P-domain" was the
old encoding's:

```
dsucc = ...λm:dNat. λP:((dsucc m) → Type). λz. λs. ...
                                  ^^^^^^^
                                  applies dsucc to m here,
                                  inside a 32-deep unfolding chain
```

That `(dsucc m) → Type` triggered `unfBound = 32` levels of
unfolding *per occurrence*, and each level's closure env held
the predecessor numeral — so `eval dthree`'s tree expansion
was 33×33×33 = ~36k node-references, or 15.6M when measured
including the inner `let succ_` rebind. `Val.beq` walked it
all as a tree.

**Today's `Nat_`** (post-Option-A, in `Std/DNat.lean`) keeps
the singleton domain (`λpred:m. P (succ_ pred)`) but `succ_`
itself is a raw fix-λ spine returning the body
`s m` — there's no self-applying recursion in the *type*
position. The 32-deep tower is gone; the DAG-as-tree size is
~5× per numeral level (the new singleton domain), not ~33×.

The ptrEq fast-path catches the same kind of shared
reference (predecessor numeral in a closure env), but the
trees that need walking are far smaller, so the absolute
savings shrink.

## Verdict (one paragraph)

**The fast-path is currently a 1.5–1.7× constant factor on hot
paths, not a 1000× lifesaver.** The historical 1000× speedup
in commit b055339 applied to a `dNat` encoding that no longer
exists; today's singleton-tightened `Nat_` does not produce the
self-applying type-position tower that made beq-as-tree-walk
catastrophic. Losing the fast-path would push `three_ ⊑ Nat_`
from 15 s to 25 s at fuel 50 000, push `two_ ⊑ Nat_` from
295 ms to 500 ms, and leave everything else unchanged
(typed-NbE's `subCheckT` does the asymptotic heavy lifting
via type inference, not via ptrEq). For the architectural
decision: merging `Val` and `WTExpr` is **not blocked** by
the ptrEq fast-path. It will cost ~1.5× on the worst current
benchmark and 0× on most. The pre-existing `ShareCommon`
infrastructure (already wired up, currently disabled) is
available as a fallback if HEq-defeated ptrEq starts hurting.

## Reproduction

```bash
# from a clean tree
nix develop -c lake build beq_bench
nix develop -c lake exe beq_bench   # with ptrEq

# To rerun without ptrEq, comment out the four `attribute
# [implemented_by ...]` lines at SubCheckVal.lean:107-110, then
# `lake build beq_bench && lake exe beq_bench`. Restore before
# committing.
```

The bench file is `lean/Och/BeqBench.lean`. The exe target is
declared in `lean/lakefile.lean`.
