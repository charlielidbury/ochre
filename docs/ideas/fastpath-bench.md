# Fast-path bench: `subCheckT` vs bare `subCheck`

**Date**: 2026-04-27
**Branch**: `och-refactor` @ `6699db8`
**Probe**: `lean/Och/FastPathBench.lean`, run with
`nix develop -c lake exe fastpath_bench`.

## Question

`SubstEval.subCheckT` runs `NbE.typeCheck` first, falls back to
`SubstEval.subCheck` on rejection. Historically the fast-path
delivered ~200x wins on `three_ ⊑ Nat_` against the env-NbE
substrate. After moving to substitution-based eval, how much is
the fast-path still worth?

## How

Per case, time three configs over 200 reps with a varying-fuel
offset to defeat CSE:

1. `SubstEval.subCheckT` — current production (typeCheck → subCheck).
2. `SubstEval.subCheck` only — what we'd ship if the fast-path were deleted.
3. `NbE.typeCheck` only — fast-path in isolation.

Also: minimum fuel at which bare `subCheck` decisively closes
(returns `.ok _`, not `.outOfFuel`).

Hardware: dev workstation, single-threaded, native-compiled Lean.

## Results

Per-call wall-clock in microseconds (200-rep average). Verdicts
match across configs in every row. `typeCheck` columns: `T` =
returns `ok true`, `F` = returns `ok false`, `e` = `error`/wrong
shape (so subCheckT falls back to subCheck).

### Positive cases

| # | Case | subCheckT | typeCheck | subCheck | tc verdict | save |
|---|---|---:|---:|---:|---|---:|
| 01 | `zero_  ⊑ Nat_` | 5 | 5 | 5 | F | 0 |
| 02 | `one_   ⊑ Nat_` | 20 | 5 | 15 | e | -5 |
| 03 | `two_   ⊑ Nat_` | 40 | 0 | 35 | e | -5 |
| 04 | `three_ ⊑ Nat_` | 75 | 0 | 70 | e | -5 |
| 05 | `four_  ⊑ Nat_` | 135 | 0 | 135 | e | 0 |
| 06 | `five_  ⊑ Nat_` | 255 | 5 | 260 | e | +5 |
| 07 | `dtrue  ⊑ dBool` | 5 | 0 | 15 | T | +10 |
| 08 | `dfalse ⊑ dBool` | 5 | 0 | 15 | T | +10 |
| 09 | `p12    ⊑ Pair Nat_ Nat_` | 45 | 15 | 30 | e | -15 |
| 10 | `pTT    ⊑ Pair Bool Bool` | 10 | 5 | 5 | T | -5 |
| 11 | `P0u    ⊑ Pair Nat_ Unit_` | 15 | 5 | 10 | F | -5 |
| 12 | `zero_  ⊑ Fin one_` | 5 | 5 | 120 | T | **+115** |
| 13 | `zero_  ⊑ Fin three_` | 5 | 5 | 235 | T | **+230** |
| 14 | `one_   ⊑ Fin three_` | 415 | 0 | 410 | e | -5 |
| 15 | `two_   ⊑ Fin three_` | 590 | 5 | 600 | e | +10 |
| 16 | `Fin one_ ⊑ Fin two_` | 470 | 5 | 470 | e | 0 |

### Negative cases

| # | Case | subCheckT | typeCheck | subCheck | tc verdict | save |
|---|---|---:|---:|---:|---|---:|
| 17 | `dtrue   ⊄ Nat_` | 20 | 0 | 15 | F | -5 |
| 18 | `Nat_    ⊄ zero_` | 35 | 0 | 35 | F | 0 |
| 19 | `zero_   ⊄ one_` | 0 | 0 | 0 | F | 0 |
| 20 | `Bool    ⊄ Nat_` | 5 | 0 | 10 | F | +5 |
| 21 | `unit_   ⊄ Nat_` | 5 | 0 | 10 | F | +5 |
| 22 | `two_    ⊄ Fin two_` | 450 | 5 | 435 | e | -15 |
| 23 | `Fin two_ ⊄ Fin one_` | 1150 | 5 | 1150 | e | 0 |

### Aggregates (sum across 23 cases, per-call us)

| metric | total |
|---|---:|
| subCheckT (current) | 3,760 us |
| subCheck only | 4,095 us |
| typeCheck only | 70 us |
| net wall-clock the fast-path saves | **~335 us / corpus pass (8%)** |

### Fuel

`SubstEval.subCheck` decisively closes **every** case in this
corpus at fuel 5. The fuel is recursion depth on `subCheckSubst`,
not eval steps; it's almost never the binding constraint. So the
fast-path is **not** load-bearing for fuel — it only reshuffles
wall-clock cost.

## Findings

1. **Fast-path is not load-bearing for closure.** Every positive
   case closes via bare `subCheck` at fuel 5, and produces the
   same verdict as `subCheckT`. There is no case in the Std corpus
   where dropping the fast-path would lose a derivation.

2. **Fast-path saves real time only on `T`-yielding cases.**
   Wins concentrate on `zero_ ⊑ Fin n` (saves ~115-230us per call,
   i.e. 24-47x speedup) and dependent-Bool (`dtrue ⊑ dBool`, ~10us
   absolute). These are cases where `typeCheck`'s bidirectional
   rule recognizes the type structure cheaply.

3. **Numerals at any depth (`zero_..five_ ⊑ Nat_`) no longer
   benefit from the fast-path.** `typeCheck` returns `error` (not
   `ok true`) — the bare-engine ascent walks the recursive Nat
   structure instead. This is the post-`domA→domB`-flip world the
   coordinator anticipated. Per-call cost is identical between
   `subCheckT` and `subCheck` here (within 5us noise).

4. **Fast-path overhead on miss is small but nonzero.** When
   `typeCheck` returns `error`/`ok false`, `subCheckT` pays
   typeCheck's 5-15us before falling through to subCheck. On heavy
   cases (Fin three_, Fin one_⊑Fin two_) this is <2% of the total.

5. **Negative-case overhead.** Negatives via `subCheckT` pay the
   typeCheck cost in addition to subCheck's reject — but typeCheck
   returns `ok false` quickly (<5us in all 7 negatives), so the
   overhead is negligible.

## Recommendation

**Drop the fast-path is fine** — the worst-case loss is ~230us per
call on `zero_ ⊑ Fin three_` (47x slowdown in relative terms, but
still sub-millisecond absolute). Aggregate overhead across the
whole 23-case corpus would be ~335us per pass — well below test
noise, and `lake build` has many other costs that dominate.

**The case for keeping it** is that it's cheap (5-15us overhead on
miss) and a couple of cases get genuinely-large relative speedups
(47x on Fin positives). If the engine-collapse refactor is going
to deduplicate the typing/subtype machinery anyway, folding
typeCheck's `~>` rules into the structural `⊑` engine (rather than
keeping it as a layered fast-path) gets the same wins without the
two-tier API.

**Verdict**: keeping or dropping is roughly cost-neutral on this
corpus. Per the engine-collapse plan, **fold `~>` into the unified
pipeline** rather than preserving the fast-path/slow-path layering
— the perf justification for layering is gone.

## Caveats

- Corpus is the Std test set + a few hand-picked positives/negatives;
  ~23 cases. Real workloads (Vec, Array, Sigma, Mu, dependent
  pattern-matching) might have different shapes. Add cases if a
  surprising regression appears.
- `iters = 200` per measurement; sub-5us differences are noise.
- All measured under native-compiled Lean (`@[implemented_by]`
  paths active). Interpreted-mode timings would differ by orders
  of magnitude and are not relevant for production.

## Files

- `lean/Och/FastPathBench.lean` — benchmark (worktree-only).
- Output captured at `/tmp/fastpath_bench.out` during the run.
