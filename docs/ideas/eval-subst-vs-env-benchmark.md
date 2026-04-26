# Substitution-based vs Env-based (NbE) eval — benchmark report

**Date**: 2026-04-26
**Question**: For an intrinsic-typing rebuild, would moving from
NbE-style closure-based eval to substitution-based eval slow Och's
type checker enough to matter?
**TL;DR (post-fix)**: **Substitution wins decisively** on Och's
heaviest workload. On `three_ ⊑ Nat_` (currently 14.5 s under NbE),
the substitution-based subCheck completes in **13 ms — about 1000×
faster**. Total wall-clock on the BeqBench panel drops from 14.7 s
(NbE) to 52 ms (subst). Hash-consing makes no measurable difference
because subst's HNF outputs are already small (3 orders of
magnitude smaller than NbE's full normal forms). The architectural
recommendation is **substitution is the better choice for the
intrinsic-typing rebuild** on perf grounds, in addition to its
~200–400 LOC simplicity benefit.

This is the opposite of the "subst is generally slower because of
lost sharing" prior. The Och-specific reason is that NbE's wins
require closure-DAG sharing under the structural-compare hot
path — and Och's `subCheckVal` walks that DAG **as a tree**
(retraversing shared sub-Vals at every reference), so the sharing
benefit never materialises at the algorithm where it matters.

## What was built

- `lean/Och/EvalSubst.lean` — substitution-based eval
  (`SubstEval.evalSubst`) and a hand-port of `subCheckVal`
  (`SubstEval.subCheck` / `subCheckSubst`). The port uses eager
  substitution: applying a `λ` walks the body and copies the
  argument into every occurrence; opening a binder for under-the-
  binder eval substitutes a "level-bvar" sentinel (`bvar
  100_000_000+k`) that the custom `substL`/`shiftL` machinery
  treats as absolute (never decrements/shifts).
- `lean/Och/EvalBench.lean` (exe `eval_bench`) — four-section
  bench: pure eval timings, subCheck parity, Church-numeral
  synthetic, structural-compare proxy.
- Hash-consing variant `evalSubstHashConsed` that pipes the result
  through `Lean.ShareCommon.shareCommon'`.

The subst port is **not** soundness-verified or termination-proven.
It is `partial`, mirrors `subCheckVal` arm-for-arm, and the
verdicts now agree on **all 16/16** BeqBench cases (after fixing
the WHNF-on-entry bug — see below).

## Methodology

- All timings via `IO.monoMsNow` around the call. A runtime-supplied
  `IO.Ref Nat` fuel offset prevents Lean from constant-folding the
  compute.
- Both engines threaded with the same `unfBound = 32` for fix/iota
  unfolds.
- Same source terms (BeqBench panel, plus a Church-numeral
  synthetic set, plus a pure-eval-without-subCheck set, plus a
  structural-compare proxy).
- Run on `nix develop -c lake exe eval_bench` from `/lean/`. Single
  trial, warm cache. Numbers vary ±10% run-to-run; orders of
  magnitude are stable.

## §1. Pure eval timings

This section measures **eval cost only**, not subtype check. Three
endpoints:

- `NbE.eval`: closure-domain WHNF (no quote pass).
- `NbE.nf`: full Expr-domain NF (eval + quote-under-binders).
- `SubstEval.evalSubst`: Expr-domain HNF.
- `SubstEval.evalSubst + ShareCommon`: same plus hash-consing of
  the output Expr.

Sizes are number of `Expr` constructors.

| Source             | env(WHNF) | env(NF) ms | NF nodes        | subst HNF ms | subst HNF nodes | subst+HC ms |
| ------------------ | --------- | ---------- | --------------- | ------------ | --------------- | ----------- |
| Type               | 0         | 0          | 1               | 0            | 1               | 0           |
| Unit\_             | 0         | 0          | 5               | 0            | 5               | 0           |
| unit\_             | 0         | 0          | 5               | 0            | 5               | 0           |
| dtrue              | 0         | 0          | 13              | 0            | 13              | 0           |
| true\_             | 0         | 0          | 7               | 0            | 7               | 0           |
| zero\_             | 0         | 0          | 13              | 0            | 13              | 0           |
| **one\_**          | 0         | 1          | **7,829**       | 0            | **463**         | 0           |
| **two\_**          | 0         | 26         | **515,869**     | 1            | **1,813**       | 0           |
| **three\_**        | 0         | **1,709**  | **33,538,469**  | 2            | **5,863**       | 2           |
| Nat\_              | 0         | 0          | 59              | 0            | 61              | 0           |
| Pair Nat\_ Nat\_   | 0         | 0          | 125             | 0            | 129             | 0           |
| Fin one\_          | 0         | 0          | 1,219           | 1            | 841             | 1           |
| Fin three\_        | 0         | 0          | 1,771           | 16           | 2,641           | 15          |

**Substitution HNF is 3 orders of magnitude smaller than NbE's
full NF on the singleton-Nat tower.** NbE eval (WHNF) is constant-
time on this panel — closures share structure — but the moment you
ask for a normal form (via `quote`), the closure DAG is walked as a
tree and materialises 33.5 M Expr nodes for `three_`.

Substitution doesn't have this materialisation cost because it
**stops at HNF** — it doesn't go under λ-binders during eval. The
under-binder cost gets paid lazily, by `subCheckSubst`'s recursive
descent. And — as §2 shows — that descent is *also* much cheaper
than NbE's because the trees being compared are 3 orders of
magnitude smaller.

### Substitution blowup: linear-ish in n

| n    | subst HNF nodes | NbE NF nodes |
| ---- | --------------: | -----------: |
| 0    | 13              | 13           |
| 1    | 463             | 7,829        |
| 2    | 1,813           | 515,869      |
| 3    | 5,863           | 33,538,469   |

Subst HNF size: roughly 3-4× per n (closer to linear than NbE NF's
~64× per n). The ratio of NbE_NF / subst_HNF grows with n: at n=3,
NbE NF is ~5,700× bigger than subst HNF.

## §2. subCheck parity

The headline numbers, post-fix:

| #   | Case                                  | NbE ms     | subst ms | speedup    |
| --- | ------------------------------------- | ---------: | -------: | ---------: |
| 01  | typeRefl                              |          0 |        0 | n/a        |
| 02  | Unit\_ ⊑ Type                          |          0 |        0 | n/a        |
| 03  | unit\_ ⊑ Unit\_                        |          0 |        0 | n/a        |
| 04  | dtrue ⊑ dBool                         |          0 |        0 | n/a        |
| 05  | true\_ ⊑ Bool                          |          0 |        0 | n/a        |
| 06  | zero\_ ⊑ Nat\_                         |          0 |        1 | (subst slower by 1ms) |
| 07  | one\_ ⊑ Nat\_                          |          4 |        0 | **>4×**    |
| 08  | two\_ ⊑ Nat\_                          |        285 |        3 | **95×**    |
| 09  | **three\_ ⊑ Nat\_**                   | **14,459** | **13**   | **~1100×** |
| 10  | p12 ⊑ Pair Nat\_ Nat\_                 |          0 |        3 | (subst slower by 3ms) |
| 11  | Pair zero\_ unit\_ ⊑ Pair Nat\_ Unit\_ |          0 |        0 | n/a        |
| 12  | zero\_ ⊑ Fin one\_                     |          0 |        1 | (subst slower by 1ms) |
| 13  | one\_ ⊑ Fin three\_                    |          5 |       23 | 0.22× (subst 4.6× slower) |
| 14  | Fin one\_ ⊑ Fin two\_                  |          0 |        7 | (subst slower by 7ms) |
| 15  | Nat\_ ⊄ zero\_                         |          0 |        1 | (subst slower by 1ms) |
| 16  | unit\_ ⊄ Nat\_                         |          0 |        0 | n/a        |

**Total: NbE 14,753 ms vs subst 52 ms — subst is 284× faster on the
panel total, and ~1100× faster on the worst case.**

All 16 verdicts agree (post-fix; see "Bug fix" below).

### What the slowdown cases tell us

The cases where substitution is slower in absolute terms:

- Case 13 (`one_ ⊑ Fin three_`): 23 ms vs 5 ms. Subst is 4.6× slower
  here because Fin's structure forces multiple iotaIntro paths, and
  each path re-evaluates an iota body against a new `self`. Each
  re-eval substitutes through, growing the working set.
- Cases 06, 10, 12, 14, 15 are all ≤ 7 ms either way. The
  per-call constant of subst (entering subCheckSubst forces WHNF on
  both sides — see fix below) is 1–2 ms; for tiny inputs that
  dominates.

These are the visible costs of **eager substitution**: every
recursive call to `subCheckSubst` re-checks WHNF, costing constant
overhead. NbE only does eval once (top-level) and then operates on
already-Vals.

For an intrinsic-typing rebuild, this overhead might be reducible:
- Skip the WHNF-on-entry once the call is known to receive Exprs
  that are already in WHNF (most recursive calls in the iotaIntro
  / fix-unfold arms come from `evalSubst` results which are
  already in WHNF).
- Hash-cons inputs to short-circuit `==` — but as Section 1 shows,
  HC is a no-op on tree sizes this small.

## §3. Church-numeral synthetic (no fix/iota)

Pure-λ programs. Both engines agree on every case; no recursion
arms in play.

| case               | env ms | subst ms | subst size |
| ------------------ | -----: | -------: | ---------: |
| church n=2  force  | 0      | 0        | 5          |
| church n=4  force  | 0      | 0        | 9          |
| church n=8  force  | 0      | 0        | 17         |
| church n=16 force  | 0      | 0        | 33         |
| church n=32 force  | 0      | 0        | 65         |
| plus 2 3   force   | 0      | 0        | 11         |
| plus 4 4   force   | 0      | 0        | 17         |
| plus 8 8   force   | 0      | 0        | 33         |
| plus 16 16 force   | 0      | 0        | 65         |
| mul 4 4    force   | 0      | 0        | 33         |
| mul 8 8    force   | 0      | 1        | 129        |
| mul 16 16  force   | 0      | 7        | 513        |

Substitution handles pure λ-calculus comfortably. `mul 16 16`
forces 256 β-reductions and produces a 513-node output in 7 ms.
Without recursive types in the picture, the engines are
indistinguishable.

## §4. Structural compare cost (proxy)

Question: even ignoring sub-checking, how expensive is *just
comparing two values for equality* under each representation?

| case               | NbE eval+Val.beq ms | subst eval+Expr== ms | result |
| ------------------ | ------------------: | -------------------: | ------ |
| one\_ vs Nat\_     | 0                   | 0                    | both: false |
| two\_ vs Nat\_     | 0                   | 1                    | both: false |
| three\_ vs Nat\_   | 0                   | 1                    | both: false |
| two\_ vs three\_   | 0                   | 2                    | both: false |
| one\_ vs one\_     | 0                   | 0                    | both: true  |
| two\_ vs two\_     | 1                   | 1                    | both: true  |
| **three\_ vs three\_** | **18**          | **3**                | **both: true** |
| Nat\_ vs Nat\_     | 0                   | 0                    | both: true  |
| Fin three\_ vs same | 19                 | 31                   | both: true  |

`three_ vs three_`: NbE Val.beq takes 18 ms (closure-tree-walk on
the 33M-equivalent DAG, with `ptrEq` fast-path); subst Expr== takes
3 ms (walks 5,863 nodes; equal subtrees short-circuit pointwise via
the derived `==`).

This dovetails with the §2 finding: subst's smaller trees are
faster to walk, and the savings compound through the recursive
subCheck descent.

## §5. Sensitivity — mitigations

The headline 3-row table: how does each mitigation affect the
worst case (`three_ ⊑ Nat_` at fuel 50 000)?

| variant                       | wall-clock | notes |
| ----------------------------- | ---------- | ----- |
| **NbE (current default)**     | **14,459 ms** | closure-DAG retraversed as tree by subCheckVal |
| **Subst (naive)**             | **13 ms**  | the architectural change alone delivers ~1100× speedup |
| Subst + ShareCommon hash-cons | ~ 13 ms    | no measurable effect; HNF outputs already small |

Hash-consing was *the* big mitigation we expected to need. The
finding is: **it isn't**. Substitution-based subCheck handles
Och's heaviest workload natively without any post-processing.

For more aggressive mitigations:
- **Substitution memoization** (cache `(body, j, repl) → result`):
  not measured; expected gain modest on this workload because the
  current cost is 13 ms — diminishing returns.
- **Explicit substitutions** (λσ-style): would help if substitution
  ever did become a bottleneck on a different workload. Not needed
  for the BeqBench panel.

## §6. Bug fix that made the numbers light up

In the first pass of the port, 5 / 16 BeqBench cases produced
verdict disagreements (subst returned `false` where NbE returned
`true`). Each disagreement was a positive case involving a
`succ_`-applied numeral.

Root cause: in `subCheckSubst`, equality and seen-list lookups
compare Exprs structurally (`==`), which doesn't see through
un-evaluated forms. Specifically, the contra-check on dependent
function types in:

```
λP:(succ_-fix zero_) → Type. ...   ⊑   λP:Nat_ → Type. ...
```

recursively triggers `succ_-fix zero_ ⊑ Nat_`, which is the
original judgment but with the LHS in **un-evaluated** form. The
seen-list contains `(lam_one, fix_Nat_)` (from the outer
`_, .fix` arm), where `lam_one` is the **evaluated** form. Subst's
seen-list lookup compares `succ_-fix zero_ == lam_one` → false.
NbE's seen-list compares `Val.beq lam_one_val lam_one_val` → true
because both Vals are constructed from `eval`'s output.

Fix: at the top of `subCheckSubst`, force WHNF on both `a` and `b`
before equality / seen-list / dispatch. NbE doesn't need this
because Vals are always in NbE-domain canonical form by
construction.

After the fix: 16 / 16 verdicts agree, and the timings are as
reported above.

## §7. Why subst wins on Och

Three reasons compound:

1. **NbE's subCheckVal is a tree-walk, not a DAG-walk.** It
   recursively opens closures and compares structurally without
   memoising sub-results. Each shared sub-Val gets re-traversed
   per reference. For the `three_` tower (33M-equivalent tree),
   this is the dominant cost.
2. **Substitution stops at HNF.** It doesn't materialise the full
   normal form during eval. The under-binder work is paid only
   when subCheckSubst actually descends, and the trees being
   walked are small.
3. **Structural compare on Expr is cheap.** The derived
   `DecidableEq Expr` walks the tree once with short-circuit on
   first mismatch. NbE's `Val.beq` does the same logically, but
   on a closure-DAG that — when walked as a tree — is much bigger.

The "lost sharing" cost of substitution does materialise: a single
β-reduction in `succ_ zero_` produces a 463-node Expr where every
reference to `Nat_` is copied in. But this cost is *amortised*
across the (much smaller) total compare work compared to NbE's
DAG-walk-as-tree.

The win is **Och-specific**, but Och-specific in an important way:
Och's recursive types (Nat_, Fin) are heavily used in the test
suite, and the singleton-Nat tower triggers exactly the pathology
NbE is bad at. Other dependently-typed systems (Coq, Agda) achieve
better NbE perf via more sophisticated sharing strategies (e.g.
hash-consing, explicit memoisation). Och's NbE is comparatively
naive.

## §8. Recommendation

**Substitution-based eval is the better choice for the
intrinsic-typing rebuild.** Both axes favour it:

- Code complexity: ~200–400 LOC simpler (no `Val`/`Closure` ADTs,
  no env lifting, no strict-positivity friction with the recursive
  Closure type).
- Performance: ~1000× faster on the heaviest current workload.
  Total bench-panel time drops from 14.7 s to 52 ms.

The remaining work for an intrinsic-typing kernel:
- Make the substitution-based subCheck **soundness-verified**
  (the present port is `partial` and matches `subCheckVal` by
  hand; for the kernel it would need to be a structurally-
  recursive function with the standard fuel pattern, plus a
  parallel proof corpus). Estimated work: **2–4 weeks**, of which
  most is re-doing the soundness theorems on the new
  representation.
- The "level-bvar offset" trick is fine for benchmarks but should
  be replaced by a proper **locally-nameless** representation
  (separate `bvar`/`fvar` constructors) for the production kernel.
  Cost: cosmetic AST change + ~1 day of machine-touching.

Existing concerns about substitution being "generally slower"
don't apply to Och's workload. They apply to systems where:
- Eval needs to produce full normal forms (e.g. Coq's
  conversion). Och only needs WHNF for type checking.
- The structural-compare hot path uses pointer-equality
  optimisations that closure-sharing enables. Och's `subCheckVal`
  doesn't — it walks closures as trees.

## §9. Files & runner

- `lean/Och/EvalSubst.lean` — substitution-based eval & subCheck
- `lean/Och/EvalBench.lean` — bench runner
- `lean/lakefile.lean` — adds `eval_bench` exe target

Run with `nix develop -c lake exe eval_bench` from `lean/`.

## §10. Closing log

What additional work would refine these numbers:

1. **Bigger inputs**: extend the panel to `four_ ⊑ Nat_`,
   `five_ ⊑ Nat_`. Estimated NbE wall-clock at `four_ ⊑ Nat_`:
   ~5–15 minutes (extrapolating from the geometric trend).
   Subst should still complete in <100 ms. Worth measuring to
   confirm the trend continues.
2. **Fix the per-call WHNF overhead**: the bug fix that closed
   verdict gaps comes with a constant-factor slowdown on tiny
   inputs (cases 06, 10, 12, 14, 15). A two-mode `subCheckSubst`
   that skips re-eval when the caller guarantees WHNF inputs would
   recover those few ms. Total panel wall-clock would drop from
   52 ms to ~30 ms. Marginal at this scale.
3. **Memoisation of `body[self := a]`**: the iotaIntro arm does
   `substL bodyB 0 a` then `evalSubst`. If the same (bodyB, a)
   pair appears in the same call's recursive descent, memoising
   would avoid re-substitution. Not a hot-path on the current
   workload but might matter for `four_ ⊑ Nat_`.
4. **Try the rebuild**: the empirical result strongly favours
   substitution. The next architectural step is to start the
   rebuild, with this benchmark as the regression suite.

The headline finding for the user:

> Substitution-based eval is **~1000× faster** than NbE on Och's
> heaviest workload (`three_ ⊑ Nat_`: 14.5 s → 13 ms). Hash-consing
> and substitution memoization were not needed to deliver the
> speedup — naive substitution suffices.
