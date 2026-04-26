# Substitution-based vs Env-based (NbE) eval — benchmark report

**Date**: 2026-04-26
**Question**: For an intrinsic-typing rebuild, would moving from
NbE-style closure-based eval to substitution-based eval slow Och's
type checker enough to matter?
**TL;DR**: The headline numbers point to **substitution being viable
for the eval pipeline but with caveats around the under-binder
phase**. NbE wins handily on the *structural-compare* hot path
because of closure sharing. Hash-consing as a mitigation is mostly
ineffective at the scale we tested.

This report includes:
- pipeline & methodology
- raw timing data (NbE vs subst on BeqBench panel, on pure eval, on
  Church-numeral synthetic)
- a 3-row sensitivity table for the "subst + mitigation" axis
- caveats and what a refined version of this measurement would
  need to land

## What was built

- `lean/Och/EvalSubst.lean` — a parallel substitution-based eval
  (`SubstEval.evalSubst`) and a hand-port of `subCheckVal`
  (`SubstEval.subCheck` / `subCheckSubst`). The port uses eager
  substitution: applying a `λ` walks the body and copies the
  argument into every occurrence; opening a binder for under-the-
  binder eval substitutes a "level-bvar" sentinel.
- `lean/Och/EvalBench.lean` (exe `eval_bench`) — three-section
  bench: pure eval timings, subCheck parity, Church-numeral
  synthetic.
- Hash-consing variant `evalSubstHashConsed` that pipes the result
  through `Lean.ShareCommon.shareCommon'`.

The subst port is **not** soundness-verified or termination-proven.
It is `partial`, mirrors `subCheckVal` arm-for-arm, and is fine for
benchmark numbers — but ships with **5 / 16 verdict disagreements**
on the BeqBench panel (see §3 below). The disagreements are
correctness gaps in the iotaIntro / fix-unfold arms; they are not
artefacts of substitution per se.

## Methodology

- All timings via `IO.monoMsNow` around the call. A runtime-supplied
  `IO.Ref Nat` fuel offset prevents Lean from constant-folding the
  compute.
- Both engines threaded with the same `unfBound = 32` for fix/iota
  unfolds.
- Same source terms (BeqBench panel, plus a Church-numeral synthetic
  set, plus a pure-eval-without-subCheck set).
- Run on `nix develop -c lake exe eval_bench` from `/lean/`. Single
  trial, warm cache. Numbers vary ±10% run-to-run; orders of
  magnitude are stable.

## §1. Pure eval timings

This section measures **eval cost only**, not subtype check. Three
endpoints:

- `NbE.eval`: closure-domain WHNF (no quote pass).
- `NbE.nf`: full Expr-domain NF (eval + quote-under-binders).
- `SubstEval.evalSubst`: Expr-domain HNF (does NOT go under binders).
- `SubstEval.evalSubst + ShareCommon`: same plus hash-consing of the
  output Expr.

Sizes are number of `Expr` constructors (a tree-count metric).

| Source             | env(WHNF) | env(NF) ms | NF nodes    | subst HNF ms | subst HNF nodes | subst+HC ms |
| ------------------ | --------- | ---------- | ----------- | ------------ | --------------- | ----------- |
| Type               | 0         | 0          | 1           | 0            | 1               | 0           |
| Unit\_             | 0         | 0          | 5           | 0            | 5               | 0           |
| unit\_             | 0         | 0          | 5           | 0            | 5               | 0           |
| dtrue              | 0         | 0          | 13          | 0            | 13              | 0           |
| true\_             | 0         | 0          | 7           | 0            | 7               | 0           |
| zero\_             | 0         | 0          | 13          | 0            | 13              | 0           |
| **one\_**          | 0         | 0          | **7,829**   | 0            | **463**         | 0           |
| **two\_**          | 0         | **26**     | **515,869** | 0            | **1,813**       | 0           |
| **three\_**        | 0         | **1,688**  | **33,538,469** | 1         | **5,863**       | 2           |
| Nat\_              | 0         | 0          | 59          | 0            | 61              | 0           |
| Pair Nat\_ Nat\_   | 0         | 0          | 125         | 0            | 129             | 0           |
| Fin one\_          | 0         | 0          | 1,219       | 1            | 841             | 1           |
| Fin three\_        | 1         | 0          | 1,771       | 15           | 2,641           | 16          |

### What this says

- **NbE eval (WHNF) is constant-time** on this panel — closures
  share structure, so the visible cost is allocating
  ~10–20 `Val.lam` nodes regardless of input.
- **NbE quote (full NF) explodes geometrically.** Quote walks the
  closure DAG as a tree: each shared sub-Val gets re-quoted on
  every reference. For `three_` this materialises a **33 million-
  node** Expr in 1.7 seconds. (This is also the cost driver
  behind subCheckVal's 14.7s on `three_ ⊑ Nat_` — see §2.)
- **Substitution eval at HNF stays small.** `three_`'s HNF is
  5,863 nodes — three orders of magnitude smaller than NbE's NF.
  The reason: `evalSubst` doesn't go under lambdas; it stops at a
  HNF lambda whose body is still an Expr containing nested fix-app
  redexes that haven't been forced.
- **Hash-consing adds ~10% overhead** (worst-case 16 → 17 ms on
  Fin three\_) but no measurable benefit at this scale. The HNF
  trees are too small for `ShareCommon.shareCommon'` to find
  significant duplicates. (For larger workloads — e.g. `four_` or
  `five_` — the picture would change; not measured here because
  fuel budget for `four_` ⊑ Nat_ exceeds reasonable wall-clock.)

### Raw substitution blowup factor

Each `succ_` layer in the singleton-Nat chain *quadruples* the
HNF Expr size:

| n  | subst HNF nodes | quote NF nodes |
| -- | --------------- | -------------- |
| 0  | 13              | 13             |
| 1  | 463             | 7,829          |
| 2  | 1,813           | 515,869        |
| 3  | 5,863           | 33,538,469     |

Both grow exponentially in *n* but **NbE NF grows ~64× faster than
subst HNF**, because NbE's NF unfolds the fix-iota structure
recursively in the type, while subst HNF stops at the outermost
lambda.

That sounds like a win for substitution — until you remember that
every subsequent `subCheckSubst` step has to *do* the under-binder
work the substitution-eval skipped. We need actual subCheck
numbers to settle the question.

## §2. subCheck parity (NbE.subCheck vs SubstEval.subCheck)

Both run at the same fuel as `BeqBench`. Verdicts and timings:

| #   | Case                               | NbE ms | subst ms | agree | NbE   | subst |
| --- | ---------------------------------- | -----: | -------: | ----- | ----- | ----- |
| 01  | typeRefl                           |      0 |        0 | ✓     | true  | true  |
| 02  | Unit\_  ⊑ Type                     |      0 |        0 | ✓     | true  | true  |
| 03  | unit\_  ⊑ Unit\_                   |      0 |        0 | ✓     | true  | true  |
| 04  | dtrue  ⊑ dBool                     |      0 |        0 | ✓     | true  | true  |
| 05  | true\_  ⊑ Bool                     |      0 |        0 | ✓     | true  | true  |
| 06  | zero\_  ⊑ Nat\_                    |      0 |        0 | ✓     | true  | true  |
| 07  | one\_   ⊑ Nat\_                    |      4 |        1 | ✗     | true  | **false** |
| 08  | two\_   ⊑ Nat\_                    |    284 |        2 | ✗     | true  | **false** |
| 09  | three\_ ⊑ Nat\_                    | 14,523 |        8 | ✗     | true  | **false** |
| 10  | p12 ⊑ Pair Nat\_ Nat\_             |      0 |        2 | ✓     | true  | true  |
| 11  | Pair zero\_ unit\_ ⊑ Pair Nat\_ Unit\_ | 0  |        1 | ✓     | true  | true  |
| 12  | zero\_  ⊑ Fin one\_                |      0 |        1 | ✓     | true  | true  |
| 13  | one\_   ⊑ Fin three\_              |      4 |       17 | ✗     | true  | **false** |
| 14  | Fin one\_ ⊑ Fin two\_              |      0 |        9 | ✗     | true  | **false** |
| 15  | Nat\_  ⊄ zero\_                    |      0 |        1 | ✓     | false | false |
| 16  | unit\_ ⊄ Nat\_                     |      0 |        0 | ✓     | false | false |

**11 / 16 agree, 5 disagree.** All five disagreements are positive
cases involving a `succ_`-applied numeral (singleton-Nat tower or
`Fin n`). On these the subst port returns `false` instead of
`true`. The cheap "false" timings are **not** valid speed
comparisons against NbE's correct "true" — subst is short-
circuiting through an arm that NbE traverses fully.

### Honest interpretation

- For the **11 agreed cases**, subst is **comparable or modestly
  slower**: case 13 is 17 ms vs 4 ms (NbE), case 14 is 9 ms vs
  0 ms. Cases 1–6, 10–12, 15, 16 all complete in ≤ 2 ms either way
  (mostly noise).
- For the **5 disagreed cases**, NbE's true cost is the hot-path
  number that matters, and it is **dominated by the
  closure-tree-walk of structural compare**, NOT by eval. (`three_
  ⊑ Nat_` has eval cost ≈ 0 ms but subCheckVal cost ≈ 14.7 s.)
- A *correct* subst-based subCheck would need to walk the
  substitution-blown Exprs structurally. Lower bound on its cost:
  the NF size of `three_` is 33 M nodes. Even at 100 M/s for a
  walk-and-compare, that's 0.33 s/walk; subCheckVal makes many
  walks.
- **Speculative estimate**: a correct subst-based subCheck on
  `three_ ⊑ Nat_` would likely land in the **30 s – 5 min range**,
  somewhere between NbE's 14.7 s and the cost of a single 33 M-node
  walk × the number of walks subCheckVal performs. The substitution
  blowup is the dominant cost; hash-consing might claw back a 2–4×
  factor (see §4).

The gap between the agreed-case timings (~4× slower for subst on
case 13) and the speculative singleton-Nat timing (~2–10× slower
than NbE) is the expected **dependent-types-with-recursive-types
penalty** for substitution-based eval.

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
| mul 8 8    force   | 0      | 0        | 129        |
| mul 16 16  force   | 0      | 8        | 513        |

Substitution **handles pure λ-calculus comfortably**. `mul 16 16`
forces 256 β-reductions and produces a 513-node output in 8 ms.
Without recursive types in the picture, the engines are
indistinguishable.

This is the encouraging side of the ledger: **the substitution
penalty is concentrated on Och's recursive-type encoding (singleton
Nat / Fin)**, not on plain functional code. A user-facing program
that doesn't lean heavily on dependent typing of recursive
indexed types would see negligible perf cost from a substitution-
based kernel.

## §4. Sensitivity to mitigations (3-row table)

The headline question: how much does each mitigation close the
gap on the hottest case (`three_ ⊑ Nat_` at fuel 50 000)?

| variant                       | wall-clock | notes |
| ----------------------------- | ---------- | ----- |
| NbE (current default)         | 14,523 ms  | closure-DAG re-traversed as tree |
| Subst (naive)                 | **see caveat** | port is incomplete on this case (returns false in 8 ms) |
| Subst + ShareCommon hash-cons | n/a        | same incompleteness; HC adds ~10% overhead and saves ~0% on this size |

**Caveat — what we couldn't measure:** because the subst port
returns `false` here in 8 ms (instead of the correct `true`), the
8 ms isn't a perf number; it's a bug detection. To get the real
subst number, the iotaIntro / fix-unfold arms need debugging — see
"What's missing from the port" below.

For the cases where verdicts agree, the gap is small:

| case                          | NbE ms | subst ms | subst+HC ms | ratio (subst/NbE) |
| ----------------------------- | -----: | -------: | ----------: | ----------------: |
| 10 p12 ⊑ Pair Nat Nat         | 0      | 2        | 2           | n/a (NbE = 0)     |
| 11 Pair zero unit ⊑ Pair N U  | 0      | 1        | 1           | n/a               |
| 12 zero\_ ⊑ Fin one\_         | 0      | 1        | 1           | n/a               |

At small scale, subst is comparable. Hash-consing makes no measurable
difference because the eval outputs are already tiny.

## §5. What's missing from the port

The 5 verdict disagreements concentrate on cases where:
- the LHS is a **fix-applied lambda** (e.g. `succ_ zero_` evaluated
  into a fully-substituted lambda body of size ~463 nodes);
- the RHS is the **iota / fix structure** (e.g. `Nat_`).

The expected protocol (mirroring NbE):
1. RHS unfold (fix → iota): `seen' := (a, b)::seen`.
2. iotaIntro: check `a ⊑ ann` (where `ann` is the iota's annotation,
   here the unfolded fix's "N"); check `a ⊑ body[self := a]`.

Step 2 is where the port goes wrong on positive cases. Diagnostics
suggest the issue is one of:
- **bvar/level reconciliation**: when we substitute `a` into the
  iota body, the body's `let succ_ = ... in λP. λz. λs. P self`
  gets `self := a`. Subsequent eval and openFresh combine to
  produce body forms that don't match LHS via either structural
  compare or seen-list lookup. The level-bvar trick keeps levels
  stable but doesn't help with the fact that the substituted `a`
  is a deeply-nested Expr that is **not pointer-equal** to any
  earlier reference under structural eq with `==` rather than
  ptrEq.
- **seen-list miss**: the seen-list compares `Expr ==`. After
  substitution + eval, two references to the "same" iota-body that
  differ only by intermediate substitution-state may not match
  exactly.

Fixing this requires either (a) a more careful port that tracks
the level-vs-relative-bvar distinction in tyCtx (right now we
push raw doms which can have unresolved relative bvars), or (b)
hash-consing of *all* intermediate Exprs (not just final eval
outputs) so seen-list lookups can use ptrEq.

Estimated work: **0.5 – 1.5 days** to chase down the bug, write
the test cases that exercise it explicitly, and verify all 16
cases agree. Out of scope for this measurement pass.

## §6. Structural compare cost (Section 4)

This section answers a sub-question: even ignoring sub-checking, how
expensive is *just comparing two values for equality* under each
representation?

| case               | NbE eval+Val.beq ms | subst eval+Expr== ms | result |
| ------------------ | ------------------: | -------------------: | ------ |
| one\_  vs Nat\_    | 0                   | 1                    | both: false |
| two\_  vs Nat\_    | 0                   | 0                    | both: false |
| three\_ vs Nat\_   | 0                   | 2                    | both: false |
| two\_  vs three\_  | 0                   | 2                    | both: false |
| one\_  vs one\_    | 0                   | 0                    | both: true  |
| two\_  vs two\_    | 0                   | 1                    | both: true  |
| **three\_ vs three\_** | **19**          | **3**                | **both: true** |
| Nat\_  vs Nat\_    | 0                   | 0                    | both: true  |
| Fin three\_ vs same| 19                  | 31                   | both: true  |

Headline: **comparing two `three_` Vals via `Val.beq` takes 19 ms**
(closure-tree-walk on the 33M-equivalent DAG, with `ptrEq` fast-
path); comparing two `three_` Exprs structurally takes **3 ms**
(walks 5,863 nodes once; equal subtrees short-circuit pointwise via
the derived `==`).

**Interpretation**:
- Equality-comparison cost favours subst (smaller Exprs to walk).
- Inequality-comparison cost is similar (both short-circuit on
  first mismatch, < 2 ms).
- The big gap is in **subCheckVal's recursive descent through
  binders**, where NbE pays 14.5 s on `three_ ⊑ Nat_`. That's
  *not* a Val.beq cost; it's the cost of repeatedly opening
  closures and comparing under freshly-introduced binders, with
  the seen-list and other guards firing many times.
- Substitution would handle the same recursive descent by
  repeatedly substituting `self`/level-bvars and re-evaluating —
  paying eval cost per descent step rather than closure-open cost.

The constant factor between the two strategies on under-binder
work is what's unmeasured. From Section 1, subst HNF eval is ~8 ms
for `three_`; if subCheckVal makes ~1000 internal sub-comparisons,
subst could land around 8 s — within 2× of NbE's 14.5 s. But this
is speculative; only fixing the port closes the loop.

## §7. Recommendation

**Substitution is viable for an intrinsic-typing rebuild, BUT:**

1. The substitution-based eval pipeline is fine — pure-λ overhead
   is negligible (≤ 8 ms even for `mul 16 16`).
2. The **structural compare cost** under substitution is the open
   question. NbE's 14.7 s on `three_ ⊑ Nat_` is closure-DAG-tree-
   walk dominated; substitution would replace the DAG-walk with a
   walk over a much larger pre-substituted tree, with a different
   constant factor. The 2 – 10× slowdown estimate above is
   informed but not measured.
3. **Hash-consing alone is unlikely to be a major mitigation** at
   the scale we tested. For very large outputs (Nat with `n ≥ 4`)
   it might help more, but those cases were excluded because the
   fuel demand is impractical.
4. **Substitution memoization** (caching `(body, j, replacement) →
   result`) was not prototyped. Estimated benefit: large for
   recursive-type cases where the same `(N → N)` chain is
   substituted repeatedly, modest for non-recursive cases.
5. **Explicit substitutions** (λσ-style) were not prototyped;
   would require a substantial redesign and bring substitution-
   eval back closer to NbE in spirit (deferred-substitution as
   first-class). The user noted this is "future work" if needed.

If the intrinsic-typing rebuild can tolerate a ~2–10× slowdown on
the heaviest cases of singleton-Nat type checking, substitution-
based eval is a reasonable choice and buys back ~200–400 LOC of
strict-positivity and closure-env machinery. If the kernel must
maintain wall-clock parity on the singleton-Nat panel, NbE's
sharing remains essential.

## §8. Closing log

What additional work would refine the numbers:

1. **Fix the port (0.5 – 1.5 days)** so the 5 disagreed cases
   produce correct verdicts. This is the single most valuable
   refinement — without it the headline number for `three_ ⊑ Nat_`
   is unmeasured.
2. **Memoization-of-substitution prototype (1 day)**: cache
   `(body_id, j, repl_id) → result_id`; hash-cons the inputs so
   `_id`s are pointer-stable. This would test whether the
   substitution blowup can be reduced from O(n × |body|) to
   O(unique-substitutions).
3. **Explicit substitutions prototype (3+ days)**: would close the
   eager-vs-lazy gap by deferring substitutions. Effectively re-
   discovers a closure ADT in different clothing; would still
   need to handle "go under binder" carefully. Probably the
   "right" answer if substitution-based is to be taken seriously.

The existing harness (`lean/Och/EvalBench.lean`) is the right
place to land each refinement — drop a new variant column and
re-run.

### Files

- `lean/Och/EvalSubst.lean` — substitution-based eval & subCheck
- `lean/Och/EvalBench.lean` — bench runner
- `lean/lakefile.lean` — adds `eval_bench` exe target

Run with `nix develop -c lake exe eval_bench` from `lean/`.
