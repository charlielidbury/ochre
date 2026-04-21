# Lazy Normalization in subCheckNF

## Problem

The `(_, .mu)` self-intro arm in `subCheckNF` does:

```
body.subst 0 a  →  absEval (entire term)  →  subCheckNF a result
```

For `dzero ⊑ dNat`, this produces a 635-node substituted body. `absEval`
eagerly normalizes the *entire* term — every lambda domain, every
application, every nested mu — before comparison even begins. Most of
this work is wasted: the comparison only needs the outermost structure,
and most sub-comparisons resolve by reflexivity.

The cascading domain checks inside absEval are the direct cause of the
exponential blowup with increasing fuel.

## Proposal

Replace the "normalize then compare" pattern with **compare-driven
normalization**: `subCheckNF` itself performs weak-head normalization
on-demand, only reducing enough to expose the outermost constructor,
then compares structurally and recurses into sub-terms only when needed.

### Key change

Currently `subCheckNF` assumes its inputs are already in normal form
(hence the "NF" suffix). The new version would accept *unreduced* terms
and normalize lazily:

```
subCheck a b :=
  let a' = whnf a    -- weak-head normalize: expose outermost constructor
  let b' = whnf b
  if a' == b' then true    -- syntactic equality catches most cases
  else match a', b' with
  | lam domA bodyA, lam domB bodyB =>
      subCheck domB domA && subCheck bodyA bodyB  -- recurse, not pre-normalized
  | _, mu ann body =>
      subCheck a (body.subst 0 a)   -- self-intro, no absEval needed
  ...
```

The crucial difference: **domains are only normalized when the comparison
demands it**, and reflexively-equal sub-terms are never inspected.

### Walk-through: `dzero ⊑ dNat`

After self-intro substitution, we compare dzero against:
```
λP:(dzero → Type). λz:(P dzero). λs:(λpred:dzero. P (dsucc pred)). P dzero
```

dzero (after mu-unfold) is:
```
λP:(dzero → Type). λz:(P dzero). λs:Type. z
```

1. **whnf both sides** → both are lambdas. No deep normalization needed.
2. **Domains**: `(dzero → Type)` vs `(dzero → Type)` — syntactically equal.
   **Skip entirely.** This is where the current code wastes most of its time:
   it normalizes inside dzero, triggering domain checks on dzero's annotation
   (dNat), which triggers self-intro on dNat, etc.
3. **Under P binder, domains**: `(P dzero)` vs `(P dzero)` — equal. **Skip.**
4. **Under z binder, domains**: `(λpred:dzero. P (dsucc pred))` vs `Type` —
   Type is top. **Trivially true.** Never look inside the lambda.
5. **Bodies**: `z` vs `P dzero` — z is a bvar. Look up type from context =
   `P dzero`. Reflexive. **Done.**

Total work: 4 equality checks + 1 context lookup. Zero cascading domain checks.

### What changes

- `subCheckNF` is renamed/refactored to accept unreduced terms
- A `whnf` function is added that reduces:
  - `app (lam dom body) arg` → `body[0 ↦ arg]` (beta)
  - `letE val body` → `body[0 ↦ val]` (let-reduce)
  - `asc term ty` → `term` (erase ascription)
  - `mu` in function position → unfold (same as current mu-app)
  - Everything else (lam, mu, bvar, type, neutral app) → stop
- `absEval` may still exist for top-level type synthesis, but subCheckNF
  no longer calls it internally
- The `ctx` (type context) is still needed for bvar lookups in neutralType

### What whnf does NOT do

- Normalize under binders (that's the whole point — defer it)
- Normalize lambda domains
- Normalize mu annotations
- Normalize function/argument positions of neutral applications

### Risks and open questions

1. **Soundness**: Does lazy normalization miss valid subtypings that eager
   normalization would catch? In principle no — whnf followed by structural
   recursion should explore the same paths, just in a different order. But
   this needs careful analysis, especially for mu unfolding.

2. **Self-intro inside whnf**: When `whnf` encounters `mu` in the body of
   a substitution result, does it unfold? It shouldn't need to — whnf only
   reduces the head, and mu is already a head form. Self-intro is handled
   by `subCheck`'s `(_, .mu)` arm.

3. **Type context management**: Currently absEval builds the TyCtx as it
   goes under binders. With lazy normalization, subCheck needs to do this
   itself — extending the context when it goes under a lambda for
   structural comparison. This is straightforward but needs to be correct.

4. **Compatibility with existing tests**: All concrete evaluation tests
   use `concEval` (unaffected). All subCheck tests at fuel≤20 should
   produce the same results. The change would make higher fuel usable
   for DNat tests.

### Relationship to the current architecture

This is a moderate refactor of `subCheckNF`. The mutual recursion between
`absEval` and `subCheckNF` would be simplified: subCheckNF would call
`whnf` (a pure structural reducer) instead of `absEval` (the full
type-checking normalizer). absEval would still be needed for top-level
`absEvalVal` and for type synthesis, but not inside the subtype checker.
