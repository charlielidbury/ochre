# Pre-normalize mu bodies at construction time

## Summary

Change `absEval` so that `μ self:Ann. body` normalizes `body` under the
binder (with `self : Ann` in the type context), just like lambda already
does. This eliminates redundant re-normalization during self-intro
subtype checks and solves the exponential blowup in `subCheckNF`.

## Background

### How lambda works now (Eval.lean ~130)

```
absEval (λdom. body) =
  dom' ← absEval dom
  body' ← absEval body   [with bvar 0 : dom' in context]
  return (lam dom' body', lam dom' body')
```

The body is normalized once at construction, with the parameter abstract.
Later, when the lambda is applied, the pre-normalized body just needs
substitution — no re-normalization of the internal structure.

### How mu works now (Eval.lean ~143)

```
absEval (μann. body) =
  ann' ← absEval ann
  return (mu ann body, ann')       ← body is RAW, not normalized
```

The body is never entered. This means:
1. Ill-typed mu bodies are not caught at construction
2. Self-intro in `subCheckNF` must call `absEval` on `body.subst 0 a`
   from scratch every time, which triggers cascading domain checks
   and causes exponential blowup with increasing fuel

### The performance problem

When checking `dzero ⊑ dNat`, self-intro substitutes dzero into dNat's
raw body (635 nodes after letE expansion). `absEval` normalizes this
from scratch: processing letE chains, going under lambda binders,
checking domains. Each domain check against a mu triggers another
self-intro, which substitutes again, which normalizes again...

With fuel ≤ 20 this terminates (failing branches get cut off). With
fuel ≥ 30 it hangs (exponential branching).

## Proposed change

### New absEval for mu

```
absEval (μann. body) =
  ann' ← absEval ann
  body' ← absEval body   [with bvar 0 : ann' in context]
  return (mu ann' body', ann')
```

This mirrors the lambda case exactly. The body is normalized once with
`self : ann'` abstract in the context.

### Why pre-normalization is cheap

When normalizing dNat's body with `self : Type` in context:

1. **letE for dzero**: `μ (self). λP:(dzero→Type). ...` — mu is a value,
   annotation check is `self` which has type `Type` from context. Trivial.
   Substitute dzero_mu into the rest.

2. **letE for dsucc**: same pattern — mu is a value, annotation check
   resolves via context. Trivial. Substitute dsucc_mu into the rest.

3. **Main lambda body**: `λP:(self→Type). λz:(P dzero). λs:(...). P self`
   — normalize under each binder. Domain checks like `dzero ⊑ self`
   resolve via neutralType as `dzero ⊑ Type` (since self has type Type
   in context). Always true. Cheap.

The letE bindings are eliminated, all domains are normalized, all
under-binder normalization is done. The result is a fully normalized
body containing `bvar 0` (abstract self-ref) in a few positions.

### Why self-intro becomes cheap after this

When checking `dzero ⊑ dNat` via self-intro:

1. `body_prenormalized.subst 0 dzero` — replaces the abstract `bvar 0`
   with dzero. Since `bvar 0` doesn't appear in function position in
   the pre-normalized body, **no new redexes are created**. The result
   is already in (or very close to) normal form.

2. `absEval` on the result is essentially a no-op (traversing a
   normal-form term).

3. `subCheckNF` compares dzero against the result — lambda-vs-lambda
   with reflexively equal domains. Trivial.

### Why the cheap domain checks at pre-normalization time are sound

At construction of `μ self:Ann. body`, we check that the body is
well-typed under the assumption `self : Ann`. Domain checks during this
normalization resolve against `Ann` (or its type). For `dNat` where
`Ann = Type`, everything is trivially ⊑ Type.

This is not "getting away with something." It establishes an invariant:
the body is valid for ANY value that is ⊑ Ann. Later, self-intro
substitutes a specific value `v` where `v ⊑ Ann` (that's what self-intro
is checking). Since `v` is more precise than the abstract `self : Ann`,
and the body already checked out with the weaker assumption,
monotonicity guarantees it still holds.

This is the same reasoning as lambda: you check the body once with the
parameter abstract (`x : Dom`), then every application passes `v ⊑ Dom`.
You don't re-check the body at every call site. The mu case has
effectively been re-checking the body at every call site — that's why
it's expensive.

## Implementation

### Step 1: Change absEval's mu case

In `Eval.lean`, the `.mu` case of `absEval` (currently ~line 143):

```lean
-- BEFORE
| .mu ann body  => do
    let (ann', _) ← absEval fuel ctx seen ann muSeen
    .ok (⟨.mu ann body⟩, ann')

-- AFTER
| .mu ann body  => do
    let (ann', _) ← absEval fuel ctx seen ann muSeen
    let (body', _) ← absEval fuel (TyCtx.extend ctx ann') seen body muSeen
    .ok (⟨.mu ann'.val body'.val⟩, ann')
```

This is structurally identical to the lambda case.

### Step 2: Verify NfExpr invariant

The `NfExpr` wrapper claims its contents are normalized (no redexes, no
ascriptions, well-scoped). After this change, mu bodies will satisfy
these invariants, whereas before they could contain arbitrary raw
expressions. This is strictly better.

### Step 3: Update self-intro in subCheckNF

The `(_, .mu)` arm currently calls `absEval` on the substituted body.
After pre-normalization, this absEval call should be much cheaper (the
body is already mostly normalized). It may even be possible to replace
it with a lighter-weight re-normalization, but this is an optimization
for later — the immediate win comes from the pre-normalized body making
absEval fast.

No structural changes to subCheckNF are needed. The same code works;
it just runs faster because the input is pre-normalized.

### Step 4: Run tests

- All existing `native_decide` tests should still pass (same semantics)
- The DNat `sorry`'d tests (`subCheck 200 dzero dNat = true`, etc.)
  should now be fast enough to run with `native_decide`
- If they pass, replace `sorry` with `native_decide`

## What this does NOT change

- `concEval` — unaffected (runtime evaluation doesn't normalize under binders)
- `subCheckNF` structure — same algorithm, same arms, just faster inputs
- The `letE` constructor — still useful for avoiding domain checks on let-bindings
- The neutralType fallback added to `(_, .mu)` — still needed for
  neutral terms under binders

## Risks

1. **Fuel consumption**: Pre-normalizing the body uses fuel at construction
   time. For deeply nested mus, this could exhaust fuel earlier. In practice,
   mu bodies are shallow (the depth comes from nesting at application time,
   not at definition time), so this should be fine.

2. **Self-referential bodies**: The body may reference `bvar 0` (self) in
   ways that create neutral terms during pre-normalization (e.g.,
   `self arg1 arg2`). These are fine — they stay neutral and get resolved
   later when a concrete value is substituted. The `muSeen` cycle detection
   already handles cases where mu-app normalization would loop.

3. **Stored body size**: The pre-normalized body might be larger than the
   raw body if letE elimination inlines large values. In the dNat case,
   the let-bound dzero and dsucc mus get substituted into the main body.
   However, these are just mu values (not expanded), so the size increase
   is modest. And the body was going to be expanded at self-intro time
   anyway — pre-normalization just moves this work earlier.

4. **Interaction with `seen` list**: The `seen` parameter for cycle
   detection is threaded through. Pre-normalization happens with the
   `seen` list from the enclosing context, which should be fine since
   mu construction doesn't introduce new subtyping obligations into
   `seen` (that happens in subCheckNF, not absEval).
