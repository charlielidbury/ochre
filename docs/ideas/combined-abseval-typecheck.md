# Combined absEval + Type Checking

Supersedes: `abseval-infer-unification.md` (which proposed adding `tyCtx`
as a second parameter). This goes further: merge type checking into
absEval entirely, eliminating `WellTyped` as a separate function.

## Core Idea

**Well-typed = absEval succeeds.** Instead of having absEval as a
pure evaluator and WellTyped as a separate checker, make absEval
return an error on ill-typed terms. A term is well-typed iff
absEval produces a result.

## What absEval Does

absEval is a beta-normalizer with ascription erasure and validation.
Precisely, it does two transformations:

1. **Beta-reduces redexes**: `(lam dom body) arg` → evaluate
   `body.subst 0 arg`. Only actual redexes (lambda applied to
   argument) are reduced. Neutral applications (where the function
   is a variable) are left as symbolic `app` terms, preserving
   dependencies.

2. **Erases ascriptions**: `(e : τ)` → evaluates both sides, checks
   the subtype relation, returns `τ` (the type side). The term `e`
   is discarded.

Everything else passes through structurally: `bvar k` → `bvar k`,
`type` → `type`, `mu ann body` → `mu ann' body` (annotation
evaluated), `lam dom body` → `lam dom' body'` (domain and body
both evaluated).

With the proposed changes, absEval additionally **validates**:
3. Applications target functions (callability check via type context)
4. Ascriptions are sound (subtype check)

Validation is a side-channel — it affects whether absEval succeeds
or fails, but does not change the output when it succeeds.

## Motivation

Currently there are three interacting systems:
- `absEval`: abstract evaluator (returns normalized types)
- `WellTyped`: type checker (checks ascriptions, callability)
- `inferType` / `inferTypeNorm` / `isCallable`: type inference helpers

These overlap and duplicate work:
- `WellTyped` calls `absEval` internally, then does additional checks
- `WellTyped` threads a `tyCtx` that `absEval` doesn't have
- `inferTypeNorm` reimplements parts of absEval's logic with type info
- The soundness theorem needs `WellTyped` as a precondition separate
  from absEval succeeding, adding proof obligations

Merging them means:
- One function, one context, one recursion
- Soundness precondition simplifies to just "absEval succeeded"
- No separate `WellTyped`, `isCallable`, `inferTypeNorm`, `normalizeType`

## Key Insight: The Value Env is the Identity

With mu-as-value (commit 6022640), mu is returned immediately without
entering the body. The only binder that extends the env is lambda,
which always adds `bvar 0`. After shifting by `Env.extend`, the env
is always `[bvar 0, bvar 1, bvar 2, ...]` — the identity mapping.
Every `bvar k` lookup returns `bvar k`.

Beta-reduction uses substitution (not env extension), so it doesn't
change this picture. The value component of the env carries no
information.

**Therefore, the value env can be eliminated entirely.** absEval needs
only a type context — a list of domain annotations for bound variables.

## Type Context

```
abbrev TyCtx := List NfExpr  -- ctx[k] = absEval'd domain type of bvar k
```

When entering `lam dom body`, evaluate the domain (`dom' ← absEval
ctx dom`) and extend with the evaluated form:

```
def TyCtx.extend (ctx : TyCtx) (ty : NfExpr) : TyCtx :=
  ty :: ctx.map (Expr.shift 1 0)
```

Entries are the **absEval'd** domain. Since absEval preserves neutral
applications, dependencies are not lost. For example, in:

```
λ(f: Nat → Nat). λ(x: f 0). x
```

The domain `f 0` is `app (bvar 0) 0`. absEval of this checks that
`bvar 0` is callable (it is — ctx says it's `Nat → Nat`), then
returns `app (bvar 0) 0` unchanged (it's a neutral application).
So ctx stores `app (bvar 0) 0` and the output is
`lam (lam Nat Nat) (lam (app (bvar 0) 0) (bvar 0))`, faithfully
representing `(f: Nat→Nat) → (x: f 0) → f 0`.

Mu never extends the context (mu-as-value means the body is never
entered by absEval).

## NfExpr: Type Alias for absEval Output

```
/-- An expression that has been through absEval with some context.
    Invariants (not enforced by the type system, proved separately):
    - No `.asc` constructors (ascriptions erased)
    - No redexes (`.app (.lam ..) ..` does not occur)
    - Well-scoped: all `.bvar k` satisfy `k < ctx.length`
    - All applications are callable: if `.app f a` occurs and `f`
      is neutral, then `inferType ctx f` is a function type
    - All domains and mu annotations are themselves NfExprs -/
abbrev NfExpr := Expr
```

This alias carries no runtime or type-level cost — it's documentation
at the type level, making it visible in signatures where absEval'd
terms flow (ctx entries, subCheckNF inputs, VCompat arguments, etc.)
vs where raw source terms are expected. The invariants are proved as
separate lemmas about absEval's output, when needed.

## Changed absEval

```
def absEval (fuel : Nat) (ctx : TyCtx) (e : Expr) : Except String NfExpr
```

### Case-by-case behavior

**bvar k**: Return `ok (bvar k)`. Always. No lookup needed — with
mu-as-value, the value env is the identity.

**lam dom body**: Evaluate domain: `dom' ← absEval ctx dom` (rejects
ill-formed domains, e.g. `Array "hello" Bool`). Evaluate body under
binder with `ctx.extend dom'`. Return `ok (lam dom' body')`.
Since absEval preserves neutral applications (no dependency loss)
and only reduces redexes and erases ascriptions, the evaluated domain
is strictly more normalized and easier for subCheckNF to compare,
without losing dependency information.

**mu ann body**: Evaluate annotation: `ann' ← absEval ctx ann`
(rejects ill-formed annotations). Return `ok (mu ann' body)`.
Same reasoning as lam domains — store the evaluated form.

**type**: Return `ok .type` (unchanged).

**asc term ty**: Type checking happens here.
1. Evaluate `term` → get `sigma`
2. Evaluate `ty` → get `tau`
3. Run `subCheckNF ctx sigma tau`
4. If check fails → `Err "ascription failed"`
5. If check passes → `ok tau`

**app f a**: Evaluate `f` and `a`, then dispatch on `f'`:
- `f'` = `lam dom body`: beta-reduce via `absEval ctx (body.subst 0 a')`
- `f'` = `mu ann body`: mu-app dispatch (match on ann/body shapes,
  same as today)
- `f'` = `type`: `Err "Type is not callable"`
- `f'` = neutral (`bvar k`, `app _ _`, etc.):
  **Validate** callability (see below), then return `ok (app f' a')`.
  The symbolic application is preserved — no reduction occurs.

### Neutral application: validation without reduction

When `f'` is neutral, absEval needs to check that the application is
valid (the function has a function type) without reducing the term.
This is done via a side-channel type inference using ctx:

**inferType as side-channel**: Compute the type of `f'` using ctx.
For `bvar k`, the type is `ctx[k]`. For `app g b`, the type is
determined recursively from `g`'s type.

- If the type is `lam dom retTy` → application is valid,
  return `ok (app f' a')` (symbolic, no reduction)
- If the type is `mu` that unfolds to `lam` → same
- Otherwise → `Err "not callable"`

**Critical**: the inferred type is used ONLY for the yes/no
callability decision. It is NOT substituted into the output.
The output remains the symbolic `app f' a'`, preserving all
dependency information.

### Example: `λ(f: Nat → Nat). f 0`

```
absEval [] (lam (lam Nat Nat) (app (bvar 0) 0))
  dom' = absEval [] (lam Nat Nat) = ok (lam Nat Nat)
  ctx = [lam Nat Nat]
  absEval [lam Nat Nat] (app (bvar 0) 0)
    f' = bvar 0 (neutral)
    a' = 0
    Side-channel: type of bvar 0 = ctx[0] = lam Nat Nat
      → it's a lam, callable ✓
    Return ok (app (bvar 0) 0)    ← symbolic, NOT reduced
  Return ok (lam (lam Nat Nat) (app (bvar 0) 0))
```

The result is `lam (lam Nat Nat) (app (bvar 0) 0)`, which represents
the type `(Nat → Nat) → f 0`. The body `app (bvar 0) 0` is symbolic,
preserving the dependency on `f`. When this type is later used (e.g.,
in subCheckNF), the symbolic application can be compared structurally
or via inferType to determine its type is `Nat`.

### Example: rejecting `λ(f: Nat → Nat). (2 : f 0)`

```
absEval [] (lam (lam Nat Nat) (asc 2 (app (bvar 0) 0)))
  ctx = [lam Nat Nat]
  absEval the ascription (asc 2 (app (bvar 0) 0)):
    sigma = absEval 2 = ok 2
    tau = absEval (app (bvar 0) 0) = ok (app (bvar 0) 0)  ← symbolic
    subCheckNF ctx 2 (app (bvar 0) 0)
      → 2 ⊑ (app (bvar 0) 0)? These are syntactically different,
        (app (bvar 0) 0) is not Type, not a lam, not a mu...
        inferType on LHS: inferType 2 = some Nat (if 2 is encoded)
        Even so, Nat ⊑ app(bvar 0, 0) is not provable.
      → false ✓ (correctly rejected)
```

This works because `f 0` stays symbolic. subCheckNF can't prove
`2 ⊑ f 0` for arbitrary `f`, so the ascription is rejected.

## What gets deleted

- `WellTyped` (Soundness.lean) — absorbed into absEval
- `isCallable` (Soundness.lean) — absorbed into absEval's app case
- `inferTypeNorm` (Soundness.lean) — replaced by side-channel inference
- `normalizeType` (Soundness.lean) — no longer needed
- The current `Env` type and `Env.extend` — replaced by `TyCtx`
- `inferType` (Subtyping.lean) — may still be needed for subCheckNF
  (see Open Question 4), but could potentially be unified with the
  side-channel inference

## Soundness Theorem

Before:
```
WellTyped fuel env e = true →
concEvalE fuel env e = some v →
absEval fuel env e = some τ →
∀ n, VCompat n v τ
```

After:
```
concEvalE fuel env e = some v →
absEval fuel ctx e = ok τ →
∀ n, VCompat n v τ
```

The `WellTyped` precondition vanishes — it's implied by `absEval`
succeeding. Premise extraction works by unfolding absEval's definition
and eliminating impossible branches (same technique as today's
soundness_gen, just without the separate WellTyped structure).

## Impact on concEvalE

Deferred. Key principle: concEvalE does not need to mirror absEval.
It's a runtime evaluator. Structural divergence is fine — VCompat
bridges the gap.

For now, concEvalE can stay as `Option Expr` with its existing env.
Note: with mu-as-value, concEvalE's env is also the identity, so
its env parameter could potentially be eliminated too. Investigation
deferred.

## Impact on subCheckNF

subCheckNF currently takes `ctx` (for inferType) and does normalization
via `normalizeDomain`. With the new absEval:

- subCheckNF could call `absEval fuel ctx` for normalization
- The normalize-both-sides hack at the top of subCheckNF can use the
  enhanced absEval
- `inferType` inside subCheckNF may be replaceable by absEval calls

Details TBD — follow-on cleanup.

## Resolved: concEvalE's Env

With mu-as-value, concEvalE's env is also the identity — the only
extension is `bvar 0` under lambda binders, and mu returns immediately
without extending. So `env[k] = bvar k` always, and the env parameter
can be eliminated:

```
def concEvalE (fuel : Nat) (e : Expr) : Option Expr
```

The `bvar k` case becomes `some (bvar k)` directly (no lookup).

This makes concEvalE very close to `concEval`. The remaining
differences:
- concEvalE normalizes under lambda binders (enters the body);
  concEval treats lambda as a value
- concEvalE treats mu as a value; concEval eagerly unrolls
- mu-app dispatch differs

Whether to keep both or merge them is a separate question — for now,
just drop the env parameter from concEvalE.

## Open Questions

None currently.

## Implementation Order

1. Define `NfExpr := Expr` alias, `TyCtx := List NfExpr`, and
   `TyCtx.extend`
2. Rewrite absEval: remove `env`, add `ctx : TyCtx`, bvar returns
   `bvar k` directly, evaluate domains and annotations
3. Add side-channel callability checking to absEval's app neutral case
   (validate only, return symbolic `app f' a'`)
4. Add ascription checking (subCheckNF call) to absEval's asc case
5. Delete WellTyped, isCallable, inferTypeNorm, normalizeType
6. Update soundness_gen: remove WellTyped precondition
7. Update all callers (subCheckNF, Tests.lean, DSNat.lean)
8. Verify DSNat tests pass (dzero ⊑ dNat)
9. Investigate whether concEvalE's env can also be eliminated
