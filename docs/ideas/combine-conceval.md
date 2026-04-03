# Combine concEval and concEvalE

## Current State

There are two concrete evaluators:

- `concEval`: substitution-based CBV for closed terms. Lambdas are
  values (bodies not entered). Mu eagerly unrolls. Free bvars fail.
- `concEvalE`: env-based normalizer. Normalizes under lambda binders.
  Mu is a value. Originally created as a proof auxiliary to mirror
  the old absEval's structure.

concEvalE was created to be structurally parallel to absEval, making
the soundness proof's induction work. But absEval has now changed
significantly (TyCtx instead of env, validation, mutual with
subCheckNF), so concEvalE no longer mirrors absEval anyway. The
original justification for having two concrete evaluators is gone.

## Proposal: Keep concEval, Delete concEvalE

concEval is the natural runtime evaluator. It operates on closed
terms, treats lambdas as values, and only enters bodies via beta-
reduction. concEvalE's normalization under binders was an artifact
of mirroring the old absEval — it has no runtime justification.

The merged evaluator is essentially the old concEval with one change:
mu becomes a value instead of eagerly unrolling.

```
def concEval (fuel : Nat) (e : Expr) : Option Expr
```

### Semantics

concEval implements two reduction rules:

```
(λ(x: τ). e) v  ⟶  e[x := v]     -- β-reduction
(e : τ)          ⟶  e              -- ascription erasure
```

Plus mu-app dispatch when a mu appears in function position.
Everything else is a value or gets stuck.

### Case-by-case behavior

**bvar k**: `none`. Free variables don't exist at runtime — all
bvars have been substituted away by beta-reduction. If this triggers,
the input was not a closed term.

**lam dom body**: `some e`. Lambda is a value. Body is not entered
until the lambda is applied.

**type**: `none`. Type is a compile-time construct — it doesn't exist
at runtime. If this triggers, the input wasn't a well-typed closed
term.

**asc term ty**: `concEval fuel term`. Ascription erased at runtime.

**mu ann body**: `some e`. Mu is a value. Only unrolled when applied
(via mu-app dispatch). This replaces the old eager unrolling, which
could diverge on recursive types used as values.

**app f a**: Evaluate f and a, then:
- f = lam: beta-reduce via `concEval fuel (body.subst 0 aVal)`
- f = mu: mu-app dispatch (match on ann/body shapes)
- otherwise: stuck `some (.app fVal aVal)`

### Mu-App Dispatch

Same dispatch as absEval for consistency:

```
| some (.mu ann body), some aVal =>
  match ann, body with
  | .lam _dom retBody, .lam _ _ =>
    concEval fuel (retBody.subst 0 aVal)
  | _, .lam _dom lamBody =>
    concEval fuel (lamBody.subst 0 aVal)
  | _, _ => some (.app body aVal)
```

## What Gets Deleted

- `concEvalE` — no longer needed
- The `Env` type and `Env.extend` — only used by concEvalE
- `Env.extend_ascFree` and related env lemmas

## Impact on Soundness

The soundness theorem becomes:

```
concEval fuel e = some v →
absEval fuel ctx e = ok τ →
∀ n, VCompat n v τ
```

No env on either side.

## Impact on VCompat

The semantic lambda disjunct currently quantifies over env:

```
∀ (fuel : Nat) (env : Env) (aV aT : Expr),
  VCompat j aV aT →
  concEvalE fuel env (bodyV.subst 0 aV) = some rv →
  absEval fuel ctx (bodyT.subst 0 aT) = ok rτ →
  VCompat j rv rτ
```

This simplifies to:

```
∀ (fuel : Nat) (aV aT : Expr),
  VCompat j aV aT →
  concEval fuel (bodyV.subst 0 aV) = some rv →
  absEval fuel ctx (bodyT.subst 0 aT) = ok rτ →
  VCompat j rv rτ
```

No env quantifier. The semantic property is cleaner: "for any
compatible arguments, beta-reducing both bodies gives compatible
results."

## Why This Works for the Proof

The old concEvalE normalized under binders so that the soundness
IH could relate the two evaluators' outputs on the same source body.
With the new approach:

- **lam case**: concEval returns the lambda as-is. absEval normalizes
  the body. VCompat between `lam dom body` (raw) and
  `lam dom' body'` (normalized) uses the semantic lambda disjunct —
  the bodies are related by what happens when they're applied, not
  by structural comparison of the un-applied bodies.

- **app case**: both evaluators beta-reduce (via substitution). The
  IH applies to the beta-reduced result. No need for concEval to
  have pre-normalized the body — beta-reduction does the work.

- **asc case**: concEval takes the term side, absEval takes the type
  side. VCompat bridges the gap via adequacy (subCheckNF).

## Implementation Order

1. Change concEval's mu case from eager unroll to value
2. Align mu-app dispatch with absEval's
3. Delete concEvalE
4. Delete Env, Env.extend, and related lemmas
5. Update VCompat to reference concEval (no env)
6. Update soundness_gen and all callers
7. Verify all tests pass
