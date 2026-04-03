# Unify absEval with Type Inference for Neutral Applications

## Problem

`absEval` currently acts as a value-level normalizer. When it encounters an
application where the function is a neutral term (bound variable), it
produces a stuck `app` node:

```
absEval env (app (bvar 2) dNat)
-- bvar 2 → env[2] = bvar 2 (neutral)
-- result: app(bvar 2, dNat)  -- stuck
```

But if we know `bvar 2 : dNat → Type` (from the typing context), we could
determine that `app(bvar 2, dNat) : Type`. This information is lost because
absEval only tracks values, not types.

This causes a concrete failure: `subCheckNF` can't verify `dzero ⊑ dNat`
for dependent Scott Nats because the body check compares `bvar 1` (z)
against `app(bvar 2, dNat)` (P dNat). Both have type `Type`, but
subCheckNF can't see this — `app(bvar 2, dNat)` is stuck and doesn't
match `.type`.

## Proposed Change

When absEval encounters `app(f, a)` and `f` evaluates to a neutral term,
instead of always returning `app(f_neutral, a_val)`, it should check if
the neutral's **type** is known to be a function. If so, return the
return type with the argument substituted.

### Current behavior

```
| .app f a =>
    match absEval fuel env f, absEval fuel env a with
    | some (.lam _dom body), some aVal => absEval fuel env (body.subst 0 aVal)
    | some (.mu ...), some aVal => ... -- mu-app dispatch
    | some f', some a' => some (.app f' a')  -- stuck: f' is neutral
    | _, _ => none
```

### Proposed behavior

```
| .app f a =>
    match absEval fuel env f, absEval fuel env a with
    | some (.lam _dom body), some aVal => absEval fuel env (body.subst 0 aVal)
    | some (.mu ...), some aVal => ... -- mu-app dispatch
    | some f', some a' =>
        -- f' is neutral. Check if its TYPE is a known function.
        match inferType tyCtx f' with
        | some (.lam _dom retTy) => absEval fuel env (retTy.subst 0 a')
        | some (.mu _ann body) =>
            let unfolded := body.subst 0 f'
            match unfolded with
            | .lam _dom retTy => absEval fuel env (retTy.subst 0 a')
            | _ => some (.app f' a')
        | _ => some (.app f' a')
    | _, _ => none
```

This requires absEval to have access to a typing context (`tyCtx`) that
maps bvar indices to their domain types. This is similar to the `tyCtx`
already added to `WellTyped` in Soundness.lean.

## Design Considerations

### 1. absEval needs a tyCtx parameter

Currently: `absEval (fuel : Nat) (env : Env) (e : Expr) : Option Expr`
Proposed: `absEval (fuel : Nat) (env : Env) (tyCtx : List Expr) (e : Expr) : Option Expr`

The `tyCtx` must be maintained in parallel with `env`:
- Lambda: `env.extend (.bvar 0)`, `tyCtx.extend dom`
- Mu: `env.extend (.mu ann body)`, `tyCtx.extend (.mu ann body)`
- Beta-reduction: both stay the same (the binder is eliminated)

This is the same pattern as WellTyped's dual env/tyCtx.

### 2. What about concEvalE?

`concEvalE` is the concrete evaluator. At runtime, we know actual values,
not types. So `concEvalE` should NOT do type inference on neutrals — it
should only encounter neutrals under binders (where parameters are
abstract), and the neutral app is a legitimate stuck term.

But wait — `concEvalE` and `absEval` are supposed to be structurally
parallel (they differ only at the ascription case). If absEval gains a
tyCtx and concEvalE doesn't, they diverge more. This needs thought.

Option A: Give concEvalE the same tyCtx but only use it in absEval's
neutral-app case. concEvalE ignores it (returns stuck app as before).

Option B: Make both use tyCtx. concEvalE uses it too — under binders,
if a neutral is applied and its type is known, concEvalE returns the
return type. This is weird for a "concrete" evaluator but maintains
structural parallelism.

Option C: Don't change concEvalE. Accept the divergence. The soundness
proof already handles the two evaluators producing different results
(that's what VCompat is for).

### 3. inferType also needs updating

The current `inferType` doesn't normalize its intermediate results. If
absEval now produces type-inferred results (not stuck apps), then
`inferType` might also benefit from the same logic — or it could delegate
to the new absEval.

Actually, the simplest approach might be: `inferType` calls `absEval` with
tyCtx to normalize, then pattern-matches. This makes `inferType` a thin
wrapper.

### 4. Impact on subCheckNF

If absEval produces `Type` instead of `app(bvar 2, dNat)`, then
subCheckNF doesn't need to handle stuck type-level applications at all.
The normalization at the top of subCheckNF (which we added) can use the
enhanced absEval, and everything reduces before structural comparison.

The normalization at top of subCheckNF currently uses `normalizeDomain`
(identity env). It should use the enhanced absEval with the ctx as tyCtx
instead. Since absEval now does type inference on neutrals, it won't
over-reduce (it returns the TYPE of the neutral application, not the
value of the bound variable).

Key insight: the over-reduction problem we hit earlier (using ctx as eval
env made `true ⊑ Nat` pass) happened because `absEval fuel ctx (bvar 0)`
returned `ctx[0]` which is the TYPE of bvar 0, not its value. With the
proposed change, `absEval fuel env (bvar 0)` still returns `env[0]`
(the value, which is neutral), and only when this neutral is APPLIED does
it check tyCtx for the type. This is the crucial distinction — we use
tyCtx for applications, not for bare lookups.

### 5. Impact on soundness proof

The soundness theorem states:
```
WellTyped fuel env e → concEvalE fuel env e = some v →
absEval fuel env e = some τ → VCompat n v τ
```

If absEval now produces type-inferred results for neutral apps, the `τ`
it returns may be different from before. For example, where it previously
returned `app(bvar 2, dNat)`, it now returns `Type`. The VCompat
relation would need to handle this — but `Type` as a type is the top
disjunct (everything is VCompat with Type), so this should be easier,
not harder.

The app case of soundness_gen would change: when both evaluators see a
neutral function, concEvalE returns `app(f_neutral, aV)` while absEval
returns the inferred return type. VCompat between a stuck app and a type
is handled by the inferType disjunct.

## Alternatives Considered

### A. inferType on RHS in subCheckNF catch-all
Add `inferType ctx b` in the catch-all and check `ty_a ⊑ ty_b`. Simpler
but ad-hoc — doesn't fix the root cause (absEval losing type info).

### B. app ⊑ app structural rule
`app(f, a) ⊑ app(g, b)` when `f ⊑ g` and `a ⊑ b`. Unsound in general
(functions are contravariant in domain). Could be restricted to same-function
apps but this is fragile.

### C. Normalize with ctx in subCheckNF
Use ctx as eval env for normalization. Over-reduces — conflates types
and values, breaks existing tests.

## Success Criteria

1. `subCheck 50 dzero_e dNat_e = true` — the motivating test case.

2. All existing subCheck/concEval/absEval tests pass. Specifically:
   - `subCheck true' Nat' = false` (must NOT over-reduce)
   - `subCheck three' two' = false`
   - `subCheck false' true' = false`
   - All Church-encoded data tests

3. `lake build` succeeds.

4. No new sorry's beyond those already present (sorry'd proofs from the
   subCheckNF normalization change may need updating but shouldn't increase).

5. `WellTyped` tests for appendVec (W6, W9) can be re-enabled once
   appendArrays is rewritten with dependent Scott Nats.

## Implementation Order

1. Add `tyCtx` parameter to `absEval` (with default `[]`).
2. In absEval's app case, when the function is neutral, use
   `inferType tyCtx f'` to check if it has a function type. If so,
   evaluate the return type instead of returning stuck app.
3. Update `concEvalE` — option A (add tyCtx param, don't use it in
   neutral case) for minimal divergence.
4. Update all callers of absEval/concEvalE to pass tyCtx.
5. In subCheckNF, normalize both sides using the enhanced absEval (with
   ctx as tyCtx) instead of normalizeDomain.
6. Run tests, verify no over-reduction.
7. Test `dzero ⊑ dNat`.
8. If successful, rewrite appendArrays with dependent Scott Nats and
   re-enable W6/W9 tests.
