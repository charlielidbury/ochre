# Mu Application Self-Reference Bug

## Status

One remaining test blocked by this: `appendArrays` standalone type check.
The north star (`appendVec : Vec T → Vec T → Vec T`) already passes
without this fix, because the domain checking + precise type annotations
are sufficient for the subtype checker to track types through the body.

## The Problem

When `absEval` encounters a mu expression in function position (`.app (.mu ann body) arg`),
it beta-reduces by substituting the argument into the body's lambda — but **skips substituting
the mu self-reference**. The self-ref becomes a dangling de Bruijn variable.

```
-- Eval.lean, absEval, .app case:
| .mu _ann body =>
  match _ann, body with
  | _, .lam _dom retBody =>
    absEval fuel ctx seen (retBody.subst 0 a'.val)  -- self-ref NOT substituted!
```

Compare with `concEval`, which does it correctly:

```
| some (.mu ann body), some aVal =>
  concEval fuel (.app (body.subst 0 (.mu ann body)) aVal)  -- unfold self-ref FIRST
```

### Concrete Impact

```
appendArrays = μ self:(... → Array_ n1 T → Array_ n2 T → Array_ (add_ n1 n2) T).
  λT. λn1. λn2. λarr1. λarr2.
    isZero_ n1 ... arr2 ... (Pair (fst_ arr1) (self T (pred_ n1) n2 (snd_ arr1) arr2)) ...
```

When `absEval` applies `appendArrays` to concrete args, `self` (the recursive reference)
becomes a dangling bvar instead of the full mu expression. Any use of `self` in the body
produces garbage. This means absEval can't verify `appendArrays` has its declared type.

## Why Naive Unfolding Fails

The obvious fix — always unfold like `concEval` — causes infinite loops for genuinely
recursive functions:

```
toZero = μ self:NatToNat. λn:Nat_. isZero_ n Nat_ zero_ (self zero_)
```

`absEval` eagerly evaluates all arguments. When normalizing under the binder `n:Nat_`:
1. Body contains `(self zero_)` as an argument to `isZero_`
2. absEval evaluates this argument (eager)
3. Unfold: `self` → `toZero` → body contains `(self zero_)` → unfold again → ...

`concEval` avoids this because `isZero_` on concrete `zero_` selects the zero branch
before `self zero_` is evaluated. But `absEval` normalizes under binders where `n` is
abstract, so both branches get evaluated.

## Proposed Solution: Seen Set for Mu Application

Thread the `seen` set (already used in `subCheckNF` for equi-recursive cycles) through
mu application in `absEval`. When unfolding a mu, add `(mu_expr, mu_expr)` to `seen`.
If we encounter the same mu application again, return a neutral term instead of unfolding.

```
| .mu ann body =>
  let mu_expr := Expr.mu ann body
  if seen.any (fun (a', _) => a' == mu_expr) then
    -- Already unfolding this mu — return neutral to prevent infinite loop
    .ok ⟨.app mu_expr a'.val⟩
  else
    let seen' := (mu_expr, mu_expr) :: seen
    absEval fuel ctx seen' (.app (body.subst 0 mu_expr) a'.val)
```

This correctly handles both cases:
- **Self-types** (like `dzero`, `dfalse`): The mu body is a non-recursive lambda.
  Unfolding once produces a lambda with no further self-references. Works immediately.
- **Recursive functions** (like `toZero`): The first unfolding replaces `self` with
  the full mu. The recursive `self zero_` triggers another application of the same mu.
  The `seen` set catches this and returns a neutral term, preventing infinite unfolding.

### Open Question

For recursive functions, the neutral term returned on the second encounter has the mu
body (without self-ref substitution) as the function. This loses type information.
A better approach might be to use the mu annotation to determine the return type:

```
-- If ann = λdom. retTy, return retTy.subst 0 arg
```

This would give the recursive call a proper inferred type based on the annotation,
even though the actual computation is blocked.

## Affected Tests

Currently blocked — get these passing:
- `subCheck appendArrays (λT. λn1. λn2. Array_ n1 T → Array_ n2 T → Array_ (add_ n1 n2) T)` currently `= false`, should be `= true` (Array.lean)
- `subCheck dzero done_` currently `= true`, should be `= false` (DNat.lean) — the corrupted normal form of `done_` (dangling self-ref) causes the checker to spuriously accept `dzero <: dsucc dzero`

Already passing (do NOT break these):
- `subCheck appendVec (λT. Vec T → Vec T → Vec T) = true`
- `subCheck appendVec_wrong (λT. Vec T → Vec T → Vec T) = false`
- `subCheck toZero NatToNat = true` (Mu.lean)
- `subCheck toZeroThunked NatToNat = true` (Mu.lean)
- `subCheck dtrue dBool = true` (DBool.lean)
- All domain checking tests (e.g. `(λx:true. x) false` fails)
