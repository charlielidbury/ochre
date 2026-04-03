# Mu as Value (Lazy Mu Evaluation)

## Problem

Currently `absEval` and `concEvalE` eagerly normalize under mu binders:

```
absEval (mu ann body) =
  match absEval (env.extend (mu ann body)) body with
  | some body' => some (mu ann body')
  | none => none
```

This causes two problems:

### 1. Fuel exhaustion with nested mus

Definitions like dependent Scott Nats use nested mus with let-bindings
(encoded as lambda+application):

```
dNat = mu dNat:Type.
  let dzero = mu dzero:dNat. ... in
  let dsucc = mu dsucc:(dNat->dNat). ... in
  body
```

When `absEval` enters the outer mu, it evaluates the body. The body
contains applications (the let-bindings), so it evaluates the arguments
(the inner mus). The inner mus reference the outer mu via self, creating
cascading evaluation that exhausts fuel.

### 2. Unnecessary complexity in the soundness proof

The mu case of `soundness_gen` is one of the hardest parts. It requires
`mu_body_subst_vcompat` (currently sorry'd) to bridge from VCompat on
normalized bodies to VCompat on self-substituted bodies. If mu were a
value, both evaluators would return the identical mu unchanged, and the
proof would be trivial via VCompat refl.

## Proposed Change

Make `mu ann body` a **value** in all three evaluators. It does not
evaluate its body until forced by application.

### absEval changes

```
-- BEFORE: normalize under the binder
| .mu ann body =>
    match absEval fuel (env.extend (.mu ann body)) body with
    | some body' => some (.mu ann body')
    | none => none

-- AFTER: mu is a value, return as-is
| .mu ann body => some (.mu ann body)
```

Same change for `concEvalE`.

### Application case (already exists, may need adjustment)

When mu appears in function position, it unfolds:

```
| .app f a =>
    match absEval fuel env f, absEval fuel env a with
    | some (.mu _ann body), some aVal =>
        -- Unfold: substitute self, then evaluate
        absEval fuel env (body.subst 0 (.mu _ann body))
        -- (existing mu-app dispatch logic may still apply for ann/body shape)
```

The existing mu-app cases in the evaluators already handle this. The key
change is just removing the eager body normalization.

### concEval (substitution-based)

`concEval` already treats mu as lazy — it unfolds on encounter:

```
| .mu ann body => concEval fuel (body.subst 0 (.mu ann body))
```

No change needed here.

## Impact on WellTyped

`WellTyped` currently recurses into mu bodies:

```
| .mu ann body =>
    WellTyped fuel (env.extend (.mu ann body)) body (Env.extend tyCtx (.mu ann body))
```

This should still work. WellTyped checks the source expression, not the
evaluated form. The mu body still needs to be well-typed; we're just
changing when the evaluator normalizes it.

## Impact on subCheckNF

`subCheckNF` already handles mu via self-intro and self-elim rules, which
unfold the mu. The structural mu-mu case:

```
| .mu _annA bodyA, .mu _annB bodyB =>
    subCheckNF fuel (Env.extend ctx (..)) seen bodyA bodyB
```

This compares bodies structurally. Since bodies are no longer normalized by
absEval, they'll be raw source bodies. This should still work since
subCheckNF operates on the syntactic structure.

## Impact on VCompat / Soundness Proof

This is the biggest win. Currently:

```
-- mu case of soundness_gen:
-- concEvalE (mu ann body) = some (mu ann bodyV')   -- normalized body
-- absEval (mu ann body) = some (mu ann bodyT')     -- normalized body
-- Need: VCompat n (mu ann bodyV') (mu ann bodyT')
-- Requires: mu_body_subst_vcompat (SORRY'D)
```

With mu as value:

```
-- mu case of soundness_gen:
-- concEvalE (mu ann body) = some (mu ann body)     -- identical!
-- absEval (mu ann body) = some (mu ann body)        -- identical!
-- Need: VCompat n (mu ann body) (mu ann body)
-- Trivially: VCompat refl
```

The `mu_body_subst_vcompat` lemma and related sorry's may become
unnecessary. The complexity shifts to the app case (mu in function
position), but that case already exists.

## Impact on inferType

`inferType` doesn't evaluate — it's purely structural. No change needed.

## Impact on Eval properties

- `ascFree_eval_equiv`: may need minor adjustment since mu bodies are no
  longer normalized, but the core argument (evaluators differ only at asc)
  still holds.
- `fuel_mono`: similar — the mu case becomes trivial (return the input).
- `absEval_ascFree` / `concEvalE_ascFree`: mu bodies may contain
  ascriptions, but since we don't evaluate them, the output mu has the same
  ascription-freedom as the input.

## Unlocks: Dependent Scott Nats

This change enables defining dependent Scott-encoded natural numbers:

```
dNat = mu dNat:Type.
  let dzero = mu dzero:dNat.
    \P:(dNat->Type). \z:(P dzero). \s:Type. z
  in
  let dsucc = mu dsucc:(dNat->dNat).
    \n:dNat. \P:(dNat->Type). \z:(P dzero).
    \s:(forall pred:dNat. P pred -> P (dsucc pred)).
    s n (n P z s)
  in
  \P:(dNat->Type). \z:(P dzero).
  \s:(forall pred:dNat. P pred -> P (dsucc pred)).
  P dNat
```

This can't work today because absEval tries to eagerly evaluate the nested
mus, causing fuel exhaustion. With mu as value, the inner mus are inert
until applied.

Dependent Scott Nats enable dependent elimination (the return type of case
analysis depends on the nat value), which is needed for functions like
`appendArrays` where different branches have different array lengths.

Currently `appendArrays` uses `Type` as the Church Nat elimination return
type (losing all type precision), which the strict `isCallable` check
correctly rejects. With dependent Scott Nats, the return type can be
precise (e.g., `Array (add n m) T`), avoiding the need for `Type` in
function position entirely.

## Success Criteria

1. `lake build` succeeds with no new sorry's beyond those already present.

2. All existing tests pass (including the currently-commented-out W6 and W9
   appendVec tests, which should be re-enabled once appendArrays is
   rewritten with dependent Scott Nats). Tests that relied on mu body
   normalization may need updating.

3. `absEval` and `concEvalE` return `mu ann body` unchanged (not
   `mu ann normalizedBody`).

4. Computation tests still work: `concEval` of programs involving mu
   (like `addRec`, recursive functions) should produce the same results.

5. `subCheck` tests still pass: subtype checking of mu types should work
   via self-intro/self-elim as before.

6. The sorry count in Soundness.lean should decrease or stay the same (the
   mu case should simplify, potentially eliminating `mu_body_subst_vcompat`
   and related sorry's).

## Implementation Order

1. Change `absEval` mu case to return `some (.mu ann body)` directly.
2. Change `concEvalE` mu case to return `some (.mu ann body)` directly.
3. Run tests, fix any that broke due to changed evaluation behavior.
4. Update the mu case of `soundness_gen` to use VCompat refl.
5. Check if `mu_body_subst_vcompat` and related lemmas are still needed.
6. Update VCompat definition if the "unfolded structural mu" disjunct can
   be simplified or removed.
7. Re-enable the appendVec WellTyped tests (W6, W9) once appendArrays is
   rewritten with dependent Scott Nats.
