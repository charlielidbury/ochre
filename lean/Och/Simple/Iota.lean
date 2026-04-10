import Och.Simple.Syntax
import Och.Simple.Subtype
import Och.Simple.Precise

/-!
# Iota extension: breaking the IotaElim circularity

This file picks up where `Precise.lean` left off. It adds a second rule
to handle the **both-sides iota** case (where both the LHS and RHS are
self-types and the original problem `dtrue ⊑ dBool` lives).

## The circularity, restated

`PSub` in `Precise.lean` has `iotaIntro : a ⊑ body[0 := a] → a ⊑ ι. body`,
which handles a RHS iota by substituting the *value* `a`. This works
beautifully when the LHS is already a lambda (non-iota). But what about
the case where the LHS is itself an iota?

Consider:
```
dBool  = ι self. ∀P:(self→⊤). (P dtrue) → (P dfalse) → P self
dtrue  = ι self. λP:(self→⊤). λt:(P dtrue). λf:⊤. t
```

To prove `dtrue ⊑ dBool`:
1. [iotaIntro] with `a := dtrue, body := dBoolBody`: now need
   `dtrue ⊑ dBoolBody[0 := dtrue]`.
2. But the LHS is STILL a head-iota. None of the structural Sub rules
   (Refl, Lam, App, ...) can make progress.
3. We need a way to *unfold* the LHS iota into its body (with the iota
   substituted for the self-reference, keeping everything well-scoped).

The previous agent identified IotaElim as the missing piece, with a
circular well-typedness side condition. The question: can we side-step
the side condition?

## Approach 1: IotaElim as equi-recursive unfolding

**Key insight**: for head-iotas (where `.iota` is literally the outermost
constructor of the LHS), there is no "type-checking side condition" to
worry about — the unfolding is a pure syntactic fact. The term
`.iota body` is "unfolded" to `body[0 := .iota body]` (substituting the
iota itself for its self-reference).

This is the *equi-recursive* view of self-types: a self-type is equal to
its one-step unfolding. We don't need any typing information; the
unfolding is a syntactic rewrite.

We add this as a direct Sub rule:

```
[IotaL] body[0 := ι. body] ⊑ b  →  ι. body ⊑ b
[IotaR] a ⊑ body[0 := ι. body]  →  a ⊑ ι. body      -- the "dumb" RHS rule
```

`[IotaR]` is the equi-recursive dual, but it is *strictly weaker* than
`[IotaIntro]` from `Precise.lean`: it substitutes the type itself, not
the value under test. We KEEP `[IotaIntro]` because its precise value
substitution is what breaks the covariant cases.

**Key question**: is combining `iotaIntro` (precise RHS unfolding) with
`iotaL` (equi-recursive LHS unfolding) sound, and does it handle the
both-sides case?

## This file

We define `ISub` — an extension of `PSub` with `iotaL` — and attempt to
derive a small both-sides iota example.

The point is **insight**, not a fully metatheoretically-verified system.
Soundness/transitivity/etc. are NOT proven here — they are stubbed.
-/

set_option autoImplicit false

namespace Och.Simple.Iota

open Och.Simple.Precise

/-- Extension of `PSub` with equi-recursive LHS iota unfolding.

    We inline all of `PSub`'s constructors here rather than reusing
    `PSub` directly so that rules interact mutually with the new iotaL. -/
inductive ISub : PCtx → PExpr → PExpr → Type where
  | refl  : (Γ : PCtx) → (a : PExpr) → ISub Γ a a
  | top   : (Γ : PCtx) → (a : PExpr) → ISub Γ a .top
  | var   : (Γ : PCtx) → (x : Nat) → (b T : PExpr) →
            Γ.get? x = some T → ISub Γ T b → ISub Γ (.var x) b
  | lam   : (Γ : PCtx) → (A B b₁ b₂ : PExpr) →
            ISub Γ B A → ISub (B :: Γ) b₁ b₂ →
            ISub Γ (.lam A b₁) (.lam B b₂)
  | app   : (Γ : PCtx) → (f a b D R : PExpr) →
            ISub Γ f (.lam D R) →
            ISub Γ a D →
            ISub Γ (R.subst 0 a) b →
            ISub Γ (.app f a) b
  | ascL  : (Γ : PCtx) → (e τ b : PExpr) →
            ISub Γ e τ → ISub Γ τ b → ISub Γ (.asc e τ) b
  | ascR  : (Γ : PCtx) → (a e τ : PExpr) →
            ISub Γ e τ → ISub Γ a e → ISub Γ a (.asc e τ)
  /-- [IotaIntro] — precise RHS unfolding: substitute the value `a` into
      the body.

      Handles covariant self-references (the `dBool.P self` case). -/
  | iotaIntro : (Γ : PCtx) → (a body : PExpr) →
                ISub Γ a (body.subst 0 a) →
                ISub Γ a (.iota body)
  /-- [IotaL] — equi-recursive LHS unfolding: substitute the iota itself
      into the body.

      NOTE: this is the contentful new rule. It does NOT have any
      well-typedness side condition. The unfolding is a purely syntactic
      rewrite, justified by viewing `ι. body` as equi-recursively equal
      to its unfolding. -/
  | iotaL : (Γ : PCtx) → (body b : PExpr) →
            ISub Γ (body.subst 0 (.iota body)) b →
            ISub Γ (.iota body) b
  /-- [DefEq] — for residual beta/ascription differences. -/
  | defEq : (Γ : PCtx) → (a b : PExpr) → PDefEq a b → ISub Γ a b

-- ============================================================
-- Test 1: A minimal both-sides iota
-- ============================================================

/-!
### Test 1 — both sides are iotas, LHS head-iota equals RHS head-iota

Take:
```
T = ι self. self → ⊤
t = ι self. λx:self. ⊤
```

These are NOT syntactically equal (`.iota (.lam (.var 0) .top)` vs
`.iota (.lam (.var 0) .top)` — wait, they ARE equal).

Let's make them differ. Use:
```
T = ι self. self → ⊤                   -- a "predicate type"
t = ι self. λx:self. x                  -- identity on self
```

Then `T = .iota (.lam (.var 0) .top)`
and  `t = .iota (.lam (.var 0) (.var 0))`

To prove `ISub Γ t T`:
1. [iotaIntro] with `a := t, body := (.lam (.var 0) .top)`:
   need `ISub Γ t ((.lam (.var 0) .top).subst 0 t)
             = ISub Γ t (.lam t .top)`
2. [iotaL] with body₁ := `.lam (.var 0) (.var 0)`, b := `.lam t .top`:
   need `ISub Γ ((.lam (.var 0) (.var 0)).subst 0 t) (.lam t .top)
             = ISub Γ (.lam t (.var 0)) (.lam t .top)`
   (after subst: domain becomes `t`, body is `.var 0` — which is the
   bound variable `x:t`, unchanged by the subst since its index is 0
   referring to the lambda binder, not the iota self.)

   Wait, let me recompute. `.lam (.var 0) (.var 0)` has:
   - domain `.var 0` which refers to the iota's self (outer binder)
   - body `.var 0` which refers to the *lambda's* bound variable (the new inner binder)

   When we subst 0 with `t`, we're substituting the OUTER binder (iota self).
   The lambda body's `.var 0` is a DIFFERENT variable — the lambda bind —
   which corresponds to "index 0 under a binder". The subst recurses with
   target+1 = 1 under the lambda. So:
   - `.lam (.var 0) (.var 0)` .subst 0 t
     = `.lam ((.var 0).subst 0 t) ((.var 0).subst 1 (t.shift 0 1))`
     = `.lam t (.var 0)` (since `.var 0 == 1` is false, `0 > 1` false, so unchanged)

   So post-subst LHS is `.lam t (.var 0)`, which is `λx:t. x`. Good.

3. [lam] with A := t, B := t, b₁ := .var 0, b₂ := .top:
   - contravariant: `ISub Γ t t` → [refl]
   - body: `ISub (t :: Γ) (.var 0) .top` → [top]

Done. This example uses `iotaIntro` + `iotaL` + `lam` + `refl` + `top`.
No DefEq needed; no circular side condition.
-/

/-- The predicate-type `T = ι self. self → ⊤`, encoded as iota over
    `λx:self. ⊤`. In de Bruijn, the inner lambda's domain references the
    iota-self at `.var 0`, and the body `.top` has no free vars. -/
def T : PExpr := .iota (.lam (.var 0) .top)

/-- The term `t = ι self. λx:self. x`: the identity function that
    "accepts itself and returns it". The inner body `.var 0` refers
    to the lambda-bound `x`, not the iota-self. -/
def t : PExpr := .iota (.lam (.var 0) (.var 0))

/-- Test 1: `t ⊑ T` with both sides iotas. -/
example (Γ : PCtx) : ISub Γ t T := by
  -- Step 1: iotaIntro on the RHS, body = (lam (var 0) top)
  apply ISub.iotaIntro Γ t (.lam (.var 0) .top)
  -- Goal: ISub Γ t ((lam (var 0) top).subst 0 t) = ISub Γ t (lam t top)
  show ISub Γ t (.lam t .top)
  -- Step 2: iotaL on the LHS, body = (lam (var 0) (var 0))
  apply ISub.iotaL Γ (.lam (.var 0) (.var 0)) (.lam t .top)
  -- Goal: ISub Γ ((lam (var 0) (var 0)).subst 0 (iota (lam (var 0) (var 0)))) (lam t top)
  --     = ISub Γ (lam t (var 0)) (lam t top)
  show ISub Γ (.lam t (.var 0)) (.lam t .top)
  -- Step 3: lam, with A=t, B=t
  apply ISub.lam Γ t t (.var 0) .top
  · exact ISub.refl Γ t
  · exact ISub.top (t :: Γ) (.var 0)

-- ============================================================
-- Test 2: the nil' ⊑ Nil' case that Precise.lean couldn't handle
-- ============================================================

/-!
### Test 2 — non-iota LHS, iota RHS, with contravariant self-ref

From `Precise.lean`:
```
Nil' = ι self. self → ⊤
nil' = λ(x : Nil'). ⊤
```

`Precise.lean` got stuck here because after [iotaIntro], the contravariant
domain check reproduced the original `nil' ⊑ Nil'` goal.

Does `iotaL` help? Let's see. The LHS is NOT an iota (it's a lambda),
so `iotaL` doesn't apply directly. Tracing:

1. Goal: `ISub Γ nil' Nil'` = `ISub Γ (.lam Nil' .top) (.iota (.lam (.var 0) .top))`
2. [iotaIntro] with `a := nil', body := (.lam (.var 0) .top)`:
   need `ISub Γ nil' (.lam nil' .top)`.
3. [lam] with A := Nil', B := nil'.
   - contravariant: `ISub Γ nil' Nil'` — BACK TO THE ORIGINAL GOAL.

Still stuck. `iotaL` doesn't apply because the LHS in the contravariant
subgoal is `nil'` (a lambda), not an iota.

**What would work?**  We need to *unfold the RHS iota* (`Nil'`) from the
original position, instead of substituting `nil'`. That's [iotaR]
(equi-recursive RHS unfolding). Let's add it.
-/

/-- `Nil' = ι self. self → ⊤`. Same as `T` above. -/
def Nil' : PExpr := .iota (.lam (.var 0) .top)

/-- `nil' = λ(x : Nil'). ⊤`. A non-iota term. -/
def nil' : PExpr := .lam Nil' .top

-- Attempt with iotaL only (expected: stuck).
-- example (Γ : PCtx) : ISub Γ nil' Nil' := by
--   apply ISub.iotaIntro Γ nil' (.lam (.var 0) .top)
--   show ISub Γ nil' (.lam nil' .top)
--   apply ISub.lam Γ Nil' nil' .top .top
--   · -- nil' ⊑ Nil' — CYCLE
--     sorry
--   · exact ISub.top _ _

-- ============================================================
-- A richer relation: add iotaR (equi-recursive RHS unfolding)
-- ============================================================

/-!
### Adding [iotaR]

If `iotaL` is sound (as equi-recursive unfolding), so is its dual
`iotaR : ISub Γ a (body.subst 0 (.iota body)) → ISub Γ a (.iota body)`.

But [iotaR] is weaker than [iotaIntro] and slightly redundant. We can
include both — they are compatible. The question is whether we can
now close `nil' ⊑ Nil'` using [iotaR] *without* taking [iotaIntro]
first.

Trace:
1. Goal: `ISub Γ nil' Nil'`
2. [iotaR] with body := `.lam (.var 0) .top`:
   need `ISub Γ nil' ((.lam (.var 0) .top).subst 0 Nil')
             = ISub Γ nil' (.lam Nil' .top)`
3. `nil' = .lam Nil' .top`, so this is `ISub Γ (.lam Nil' .top) (.lam Nil' .top)` — [refl].

DONE — no recursion, no DefEq. The key was using [iotaR] (equi-recursive)
instead of [iotaIntro] (precise). **In the contravariant case,
equi-recursive unfolding is actually the RIGHT move**: we want both sides
to match at the unfolded level so that the domain check is reflexive.

`[iotaIntro]` excels when the self-reference appears COVARIANTLY
(substituting the value collapses both sides' appearances of the
self-ref). `[iotaR]` excels when the self-reference appears
CONTRAVARIANTLY (substituting the type keeps the two sides symmetric).

**Conjecture**: adding BOTH `iotaIntro` + `iotaR` + `iotaL` handles both
polarities.

Let's define the extended relation and test.
-/

/-- `JSub` = `ISub` + iotaR. -/
inductive JSub : PCtx → PExpr → PExpr → Type where
  | refl  : (Γ : PCtx) → (a : PExpr) → JSub Γ a a
  | top   : (Γ : PCtx) → (a : PExpr) → JSub Γ a .top
  | var   : (Γ : PCtx) → (x : Nat) → (b T : PExpr) →
            Γ.get? x = some T → JSub Γ T b → JSub Γ (.var x) b
  | lam   : (Γ : PCtx) → (A B b₁ b₂ : PExpr) →
            JSub Γ B A → JSub (B :: Γ) b₁ b₂ →
            JSub Γ (.lam A b₁) (.lam B b₂)
  | app   : (Γ : PCtx) → (f a b D R : PExpr) →
            JSub Γ f (.lam D R) →
            JSub Γ a D →
            JSub Γ (R.subst 0 a) b →
            JSub Γ (.app f a) b
  | ascL  : (Γ : PCtx) → (e τ b : PExpr) →
            JSub Γ e τ → JSub Γ τ b → JSub Γ (.asc e τ) b
  | ascR  : (Γ : PCtx) → (a e τ : PExpr) →
            JSub Γ e τ → JSub Γ a e → JSub Γ a (.asc e τ)
  | iotaIntro : (Γ : PCtx) → (a body : PExpr) →
                JSub Γ a (body.subst 0 a) →
                JSub Γ a (.iota body)
  | iotaL : (Γ : PCtx) → (body b : PExpr) →
            JSub Γ (body.subst 0 (.iota body)) b →
            JSub Γ (.iota body) b
  /-- [iotaR] — equi-recursive RHS unfolding. Weaker than iotaIntro but
      covers different use cases (especially contravariant self-ref). -/
  | iotaR : (Γ : PCtx) → (a body : PExpr) →
            JSub Γ a (body.subst 0 (.iota body)) →
            JSub Γ a (.iota body)
  | defEq : (Γ : PCtx) → (a b : PExpr) → PDefEq a b → JSub Γ a b

/-- Test 2 with JSub: nil' ⊑ Nil' via iotaR + refl. -/
example (Γ : PCtx) : JSub Γ nil' Nil' := by
  apply JSub.iotaR Γ nil' (.lam (.var 0) .top)
  -- Goal: JSub Γ nil' ((.lam (.var 0) .top).subst 0 Nil')
  --     = JSub Γ nil' (.lam Nil' .top)
  show JSub Γ nil' (.lam Nil' .top)
  -- nil' = .lam Nil' .top, so this is reflexivity.
  exact JSub.refl Γ (.lam Nil' .top)

/-- Test 1 with JSub: t ⊑ T via iotaIntro + iotaL + lam. -/
example (Γ : PCtx) : JSub Γ t T := by
  apply JSub.iotaIntro Γ t (.lam (.var 0) .top)
  show JSub Γ t (.lam t .top)
  apply JSub.iotaL Γ (.lam (.var 0) (.var 0)) (.lam t .top)
  show JSub Γ (.lam t (.var 0)) (.lam t .top)
  apply JSub.lam Γ t t (.var 0) .top
  · exact JSub.refl Γ t
  · exact JSub.top (t :: Γ) (.var 0)

-- ============================================================
-- Test 3: the realistic dBool pattern (simplified)
-- ============================================================

/-!
### Test 3 — a dBool-shaped test

Let's do a dBool-style cycle with the minimum necessary structure.
A faithful dBool is big, so we use a cut-down version:

```
dBool = ι self. (self → ⊤) → ⊤
dtrue = ι self. λk:(self → ⊤). ⊤
```

(`self → ⊤` = `.lam (.var 0) .top` under the iota binder)
(`(self → ⊤) → ⊤` = `.lam (.lam (.var 0) .top) .top`)

`dBool` body `(self → ⊤) → ⊤` is `.lam (.lam (.var 0) .top) .top`.
`dtrue` body `λk:(self → ⊤). ⊤` is `.lam (.lam (.var 0) .top) .top` —
SAME shape! So `dBool = dtrue` syntactically. Not a useful test.

Let's differ them:
```
dBool = ι self. (self → ⊤) → ⊤
dtrue = ι self. λk:(self → ⊤). k self
```

`dtrue` body: `.lam (.lam (.var 0) .top) (.app (.var 0) (.var 1))`
(`.var 0` is k; `.var 1` is iota-self).

Goal: `JSub Γ dtrue dBool`.

Step 1: [iotaIntro] a := dtrue, body := `.lam (.lam (.var 0) .top) .top`:
  need `JSub Γ dtrue ((.lam (.lam (.var 0) .top) .top).subst 0 dtrue)`

  Subst: outer lam's domain is `.lam (.var 0) .top` under one new binder
  for k, so subst 0 dtrue replaces the iota-self (which is shifted to .var 1
  under the lambda). Wait — we're substituting at depth 0 at the TOP level,
  then recursing into the lam which shifts the target.

  `(.lam D B).subst 0 dtrue
    = .lam (D.subst 0 dtrue) (B.subst 1 (dtrue.shift 0 1))`

  Here D = `.lam (.var 0) .top`. `.var 0` inside D refers to the iota-self
  (since it's NOT under any new binder yet — wait, it IS under D's own lam
  binder). Let me recompute.

  `D = .lam (.var 0) .top`. This lambda has its own binder. The `.var 0`
  inside is the lambda's param (`x`), NOT the iota-self. So subst 0 doesn't
  touch it. Actually wait — the iota-self becomes `.var 1` under this inner
  lam, so .subst at index 1. But we're calling .subst 0 on the *outer* level,
  and inside the lam we recurse to .subst 1. The `.var 0` inside D's body
  (`.var 0` = lambda bind x) is at index 0 at the target+1=1 level... the
  substitute target is 1, we look at `.var 0`, `0 != 1`, `0 < 1`, so unchanged.
  The `.top` is unchanged. So D.subst 0 dtrue = D itself (no iota-self in D).

  Actually wait, in `dBool = ι self. (self → ⊤) → ⊤`, the "self" is the
  domain of the INNER lambda (`self → ⊤`). Let me redo the de Bruijn.

  `(self → ⊤) → ⊤` under the iota binder:
    - outer lam (domain = self → ⊤, body = ⊤)
    - outer lam's domain = "self → ⊤" = λ_:self. ⊤
      - inner lam (domain = self, body = ⊤)
      - inner lam's domain `self` — under iota binder + nothing else, so `.var 0`
      - inner lam's body `⊤`
    - So outer lam's domain = .lam (.var 0) .top
    - outer lam's body = .top (no free vars)

  Full: `.iota (.lam (.lam (.var 0) .top) .top)`

  The `.var 0` here is at depth 1 under iota (wrapped by outer lam... wait,
  NO — it's inside the *domain* of the outer lam. The domain of a lam is
  NOT under that lam's binder. So .var 0 in D still refers to the iota-self
  (depth 0 from iota). Good.

  Now subst .iota body at 0, recursively:
    .lam D B → .lam (D.subst 0 v) (B.subst 1 v↑)
    where D = .lam (.var 0) .top.
    D.subst 0 v: recursively, .lam (.var 0) .top
      = .lam ((.var 0).subst 0 v) ((.top).subst 1 v↑)
      = .lam v .top
      (since (.var 0).subst 0 v = v, because k=0 == target=0)
    So D.subst 0 v = .lam v .top.
    B = .top, B.subst _ _ = .top.

  Full: `.lam (.lam dtrue .top) .top`

Step 1 output: need `JSub Γ dtrue (.lam (.lam dtrue .top) .top)`.

Step 2: iotaL on LHS (dtrue = .iota dtrue_body):
  dtrue_body = `.lam (.lam (.var 0) .top) (.app (.var 0) (.var 1))`
  Subst 0 dtrue: the domain contains `.var 0` = lambda k's param… no wait.

  Recompute. dtrue_body = .lam (D_k) (body_k) where:
    D_k = .lam (.var 0) .top = "self → ⊤"  -- here .var 0 = iota-self
    body_k = .app (.var 0) (.var 1)         -- .var 0 = k, .var 1 = iota-self

  dtrue_body.subst 0 dtrue:
    = .lam (D_k.subst 0 dtrue) (body_k.subst 1 (dtrue.shift 0 1))

  D_k.subst 0 dtrue = .lam dtrue .top (same calc as above).
  body_k.subst 1 (dtrue↑): .app with .var 0 and .var 1:
    .var 0: k = 0, target = 1, 0 != 1, 0 < 1, unchanged → .var 0
    .var 1: k = 1, target = 1, equal → replacement = dtrue↑

  So body_k.subst 1 (dtrue↑) = .app (.var 0) (dtrue.shift 0 1)

  dtrue_body.subst 0 dtrue = .lam (.lam dtrue .top) (.app (.var 0) (dtrue.shift 0 1))

Step 2 goal:
  JSub Γ (.lam (.lam dtrue .top) (.app (.var 0) (dtrue.shift 0 1)))
         (.lam (.lam dtrue .top) .top)

Step 3: [lam]
  - A = .lam dtrue .top, B = .lam dtrue .top → refl
  - body: JSub ((.lam dtrue .top) :: Γ) (.app (.var 0) (dtrue.shift 0 1)) .top
    → [top]

Done. Beautiful — the dtrue ⊑ dBool simplified form goes through with
iotaIntro + iotaL + lam + refl + top. No DefEq!
-/

def dBool : PExpr := .iota (.lam (.lam (.var 0) .top) .top)
def dtrue : PExpr := .iota (.lam (.lam (.var 0) .top) (.app (.var 0) (.var 1)))

/-- Test 3: simplified dtrue ⊑ dBool. Both sides are iotas. -/
example (Γ : PCtx) : JSub Γ dtrue dBool := by
  -- Step 1: iotaIntro with a := dtrue, body := body_dBool
  apply JSub.iotaIntro Γ dtrue (.lam (.lam (.var 0) .top) .top)
  -- Goal after subst: JSub Γ dtrue (.lam (.lam dtrue .top) .top)
  show JSub Γ dtrue (.lam (.lam dtrue .top) .top)
  -- Step 2: iotaL on LHS with body := body_dtrue
  apply JSub.iotaL Γ (.lam (.lam (.var 0) .top) (.app (.var 0) (.var 1)))
  -- Goal after subst: JSub Γ
  --   (.lam (.lam dtrue .top) (.app (.var 0) (dtrue.shift 0 1)))
  --   (.lam (.lam dtrue .top) .top)
  show JSub Γ
    (.lam (.lam dtrue .top) (.app (.var 0) (dtrue.shift 0 1)))
    (.lam (.lam dtrue .top) .top)
  -- Step 3: lam
  apply JSub.lam Γ (.lam dtrue .top) (.lam dtrue .top)
    (.app (.var 0) (dtrue.shift 0 1)) .top
  · exact JSub.refl Γ (.lam dtrue .top)
  · exact JSub.top _ _

-- ============================================================
-- Test 4: richer dBool with P : self → ⊤ pattern
-- ============================================================

/-!
### Test 4 — dBool with an actual `P` predicate

```
dBool2 = ι self. (self → ⊤) → (self → ⊤)
dtrue2 = ι self. λk:(self → ⊤). λx:self. k x
```

This is closer to the real Cedille encoding: the outer lam binds `P`
(a predicate on self), the inner lam binds `x` (an element of self),
and the body applies `P` to `x`. Both sides are iotas; the LHS body
really does something with both arguments.

This exercises:
- iotaIntro (value substitution on RHS)
- iotaL (equi-rec unfolding of LHS iota)
- lam on two nested lambdas
- refl on the shifted `dtrue2` (domains match after both substitutions)
- top on the body (`k x ⊑ ⊤`)
-/

def dBool2 : PExpr :=
  .iota (.lam (.lam (.var 0) .top) (.lam (.var 1) .top))

def dtrue2 : PExpr :=
  .iota (.lam (.lam (.var 0) .top) (.lam (.var 1) (.app (.var 1) (.var 0))))

/-- Test 4: dtrue2 ⊑ dBool2 — richer dBool pattern with a real predicate. -/
example (Γ : PCtx) : JSub Γ dtrue2 dBool2 := by
  -- Step 1: iotaIntro
  apply JSub.iotaIntro Γ dtrue2 (.lam (.lam (.var 0) .top) (.lam (.var 1) .top))
  -- Goal: JSub Γ dtrue2 ((...).subst 0 dtrue2)
  --     = JSub Γ dtrue2 (.lam (.lam dtrue2 .top) (.lam (dtrue2.shift 0 1) .top))
  show JSub Γ dtrue2
    (.lam (.lam dtrue2 .top) (.lam (dtrue2.shift 0 1) .top))
  -- Step 2: iotaL
  apply JSub.iotaL Γ
    (.lam (.lam (.var 0) .top) (.lam (.var 1) (.app (.var 1) (.var 0))))
  -- Goal after subst: the LHS becomes
  --   .lam (.lam dtrue2 .top) (.lam (dtrue2.shift 0 1) (.app (.var 1) (.var 0)))
  show JSub Γ
    (.lam (.lam dtrue2 .top) (.lam (dtrue2.shift 0 1) (.app (.var 1) (.var 0))))
    (.lam (.lam dtrue2 .top) (.lam (dtrue2.shift 0 1) .top))
  -- Step 3: outer lam
  apply JSub.lam Γ (.lam dtrue2 .top) (.lam dtrue2 .top)
  · exact JSub.refl Γ (.lam dtrue2 .top)
  -- Step 4: inner lam
  apply JSub.lam ((.lam dtrue2 .top) :: Γ)
    (dtrue2.shift 0 1) (dtrue2.shift 0 1)
  · exact JSub.refl _ (dtrue2.shift 0 1)
  -- Step 5: top closes the body
  exact JSub.top _ _

-- ============================================================
-- Test 5: faithful dBool with P self -> P self (real Church/Cedille)
-- ============================================================

/-!
### Test 5 — faithful dBool with `P self → P self` and uses iotaIntro's
precision

```
dBool3 = ι self. ∀P:(self → ⊤). P self → P self
dtrue3 = ι self. λP:(self → ⊤). λp:(P self). p
```

This is THE canonical Church-dependent Bool structure (minus dfalse,
which we elide for brevity). Both sides are iotas; both reference `self`
under `P` (a predicate), so the `iotaIntro` value substitution is
essential for making `P self` on the RHS match `P self` on the LHS
after unfolding.

We close this WITHOUT DefEq using the same three-rule combo: iotaIntro,
iotaL, and structural rules (lam, var, refl, top). The `var` rule
discharges the body with `p : P dtrue3` against `P dtrue3` by
reflexivity on the context lookup.
-/

def dBool3 : PExpr :=
  .iota (.lam (.lam (.var 0) .top)
    (.lam (.app (.var 0) (.var 1)) (.app (.var 1) (.var 2))))

def dtrue3 : PExpr :=
  .iota (.lam (.lam (.var 0) .top)
    (.lam (.app (.var 0) (.var 1)) (.var 0)))

/-- Test 5: dtrue3 ⊑ dBool3 — the canonical Church-dependent Bool. -/
example (Γ : PCtx) : JSub Γ dtrue3 dBool3 := by
  apply JSub.iotaIntro Γ dtrue3
    (.lam (.lam (.var 0) .top)
      (.lam (.app (.var 0) (.var 1)) (.app (.var 1) (.var 2))))
  show JSub Γ dtrue3
    (.lam (.lam dtrue3 .top)
      (.lam (.app (.var 0) (dtrue3.shift 0 1))
        (.app (.var 1) (dtrue3.shift 0 2))))
  apply JSub.iotaL Γ
    (.lam (.lam (.var 0) .top)
      (.lam (.app (.var 0) (.var 1)) (.var 0)))
  show JSub Γ
    (.lam (.lam dtrue3 .top)
      (.lam (.app (.var 0) (dtrue3.shift 0 1)) (.var 0)))
    (.lam (.lam dtrue3 .top)
      (.lam (.app (.var 0) (dtrue3.shift 0 1))
        (.app (.var 1) (dtrue3.shift 0 2))))
  -- Outer lam (P : dtrue3 → ⊤)
  apply JSub.lam Γ (.lam dtrue3 .top) (.lam dtrue3 .top)
  · exact JSub.refl Γ (.lam dtrue3 .top)
  -- Inner lam (p : P dtrue3)
  apply JSub.lam ((.lam dtrue3 .top) :: Γ)
    (.app (.var 0) (dtrue3.shift 0 1))
    (.app (.var 0) (dtrue3.shift 0 1))
  · exact JSub.refl _ _
  -- Body: JSub [p:P dt, P:dt→⊤, Γ] (.var 0) (.app (.var 1) (dtrue3.shift 0 2))
  -- Use [var] with T := the RHS (the context lookup gives exactly this).
  apply JSub.var _ 0 _ (.app (.var 1) (dtrue3.shift 0 2))
  · -- Γ.get? 0 lookup: innermost entry is (.app (.var 0) (dtrue3.shift 0 1)),
    -- shifted by 0+1=1 → (.app (.var 1) (dtrue3.shift 0 2))
    rfl
  · exact JSub.refl _ _

-- ============================================================
-- Summary
-- ============================================================

/-!
## Findings

### What works

Adding two equi-recursive unfolding rules alongside `[iotaIntro]`:

1. **[iotaL]** `body[0 := ι. body] ⊑ b → ι. body ⊑ b`  — LHS head-iota
   equi-recursive unfolding
2. **[iotaR]** `a ⊑ body[0 := ι. body] → a ⊑ ι. body`  — RHS head-iota
   equi-recursive unfolding

gives us three self-type rules:
- **[iotaIntro]** (precise): best for covariant self-ref positions
- **[iotaR]** (equi-rec RHS): best for contravariant self-ref and "LHS is
  a lambda matching the iota's body" cases
- **[iotaL]** (equi-rec LHS): best when the LHS is itself a head-iota

With these three, we mechanically closed:
- `t ⊑ T` (both sides iotas) — uses iotaIntro + iotaL + lam + refl + top
- `nil' ⊑ Nil'` (contravariant) — uses iotaR + refl
- Simplified `dtrue ⊑ dBool` — uses iotaIntro + iotaL + lam + refl + top

**No DefEq needed.** All three tests close with purely structural steps
after the iota rules fire. **No circular well-typedness condition** is
used — the equi-recursive rules are pure syntactic rewrites.

### Why no circularity?

The previous agent's `[IotaElim]` rule had the form:
```
(Γ ⊢ a : ι. body) → Γ ⊢ body[0 := a] ⊑ b → Γ ⊢ a ⊑ b
```
The well-typedness premise `a : ι. body` is circular with subtyping.

Our `[iotaL]` is strictly weaker but sufficient:
```
Γ ⊢ body[0 := ι. body] ⊑ b → Γ ⊢ (ι. body) ⊑ b
```
The substitution is NOT the value `a`, it's the iota itself — so no
well-typedness side condition is needed. This is the trick: we traded
precision for a purely syntactic rule.

### Open concerns (what is NOT checked here)

1. **Soundness.** Is `ISub`/`JSub` sound w.r.t. the intended semantics?
   Specifically, is it true that `Γ ⊢ ι. body ≡ body[0 := ι. body]`
   holds definitionally in the model? For equi-recursive self-types, yes.
   For iso-recursive (with explicit fold/unfold), no. Simple Och is closer
   to equi-recursive, so this should be fine.

2. **Transitivity and decidability.** Transitivity is NOT proven for
   `JSub`. The concern: can a chain like `a ⊑ iota.body[0 := a] ⊑ ...`
   nontrivially fail to compose? A lexicographic termination argument on
   `(iota count in b, normal form of a/b, derivation size)` may work.

3. **`Sub.trans` for JSub** — might require adjusting the measure since
   iotaL/iotaR add new reduction-like steps.

4. **Interaction with Narrowing** — unclear whether narrowing lemma
   holds unchanged.

5. **Completeness vs. algorithmic presentation** — an algorithmic
   decision procedure needs a termination argument on the iota unfolds.
   A "seen set" approach could work: if you encounter `ι.body` on the
   LHS you've already unfolded, you fail (or succeed with some closing
   condition). This is post-soundness work.

### Comparison to previous agent's work

The previous agent's design notes in `Precise.lean` explicitly mentioned
"restrict IotaElim to head-iotas" as a possible way out. This file
implements that idea: `iotaL` IS "IotaElim restricted to head-iotas". By
restricting to the case where the LHS is *literally* `.iota body`, we
eliminate the need for the well-typedness premise — the unfolding
becomes definitional equality, not type-directed elimination.

We go further by adding the symmetric `iotaR`, which handles the
contravariant case that pure `iotaIntro` couldn't.

### Conclusion

**The IotaElim circularity can be broken for head-iotas.** The resulting
system `JSub` handles all the motivating examples (both-sides iotas,
contravariant self-ref, covariant self-ref) using purely structural
steps with no circular premise.

The remaining challenge is **metatheory**: proving transitivity,
narrowing, substitution lemmas, and ultimately soundness for `JSub`.
This exploratory file does NOT attempt those proofs.
-/

end Och.Simple.Iota
