import Och.Simple.Syntax
import Och.Simple.Subtype
import Och.Simple.Properties

/-!
# Challenge: `dtrue ⊑ Bool` via split ι / fix (VALUE-SUB attempt)

This file explores the whiteboard target under the **value-substitution**
iotaIntro rule:

```
iotaIntro:  a ⊑ ι A. b   ←   a ⊑ A   ∧   a ⊑ b[0 := a]
```

(Contrast: the prior "fixed-self" attempt substituted the iota itself.
See `docs/research/iota-fix-split.md` for the analysis of why fixed-self
is transitively safe but does not yield true self-types.)

```
cBool = λA:⊤. A → A → A
true  = λA:⊤. λt:A. λf:A. t
false = λA:⊤. λt:A. λf:A. f
Bool  = ι self:cBool. λP:(cBool → ⊤). P true → P false → P self
dtrue = true
```

Goal: `Sub [] dtrue Bool`.

## Status: STILL NOT closable under value-sub.

The obstruction is unchanged from the fixed-self attempt. The
contravariant wall surfaces BEFORE the `P self` self-reference is
decomposed, and value-sub only affects the deepest `P self` position.

### What value-sub changes (and what it doesn't)

After `Sub.iotaIntro`, the body leg becomes
`dtrue ⊑ BoolBody.subst 0 dtrue`, where `BoolBody.subst 0 dtrue`
substitutes `dtrue` for the self-var at every depth (shifted
appropriately). Crucially:

* The `P true` and `P false` domains use `var 0` / `var 1` which refer
  to `P` (the first lambda binder), NOT to self.
* Only the body position `app (var 2) (var 3)` contains a self-ref
  (var 3 shifts to self = 0 at the iota level). After `subst 0 dtrue`,
  this becomes `app (var 2) dtrue`.

So `BoolBody.subst 0 dtrue =
  λP:cBoolToTop. λ(app P cTrue). λ(app P cFalse). (app P dtrue)`
(modulo de Bruijn indices).

Checking `dtrue ⊑ BoolBody.subst 0 dtrue` by [Lam] decomposition
reaches, at depth 2, the contravariant domain check
`app (var 0) cTrue ⊑ var 0`, where `var 0 = cBoolToTop = cBool→⊤`.
[App] decomposition yields the residual `⊤ ⊑ cBool→⊤`, which is
false under the 7 base rules.

**This is the same [App] wall the fixed-self attempt hit.** Value-sub
does not help because the wall is not on a self-position.

## What we prove here

* `cTrue_sub_cBool`: the standard Church-Bool subtyping.
* `cTrue_sub_iota_trivial`: `cTrue ⊑ ι ⊤. cBool` — a no-self iota
  where the body leg becomes `cTrue ⊑ cBool.subst 0 cTrue = cBool`.
* `dtrue_sub_Bool`: sorry'd with a detailed diagnosis at the exact
  obstruction point.

## Why the prior (fixed-self) and this (value-sub) attempts converge

Both rules require discharging a body-leg obligation that, for the
whiteboard encoding, is identical modulo which term fills a single
position (var 3 / self). Both derivations hit the [App] wall on
the preceding `app P cTrue ⊑ cBool→⊤` check, which has nothing to do
with self. Thus:

* fixed-self: cut-measure safe, trans closes, but wall at [App].
* value-sub: cut-measure broken for general trans(iotaIntro, iotaIntro),
  body leg has value-sub flavour — but still wall at [App].

The conclusion stands: to close `dtrue ⊑ Bool`, we need a rule that
unblocks the domain check `app P cTrue ⊑ cBool→⊤`, not a change to
the iota substitution semantics.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Och.Simple.Challenge

open Och.Simple Expr

-- ============================================================
-- Definitions (closed terms)
-- ============================================================

/-- `cBool = λt:⊤. λa:t. λb:t. t` (Church-encoded Bool type). -/
def cBool : Expr := .lam .top (.lam (.var 0) (.lam (.var 1) (.var 2)))

/-- `true = λt:⊤. λa:t. λb:t. a` (Church true). -/
def cTrue : Expr := .lam .top (.lam (.var 0) (.lam (.var 1) (.var 1)))

/-- `false = λt:⊤. λa:t. λb:t. b` (Church false). -/
def cFalse : Expr := .lam .top (.lam (.var 0) (.lam (.var 1) (.var 0)))

/-- `cBool → ⊤ = λ_:cBool. ⊤`. -/
def cBoolToTop : Expr := .lam cBool .top

/-- `Bool = ι self:cBool. λP:(cBool→⊤). P true → P false → P self` -/
def Bool : Expr :=
  .iota cBool
    (.lam cBoolToTop
      (.lam (.app (.var 0) cTrue)
        (.lam (.app (.var 1) cFalse)
          (.app (.var 2) (.var 3)))))

/-- `dtrue = true`. -/
def dtrue : Expr := cTrue

-- ============================================================
-- Step 1: `Sub [] cTrue cBool`
-- ============================================================

/-- `Sub [] cTrue cBool`. Standard Church Bool argument. -/
noncomputable def cTrue_sub_cBool : Sub [] cTrue cBool := by
  apply Sub.lam [] .top .top (.lam (.var 0) (.lam (.var 1) (.var 1)))
    (.lam (.var 0) (.lam (.var 1) (.var 2)))
  · exact Sub.refl _ _
  apply Sub.lam _ (.var 0) (.var 0) _ _
  · exact Sub.refl _ _
  apply Sub.lam _ (.var 1) (.var 1) _ _
  · exact Sub.refl _ _
  apply Sub.var _ 1 (.var 2) (.var 2)
  · rfl
  · exact Sub.refl _ _

-- ============================================================
-- Simpler theorem: `Sub [] cTrue (ι ⊤. cBool)`
-- ============================================================

/-- Trivial iota where body is closed (doesn't use self).
    `Sub [] cTrue (ι ⊤. cBool)`. Via value-sub [IotaIntro]:
    - `cTrue ⊑ ⊤`  (by [Top])
    - `cTrue ⊑ cBool.subst 0 cTrue = cBool` (since cBool is closed). -/
noncomputable def cTrue_sub_iota_trivial : Sub [] cTrue (.iota .top cBool) := by
  apply Sub.iotaIntro [] cTrue .top cBool
  · exact Sub.top _ _
  · -- goal: Sub [] cTrue (cBool.subst 0 cTrue)
    -- cBool is closed (no free vars), so subst-any-value returns cBool.
    show Sub [] cTrue (cBool.subst 0 cTrue)
    have : cBool.subst 0 cTrue = cBool := by rfl
    rw [this]
    exact cTrue_sub_cBool

-- ============================================================
-- The target theorem: `Sub [] dtrue Bool` — NOT PROVABLE
-- ============================================================

/-- The target theorem under value-sub iotaIntro.

    After `Sub.iotaIntro` the body leg becomes

        dtrue ⊑ BoolBody.subst 0 dtrue

    where (computing the substitution with `dtrue` = cTrue, a closed term)

        BoolBody.subst 0 dtrue =
          .lam cBoolToTop
            (.lam (app (var 0) cTrue)
              (.lam (app (var 1) cFalse)
                (app (var 2) dtrue)))

    (cBoolToTop/cTrue/cFalse are closed so shifts/subs leave them alone;
    only the deepest `var 3` — the iota self-ref at depth 3 — is
    replaced by `dtrue` shifted by 3, which equals `dtrue` since it's
    closed.)

    [Lam] decomposes the outermost lambda: contra domain `cBoolToTop ⊑ .top`
    closes by [Top]; body goes under `[cBoolToTop]`.

    Second [Lam]: contra domain `app (var 0) cTrue ⊑ var 0` in context
    `[cBoolToTop]`. Here `var 0 = cBoolToTop = .lam cBool .top`. Via
    [App] on LHS:

      * `var 0 ⊑ .lam D R` via [Var] gives `D = cBool`, `R = .top`.
      * `cTrue ⊑ cBool` — ok.
      * `.top ⊑ var 0` (= `.top ⊑ cBoolToTop = cBool→⊤`) — FALSE.

    Value-sub does NOT help: this wall is in the contravariant domain
    check of the second lambda, where no self-reference participates.
    Value-sub only affects the body at depth 3 (`P self`).

    We close everything we can and sorry at the exact obstruction. -/
noncomputable def dtrue_sub_Bool : Sub [] dtrue Bool := by
  -- Step 1: [IotaIntro] (value-sub). Ann leg = cBool check. Body leg below.
  apply Sub.iotaIntro [] dtrue cBool
    (.lam cBoolToTop
      (.lam (.app (.var 0) cTrue)
        (.lam (.app (.var 1) cFalse)
          (.app (.var 2) (.var 3)))))
  · -- Annotation leg: dtrue ⊑ cBool.
    exact cTrue_sub_cBool
  · -- Body leg: dtrue ⊑ BoolBody.subst 0 dtrue.
    -- Compute what BoolBody.subst 0 dtrue reduces to.
    show Sub [] dtrue
      ((Expr.lam cBoolToTop
          (.lam (.app (.var 0) cTrue)
            (.lam (.app (.var 1) cFalse)
              (.app (.var 2) (.var 3))))).subst 0 dtrue)
    -- By definitional reduction on subst (cBoolToTop/cTrue/cFalse/dtrue
    -- are all closed; their shifts are identity), the RHS evaluates to:
    --   .lam cBoolToTop (.lam (app (var 0) cTrue) (.lam (app (var 1) cFalse) (app (var 2) dtrue)))
    have hreduce : (Expr.lam cBoolToTop
        (.lam (.app (.var 0) cTrue)
          (.lam (.app (.var 1) cFalse)
            (.app (.var 2) (.var 3))))).subst 0 dtrue =
        (.lam cBoolToTop
          (.lam (.app (.var 0) cTrue)
            (.lam (.app (.var 1) cFalse)
              (.app (.var 2) dtrue)))) := by rfl
    rw [hreduce]
    -- Now: dtrue ⊑ .lam cBoolToTop (.lam (app 0 cTrue) (.lam (app 1 cFalse) (app 2 dtrue)))
    -- dtrue = cTrue = .lam .top (.lam (.var 0) (.lam (.var 1) (.var 1)))
    -- First [Lam]: contra cBoolToTop ⊑ .top  (Top); body under cBoolToTop.
    apply Sub.lam [] .top cBoolToTop
      (.lam (.var 0) (.lam (.var 1) (.var 1)))
      (.lam (.app (.var 0) cTrue) (.lam (.app (.var 1) cFalse) (.app (.var 2) dtrue)))
    · exact Sub.top _ _
    -- Second [Lam]: contra `app (var 0) cTrue ⊑ var 0` in [cBoolToTop].
    apply Sub.lam [cBoolToTop] (.var 0) (.app (.var 0) cTrue)
      (.lam (.var 1) (.var 1))
      (.lam (.app (.var 1) cFalse) (.app (.var 2) dtrue))
    · -- *** OBSTRUCTION ***
      -- Goal: Sub [cBoolToTop] (.app (.var 0) cTrue) (.var 0).
      -- Via [App] on LHS: need (var 0) ⊑ (.lam D R), cTrue ⊑ D, R.subst 0 cTrue ⊑ var 0.
      -- [Var] gives (var 0) ⊑ cBoolToTop (shifted = itself) = .lam cBool .top.
      -- So D = cBool, R = .top. Then R.subst 0 cTrue = .top.
      -- Final: .top ⊑ var 0 = .top ⊑ cBoolToTop = .top ⊑ (.lam cBool .top).
      -- [Top] says a ⊑ top, not top ⊑ arrow. No base rule closes this.
      -- Value-sub doesn't help: the self-ref (var 3) is at a deeper
      -- position, not in this domain check.
      sorry
    -- (The body-leg sub-steps would close if we could get past this;
    -- in particular at depth 3, after value-sub, the LHS and RHS
    -- positions under `app P cTrue` / `app P cFalse` decompositions
    -- would rely on the same obstruction in a different spot, plus a
    -- reflexive match at `app (var 2) dtrue` since both sides there
    -- would unify to cTrue / dtrue. But we never reach that point.)
    sorry

end Och.Simple.Challenge
