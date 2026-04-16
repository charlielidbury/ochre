import Och.Simple.Syntax
import Och.Simple.Subtype
import Och.Simple.Properties

/-!
# Challenge: `dtrue ⊑ Bool` via split ι / fix

This file explores the whiteboard target:

```
cBool = λA:⊤. A → A → A
true  = λA:⊤. λt:A. λf:A. t
false = λA:⊤. λt:A. λf:A. f
Bool  = ι self:cBool. λP:(cBool → ⊤). P true → P false → P self
dtrue = true
```

Goal: `Sub [] dtrue Bool`.

## Status: the target theorem is NOT closable in Simple Och + ι/fix
  alone.

The obstruction is NOT related to ι/fix or self-types. It is a
general [App] obstruction: the contravariant-position
`(P true) ⊑ cBool→⊤` that appears during [Lam] decomposition of
`dtrue` against Bool's body requires showing

    (app P true) ⊑ (cBool→⊤)

where `P : cBool → ⊤` in context. [App] decomposition yields a
residual `⊤ ⊑ (cBool→⊤)`, which is false (⊤ is top, not bottom).

Informally, applying a function `P : cBool→⊤` to `true` "should"
beta-reduce to `⊤`, giving `⊤ ⊑ cBool→⊤` — still false. The issue
is that `⊤` cannot be narrowed to a specific function type.

This obstruction would block any structurally-minded inductive
subtype system. It would require a `[BetaL]` / `[DefEq]` rule (to
beta-reduce on the LHS) PLUS a weakening rule that allows widening
from a specific type to ⊤ — but that's already [Top], which goes
the wrong way.

The conclusion is that the ι/fix split IS a clean design, but by
itself does NOT enable this particular theorem. See
`docs/research/iota-fix-split.md` for the detailed writeup.

## What this file demonstrates

We prove a related but simpler theorem:

    `Sub [] true (.iota cBool (var 0))`

i.e., `true ⊑ ι self:cBool. self`. This is the trivial self-type
where the body is just `self`. After [IotaIntro] unfolding:

    true ⊑ cBool          (covariant ann, standard Church Bool proof)
    true ⊑ (var 0).subst 0 (.iota cBool (var 0)) = ι cBool. (var 0)

The second goal cycles to the original goal, so this is still
not closable inductively. But it isolates the cycle to the ι
rule specifically.

We ALSO prove:

    `Sub [] true (.iota ⊤ cBool)`

i.e., `true ⊑ ι self:⊤. cBool`. Here the body is `cBool` (self
is never used). After [IotaIntro]:

    true ⊑ ⊤              (trivial [Top])
    true ⊑ cBool.subst 0 (.iota ⊤ cBool) = cBool  (since cBool closed)

Both legs close. This demonstrates the iotaIntro rule works on
trivial "non-self-referential" iotas.
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
    `Sub [] cTrue (ι ⊤. cBool)`. Via [IotaIntro]:
    - `cTrue ⊑ ⊤`  (by [Top])
    - `cTrue ⊑ cBool.subst 0 (ι ⊤. cBool) = cBool` (since cBool is closed). -/
noncomputable def cTrue_sub_iota_trivial : Sub [] cTrue (.iota .top cBool) := by
  apply Sub.iotaIntro [] cTrue .top cBool
  · exact Sub.top _ _
  · -- goal: Sub [] cTrue (cBool.subst 0 (.iota .top cBool))
    -- cBool is closed, so subst is identity (well, need subst to leave cBool alone)
    -- cBool has no bvar 0 at top, but has bvar 0,1,2 inside its lambdas
    -- Since we subst at target 0 with the iota as replacement, the inner bvar 0's
    -- are at different depths. But cBool is closed — all its bvars are bound by
    -- its own lambdas. Let me compute...
    -- cBool = lam top (lam (var 0) (lam (var 1) (var 2)))
    -- subst 0 X walks in. First lam: subst 0 X on top is top. Body: subst 1 X_shifted.
    -- Inside the outer lam, under depth 1, we subst 1. But cBool's body has var 0
    -- (referring to the outer lam binding) and var 1/2 referring higher.
    -- Need to compute cBool.subst 0 X where X is closed. Result should = cBool
    -- (since cBool's bvars are all captured by its own lambdas, no free bvar 0).
    show Sub [] cTrue (cBool.subst 0 (.iota .top cBool))
    -- Lean should compute this via rfl — if not, we use a helper.
    -- Use subst_shift_cancel: if cBool has no free vars at 0, subst leaves it alone.
    -- Actually cBool as written is `.lam top (.lam (var 0) (.lam (var 1) (var 2)))`.
    -- When we subst 0 X, we get:
    --   .lam (top.subst 0 X) ((.lam (var 0) (.lam (var 1) (var 2))).subst 1 X_s)
    -- = .lam top (.lam ((var 0).subst 1 X_s) ((.lam (var 1) (var 2)).subst 2 X_ss))
    -- var 0.subst 1 X_s: 0 < 1, so stays var 0.
    -- (lam (var 1) (var 2)).subst 2 X_ss = .lam ((var 1).subst 2 X_ss) ((var 2).subst 3 ...)
    -- var 1 < 2, stays var 1. var 2 < 3, stays var 2.
    -- So the whole thing equals cBool.
    have : cBool.subst 0 (.iota .top cBool) = cBool := by rfl
    rw [this]
    exact cTrue_sub_cBool

-- ============================================================
-- The target theorem: `Sub [] dtrue Bool` — NOT PROVABLE
-- ============================================================

/-- The target theorem. NOT PROVABLE with just [IotaIntro] + the base 7 rules.

    The body leg requires closing the subtyping goal

        cTrue ⊑ BoolBody.subst 0 Bool

    Under outermost [Lam], this reduces (under `cBoolToTop :: []`) to

        cTrue's 2nd-lambda body ⊑ RHS's 2nd-lambda body

    which has a contravariant domain check of the form

        app (var 0) cTrue ⊑ (var 0)

    in context `[cBoolToTop]`. Under [App] on LHS:

        (var 0) ⊑ λD.R  ∧  cTrue ⊑ D  ∧  R[0 := cTrue] ⊑ (var 0)

    With [Var] giving (var 0) ⊑ cBoolToTop = (λ_:cBool. ⊤), we get
    D = cBool, R = ⊤, and then

        ⊤ ⊑ (var 0) = cBoolToTop = cBool → ⊤

    which is FALSE (Top is top, not bottom).

    This is NOT a self-type issue — [IotaIntro] substitutes correctly.
    The issue is a missing "Beta" / "DefEq" rule that would let us
    reduce `(λ_:cBool. ⊤) cTrue` to `⊤` BEFORE the [Lam] check, so the
    contravariant domain check becomes `⊤ ⊑ cBool→⊤` (still false via
    structural rules, but potentially handleable by a special rule).

    We leave this as a sorry documenting the gap. -/
noncomputable def dtrue_sub_Bool : Sub [] dtrue Bool := by
  sorry

end Och.Simple.Challenge
