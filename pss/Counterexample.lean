import PSS

/-!
# Counterexample: PSS.Sub [] .top (.lam .top .top)

This file constructs a derivation showing that Top is a subtype of
λ(Top).Top in the wf-free PSS.Sub relation. This demonstrates that
the relation is too permissive.

## The derivation chain

```
  .top
    ≤ .app (.lam (.lam .top .top) (.bvar 0)) .top   [by beta_R]
    ≤ .app (.lam (.lam .top .top) (.lam .top .top)) .top  [by app_cong + bvar + lam]
    ≤ .lam .top .top                                  [by beta_L]
```

## Key insight

beta_R with body = (.bvar 0) introduces an application .app (.lam D (.bvar 0)) .top
whose beta-reduct is .top (since (.bvar 0)[.top] = .top). Crucially, the domain D
can be chosen to be (.lam .top .top) — a lambda type.

In context [D] = [.lam .top .top], the bvar rule promotes (.bvar 0) to D itself
(since D.shift 1 0 = D when D is closed). The lam rule then allows replacing the
body (.bvar 0) with (.lam .top .top), changing the function from
(.lam D (.bvar 0)) to (.lam D (.lam .top .top)).

The app_cong rule propagates this change, and beta_L reduces the new application:
(.lam .top .top)[.top] = .lam .top .top, yielding a lambda on the RHS.

## Why the paper's system avoids this

In the paper's declarative system, DS-TRANS requires the middle term to be
well-formed (Γ ⊢ t wf). The application .app (.lam (.lam .top .top) (.bvar 0)) .top
would need W-APP, which requires .top ≤ (.lam .top .top) — exactly the conclusion
we're trying to derive! So the circularity blocks the derivation.

Our PSS.Sub drops the wf requirement on the middle term of trans, breaking
this circularity and allowing the derivation to go through.
-/

open Expr PSS

-- ============================================================================
-- Step-by-step construction
-- ============================================================================

-- Step 1: beta_R — .top ≤ .app (.lam (.lam .top .top) (.bvar 0)) .top
--
-- beta_R : Sub Γ (body.subst 0 arg) (.app (.lam dom body) arg)
-- With dom = (.lam .top .top), body = (.bvar 0), arg = .top:
-- (.bvar 0).subst 0 .top = .top ✓
private def step1 : PSS.Sub [] .top (.app (.lam (.lam .top .top) (.bvar 0)) .top) :=
  @PSS.Sub.beta_R [] (.lam .top .top) (.bvar 0) .top

-- Step 2: bvar rule in context [.lam .top .top]
--
-- (.bvar 0) ≤ (.lam .top .top).shift 1 0 = (.lam .top .top)
private def step2 : PSS.Sub [.lam .top .top] (.bvar 0) (.lam .top .top) :=
  @PSS.Sub.bvar [.lam .top .top] 0 (.lam .top .top) rfl

-- Step 3: lam rule — change body from (.bvar 0) to (.lam .top .top)
private def step3 : PSS.Sub [] (.lam (.lam .top .top) (.bvar 0))
                                (.lam (.lam .top .top) (.lam .top .top)) :=
  .lam (.refl _) (.refl _) step2

-- Step 4: app_cong — propagate the function change to the application
private def step4 : PSS.Sub [] (.app (.lam (.lam .top .top) (.bvar 0)) .top)
                                (.app (.lam (.lam .top .top) (.lam .top .top)) .top) :=
  .app_cong step3 (.refl _) (.refl _)

-- Step 5: beta_L — reduce the application
--
-- (.lam .top .top).subst 0 .top = .lam .top .top ✓
private def step5 : PSS.Sub [] (.app (.lam (.lam .top .top) (.lam .top .top)) .top)
                                (.lam .top .top) :=
  @PSS.Sub.beta_L [] (.lam .top .top) (.lam .top .top) .top

-- ============================================================================
-- THE COUNTEREXAMPLE
-- ============================================================================

/-- **Counterexample**: Top ≤ λ(Top).Top is derivable in the wf-free relation.

    This should NOT be derivable in a sound subtyping relation, because
    Top is not a function — applying Top to an argument gets stuck. -/
theorem top_sub_lam_top : PSS.Sub [] .top (.lam .top .top) :=
  .trans step1 (.trans step4 step5)

-- ============================================================================
-- Consequences
-- ============================================================================

/-- Corollary: Top ≡ λ(Top).Top (they are equivalent in the relation). -/
theorem top_equiv_lam_top : PSS.Sub [] .top (.lam .top .top)
                          ∧ PSS.Sub [] (.lam .top .top) .top :=
  ⟨top_sub_lam_top, .top _⟩

/-- (.app .top .top) evaluates to a stuck (non-value) result.
    `concEval 100 (.app .top .top)` returns `Outcome.ok (.app .top .top)` —
    .top is not a lambda, so application gets stuck and returns the unevaluated app.
    Yet our relation says `Sub [] .top (.lam .top .top)`, meaning .top is a function type
    and .app .top .top should be well-formed. This is the unsoundness. -/
example : ¬ (Expr.app .top .top).IsValue := by decide
