import Och.Syntax
import Och.Eval
import Och.Subtyping
import Och.Monotonicity

open Expr

/-!
# Counterexample: absEval_succeeds_envsub is FALSE as stated

This file demonstrates that `absEval_succeeds_envsub` (Monotonicity.lean) cannot
be proven without an additional well-formedness condition on the environment.

## The counterexample

- Γ₁ = [(y, Type)]
- Γ₂ = [(y, λx:Type. z)]   where z is NOT bound in Γ₂
- e  = y y

EnvSubTrans Γ₂ Γ₁ holds because (λx:Type. z) ⊑ Type (via top).
absEval 2 Γ₁ e = some Type   (Type applied to Type = Type)
absEval 2 Γ₂ e = none        (applying λx:Type. z to (λx:Type. z) tries to
                                evaluate z in env {x ↦ λx:Type.z, y ↦ λx:Type.z},
                                but z is not bound → none)

## Why this matters

The theorem claims: if absEval succeeds in Γ₁ and EnvSubTrans Γ₂ Γ₁, then absEval
succeeds in Γ₂ (same expression). This is false because Γ₂ can contain lambda
values with free variables that are not bound in the env. Such envs never arise
from well-formed evaluation (absEval normalizes lambda bodies, which would fail
if free vars are missing), but EnvSubTrans has no well-formedness requirement.

## The fix

Add a well-formedness precondition on Γ₂. Options:
1. `EnvEvalable fuel Γ₂`: all env values succeed when re-evaluated in Γ₂
2. `EnvClosed Γ₂`: all free vars in env values are bound in Γ₂
3. Restrict to envs produced by absEval (specific to each use site)

Option 3 is recommended: in the actual use site (soundnessC_direct lam case),
Γ₂ comes from readback, which guarantees well-formedness by construction.
-/

def Γ₁_ce : Env := [("y", .type)]
def Γ₂_ce : Env := [("y", .lam "x" .type (.var "z"))]
def e_ce : Expr := .app (.var "y") (.var "y")

-- Verify EnvSubTrans Γ₂ Γ₁ holds (via top: lam ⊑ type)
example : EnvSubTrans Γ₂_ce Γ₁_ce := by
  intro x τ₁ h
  simp only [Γ₁_ce, Env.lookup] at h
  by_cases hx : "y" = x
  · subst hx; simp [Env.lookup] at h; subst h
    exact ⟨.lam "x" .type (.var "z"), by simp [Γ₂_ce, Env.lookup], .step (.top _)⟩
  · simp [Env.lookup, show ¬("y" == x) = true from by simp [BEq.beq, hx]] at h

-- Verify absEval succeeds in Γ₁
example : absEval 2 Γ₁_ce e_ce = some .type := by native_decide

-- Verify absEval FAILS in Γ₂ (the counterexample!)
example : absEval 2 Γ₂_ce e_ce = none := by native_decide

/-!
# Counterexample: absEval_freeVars_covered is FALSE for app-lam case

The theorem claims: if `absEval fuel Γ e = some τ` and `EnvClosed Γ` and
`e.freeVars` covered by `Γ`, then `τ.freeVars` are covered by `Γ`.

This is FALSE because absEval does NOT evaluate domain annotations in lambdas.
When a lambda is returned by absEval, the domain annotation is kept verbatim.
If the lambda was produced inside an extended env (e.g., during beta-reduction),
the domain annotation can reference variables from that extended env that are
NOT in the original env.

## Counterexample

  Γ = []
  e = (λx:Type. λy:x. y) Type
  τ = λy:x. y

  absEval 10 [] e = some (lam "y" (var "x") (var "y"))
  τ.freeVars = ["x"]
  [].lookup "x" = none

  EnvClosed [] is vacuously true ✓
  e.freeVars = [] (x is bound in the outer lambda) ✓
  But τ has "x" free (domain annotation var "x" survives evaluation) ✗

## Root cause

absEval for lam: `some (.lam x dom body')` — dom is UNCHANGED.
When f evaluates to `λx:T. λy:(var x). y` and is applied to Type,
the beta-reduction evaluates the body `λy:(var x). y` in env {x ↦ Type},
producing `λy:(var x). y` (domain `var x` is NOT evaluated).
The domain `var x` refers to the binder `x` which is no longer in scope.

## Impact

absEval_freeVars_covered (Monotonicity.lean) cannot be closed for the
app-lam case. The approach of using freeVars/EnvClosed to fix
absEval_succeeds_envsub is blocked.

Alternative approaches for absEval_succeeds_envsub:
1. Track "evaluable vars" (vars in evaluable positions, excluding domain
   annotations) instead of all freeVars
2. Build absEvalC (closure-based abstract evaluator, SUGGESTIONS.md item 2)
   which avoids the body normalization mismatch entirely
3. Modify absEval to also evaluate domain annotations (but this was
   deliberately avoided — see Eval.lean comment about contravariance)
-/

-- Verify: closed term with no free vars
def e_fv_ce : Expr := .app (.lam "x" .type (.lam "y" (.var "x") (.var "y"))) .type
example : e_fv_ce.freeVars = [] := by native_decide

-- Verify: absEval succeeds
example : absEval 10 ([] : Env) e_fv_ce =
    some (.lam "y" (.var "x") (.var "y")) := by native_decide

-- Verify: result has "x" free
example : (Expr.lam "y" (.var "x") (.var "y")).freeVars = ["x"] := by native_decide

-- Verify: "x" not in empty env
example : ([] : Env).lookup "x" = none := by native_decide
