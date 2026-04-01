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
