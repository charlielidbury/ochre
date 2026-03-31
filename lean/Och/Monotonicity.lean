import Och.Syntax
import Och.Eval
import Och.Subtyping

/-!
# Monotonicity

Narrowing the abstract environment narrows (or preserves) the abstract result.

```
If  Γ₂ ⊑ Γ₁  then  (Γ₁ ⊢ e ⇝ τ₁)  and  (Γ₂ ⊢ e ⇝ τ₂)  implies  τ₂ ⊑ τ₁.
```

This is the property that makes strong mutation sound in Ochre: after `x = 5`,
narrowing x's type from Nat to 5 must not break any previously-checked types.

Agents: this is the second primary goal, and historically the harder one.
The counterexample from Ochre's Proposition 5.2.9 was a monotonicity failure.
-/

open Expr

/-- Environment subtyping: Γ₂ ⊑ Γ₁ pointwise. -/
def EnvSub (Γ₂ Γ₁ : Env) : Prop :=
  ∀ x τ₁, Γ₁.lookup x = some τ₁ → ∃ τ₂, Γ₂.lookup x = some τ₂ ∧ Subtype' τ₂ τ₁

/-- **Monotonicity theorem.**

    If Γ₂ is more precise than Γ₁, and abstract evaluation succeeds in both,
    then the result under Γ₂ is more precise than under Γ₁. -/
theorem monotonicity
    (Γ₁ Γ₂ : Env) (e τ₁ τ₂ : Expr) (fuel : Nat)
    (h_env : EnvSub Γ₂ Γ₁)
    (h_abs₁ : absEval fuel Γ₁ e = some τ₁)
    (h_abs₂ : absEval fuel Γ₂ e = some τ₂)
    : Subtype' τ₂ τ₁ := by
  sorry
