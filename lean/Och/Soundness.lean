import Och.Syntax
import Och.Eval
import Och.Subtyping

/-!
# Soundness

The main theorem: if abstract evaluation says `e` has type `τ`, and concrete
evaluation produces value `v`, then `v ⊑ τ`.

```
If  Γ ⊢ e ⇝ τ  and  γ ⊨ Γ  and  γ ⊢ e ⇓ v,  then  v ⊑ τ.
```

Agents: this is the primary goal. Everything else exists to support this proof.
You may change any definitions in Syntax, Eval, Subtyping to make this provable,
as long as Tests.lean still passes.
-/

open Expr

/-- A concrete environment is consistent with an abstract environment when
    every binding in the abstract env is a supertype of the concrete value. -/
def EnvConsistent (γ : Env) (Γ : Env) : Prop :=
  ∀ x τ, Γ.lookup x = some τ → ∃ v, γ.lookup x = some v ∧ Subtype' v τ

/-- **Soundness theorem.**

    If abstract evaluation of `e` in `Γ` yields `τ`, and concrete evaluation
    of `e` (with variables resolved from `γ`) yields `v`, and `γ` is consistent
    with `Γ`, then `v ⊑ τ`. -/
theorem soundness
    (Γ : Env) (γ : Env) (e τ v : Expr) (fuel : Nat)
    (h_abs : absEval fuel Γ e = some τ)
    (h_conc : concEval fuel (e) = some v)  -- NOTE: concrete eval needs env too; fix this
    (h_env : EnvConsistent γ Γ)
    : Subtype' v τ := by
  sorry
