import Och.Syntax
import Och.Eval
import Och.Subtyping

/-!
# Monotonicity

Narrowing the abstract environment narrows (or preserves) the abstract result.

```
If  Γ₂ ⊑ Γ₁  then  (Γ₁ ⊢ e ⇝ τ₁)  and  (Γ₂ ⊢ e ⇝ τ₂)  implies  τ₂ ⊑ τ₁.
```

## Proof status

The proof proceeds by induction on fuel and case analysis on the expression.
Cases var, lam, type, asc are complete. The app case has two sub-cases:
- **Stuck application** (neither eval produces a lambda): proven via `app_cong`.
- **Beta-reduction** (at least one eval produces a lambda): requires a
  substitution monotonicity lemma and is left as sorry.

### The hard part: application after beta-reduction

When `f` evaluates to different lambdas in Γ₁ and Γ₂ (because normalization
under binders produces different bodies), the substituted expressions
`body₁.subst x v₁` and `body₂.subst x v₂` are different. The IH only
covers the SAME expression in different environments, so it doesn't apply.

A proof would need one of:
1. A substitution monotonicity lemma relating `absEval Γ₂ (body₂.subst x v₂)`
   and `absEval Γ₁ (body₁.subst x v₁)` given `Subtype' body₂ body₁` and
   `Subtype' v₂ v₁`.
2. A logical relations / step-indexed argument.
3. An environment-based (closure) evaluator where the same source body is
   evaluated in related extended environments.

### Known issue: dependent domains

There is a deeper issue: when a lambda's domain depends on a narrowed
variable, the result has a narrower domain, but function subtyping is
CONTRAVARIANT in the domain. This means `λx:3. x ⊑ λx:Nat. x` fails
even though 3 ⊑ Nat. This is a fundamental tension between dependent
types and monotonicity (related to Ochre's Prop 5.2.9). The spec claims
monotonicity holds, but this specific pattern may require a different
subtyping rule or evaluation strategy for dependent domains.
-/

open Expr

/-- Environment subtyping: Γ₂ ⊑ Γ₁ pointwise. -/
def EnvSub (Γ₂ Γ₁ : Env) : Prop :=
  ∀ x τ₁, Γ₁.lookup x = some τ₁ → ∃ τ₂, Γ₂.lookup x = some τ₂ ∧ Subtype' τ₂ τ₁

/-- Extending both environments with the same binding preserves EnvSub. -/
theorem envSub_extend {Γ₂ Γ₁ : Env} (h : EnvSub Γ₂ Γ₁) (x : Name) (v : Expr) :
    EnvSub ((x, v) :: Γ₂) ((x, v) :: Γ₁) := by
  intro y τ₁ h_lookup
  simp only [Env.lookup] at h_lookup ⊢
  split at h_lookup <;> split
  · -- y == x in both: same binding
    rename_i h_eq _
    cases h_lookup
    exact ⟨v, rfl, Subtype'.refl v⟩
  · -- y == x in Γ₁ but not Γ₂: contradiction (same name check)
    rename_i h1 h2
    exact absurd h1 h2
  · -- y ≠ x in Γ₁ but == x in Γ₂: contradiction
    rename_i h1 h2
    exact absurd h2 h1
  · -- y ≠ x: from the tail
    have ⟨τ₂, h_l2, h_sub⟩ := h y τ₁ h_lookup
    exact ⟨τ₂, h_l2, h_sub⟩

/-- **Monotonicity theorem.**

    If Γ₂ is more precise than Γ₁, and abstract evaluation succeeds in both,
    then the result under Γ₂ is more precise than under Γ₁.

    See module docstring for proof status and known blockers. -/
theorem monotonicity
    (Γ₁ Γ₂ : Env) (e τ₁ τ₂ : Expr) (fuel : Nat)
    (h_env : EnvSub Γ₂ Γ₁)
    (h_abs₁ : absEval fuel Γ₁ e = some τ₁)
    (h_abs₂ : absEval fuel Γ₂ e = some τ₂)
    : Subtype' τ₂ τ₁ := by
  induction fuel generalizing Γ₁ Γ₂ e τ₁ τ₂ with
  | zero => simp [absEval] at h_abs₁
  | succ n ih =>
    cases e with
    | var x =>
      simp [absEval] at h_abs₁ h_abs₂
      have ⟨τ₂', h_l2, h_sub⟩ := h_env x τ₁ h_abs₁
      rw [h_l2] at h_abs₂
      cases h_abs₂
      exact h_sub
    | lam x dom body =>
      simp only [absEval] at h_abs₁ h_abs₂
      -- Destructure the match on absEval of the body
      cases h1 : absEval n ((x, .var x) :: Γ₁) body with
      | none => simp [h1] at h_abs₁
      | some body₁ =>
        simp [h1] at h_abs₁
        cases h2 : absEval n ((x, .var x) :: Γ₂) body with
        | none => simp [h2] at h_abs₂
        | some body₂ =>
          simp [h2] at h_abs₂
          rw [← h_abs₁, ← h_abs₂]
          exact Subtype'.lam_body (ih _ _ body _ _ (envSub_extend h_env x (.var x)) h1 h2)
    | type =>
      simp [absEval] at h_abs₁ h_abs₂
      rw [← h_abs₁, ← h_abs₂]
      exact Subtype'.refl .type
    | asc term ty =>
      simp only [absEval] at h_abs₁ h_abs₂
      exact ih _ _ ty _ _ h_env h_abs₁ h_abs₂
    | app f a =>
      -- Unfold absEval for app in both envs
      simp only [absEval] at h_abs₁ h_abs₂
      -- We need to case-split on whether f and a evaluate successfully,
      -- and whether f evaluates to a lambda (beta) or not (stuck).
      cases hf₁ : absEval n Γ₁ f with
      | none => simp [hf₁] at h_abs₁
      | some f₁ =>
        cases ha₁ : absEval n Γ₁ a with
        | none => simp [hf₁, ha₁] at h_abs₁
        | some a₁ =>
          cases hf₂ : absEval n Γ₂ f with
          | none => simp [hf₂] at h_abs₂
          | some f₂ =>
            cases ha₂ : absEval n Γ₂ a with
            | none => simp [hf₂, ha₂] at h_abs₂
            | some a₂ =>
              -- We have f₁, a₁, f₂, a₂. By IH: f₂ ⊑ f₁ and a₂ ⊑ a₁.
              have hf_sub := ih Γ₁ Γ₂ f f₁ f₂ h_env hf₁ hf₂
              have ha_sub := ih Γ₁ Γ₂ a a₁ a₂ h_env ha₁ ha₂
              -- Case-split on whether f₁ and f₂ are lambdas
              -- by rewriting h_abs₁/h_abs₂ with the known values of f/a evals
              rw [hf₁, ha₁] at h_abs₁
              rw [hf₂, ha₂] at h_abs₂
              cases f₁ with
              | lam x₁ dom₁ body₁ =>
                cases f₂ with
                | lam x₂ dom₂ body₂ =>
                  -- Both lambdas: beta-reduction in both envs.
                  -- Requires substitution monotonicity lemma.
                  sorry
                | _ =>
                  -- f₁ lambda, f₂ not. Requires additional analysis.
                  sorry
              | _ =>
                cases f₂ with
                | lam x₂ dom₂ body₂ =>
                  -- f₁ not lambda, f₂ lambda. Requires additional rules.
                  sorry
                | _ =>
                  -- Both stuck: τ₁ = app f₁ a₁, τ₂ = app f₂ a₂
                  simp at h_abs₁ h_abs₂
                  rw [← h_abs₁, ← h_abs₂]
                  exact Subtype'.app_cong hf_sub ha_sub
