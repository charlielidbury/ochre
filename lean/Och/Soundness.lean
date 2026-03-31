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

## Proof structure

concEval and absEval are structurally identical except at ascription:
- absEval: `(e : τ)` → evaluate τ (take the type)
- concEval: `(e : τ)` → evaluate e (take the value)

For all other cases (var, lam, type, app), the evaluators do the same thing
with the same environments, so soundness follows by induction.

The ascription case requires a **well-typedness** hypothesis: that the
abstract type of the term `e` is a subtype of the annotation `τ`. Without
this, an ascription like `(true : Nat)` would be accepted by absEval
(returning Nat) while concEval produces true, and true ⊑ Nat is false.
-/

open Expr

/-- A concrete environment is consistent with an abstract environment when
    every binding in the abstract env is a supertype of the concrete value. -/
def EnvConsistent (γ : Env) (Γ : Env) : Prop :=
  ∀ x τ, Γ.lookup x = some τ → ∃ v, γ.lookup x = some v ∧ Subtype' v τ

/-- Well-typedness: all ascriptions encountered during evaluation are sound.

    This is defined mutually with the evaluation structure. For an ascription
    `(term : ty)`, well-typedness requires:
    1. Both term and ty evaluate successfully
    2. The abstract type of term is ⊑ the abstract type of ty
    3. The subterms are themselves well-typed

    This ensures the evaluator never encounters an unsound ascription. -/
def WellTyped (fuel : Nat) (Γ : Env) (e : Expr) : Prop :=
  match fuel with
  | 0 => True  -- vacuously true: absEval returns none at fuel 0
  | fuel + 1 =>
    match e with
    | .var _ => True
    | .lam x _ body => WellTyped fuel ((x, .var x) :: Γ) body
    | .type => True
    | .asc term ty =>
        WellTyped fuel Γ term ∧ WellTyped fuel Γ ty ∧
        ∃ σ τ', absEval fuel Γ term = some σ ∧
                absEval fuel Γ ty = some τ' ∧
                Subtype' σ τ'
    | .app f a =>
        WellTyped fuel Γ f ∧ WellTyped fuel Γ a ∧
        -- If f evaluates to a lambda, the substituted body must also be well-typed
        match absEval fuel Γ f, absEval fuel Γ a with
        | some (.lam x _ body), some aVal => WellTyped fuel Γ (body.subst x aVal)
        | _, _ => True

/-- **Soundness theorem.**

    If abstract evaluation of `e` in `Γ` yields `τ`, and concrete evaluation
    of `e` in `γ` yields `v`, and `γ` is consistent with `Γ` (every concrete
    value is ⊑ the abstract type), and `e` is well-typed (all ascriptions are
    sound), then `v ⊑ τ`.

    The proof proceeds by induction on fuel. For all cases except ascription,
    concEval and absEval are identical, so v = τ and we get Subtype'.refl.
    For ascription, well-typedness provides the bridge: v ⊑ σ (by IH on term)
    and σ ⊑ τ (by well-typedness), so v ⊑ τ by transitivity. -/
theorem soundness
    (Γ : Env) (γ : Env) (e τ v : Expr) (fuel : Nat)
    (h_abs : absEval fuel Γ e = some τ)
    (h_conc : concEval fuel γ e = some v)
    (h_env : EnvConsistent γ Γ)
    (h_wt : WellTyped fuel Γ e)
    : Subtype' v τ := by
  induction fuel generalizing Γ γ e τ v with
  | zero => simp [absEval] at h_abs
  | succ n ih =>
    cases e with
    | var x =>
      simp [absEval, concEval] at h_abs h_conc
      have ⟨val, h_lv, h_sub⟩ := h_env x τ h_abs
      rw [h_lv] at h_conc
      cases h_conc
      exact h_sub
    | type =>
      simp [absEval, concEval] at h_abs h_conc
      rw [← h_abs, ← h_conc]
      exact Subtype'.refl .type
    | lam x dom body =>
      simp only [absEval, concEval] at h_abs h_conc
      -- Both evaluate body under (x, var x) :: env
      cases hb_abs : absEval n ((x, .var x) :: Γ) body with
      | none => simp [hb_abs] at h_abs
      | some body_a =>
        simp [hb_abs] at h_abs
        cases hb_conc : concEval n ((x, .var x) :: γ) body with
        | none => simp [hb_conc] at h_conc
        | some body_c =>
          simp [hb_conc] at h_conc
          rw [← h_abs, ← h_conc]
          -- Need: lam x dom body_c ⊑ lam x dom body_a
          -- By IH on body with extended envs
          have h_wt' : WellTyped n ((x, .var x) :: Γ) body := h_wt
          have h_env' : EnvConsistent ((x, .var x) :: γ) ((x, .var x) :: Γ) := by
            intro y ty h_lookup
            simp only [Env.lookup] at h_lookup ⊢
            split at h_lookup <;> split
            · -- y == x in both
              cases h_lookup
              exact ⟨.var x, rfl, Subtype'.refl _⟩
            · rename_i h1 h2; exact absurd h1 h2
            · rename_i h1 h2; exact absurd h2 h1
            · exact h_env y ty h_lookup
          exact Subtype'.lam_body (ih _ _ body _ _ hb_abs hb_conc h_env' h_wt')
    | asc term ty =>
      simp only [absEval, concEval] at h_abs h_conc
      -- h_abs: absEval n Γ ty = some τ
      -- h_conc: concEval n γ term = some v
      have ⟨h_wt_term, _, σ, τ', h_abs_term, h_abs_ty, h_sub_wt⟩ := h_wt
      -- τ' = τ since both come from absEval n Γ ty
      rw [h_abs] at h_abs_ty; cases h_abs_ty
      -- By IH on term: v ⊑ σ
      have h_vs : Subtype' v σ := ih Γ γ term σ v h_abs_term h_conc h_env h_wt_term
      -- By well-typedness: σ ⊑ τ. By transitivity: v ⊑ τ.
      exact Subtype'.trans h_vs h_sub_wt
    | app f a =>
      simp only [absEval, concEval] at h_abs h_conc
      -- Both evaluators: eval f, eval a, then beta-reduce or stuck
      cases hf_abs : absEval n Γ f with
      | none => simp [hf_abs] at h_abs
      | some f_a =>
        cases ha_abs : absEval n Γ a with
        | none => simp [hf_abs, ha_abs] at h_abs
        | some a_a =>
          cases hf_conc : concEval n γ f with
          | none => simp [hf_conc] at h_conc
          | some f_c =>
            cases ha_conc : concEval n γ a with
            | none => simp [hf_conc, ha_conc] at h_conc
            | some a_c =>
              -- By IH: f_c ⊑ f_a and a_c ⊑ a_a
              have h_wt_f : WellTyped n Γ f := h_wt.1
              have h_wt_a : WellTyped n Γ a := h_wt.2.1
              have hf_sub := ih Γ γ f f_a f_c hf_abs hf_conc h_env h_wt_f
              have ha_sub := ih Γ γ a a_a a_c ha_abs ha_conc h_env h_wt_a
              -- Case-split on whether f_a and f_c are lambdas
              rw [hf_abs, ha_abs] at h_abs
              rw [hf_conc, ha_conc] at h_conc
              cases f_a with
              | lam x_a dom_a body_a =>
                cases f_c with
                | lam x_c dom_c body_c =>
                  -- Both lambdas: beta-reduce in both envs
                  -- Need IH on the substituted bodies
                  -- h_abs: absEval n Γ (body_a.subst x_a a_a) = some τ
                  -- h_conc: concEval n γ (body_c.subst x_c a_c) = some v
                  -- But these are DIFFERENT expressions! IH requires same expr.
                  sorry
                | _ =>
                  -- f_c is not lambda but f_a is. Since f_c ⊑ f_a = lam,
                  -- this is a subtle case.
                  sorry
              | _ =>
                cases f_c with
                | lam x_c dom_c body_c =>
                  -- f_a not lambda, f_c is lambda. Since f_c ⊑ f_a,
                  -- lam ⊑ non-lam — can happen via top.
                  sorry
                | _ =>
                  -- Both stuck: τ = app f_a a_a, v = app f_c a_c
                  simp at h_abs h_conc
                  rw [← h_abs, ← h_conc]
                  exact Subtype'.app_cong hf_sub ha_sub
