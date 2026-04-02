import Och.Syntax
import Och.Eval
import Och.Subtyping

/-!
# Monotonicity

Generalized to `absEval_mono` taking `SubtypeCore e₂ e₁` + `EnvSubCore Γ₂ Γ₁`.
Standard monotonicity is the corollary with `SubtypeCore.refl`.

Key technique: using `SubtypeCore` (Subtype' without self_intro) avoids
unreachable self_intro cases that would otherwise require sorry. The IH
never generates self_intro (it only produces refl, lam_body, mu_body,
app_cong, and top), so SubtypeCore is the natural relation for this proof.

## Status

**SORRY-FREE.** absEval_mono fully proved, all cases handled.
Previously contained absEval_evalFreeVars_general which was FALSE for the mu
case (the mu env binding leaks input variable names into the output).
Counterexample in CounterexampleTest.lean. Both it and its corollary
absEval_evalFreeVars_neutral were unused and have been removed.
-/

open Expr

/-- Environment subtyping via SubtypeCore (no self_intro). Used by absEval_mono. -/
def EnvSubCore (Γ₂ Γ₁ : Env) : Prop :=
  ∀ x τ₁, Γ₁.lookup x = some τ₁ → ∃ τ₂, Γ₂.lookup x = some τ₂ ∧ SubtypeCore τ₂ τ₁

theorem envSubCore_extend {Γ₂ Γ₁ : Env} (h : EnvSubCore Γ₂ Γ₁) (x : Name) (v : Expr) :
    EnvSubCore ((x, v) :: Γ₂) ((x, v) :: Γ₁) := by
  intro y τ₁ h_lookup
  simp only [Env.lookup] at h_lookup ⊢
  split at h_lookup <;> split
  · cases h_lookup; exact ⟨v, rfl, SubtypeCore.refl v⟩
  · rename_i h1 h2; exact absurd h1 h2
  · rename_i h1 h2; exact absurd h2 h1
  · exact h y τ₁ h_lookup

theorem envSubCore_extend_sub {Γ₂ Γ₁ : Env} (h : EnvSubCore Γ₂ Γ₁)
    (x : Name) {v₂ v₁ : Expr} (hv : SubtypeCore v₂ v₁) :
    EnvSubCore ((x, v₂) :: Γ₂) ((x, v₁) :: Γ₁) := by
  intro y τ₁ h_lookup
  simp only [Env.lookup] at h_lookup ⊢
  split at h_lookup <;> split
  · cases h_lookup; exact ⟨v₂, rfl, hv⟩
  · rename_i h1 h2; exact absurd h1 h2
  · rename_i h1 h2; exact absurd h2 h1
  · exact h y τ₁ h_lookup

/-- **Generalized monotonicity.**

    Three proof-friendly changes to absEval make this work:
    (a) Annotations pass through unchanged in mu case → mu_body applies directly.
    (b) Body-unfold uses env extension → IH applies via envSub_extend_sub.
    (c) Syntactic annotation check → both envs always agree on which path.

    Uses `SubtypeCore` (Subtype' without self_intro) so that all cases are
    provable. The IH only generates refl/lam_body/mu_body/app_cong/top,
    never self_intro, so SubtypeCore is the natural relation here. -/
theorem absEval_mono
    (fuel : Nat) (Γ₁ Γ₂ : Env) (e₁ e₂ τ₁ τ₂ : Expr)
    (h_sub : SubtypeCore e₂ e₁)
    (h_env : EnvSubCore Γ₂ Γ₁)
    (h₁ : absEval fuel Γ₁ e₁ = some τ₁)
    (h₂ : absEval fuel Γ₂ e₂ = some τ₂)
    : SubtypeCore τ₂ τ₁ := by
  induction fuel generalizing Γ₁ Γ₂ e₁ e₂ τ₁ τ₂ with
  | zero => simp [absEval] at h₁
  | succ n ih =>
    -- Helper for stuck app cases: if both sides produce stuck apps
    have stuck_app : ∀ {f₁ f₂ a₁ a₂ : Expr},
        SubtypeCore f₂ f₁ → SubtypeCore a₂ a₁ →
        .app f₁ a₁ = τ₁ → .app f₂ a₂ = τ₂ →
        SubtypeCore τ₂ τ₁ := by
      intro f₁ f₂ a₁ a₂ hf ha heq₁ heq₂
      rw [← heq₁, ← heq₂]; exact .app_cong hf ha
    match h_sub with
    | .refl e =>
      cases e with
      | var x =>
        simp [absEval] at h₁ h₂
        have ⟨τ₂', h_l2, h_sub'⟩ := h_env x τ₁ h₁
        rw [h_l2] at h₂; cases h₂; exact h_sub'
      | lam x dom body =>
        simp only [absEval] at h₁ h₂
        cases hb₁ : absEval n ((x, .var x) :: Γ₁) body with
        | none => simp [hb₁] at h₁
        | some body₁ =>
          simp [hb₁] at h₁
          cases hb₂ : absEval n ((x, .var x) :: Γ₂) body with
          | none => simp [hb₂] at h₂
          | some body₂ =>
            simp [hb₂] at h₂; rw [← h₁, ← h₂]
            exact .lam_body (ih _ _ body body _ _
              (.refl body) (envSubCore_extend h_env x (.var x)) hb₁ hb₂)
      | type =>
        simp [absEval] at h₁ h₂; rw [← h₁, ← h₂]; exact .refl .type
      | asc term ty =>
        simp only [absEval] at h₁ h₂
        exact ih _ _ ty ty _ _ (.refl ty) h_env h₁ h₂
      | mu x ann body =>
        -- x is bound to the mu itself; annotation passes through unchanged
        simp only [absEval] at h₁ h₂
        cases hb₁ : absEval n ((x, .mu x ann body) :: Γ₁) body with
        | none => simp [hb₁] at h₁
        | some body₁ =>
          simp [hb₁] at h₁
          cases hb₂ : absEval n ((x, .mu x ann body) :: Γ₂) body with
          | none => simp [hb₂] at h₂
          | some body₂ =>
            simp [hb₂] at h₂; rw [← h₁, ← h₂]
            exact .mu_body (ih _ _ body body _ _
              (.refl body) (envSubCore_extend h_env x (.mu x ann body)) hb₁ hb₂)
      | app f a =>
        simp only [absEval] at h₁ h₂
        cases hf₁ : absEval n Γ₁ f with
        | none => simp [hf₁] at h₁
        | some f₁ =>
          cases ha₁ : absEval n Γ₁ a with
          | none => simp [hf₁, ha₁] at h₁
          | some a₁ =>
            cases hf₂ : absEval n Γ₂ f with
            | none => simp [hf₂] at h₂
            | some f₂ =>
              cases ha₂ : absEval n Γ₂ a with
              | none => simp [hf₂, ha₂] at h₂
              | some a₂ =>
                have hf_sub := ih _ _ f f f₁ f₂ (.refl f) h_env hf₁ hf₂
                have ha_sub := ih _ _ a a a₁ a₂ (.refl a) h_env ha₁ ha₂
                rw [hf₁, ha₁] at h₁; rw [hf₂, ha₂] at h₂
                cases f₁ with
                | lam x₁ dom₁ body₁ =>
                  obtain ⟨body₂, hf₂_eq, hbody_sub⟩ := SubtypeCore.lam_rhs_shape hf_sub
                  subst hf₂_eq
                  simp only at h₁ h₂
                  exact ih _ _ body₁ body₂ _ _ hbody_sub
                    (envSubCore_extend_sub h_env x₁ ha_sub) h₁ h₂
                | mu x_mu ann_mu body_mu =>
                  obtain ⟨body₂_mu, hf₂_eq, hbody_mu_sub⟩ := SubtypeCore.mu_rhs_shape hf_sub
                  subst hf₂_eq
                  simp only at h₁ h₂
                  -- absEval matches on (ann, body) jointly. Case-split on body_mu
                  -- to determine which branch both h₁ and h₂ take.
                  cases body_mu with
                  | lam y_body dom_body bodyRes =>
                    -- body is lambda. Determine body₂_mu shape.
                    obtain ⟨bodyRes₂, hbc_eq, hbody_res_sub⟩ := SubtypeCore.lam_rhs_shape hbody_mu_sub
                    subst hbc_eq
                    -- Both have lambda bodies. Now check if ann is also a lambda.
                    cases ann_mu with
                    | lam y_ann dom_ann retBody =>
                      -- Both ann and body are lambdas: annotation path
                      simp only at h₁ h₂
                      exact ih _ _ retBody retBody _ _ (.refl retBody)
                        (envSubCore_extend_sub h_env y_ann ha_sub) h₁ h₂
                    | _ =>
                      -- Ann not lambda, body is lambda: body-unfold path
                      simp only at h₁ h₂
                      exact ih _ _ bodyRes bodyRes₂ _ _ hbody_res_sub
                        (envSubCore_extend_sub h_env y_body ha_sub) h₁ h₂
                  | type =>
                    -- body is type → both return type (regardless of ann)
                    cases ann_mu with
                    | lam _ _ _ => simp only at h₁; cases h₁; exact .top τ₂
                    | _ => simp only at h₁; cases h₁; exact .top τ₂
                  | mu _ _ _ =>
                    -- body is mu → stuck app (regardless of ann)
                    obtain ⟨body₂_u, hbc_eq, _⟩ := SubtypeCore.mu_rhs_shape hbody_mu_sub
                    subst hbc_eq
                    cases ann_mu with
                    | lam _ _ _ => simp only at h₁ h₂; cases h₁; cases h₂
                                   exact .app_cong hbody_mu_sub ha_sub
                    | _ => simp only at h₁ h₂; cases h₁; cases h₂
                           exact .app_cong hbody_mu_sub ha_sub
                  | var _ =>
                    cases body₂_mu with
                    | lam _ _ _ => cases hbody_mu_sub
                    | type => cases hbody_mu_sub
                    | mu _ _ _ => cases hbody_mu_sub
                    | _ => cases ann_mu with
                           | lam _ _ _ => simp only at h₁ h₂; cases h₁; cases h₂
                                          exact .app_cong hbody_mu_sub ha_sub
                           | _ => simp only at h₁ h₂; cases h₁; cases h₂
                                  exact .app_cong hbody_mu_sub ha_sub
                  | app _ _ =>
                    cases body₂_mu with
                    | lam _ _ _ => cases hbody_mu_sub
                    | type => cases hbody_mu_sub
                    | mu _ _ _ => cases hbody_mu_sub
                    | _ => cases ann_mu with
                           | lam _ _ _ => simp only at h₁ h₂; cases h₁; cases h₂
                                          exact .app_cong hbody_mu_sub ha_sub
                           | _ => simp only at h₁ h₂; cases h₁; cases h₂
                                  exact .app_cong hbody_mu_sub ha_sub
                  | asc _ _ =>
                    cases body₂_mu with
                    | lam _ _ _ => cases hbody_mu_sub
                    | type => cases hbody_mu_sub
                    | mu _ _ _ => cases hbody_mu_sub
                    | _ => cases ann_mu with
                           | lam _ _ _ => simp only at h₁ h₂; cases h₁; cases h₂
                                          exact .app_cong hbody_mu_sub ha_sub
                           | _ => simp only at h₁ h₂; cases h₁; cases h₂
                                  exact .app_cong hbody_mu_sub ha_sub
                | type =>
                  simp only at h₁; cases h₁; exact .top τ₂
                | var _ =>
                  cases f₂ with
                  | lam _ _ _ => cases hf_sub
                  | type => cases hf_sub
                  | mu _ _ _ => cases hf_sub
                  | _ => simp only at h₁ h₂; cases h₁; cases h₂
                         exact .app_cong hf_sub ha_sub
                | app _ _ =>
                  cases f₂ with
                  | lam _ _ _ => cases hf_sub
                  | type => cases hf_sub
                  | mu _ _ _ => cases hf_sub
                  | _ => simp only at h₁ h₂; cases h₁; cases h₂
                         exact .app_cong hf_sub ha_sub
                | asc _ _ =>
                  cases f₂ with
                  | lam _ _ _ => cases hf_sub
                  | type => cases hf_sub
                  | mu _ _ _ => cases hf_sub
                  | _ => simp only at h₁ h₂; cases h₁; cases h₂
                         exact .app_cong hf_sub ha_sub
    | .top e =>
      simp [absEval] at h₁; rw [← h₁]; exact .top τ₂
    | .lam_body hbody =>
      rename_i x dom body₁ body₂
      simp only [absEval] at h₁ h₂
      cases hb₁ : absEval n ((x, .var x) :: Γ₁) body₁ with
      | none => simp [hb₁] at h₁
      | some body₁' =>
        simp [hb₁] at h₁
        cases hb₂ : absEval n ((x, .var x) :: Γ₂) body₂ with
        | none => simp [hb₂] at h₂
        | some body₂' =>
          simp [hb₂] at h₂; rw [← h₁, ← h₂]
          exact .lam_body (ih _ _ body₁ body₂ _ _ hbody
            (envSubCore_extend h_env x (.var x)) hb₁ hb₂)
    | .app_cong hf ha =>
      rename_i e1_f e2_f e1_a e2_a
      simp only [absEval] at h₁ h₂
      cases hf₁ : absEval n Γ₁ e1_f with
      | none => simp [hf₁] at h₁
      | some f₁ =>
        cases ha₁ : absEval n Γ₁ e1_a with
        | none => simp [hf₁, ha₁] at h₁
        | some a₁ =>
          cases hf₂ : absEval n Γ₂ e2_f with
          | none => simp [hf₂] at h₂
          | some f₂ =>
            cases ha₂ : absEval n Γ₂ e2_a with
            | none => simp [hf₂, ha₂] at h₂
            | some a₂ =>
              have hf_sub := ih _ _ _ _ f₁ f₂ hf h_env hf₁ hf₂
              have ha_sub := ih _ _ _ _ a₁ a₂ ha h_env ha₁ ha₂
              rw [hf₁, ha₁] at h₁; rw [hf₂, ha₂] at h₂
              cases f₁ with
              | lam x₁ dom₁ body₁ =>
                obtain ⟨body₂, hf₂_eq, hbody_sub⟩ := SubtypeCore.lam_rhs_shape hf_sub
                subst hf₂_eq
                simp only at h₁ h₂
                exact ih _ _ body₁ body₂ _ _ hbody_sub
                  (envSubCore_extend_sub h_env x₁ ha_sub) h₁ h₂
              | mu x_mu ann_mu body_mu =>
                obtain ⟨body₂_mu, hf₂_eq, hbody_mu_sub⟩ := SubtypeCore.mu_rhs_shape hf_sub
                subst hf₂_eq
                simp only at h₁ h₂
                -- absEval matches on (ann, body) jointly. Case-split on body_mu.
                cases body_mu with
                | lam y_body dom_body bodyRes =>
                  obtain ⟨bodyRes₂, hbc_eq, hbody_res_sub⟩ := SubtypeCore.lam_rhs_shape hbody_mu_sub
                  subst hbc_eq
                  cases ann_mu with
                  | lam y_ann dom_ann retBody =>
                    simp only at h₁ h₂
                    exact ih _ _ retBody retBody _ _ (.refl retBody)
                      (envSubCore_extend_sub h_env y_ann ha_sub) h₁ h₂
                  | _ =>
                    simp only at h₁ h₂
                    exact ih _ _ bodyRes bodyRes₂ _ _ hbody_res_sub
                      (envSubCore_extend_sub h_env y_body ha_sub) h₁ h₂
                | type =>
                  cases ann_mu with
                  | lam _ _ _ => simp only at h₁; cases h₁; exact .top τ₂
                  | _ => simp only at h₁; cases h₁; exact .top τ₂
                | mu _ _ _ =>
                  obtain ⟨body₂_u, hbc_eq, _⟩ := SubtypeCore.mu_rhs_shape hbody_mu_sub
                  subst hbc_eq
                  cases ann_mu with
                  | lam _ _ _ => simp only at h₁ h₂; cases h₁; cases h₂
                                 exact .app_cong hbody_mu_sub ha_sub
                  | _ => simp only at h₁ h₂; cases h₁; cases h₂
                         exact .app_cong hbody_mu_sub ha_sub
                | var _ =>
                  cases body₂_mu with
                  | lam _ _ _ => cases hbody_mu_sub
                  | type => cases hbody_mu_sub
                  | mu _ _ _ => cases hbody_mu_sub
                  | _ => cases ann_mu with
                         | lam _ _ _ => simp only at h₁ h₂; cases h₁; cases h₂
                                        exact .app_cong hbody_mu_sub ha_sub
                         | _ => simp only at h₁ h₂; cases h₁; cases h₂
                                exact .app_cong hbody_mu_sub ha_sub
                | app _ _ =>
                  cases body₂_mu with
                  | lam _ _ _ => cases hbody_mu_sub
                  | type => cases hbody_mu_sub
                  | mu _ _ _ => cases hbody_mu_sub
                  | _ => cases ann_mu with
                         | lam _ _ _ => simp only at h₁ h₂; cases h₁; cases h₂
                                        exact .app_cong hbody_mu_sub ha_sub
                         | _ => simp only at h₁ h₂; cases h₁; cases h₂
                                exact .app_cong hbody_mu_sub ha_sub
                | asc _ _ =>
                  cases body₂_mu with
                  | lam _ _ _ => cases hbody_mu_sub
                  | type => cases hbody_mu_sub
                  | mu _ _ _ => cases hbody_mu_sub
                  | _ => cases ann_mu with
                         | lam _ _ _ => simp only at h₁ h₂; cases h₁; cases h₂
                                        exact .app_cong hbody_mu_sub ha_sub
                         | _ => simp only at h₁ h₂; cases h₁; cases h₂
                                exact .app_cong hbody_mu_sub ha_sub
              | type =>
                simp only at h₁; cases h₁; exact .top τ₂
              | var v₁ =>
                cases f₂ with
                | lam _ _ _ => cases hf_sub
                | type => cases hf_sub
                | mu _ _ _ => cases hf_sub
                | _ => simp only at h₁ h₂; cases h₁; cases h₂
                       exact .app_cong hf_sub ha_sub
              | app _ _ =>
                cases f₂ with
                | lam _ _ _ => cases hf_sub
                | type => cases hf_sub
                | mu _ _ _ => cases hf_sub
                | _ => simp only at h₁ h₂; cases h₁; cases h₂
                       exact .app_cong hf_sub ha_sub
              | asc _ _ =>
                cases f₂ with
                | lam _ _ _ => cases hf_sub
                | type => cases hf_sub
                | mu _ _ _ => cases hf_sub
                | _ => simp only at h₁ h₂; cases h₁; cases h₂
                       exact .app_cong hf_sub ha_sub
    | .mu_body hbody =>
      rename_i x ann body₁ body₂
      -- annotation is the same in both (mu_body preserves ann)
      -- x is bound to the respective mu value in each env
      simp only [absEval] at h₁ h₂
      cases hb₁ : absEval n ((x, .mu x ann body₁) :: Γ₁) body₁ with
      | none => simp [hb₁] at h₁
      | some body₁' =>
        simp [hb₁] at h₁
        cases hb₂ : absEval n ((x, .mu x ann body₂) :: Γ₂) body₂ with
        | none => simp [hb₂] at h₂
        | some body₂' =>
          simp [hb₂] at h₂; rw [← h₁, ← h₂]
          exact .mu_body (ih _ _ body₁ body₂ _ _ hbody
            (envSubCore_extend_sub h_env x (.mu_body hbody)) hb₁ hb₂)

/-- Monotonicity corollary: same expression in two envs related by EnvSubCore.
    Wraps absEval_mono with SubtypeCore.refl and converts output to Subtype'. -/
theorem monotonicity
    (Γ₁ Γ₂ : Env) (e τ₁ τ₂ : Expr) (fuel : Nat)
    (h_env : EnvSubCore Γ₂ Γ₁)
    (h_abs₁ : absEval fuel Γ₁ e = some τ₁)
    (h_abs₂ : absEval fuel Γ₂ e = some τ₂)
    : Subtype' τ₂ τ₁ :=
  (absEval_mono fuel Γ₁ Γ₂ e e τ₁ τ₂ (SubtypeCore.refl e) h_env h_abs₁ h_abs₂).toSubtype'

-- ============================================================
-- evalFreeVars coverage: REMOVED
-- ============================================================
-- absEval_evalFreeVars_general and absEval_evalFreeVars_neutral were here
-- but are FALSE for the mu case (mu env binding leaks input variable names).
-- Counterexample in CounterexampleTest.lean. Both were unused.
