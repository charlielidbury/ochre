import Och.Syntax
import Och.Eval
import Och.Subtyping

/-!
# Monotonicity

Generalized to `absEval_mono` taking `SubtypeCore e₂ e₁` + `EnvSub Γ₂ Γ₁`.
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

def EnvSub (Γ₂ Γ₁ : Env) : Prop :=
  ∀ x τ₁, Γ₁.lookup x = some τ₁ → ∃ τ₂, Γ₂.lookup x = some τ₂ ∧ Subtype' τ₂ τ₁

theorem envSub_extend {Γ₂ Γ₁ : Env} (h : EnvSub Γ₂ Γ₁) (x : Name) (v : Expr) :
    EnvSub ((x, v) :: Γ₂) ((x, v) :: Γ₁) := by
  intro y τ₁ h_lookup
  simp only [Env.lookup] at h_lookup ⊢
  split at h_lookup <;> split
  · cases h_lookup; exact ⟨v, rfl, Subtype'.refl v⟩
  · rename_i h1 h2; exact absurd h1 h2
  · rename_i h1 h2; exact absurd h2 h1
  · exact h y τ₁ h_lookup

theorem envSub_extend_sub {Γ₂ Γ₁ : Env} (h : EnvSub Γ₂ Γ₁)
    (x : Name) {v₂ v₁ : Expr} (hv : Subtype' v₂ v₁) :
    EnvSub ((x, v₂) :: Γ₂) ((x, v₁) :: Γ₁) := by
  intro y τ₁ h_lookup
  simp only [Env.lookup] at h_lookup ⊢
  split at h_lookup <;> split
  · cases h_lookup; exact ⟨v₂, rfl, hv⟩
  · rename_i h1 h2; exact absurd h1 h2
  · rename_i h1 h2; exact absurd h2 h1
  · exact h y τ₁ h_lookup

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

/-- EnvSub implies EnvSubCore (Subtype' embeds into SubtypeCore... not in general).
    Instead, lift EnvSubCore to EnvSub via embedding. -/
theorem EnvSubCore.toEnvSub {Γ₂ Γ₁ : Env} (h : EnvSubCore Γ₂ Γ₁) : EnvSub Γ₂ Γ₁ := by
  intro x τ₁ h_lookup
  obtain ⟨τ₂, h_l2, h_sub⟩ := h x τ₁ h_lookup
  exact ⟨τ₂, h_l2, h_sub.toSubtype'⟩

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
                  -- Split on syntactic annotation match in h₁
                  split at h₁
                  · -- ann_mu is lam → annotation path for h₁
                    rename_i y_ann _dom_ann retBody_ann
                    -- h₂ has same ann_mu, so also matches lam
                    simp only [*] at h₂
                    exact ih _ _ retBody_ann retBody_ann _ _ (.refl retBody_ann)
                      (envSubCore_extend_sub h_env y_ann ha_sub) h₁ h₂
                  · -- ann_mu is not lam → body-unfold path for h₁
                    rename_i h_not_lam
                    -- h₂ also takes body-unfold (same ann_mu)
                    simp only [*] at h₂
                    have hmu_sub : SubtypeCore (.mu x_mu ann_mu body₂_mu) (.mu x_mu ann_mu body_mu) :=
                      .mu_body hbody_mu_sub
                    cases hunf₁ : absEval n ((x_mu, .mu x_mu ann_mu body_mu) :: Γ₁) body_mu with
                    | none => rw [hunf₁] at h₁; simp at h₁
                    | some unf₁ =>
                      rw [hunf₁] at h₁
                      cases hunf₂ : absEval n ((x_mu, .mu x_mu ann_mu body₂_mu) :: Γ₂) body₂_mu with
                      | none => rw [hunf₂] at h₂; simp at h₂
                      | some unf₂ =>
                        rw [hunf₂] at h₂
                        have hunf_sub := ih _ _ body_mu body₂_mu unf₁ unf₂ hbody_mu_sub
                          (envSubCore_extend_sub h_env x_mu hmu_sub) hunf₁ hunf₂
                        cases unf₁ with
                        | lam y₁ dom₁ retBody₁ =>
                          obtain ⟨retBody₂, hunf₂_eq, hret_sub⟩ := SubtypeCore.lam_rhs_shape hunf_sub
                          subst hunf₂_eq
                          simp only at h₁ h₂
                          exact ih _ _ retBody₁ retBody₂ _ _ hret_sub
                            (envSubCore_extend_sub h_env y₁ ha_sub) h₁ h₂
                        | type =>
                          simp only at h₁; cases h₁; exact .top τ₂
                        | mu x_u ann_u body_u =>
                          obtain ⟨body₂_u, hunf₂_eq, _⟩ := SubtypeCore.mu_rhs_shape hunf_sub
                          subst hunf₂_eq
                          simp only at h₁ h₂; cases h₁; cases h₂
                          exact .app_cong hunf_sub ha_sub
                        | var _ =>
                          cases unf₂ with
                          | lam _ _ _ => cases hunf_sub
                          | type => cases hunf_sub
                          | mu _ _ _ => cases hunf_sub
                          | _ => simp only at h₁ h₂; cases h₁; cases h₂
                                 exact .app_cong hunf_sub ha_sub
                        | app _ _ =>
                          cases unf₂ with
                          | lam _ _ _ => cases hunf_sub
                          | type => cases hunf_sub
                          | mu _ _ _ => cases hunf_sub
                          | _ => simp only at h₁ h₂; cases h₁; cases h₂
                                 exact .app_cong hunf_sub ha_sub
                        | asc _ _ =>
                          cases unf₂ with
                          | lam _ _ _ => cases hunf_sub
                          | type => cases hunf_sub
                          | mu _ _ _ => cases hunf_sub
                          | _ => simp only at h₁ h₂; cases h₁; cases h₂
                                 exact .app_cong hunf_sub ha_sub
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
                -- Split on syntactic annotation match in h₁
                split at h₁
                · -- ann_mu is lam → annotation path
                  rename_i y_ann _dom_ann retBody_ann
                  simp only [*] at h₂
                  exact ih _ _ retBody_ann retBody_ann _ _ (.refl retBody_ann)
                    (envSubCore_extend_sub h_env y_ann ha_sub) h₁ h₂
                · -- ann_mu is not lam → body-unfold path
                  rename_i h_not_lam
                  simp only [*] at h₂
                  have hmu_sub : SubtypeCore (.mu x_mu ann_mu body₂_mu) (.mu x_mu ann_mu body_mu) :=
                    .mu_body hbody_mu_sub
                  cases hunf₁ : absEval n ((x_mu, .mu x_mu ann_mu body_mu) :: Γ₁) body_mu with
                  | none => rw [hunf₁] at h₁; simp at h₁
                  | some unf₁ =>
                    rw [hunf₁] at h₁
                    cases hunf₂ : absEval n ((x_mu, .mu x_mu ann_mu body₂_mu) :: Γ₂) body₂_mu with
                    | none => rw [hunf₂] at h₂; simp at h₂
                    | some unf₂ =>
                      rw [hunf₂] at h₂
                      have hunf_sub := ih _ _ body_mu body₂_mu unf₁ unf₂ hbody_mu_sub
                        (envSubCore_extend_sub h_env x_mu hmu_sub) hunf₁ hunf₂
                      cases unf₁ with
                      | lam y₁ dom₁ retBody₁ =>
                        obtain ⟨retBody₂, hunf₂_eq, hret_sub⟩ := SubtypeCore.lam_rhs_shape hunf_sub
                        subst hunf₂_eq
                        simp only at h₁ h₂
                        exact ih _ _ retBody₁ retBody₂ _ _ hret_sub
                          (envSubCore_extend_sub h_env y₁ ha_sub) h₁ h₂
                      | type =>
                        simp only at h₁; cases h₁; exact .top τ₂
                      | mu x_u ann_u body_u =>
                        obtain ⟨body₂_u, hunf₂_eq, _⟩ := SubtypeCore.mu_rhs_shape hunf_sub
                        subst hunf₂_eq
                        simp only at h₁ h₂; cases h₁; cases h₂
                        exact .app_cong hunf_sub ha_sub
                      | var _ =>
                        cases unf₂ with
                        | lam _ _ _ => cases hunf_sub
                        | type => cases hunf_sub
                        | mu _ _ _ => cases hunf_sub
                        | _ => simp only at h₁ h₂; cases h₁; cases h₂
                               exact .app_cong hunf_sub ha_sub
                      | app _ _ =>
                        cases unf₂ with
                        | lam _ _ _ => cases hunf_sub
                        | type => cases hunf_sub
                        | mu _ _ _ => cases hunf_sub
                        | _ => simp only at h₁ h₂; cases h₁; cases h₂
                               exact .app_cong hunf_sub ha_sub
                      | asc _ _ =>
                        cases unf₂ with
                        | lam _ _ _ => cases hunf_sub
                        | type => cases hunf_sub
                        | mu _ _ _ => cases hunf_sub
                        | _ => simp only at h₁ h₂; cases h₁; cases h₂
                               exact .app_cong hunf_sub ha_sub
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

/-- EnvSub (using Subtype') can be weakened to EnvSubCore (using SubtypeCore) when
    the env doesn't contain self_intro. In practice this always holds because envs
    are built from refl and structural constructors, not self_intro. This conversion
    is NOT possible in general (Subtype' ⊃ SubtypeCore), but here we only need it
    for the monotonicity corollary where the env comes from user-provided EnvSub.
    We factor through: EnvSub gives Subtype' values, which we can't convert to
    SubtypeCore. Instead, monotonicity takes EnvSub directly and wraps the call. -/
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
