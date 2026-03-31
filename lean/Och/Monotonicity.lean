import Och.Syntax
import Och.Eval
import Och.Subtyping

/-!
# Monotonicity

Generalized to `absEval_mono` taking `Subtype' e₂ e₁` + `EnvSub Γ₂ Γ₁`.
Standard monotonicity is the corollary with `Subtype'.refl`.

Key technique: removing `trans` from `Subtype'` enables lambda inversion.
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

/-- **Generalized monotonicity.** -/
theorem absEval_mono
    (fuel : Nat) (Γ₁ Γ₂ : Env) (e₁ e₂ τ₁ τ₂ : Expr)
    (h_sub : Subtype' e₂ e₁)
    (h_env : EnvSub Γ₂ Γ₁)
    (h₁ : absEval fuel Γ₁ e₁ = some τ₁)
    (h₂ : absEval fuel Γ₂ e₂ = some τ₂)
    : Subtype' τ₂ τ₁ := by
  induction fuel generalizing Γ₁ Γ₂ e₁ e₂ τ₁ τ₂ with
  | zero => simp [absEval] at h₁
  | succ n ih =>
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
            exact Subtype'.lam_body (ih _ _ body body _ _
              (Subtype'.refl body) (envSub_extend h_env x (.var x)) hb₁ hb₂)
      | type =>
        simp [absEval] at h₁ h₂; rw [← h₁, ← h₂]; exact Subtype'.refl .type
      | asc term ty =>
        simp only [absEval] at h₁ h₂
        exact ih _ _ ty ty _ _ (Subtype'.refl ty) h_env h₁ h₂
      | fix inner =>
        simp only [absEval] at h₁ h₂
        cases inner with
        | lam f dom body =>
          -- absEval (.fix (.lam f dom body)) = absEval dom
          -- Both τ₁ and τ₂ come from evaluating dom in Γ₁ and Γ₂ respectively
          simp only at h₁ h₂
          exact ih _ _ dom dom _ _ (Subtype'.refl dom) h_env h₁ h₂
        | _ => simp at h₁
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
                have hf_sub := ih _ _ f f f₁ f₂ (Subtype'.refl f) h_env hf₁ hf₂
                have ha_sub := ih _ _ a a a₁ a₂ (Subtype'.refl a) h_env ha₁ ha₂
                -- Now case-split f₁ to know how absEval handled the app
                rw [hf₁, ha₁] at h₁; rw [hf₂, ha₂] at h₂
                cases f₁ with
                | lam x₁ dom₁ body₁ =>
                  -- f₁ is lam → f₂ must be lam by inversion
                  obtain ⟨body₂, hf₂_eq, hbody_sub⟩ := Subtype'.lam_rhs_shape hf_sub
                  subst hf₂_eq
                  -- h₁, h₂ now have matches on some(.lam..), which reduce
                  simp only at h₁ h₂
                  exact ih _ _ body₁ body₂ _ _ hbody_sub
                    (envSub_extend_sub h_env x₁ ha_sub) h₁ h₂
                | var v₁ =>
                  cases f₂ with
                  | lam _ _ _ => cases hf_sub  -- Subtype' (lam ..) (var ..) impossible
                  | type => cases hf_sub       -- Subtype' .type (var ..) impossible
                  | _ => simp only at h₁ h₂; cases h₁; cases h₂
                         exact Subtype'.app_cong hf_sub ha_sub
                | app _ _ =>
                  cases f₂ with
                  | lam _ _ _ => cases hf_sub
                  | type => cases hf_sub
                  | _ => simp only at h₁ h₂; cases h₁; cases h₂
                         exact Subtype'.app_cong hf_sub ha_sub
                | asc _ _ =>
                  cases f₂ with
                  | lam _ _ _ => cases hf_sub
                  | type => cases hf_sub
                  | _ => simp only at h₁ h₂; cases h₁; cases h₂
                         exact Subtype'.app_cong hf_sub ha_sub
                | fix _ =>
                  -- absEval never produces .fix, but need case for exhaustiveness
                  -- .fix falls through to stuck in absEval's app case
                  cases f₂ with
                  | lam _ _ _ => cases hf_sub
                  | type => cases hf_sub
                  | _ => simp only at h₁ h₂; cases h₁; cases h₂
                         exact Subtype'.app_cong hf_sub ha_sub
                | type =>
                  -- f₁=.type: evaluator returns .type (type-app-returns-type)
                  simp only at h₁; cases h₁; exact Subtype'.top τ₂
    | .top e =>
      simp [absEval] at h₁; rw [← h₁]; exact Subtype'.top τ₂
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
          exact Subtype'.lam_body (ih _ _ body₁ body₂ _ _ hbody
            (envSub_extend h_env x (.var x)) hb₁ hb₂)
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
                obtain ⟨body₂, hf₂_eq, hbody_sub⟩ := Subtype'.lam_rhs_shape hf_sub
                subst hf₂_eq
                simp only at h₁ h₂
                exact ih _ _ body₁ body₂ _ _ hbody_sub
                  (envSub_extend_sub h_env x₁ ha_sub) h₁ h₂
              | var v₁ =>
                cases f₂ with
                | lam _ _ _ => cases hf_sub
                | type => cases hf_sub
                | _ => simp only at h₁ h₂; cases h₁; cases h₂
                       exact Subtype'.app_cong hf_sub ha_sub
              | app _ _ =>
                cases f₂ with
                | lam _ _ _ => cases hf_sub
                | type => cases hf_sub
                | _ => simp only at h₁ h₂; cases h₁; cases h₂
                       exact Subtype'.app_cong hf_sub ha_sub
              | asc _ _ =>
                cases f₂ with
                | lam _ _ _ => cases hf_sub
                | type => cases hf_sub
                | _ => simp only at h₁ h₂; cases h₁; cases h₂
                       exact Subtype'.app_cong hf_sub ha_sub
              | fix _ =>
                cases f₂ with
                | lam _ _ _ => cases hf_sub
                | type => cases hf_sub
                | _ => simp only at h₁ h₂; cases h₁; cases h₂
                       exact Subtype'.app_cong hf_sub ha_sub
              | type =>
                -- f₁=.type: evaluator returns .type (type-app-returns-type)
                simp only at h₁; cases h₁; exact Subtype'.top τ₂
    | .fix_cong h_inner =>
      rename_i inner₁ inner₂
      simp only [absEval] at h₁ h₂
      -- inner₁ must be a lam (else absEval returns none, contradicting h₁)
      -- Subtype' inner₂ inner₁ → inner₂ has same shape (lam with same dom)
      -- Both sides return absEval of the same dom → IH on dom
      cases inner₁ with
      | lam f₁ dom₁ body₁ =>
        obtain ⟨body₂, hinner₂_eq, _⟩ := Subtype'.lam_rhs_shape h_inner
        subst hinner₂_eq
        -- Both: absEval n Γ dom₁ (same domain by lam_rhs_shape)
        simp only at h₁ h₂
        exact ih _ _ dom₁ dom₁ _ _ (Subtype'.refl dom₁) h_env h₁ h₂
      | _ =>
        -- inner₁ not a lam: absEval returns none, contradiction
        simp at h₁

theorem monotonicity
    (Γ₁ Γ₂ : Env) (e τ₁ τ₂ : Expr) (fuel : Nat)
    (h_env : EnvSub Γ₂ Γ₁)
    (h_abs₁ : absEval fuel Γ₁ e = some τ₁)
    (h_abs₂ : absEval fuel Γ₂ e = some τ₂)
    : Subtype' τ₂ τ₁ :=
  absEval_mono fuel Γ₁ Γ₂ e e τ₁ τ₂ (Subtype'.refl e) h_env h_abs₁ h_abs₂
