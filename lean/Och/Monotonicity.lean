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
      | iota x body =>
        -- Structurally identical to the lam case
        simp only [absEval] at h₁ h₂
        cases hb₁ : absEval n ((x, .var x) :: Γ₁) body with
        | none => simp [hb₁] at h₁
        | some body₁ =>
          simp [hb₁] at h₁
          cases hb₂ : absEval n ((x, .var x) :: Γ₂) body with
          | none => simp [hb₂] at h₂
          | some body₂ =>
            simp [hb₂] at h₂; rw [← h₁, ← h₂]
            exact Subtype'.iota_body (ih _ _ body body _ _
              (Subtype'.refl body) (envSub_extend h_env x (.var x)) hb₁ hb₂)
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
                  cases f₂ with
                  | lam _ _ _ => cases hf_sub
                  | type => cases hf_sub
                  | _ => simp only at h₁ h₂; cases h₁; cases h₂
                         exact Subtype'.app_cong hf_sub ha_sub
                | iota _ _ =>
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
              | iota _ _ =>
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
    | .iota_body hbody =>
      -- Structurally identical to the lam_body case
      rename_i x body₁ body₂
      simp only [absEval] at h₁ h₂
      cases hb₁ : absEval n ((x, .var x) :: Γ₁) body₁ with
      | none => simp [hb₁] at h₁
      | some body₁' =>
        simp [hb₁] at h₁
        cases hb₂ : absEval n ((x, .var x) :: Γ₂) body₂ with
        | none => simp [hb₂] at h₂
        | some body₂' =>
          simp [hb₂] at h₂; rw [← h₁, ← h₂]
          exact Subtype'.iota_body (ih _ _ body₁ body₂ _ _ hbody
            (envSub_extend h_env x (.var x)) hb₁ hb₂)

theorem monotonicity
    (Γ₁ Γ₂ : Env) (e τ₁ τ₂ : Expr) (fuel : Nat)
    (h_env : EnvSub Γ₂ Γ₁)
    (h_abs₁ : absEval fuel Γ₁ e = some τ₁)
    (h_abs₂ : absEval fuel Γ₂ e = some τ₂)
    : Subtype' τ₂ τ₁ :=
  absEval_mono fuel Γ₁ Γ₂ e e τ₁ τ₂ (Subtype'.refl e) h_env h_abs₁ h_abs₂

-- ============================================================
-- Generalized monotonicity with SubtypeTrans
-- ============================================================

/-- Environment subtyping via SubtypeTrans (transitive closure). -/
def EnvSubTrans (Γ₂ Γ₁ : Env) : Prop :=
  ∀ x τ₁, Γ₁.lookup x = some τ₁ → ∃ τ₂, Γ₂.lookup x = some τ₂ ∧ SubtypeTrans τ₂ τ₁

/-- An env is "closed" if every free variable in every env value is bound in the env.
    This excludes envs like [(y, λx:Type. z)] where z is unbound — these never
    arise from well-formed evaluation but aren't ruled out by EnvSubTrans. -/
def EnvClosed (Γ : Env) : Prop :=
  ∀ x τ, Γ.lookup x = some τ → ∀ y, y ∈ τ.freeVars → Γ.lookup y ≠ none

/-- Extending a closed env with a binding whose value has free vars covered by the
    extended env preserves closedness. -/
theorem envClosed_extend {Γ : Env} (h : EnvClosed Γ)
    (x : Name) (v : Expr) (hv : ∀ y, y ∈ v.freeVars → Env.lookup ((x, v) :: Γ) y ≠ none) :
    EnvClosed ((x, v) :: Γ) := by
  intro z τ h_lookup y hy
  simp only [Env.lookup] at h_lookup ⊢
  split at h_lookup
  · -- z = x, so τ = v
    cases h_lookup; exact hv y hy
  · -- z ≠ x, so τ is from Γ
    have h_old := h z τ h_lookup y hy
    split
    · -- y = x → found
      exact fun h => absurd h (by simp)
    · exact h_old

theorem envSubTrans_extend {Γ₂ Γ₁ : Env} (h : EnvSubTrans Γ₂ Γ₁) (x : Name) (v : Expr) :
    EnvSubTrans ((x, v) :: Γ₂) ((x, v) :: Γ₁) := by
  intro y τ₁ h_lookup
  simp only [Env.lookup] at h_lookup ⊢
  split at h_lookup <;> split
  · cases h_lookup; exact ⟨v, rfl, SubtypeTrans.step (Subtype'.refl v)⟩
  · rename_i h1 h2; exact absurd h1 h2
  · rename_i h1 h2; exact absurd h2 h1
  · exact h y τ₁ h_lookup

theorem envSubTrans_extend_sub {Γ₂ Γ₁ : Env} (h : EnvSubTrans Γ₂ Γ₁)
    (x : Name) {v₂ v₁ : Expr} (hv : SubtypeTrans v₂ v₁) :
    EnvSubTrans ((x, v₂) :: Γ₂) ((x, v₁) :: Γ₁) := by
  intro y τ₁ h_lookup
  simp only [Env.lookup] at h_lookup ⊢
  split at h_lookup <;> split
  · cases h_lookup; exact ⟨v₂, rfl, hv⟩
  · rename_i h1 h2; exact absurd h1 h2
  · rename_i h1 h2; exact absurd h2 h1
  · exact h y τ₁ h_lookup

/-- **Generalized monotonicity with SubtypeTrans.**

    Same structure as `soundness_gen`: induction on fuel, case split on e₁
    (the abstract/wider expression), use SubtypeTrans target shape lemmas
    to constrain e₂.

    This is the SubtypeTrans analogue of `absEval_mono`. The key difference:
    - `absEval_mono` takes `Subtype' e₂ e₁` + `EnvSub`, returns `Subtype'`
    - `absEval_mono_trans` takes `SubtypeTrans e₂ e₁` + `EnvSubTrans`, returns `SubtypeTrans`

    The app-beta case is handled by case-splitting on e₁, NOT on h_sub.
    SubtypeTrans.lam_target_shape gives the body relationship, and the IH
    at lower fuel handles the recursive call with SubtypeTrans bodies+envs. -/
theorem absEval_mono_trans
    (fuel : Nat) (Γ₁ Γ₂ : Env) (e₁ e₂ τ₁ τ₂ : Expr)
    (h_sub : SubtypeTrans e₂ e₁)
    (h_env : EnvSubTrans Γ₂ Γ₁)
    (h₁ : absEval fuel Γ₁ e₁ = some τ₁)
    (h₂ : absEval fuel Γ₂ e₂ = some τ₂)
    : SubtypeTrans τ₂ τ₁ := by
  induction fuel generalizing Γ₁ Γ₂ e₁ e₂ τ₁ τ₂ with
  | zero => simp [absEval] at h₁
  | succ n ih =>
    cases e₁ with
    | var x =>
      have := h_sub.var_target; subst this
      simp [absEval] at h₁ h₂
      have ⟨τ₂', h_l2, h_sub'⟩ := h_env x τ₁ h₁
      rw [h_l2] at h₂; cases h₂; exact h_sub'
    | type =>
      simp [absEval] at h₁; rw [← h₁]
      exact SubtypeTrans.step (Subtype'.top τ₂)
    | lam x dom body₁ =>
      obtain ⟨body₂, hec_eq, h_body_sub⟩ := h_sub.lam_target_shape
      subst hec_eq
      simp only [absEval] at h₁ h₂
      cases hb₁ : absEval n ((x, .var x) :: Γ₁) body₁ with
      | none => simp [hb₁] at h₁
      | some body₁' =>
        simp [hb₁] at h₁
        cases hb₂ : absEval n ((x, .var x) :: Γ₂) body₂ with
        | none => simp [hb₂] at h₂
        | some body₂' =>
          simp [hb₂] at h₂; rw [← h₁, ← h₂]
          exact SubtypeTrans.lam_body (ih _ _ body₁ body₂ _ _ h_body_sub
            (envSubTrans_extend h_env x (.var x)) hb₁ hb₂)
    | asc term ty =>
      have := h_sub.asc_target; subst this
      simp only [absEval] at h₁ h₂
      exact ih _ _ ty ty _ _ (SubtypeTrans.step (Subtype'.refl ty)) h_env h₁ h₂
    | iota x body₁ =>
      obtain ⟨body₂, hec_eq, h_body_sub⟩ := h_sub.iota_target_shape
      subst hec_eq
      simp only [absEval] at h₁ h₂
      cases hb₁ : absEval n ((x, .var x) :: Γ₁) body₁ with
      | none => simp [hb₁] at h₁
      | some body₁' =>
        simp [hb₁] at h₁
        cases hb₂ : absEval n ((x, .var x) :: Γ₂) body₂ with
        | none => simp [hb₂] at h₂
        | some body₂' =>
          simp [hb₂] at h₂; rw [← h₁, ← h₂]
          exact SubtypeTrans.iota_body (ih _ _ body₁ body₂ _ _ h_body_sub
            (envSubTrans_extend h_env x (.var x)) hb₁ hb₂)
    | fix inner₁ =>
      obtain ⟨inner₂, hec_eq, h_inner_sub⟩ := h_sub.fix_target_shape
      subst hec_eq
      simp only [absEval] at h₁ h₂
      cases inner₁ with
      | lam f₁ dom₁ body₁ =>
        obtain ⟨body₂, hinner₂_eq, _⟩ := h_inner_sub.lam_target_shape
        subst hinner₂_eq
        -- Both sides evaluate dom₁ (same domain by lam_target_shape)
        simp only at h₁ h₂
        exact ih _ _ dom₁ dom₁ _ _ (SubtypeTrans.step (Subtype'.refl dom₁)) h_env h₁ h₂
      | _ => simp at h₁
    | app f₁ a₁ =>
      obtain ⟨f₂, a₂, hec_eq, h_f_sub, h_a_sub⟩ := h_sub.app_target_shape
      subst hec_eq
      simp only [absEval] at h₁ h₂
      cases hf₁ : absEval n Γ₁ f₁ with
      | none => simp [hf₁] at h₁
      | some τ_f₁ =>
        cases ha₁ : absEval n Γ₁ a₁ with
        | none => simp [hf₁, ha₁] at h₁
        | some τ_a₁ =>
          cases hf₂ : absEval n Γ₂ f₂ with
          | none => simp [hf₂] at h₂
          | some τ_f₂ =>
            cases ha₂ : absEval n Γ₂ a₂ with
            | none => simp [hf₂, ha₂] at h₂
            | some τ_a₂ =>
              have ih_f := ih _ _ f₁ f₂ _ _ h_f_sub h_env hf₁ hf₂
              have ih_a := ih _ _ a₁ a₂ _ _ h_a_sub h_env ha₁ ha₂
              rw [hf₁, ha₁] at h₁; rw [hf₂, ha₂] at h₂
              cases τ_f₁ with
              | lam x₁ dom₁ body₁ =>
                obtain ⟨body₂, hf₂_eq, hbody_sub⟩ := ih_f.lam_target_shape
                subst hf₂_eq
                simp only at h₁ h₂
                exact ih _ _ body₁ body₂ _ _ hbody_sub
                  (envSubTrans_extend_sub h_env x₁ ih_a) h₁ h₂
              | type =>
                simp only at h₁; cases h₁
                exact SubtypeTrans.step (Subtype'.top τ₂)
              | var v₁ =>
                have := ih_f.var_target; subst this
                simp only at h₁ h₂; cases h₁; cases h₂
                exact SubtypeTrans.app_cong ih_f ih_a
              | app f₁' a₁' =>
                obtain ⟨f₂', a₂', hvf_eq, _, _⟩ := ih_f.app_target_shape
                subst hvf_eq
                simp only at h₁ h₂; cases h₁; cases h₂
                exact SubtypeTrans.app_cong ih_f ih_a
              | asc t' τ' =>
                have := ih_f.asc_target; subst this
                simp only at h₁ h₂; cases h₁; cases h₂
                exact SubtypeTrans.app_cong ih_f ih_a
              | fix inner' =>
                obtain ⟨inner₂', _, _⟩ := ih_f.fix_target_shape
                subst ‹τ_f₂ = .fix inner₂'›
                simp only at h₁ h₂; cases h₁; cases h₂
                exact SubtypeTrans.app_cong ih_f ih_a
              | iota x' body' =>
                obtain ⟨body₂', _, _⟩ := ih_f.iota_target_shape
                subst ‹τ_f₂ = .iota x' body₂'›
                simp only at h₁ h₂; cases h₁; cases h₂
                exact SubtypeTrans.app_cong ih_f ih_a

/-- Standard monotonicity corollary with SubtypeTrans envs. -/
theorem monotonicity_trans
    (Γ₁ Γ₂ : Env) (e τ₁ τ₂ : Expr) (fuel : Nat)
    (h_env : EnvSubTrans Γ₂ Γ₁)
    (h_abs₁ : absEval fuel Γ₁ e = some τ₁)
    (h_abs₂ : absEval fuel Γ₂ e = some τ₂)
    : SubtypeTrans τ₂ τ₁ :=
  absEval_mono_trans fuel Γ₁ Γ₂ e e τ₁ τ₂ (SubtypeTrans.step (Subtype'.refl e))
    h_env h_abs₁ h_abs₂

/-- **Totality under env narrowing (same expression).**

    If absEval succeeds in Γ₁ with expression e, and Γ₂ ⊑ Γ₁ (EnvSubTrans),
    then absEval succeeds in Γ₂ with the same expression. Together with
    `monotonicity_trans`, this gives the full "mono + succeed" package.

    **⚠ THIS THEOREM IS FALSE AS STATED.** See `CounterexampleTest.lean` for a
    concrete counterexample where Γ₂ = [(y, λx:Type. z)] (z unbound) and
    Γ₁ = [(y, Type)]. EnvSubTrans holds via `top`, absEval succeeds in Γ₁
    (Type applied = Type) but fails in Γ₂ (z not in scope during beta-reduction).

    The issue: EnvSubTrans has no well-formedness requirement — env values can
    contain free variables not bound in the env. In practice, envs built by
    absEval are well-formed (normalization under binders would have failed for
    unbound vars), but this isn't captured by the theorem's hypotheses.

    **Fix needed:** Add a well-formedness precondition on Γ₂. Options:
    1. `EnvClosed Γ₂` — all free vars in env values are bound in the env
    2. Restrict to envs produced by absEval (specific to each use site)
    3. Require `∀ x τ, Γ₂.lookup x = some τ → ∃ τ', absEval fuel Γ₂ τ = some τ'`

    **Current use site** (soundnessC_direct lam case): Γ₂ comes from readback,
    which guarantees well-formedness by construction. So the fix is tractable.

    **Status:** All cases proved EXCEPT app-lam. The sorry is specifically for:
    when f evaluates to a lambda in Γ₂ but to Type in Γ₁, there's no Γ₁-side
    body evaluation to bootstrap from. -/
theorem absEval_succeeds_envsub
    (fuel : Nat) (Γ₁ Γ₂ : Env) (e τ₁ : Expr)
    (h_env : EnvSubTrans Γ₂ Γ₁)
    (h₁ : absEval fuel Γ₁ e = some τ₁)
    : ∃ τ₂, absEval fuel Γ₂ e = some τ₂ := by
  induction fuel generalizing Γ₁ Γ₂ e τ₁ with
  | zero => simp [absEval] at h₁
  | succ n ih =>
    cases e with
    | var x =>
      simp only [absEval] at h₁ ⊢
      obtain ⟨τ₂, h_l2, _⟩ := h_env x τ₁ h₁
      exact ⟨τ₂, h_l2⟩
    | type =>
      exact ⟨.type, rfl⟩
    | lam x dom body =>
      simp only [absEval] at h₁ ⊢
      cases hb₁ : absEval n ((x, .var x) :: Γ₁) body with
      | none => simp [hb₁] at h₁
      | some body₁' =>
        have ⟨body₂', hb₂⟩ := ih ((x, .var x) :: Γ₁) ((x, .var x) :: Γ₂) body body₁'
          (envSubTrans_extend h_env x (.var x)) hb₁
        rw [hb₂]; exact ⟨_, rfl⟩
    | asc term ty =>
      simp only [absEval] at h₁ ⊢
      exact ih Γ₁ Γ₂ ty τ₁ h_env h₁
    | iota x body =>
      simp only [absEval] at h₁ ⊢
      cases hb₁ : absEval n ((x, .var x) :: Γ₁) body with
      | none => simp [hb₁] at h₁
      | some body₁' =>
        have ⟨body₂', hb₂⟩ := ih ((x, .var x) :: Γ₁) ((x, .var x) :: Γ₂) body body₁'
          (envSubTrans_extend h_env x (.var x)) hb₁
        rw [hb₂]; exact ⟨_, rfl⟩
    | fix inner =>
      simp only [absEval] at h₁ ⊢
      cases inner with
      | lam f dom body =>
        exact ih Γ₁ Γ₂ dom τ₁ h_env h₁
      | _ => simp [absEval] at h₁
    | app f a =>
      simp only [absEval] at h₁ ⊢
      cases hf₁ : absEval n Γ₁ f with
      | none => simp [hf₁] at h₁
      | some τ_f₁ =>
        cases ha₁ : absEval n Γ₁ a with
        | none => simp [hf₁, ha₁] at h₁
        | some τ_a₁ =>
          -- IH: sub-evals succeed in Γ₂
          obtain ⟨τ_f₂, hf₂⟩ := ih Γ₁ Γ₂ f τ_f₁ h_env hf₁
          obtain ⟨τ_a₂, ha₂⟩ := ih Γ₁ Γ₂ a τ_a₁ h_env ha₁
          -- Monotonicity gives shape relationship: τ_f₂ ⊑ τ_f₁
          have h_f_sub := monotonicity_trans Γ₁ Γ₂ f τ_f₁ τ_f₂ n h_env hf₁ hf₂
          rw [hf₁, ha₁] at h₁
          -- Case split on τ_f₂ (which appears in the goal after rw)
          rw [hf₂, ha₂]
          cases τ_f₂ with
          | lam x dom body₂ =>
            -- τ_f₂ is lam → beta-reduce in Γ₂. Need body eval to succeed.
            simp only
            -- Get SubtypeTrans on a for env extension
            have h_a_sub := monotonicity_trans Γ₁ Γ₂ a τ_a₁ τ_a₂ n h_env ha₁ ha₂
            -- SubtypeTrans (lam x dom body₂) τ_f₁ → τ_f₁ = lam x dom body₁ or type
            -- Use lam_lhs to get the two possible shapes of τ_f₁
            -- For now, sorry the whole lam sub-case (needs generalized IH for body₂ ≠ body₁)
            sorry
          | type =>
            simp only; exact ⟨.type, rfl⟩
          | var _ =>
            simp only; exact ⟨_, rfl⟩
          | app _ _ =>
            simp only; exact ⟨_, rfl⟩
          | asc _ _ =>
            simp only; exact ⟨_, rfl⟩
          | fix _ =>
            simp only; exact ⟨_, rfl⟩
          | iota _ _ =>
            simp only; exact ⟨_, rfl⟩
