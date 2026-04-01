import Och.Syntax
import Och.Eval
import Och.Subtyping

/-!
# Monotonicity

Generalized to `absEval_mono` taking `Subtype' e₂ e₁` + `EnvSub Γ₂ Γ₁`.
Standard monotonicity is the corollary with `Subtype'.refl`.

Key technique: removing `trans` from `Subtype'` enables lambda inversion.

## Status after mu unification

absEval now does NOT normalize mu annotations (they pass through unchanged).
This makes the mu case straightforward: mu_body applies directly since both
evaluations produce the same annotation.

The remaining challenge is the mu-app case (mu in function position). absEval
branches on whether the annotation evaluates to a lam:
- Annotation is lam → beta-reduce annotation with arg (fix-like path)
- Annotation is non-lam → unfold body, re-evaluate (iota-like path)

The lam-annotation case is PROVED (both in .refl and .app_cong subcases).
The remaining sorrys are:
- Body-unfold path (needs a substitution congruence lemma for Subtype')
- Cross-cases where envs disagree on annotation shape
- None cases (need absEval_succeeds_envsub)
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

/-- **Generalized monotonicity.**

    absEval does NOT normalize annotations in the mu case, so mu_body
    applies directly (same annotation in both results). The hard remaining
    case is mu in function position (app case), where annotation-based vs
    body-unfolding paths may diverge across envs. The lam-annotation subcase
    is fully proved; remaining subcases need a substitution congruence lemma
    for Subtype' or absEval_succeeds_envsub. -/
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
    -- Helper for stuck app cases: if both sides produce stuck apps
    have stuck_app : ∀ {f₁ f₂ a₁ a₂ : Expr},
        Subtype' f₂ f₁ → Subtype' a₂ a₁ →
        .app f₁ a₁ = τ₁ → .app f₂ a₂ = τ₂ →
        Subtype' τ₂ τ₁ := by
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
              (.refl body) (envSub_extend h_env x (.var x)) hb₁ hb₂)
      | type =>
        simp [absEval] at h₁ h₂; rw [← h₁, ← h₂]; exact .refl .type
      | asc term ty =>
        simp only [absEval] at h₁ h₂
        exact ih _ _ ty ty _ _ (.refl ty) h_env h₁ h₂
      | mu x ann body =>
        -- annotation passes through unchanged → mu_body applies directly
        simp only [absEval] at h₁ h₂
        cases hb₁ : absEval n ((x, .var x) :: Γ₁) body with
        | none => simp [hb₁] at h₁
        | some body₁ =>
          simp [hb₁] at h₁
          cases hb₂ : absEval n ((x, .var x) :: Γ₂) body with
          | none => simp [hb₂] at h₂
          | some body₂ =>
            simp [hb₂] at h₂; rw [← h₁, ← h₂]
            exact .mu_body (ih _ _ body body _ _
              (.refl body) (envSub_extend h_env x (.var x)) hb₁ hb₂)
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
                  obtain ⟨body₂, hf₂_eq, hbody_sub⟩ := Subtype'.lam_rhs_shape hf_sub
                  subst hf₂_eq
                  simp only at h₁ h₂
                  exact ih _ _ body₁ body₂ _ _ hbody_sub
                    (envSub_extend_sub h_env x₁ ha_sub) h₁ h₂
                | mu x_mu ann_mu body_mu =>
                  -- mu in function position: both sides take the mu app path
                  obtain ⟨body₂_mu, hf₂_eq, hbody_mu_sub⟩ := Subtype'.mu_rhs_shape hf_sub
                  subst hf₂_eq
                  -- Both annotations are the SAME (ann_mu) since mu_body preserves ann
                  simp only at h₁ h₂
                  -- Case split on annotation evaluation in both envs
                  cases hann₁ : absEval n Γ₁ ann_mu with
                  | none =>
                    rw [hann₁] at h₁
                    -- Γ₁ ann fails → body unfold path for Γ₁
                    cases hann₂ : absEval n Γ₂ ann_mu with
                    | none =>
                      rw [hann₂] at h₂
                      sorry -- both ann fail: body unfold path for both
                    | some ann₂_val =>
                      rw [hann₂] at h₂
                      sorry -- Γ₁ ann fails, Γ₂ ann succeeds
                  | some ann₁_val =>
                    rw [hann₁] at h₁
                    cases hann₂ : absEval n Γ₂ ann_mu with
                    | none =>
                      rw [hann₂] at h₂
                      sorry -- Γ₁ ann succeeds, Γ₂ ann fails
                    | some ann₂_val =>
                      rw [hann₂] at h₂
                      have hann_sub := ih _ _ ann_mu ann_mu ann₁_val ann₂_val (.refl ann_mu) h_env hann₁ hann₂
                      cases ann₁_val with
                      | lam y₁ dom₁ retBody₁ =>
                        -- Γ₁ annotation is lam → by lam_rhs_shape, Γ₂ is also lam
                        obtain ⟨retBody₂, hann₂_eq, hret_sub⟩ := Subtype'.lam_rhs_shape hann_sub
                        subst hann₂_eq
                        -- Both take annotation path: beta-reduce ann with arg
                        simp only at h₁ h₂
                        exact ih _ _ retBody₁ retBody₂ _ _ hret_sub
                          (envSub_extend_sub h_env y₁ ha_sub) h₁ h₂
                      | _ =>
                        -- ann₁ not lam → check ann₂
                        simp only at h₁
                        cases ann₂_val with
                        | lam y₂ dom₂ retBody₂ =>
                          -- ann₂ is lam but ann₁ isn't. By Subtype', lam ⊑ non-lam
                          -- only possible if ann₁ = type (via .top)
                          sorry -- cross case: Γ₂ ann=lam, Γ₁ ann=non-lam
                        | _ =>
                          -- Neither is lam → both take body unfold path
                          simp only at h₂
                          sorry -- both non-lam: body unfold for both
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
              | mu x_mu ann_mu body_mu =>
                obtain ⟨body₂_mu, hf₂_eq, hbody_mu_sub⟩ := Subtype'.mu_rhs_shape hf_sub
                subst hf₂_eq
                simp only at h₁ h₂
                -- Case split on annotation evaluation in both envs
                cases hann₁ : absEval n Γ₁ ann_mu with
                | none =>
                  rw [hann₁] at h₁
                  cases hann₂ : absEval n Γ₂ ann_mu with
                  | none =>
                    rw [hann₂] at h₂
                    sorry -- both ann fail: body unfold path for both
                  | some ann₂_val =>
                    rw [hann₂] at h₂
                    sorry -- Γ₁ ann fails, Γ₂ ann succeeds
                | some ann₁_val =>
                  rw [hann₁] at h₁
                  cases hann₂ : absEval n Γ₂ ann_mu with
                  | none =>
                    rw [hann₂] at h₂
                    sorry -- Γ₁ ann succeeds, Γ₂ ann fails
                  | some ann₂_val =>
                    rw [hann₂] at h₂
                    have hann_sub := ih _ _ ann_mu ann_mu ann₁_val ann₂_val (.refl ann_mu) h_env hann₁ hann₂
                    cases ann₁_val with
                    | lam y₁ dom₁ retBody₁ =>
                      obtain ⟨retBody₂, hann₂_eq, hret_sub⟩ := Subtype'.lam_rhs_shape hann_sub
                      subst hann₂_eq
                      simp only at h₁ h₂
                      exact ih _ _ retBody₁ retBody₂ _ _ hret_sub
                        (envSub_extend_sub h_env y₁ ha_sub) h₁ h₂
                    | _ =>
                      simp only at h₁
                      cases ann₂_val with
                      | lam y₂ dom₂ retBody₂ =>
                        sorry -- cross case: Γ₂ ann=lam, Γ₁ ann=non-lam
                      | _ =>
                        simp only at h₂
                        sorry -- both non-lam: body unfold for both
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
      simp only [absEval] at h₁ h₂
      cases hb₁ : absEval n ((x, .var x) :: Γ₁) body₁ with
      | none => simp [hb₁] at h₁
      | some body₁' =>
        simp [hb₁] at h₁
        cases hb₂ : absEval n ((x, .var x) :: Γ₂) body₂ with
        | none => simp [hb₂] at h₂
        | some body₂' =>
          simp [hb₂] at h₂; rw [← h₁, ← h₂]
          exact .mu_body (ih _ _ body₁ body₂ _ _ hbody
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

/-- **Generalized monotonicity with SubtypeTrans.** Sorry'd — depends on
    absEval_mono being fully proved. -/
theorem absEval_mono_trans
    (fuel : Nat) (Γ₁ Γ₂ : Env) (e₁ e₂ τ₁ τ₂ : Expr)
    (h_sub : SubtypeTrans e₂ e₁)
    (h_env : EnvSubTrans Γ₂ Γ₁)
    (h₁ : absEval fuel Γ₁ e₁ = some τ₁)
    (h₂ : absEval fuel Γ₂ e₂ = some τ₂)
    : SubtypeTrans τ₂ τ₁ := by
  sorry

/-- Standard monotonicity corollary with SubtypeTrans envs. -/
theorem monotonicity_trans
    (Γ₁ Γ₂ : Env) (e τ₁ τ₂ : Expr) (fuel : Nat)
    (h_env : EnvSubTrans Γ₂ Γ₁)
    (h_abs₁ : absEval fuel Γ₁ e = some τ₁)
    (h_abs₂ : absEval fuel Γ₂ e = some τ₂)
    : SubtypeTrans τ₂ τ₁ :=
  absEval_mono_trans fuel Γ₁ Γ₂ e e τ₁ τ₂ (SubtypeTrans.step (Subtype'.refl e))
    h_env h_abs₁ h_abs₂

/-- **Totality under env narrowing.** Sorry'd — was already sorry'd before mu.
    Needed for the mu-app none cases in absEval_mono. -/
theorem absEval_succeeds_envsub
    (fuel : Nat) (Γ₁ Γ₂ : Env) (e τ₁ : Expr)
    (h_env : EnvSubTrans Γ₂ Γ₁)
    (h₁ : absEval fuel Γ₁ e = some τ₁)
    : ∃ τ₂, absEval fuel Γ₂ e = some τ₂ := by
  sorry

-- ============================================================
-- evalFreeVars coverage: absEval outputs have evalFreeVars ⊆ neutralVars(Γ)
-- ============================================================

/-- A variable is "neutral" in an env if it maps to itself. -/
def isNeutral (Γ : Env) (x : Name) : Prop :=
  Γ.lookup x = some (.var x)

/-- An env is "eval-closed" if every env value's evalFreeVars are neutral. -/
def EnvEvalClosed' (Γ : Env) : Prop :=
  ∀ x v, Γ.lookup x = some v → ∀ y, y ∈ v.evalFreeVars → isNeutral Γ y

/-- Extending an eval-closed env with a neutral binding preserves closedness. -/
theorem envEvalClosed'_extend_neutral {Γ : Env} (h : EnvEvalClosed' Γ) (x : Name) :
    EnvEvalClosed' ((x, .var x) :: Γ) := by
  intro y v h_lookup z h_z_free
  simp only [Env.lookup] at h_lookup
  simp only [isNeutral, Env.lookup]
  split at h_lookup <;> rename_i h_eq
  · cases h_lookup
    simp [Expr.evalFreeVars] at h_z_free
    subst h_z_free
    simp [h_eq]
  · have h_neutral := h y v h_lookup z h_z_free
    simp only [isNeutral, Env.lookup] at h_neutral
    split
    · rename_i h_zx
      have : x = z := by exact beq_iff_eq.mp h_zx
      rw [this]
    · exact h_neutral

/-- Helper: extending env with neutral binding preserves eval-coverage for P ∨ (· = x). -/
private theorem env_extend_neutral_or (Γ : Env) (x : Name) (P : Name → Prop)
    (h_env : ∀ z v, Γ.lookup z = some v → ∀ w, w ∈ v.evalFreeVars → P w) :
    ∀ z v, Env.lookup ((x, .var x) :: Γ) z = some v →
    ∀ w, w ∈ v.evalFreeVars → P w ∨ w = x := by
  intro z v h_lookup w hw
  simp only [Env.lookup] at h_lookup
  split at h_lookup <;> rename_i h_eq
  · cases h_lookup; simp [Expr.evalFreeVars] at hw; exact Or.inr hw
  · exact Or.inl (h_env z v h_lookup w hw)

/-- Helper: extending env with a value whose evalFreeVars ⊆ P preserves coverage. -/
private theorem env_extend_val (Γ : Env) (x : Name) (v : Expr) (P : Name → Prop)
    (h_env : ∀ z u, Γ.lookup z = some u → ∀ w, w ∈ u.evalFreeVars → P w)
    (hv : ∀ w, w ∈ v.evalFreeVars → P w) :
    ∀ z u, Env.lookup ((x, v) :: Γ) z = some u → ∀ w, w ∈ u.evalFreeVars → P w := by
  intro z u h_lookup w hw
  simp only [Env.lookup] at h_lookup
  split at h_lookup <;> rename_i h_eq
  · cases h_lookup; exact hv w hw
  · exact h_env z u h_lookup w hw

/-- **General coverage: absEval outputs have evalFreeVars ⊆ P.** -/
theorem absEval_evalFreeVars_general
    (fuel : Nat) (Γ : Env) (e τ : Expr)
    (P : Name → Prop)
    (h_eval : absEval fuel Γ e = some τ)
    (h_env : ∀ x v, Γ.lookup x = some v → ∀ y, y ∈ v.evalFreeVars → P y)
    : ∀ y, y ∈ τ.evalFreeVars → P y := by
  induction fuel generalizing Γ e τ P with
  | zero => simp [absEval] at h_eval
  | succ n ih =>
    -- Helper for binder cases (lam body, mu body): body normalized under (x, var x),
    -- result's evalFreeVars = body'.evalFreeVars.filter(·!=x) ⊆ P.
    have binder_case : ∀ (x : Name) (body body' : Expr),
        absEval n ((x, .var x) :: Γ) body = some body' →
        ∀ y, y ∈ body'.evalFreeVars.filter (· != x) → P y := by
      intro x body body' hb y hy
      have ⟨h_mem, h_ne⟩ := List.mem_filter.mp hy
      have ih_body := ih ((x, .var x) :: Γ) body body' (fun z => P z ∨ z = x) hb
        (env_extend_neutral_or Γ x P h_env) y h_mem
      cases ih_body with
      | inl h => exact h
      | inr h =>
        exfalso
        have h_ne' : ¬(y == x) = true := by
          intro heq; rw [beq_iff_eq.mp heq] at h_ne; simp at h_ne
        exact h_ne' (beq_iff_eq.mpr h)
    cases e with
    | var x =>
      simp only [absEval] at h_eval
      exact h_env x τ h_eval
    | type =>
      simp only [absEval] at h_eval; cases h_eval
      intro y hy; simp [Expr.evalFreeVars] at hy
    | asc _term ty =>
      simp only [absEval] at h_eval
      exact ih Γ ty τ P h_eval h_env
    | lam x _dom body =>
      simp only [absEval] at h_eval
      cases hb : absEval n ((x, .var x) :: Γ) body with
      | none => simp [hb] at h_eval
      | some body' =>
        simp [hb] at h_eval; cases h_eval
        -- evalFreeVars(.lam x _dom body') = body'.evalFreeVars.filter(·!=x)
        exact binder_case x body body' hb
    | mu x ann body =>
      simp only [absEval] at h_eval
      cases hb : absEval n ((x, .var x) :: Γ) body with
      | none => simp [hb] at h_eval
      | some body' =>
        simp [hb] at h_eval; cases h_eval
        -- evalFreeVars(.mu x ann body') = body'.evalFreeVars.filter(·!=x)
        exact binder_case x body body' hb
    | app f a =>
      simp only [absEval] at h_eval
      cases hf : absEval n Γ f with
      | none => simp [hf] at h_eval
      | some τ_f =>
        cases ha : absEval n Γ a with
        | none => simp [hf, ha] at h_eval
        | some τ_a =>
          rw [hf, ha] at h_eval
          have ih_f := ih Γ f τ_f P hf h_env
          have ih_a := ih Γ a τ_a P ha h_env
          cases τ_f with
          | lam x _dom body =>
            simp only at h_eval
            exact ih ((x, τ_a) :: Γ) body τ P h_eval
              (env_extend_val Γ x τ_a P h_env ih_a)
          | type =>
            simp only at h_eval; cases h_eval
            intro y hy; simp [Expr.evalFreeVars] at hy
          | mu x_mu ann_mu body_mu =>
            -- mu-elim: annotation-first approach, then fallback to body unfolding.
            -- First, try using the annotation.
            simp only at h_eval
            -- Split on absEval n Γ ann_mu
            split at h_eval
            · -- Annotation evaluates to a lambda: beta-reduce with arg
              exact ih _ _ τ P h_eval (env_extend_val Γ _ τ_a P h_env ih_a)
            · -- Annotation not a lambda: fallback to body unfolding
              -- Split on absEval n Γ (body_mu.subst x_mu (.mu x_mu ann_mu body_mu))
              split at h_eval
              · -- Unfolded body is a lambda: beta-reduce with arg
                exact ih _ _ τ P h_eval (env_extend_val Γ _ τ_a P h_env ih_a)
              · -- Unfolded body is .type
                cases h_eval; intro z hz; simp [Expr.evalFreeVars] at hz
              · -- Unfolded body is something else: stuck application
                rename_i _ _ _ fVal _ _ hunf_eval
                cases h_eval
                intro z hz
                rcases List.mem_append.mp hz with h1 | h2
                · exact ih Γ _ fVal P hunf_eval h_env z h1
                · exact ih_a z h2
              · -- Unfolded body eval failed: contradiction with h_eval
                exact absurd h_eval (by simp)
          | var _ =>
            simp only at h_eval; cases h_eval
            intro y hy
            rcases List.mem_append.mp hy with h1 | h2
            · exact ih_f y h1
            · exact ih_a y h2
          | app _ _ =>
            simp only at h_eval; cases h_eval
            intro y hy
            rcases List.mem_append.mp hy with h1 | h2
            · exact ih_f y h1
            · exact ih_a y h2
          | asc _ _ =>
            simp only at h_eval; cases h_eval
            intro y hy
            rcases List.mem_append.mp hy with h1 | h2
            · exact ih_f y h1
            · exact ih_a y h2

/-- **absEval outputs have evalFreeVars ⊆ neutralVars(Γ).** -/
theorem absEval_evalFreeVars_neutral
    (fuel : Nat) (Γ : Env) (e τ : Expr)
    (h_eval : absEval fuel Γ e = some τ)
    (h_env : EnvEvalClosed' Γ)
    : ∀ y, y ∈ τ.evalFreeVars → isNeutral Γ y :=
  absEval_evalFreeVars_general fuel Γ e τ (isNeutral Γ) h_eval h_env
