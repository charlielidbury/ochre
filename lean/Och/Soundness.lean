import Och.Syntax
import Och.Eval
import Och.Subtyping
import Och.Monotonicity

/-!
# Soundness

If abstract evaluation says `e` has type `τ`, and concrete evaluation
produces value `v`, then `v ⊑ τ` (in SubtypeTrans).

The proof uses a generalized `soundness_gen` that takes `SubtypeTrans e_c e_a`
(related expressions) since the app-beta case produces different normalized
bodies from the function IH.

## Status after mu unification

The soundness proof is PARTIALLY PROVED. All non-mu cases are done:
- var, lam, type, asc: direct from env consistency / IH / WellTyped
- app-lam: SubtypeTrans.lam_target_shape inverts concrete function,
  IH on bodies with envConsistent_extend_sub
- app-stuck: SubtypeTrans.app_cong on stuck applications
- lam_body, app_cong: same as refl counterparts

Five sorrys remain, ALL mu-related or the SubtypeTrans.trans case.
The fundamental blocker: EnvConsistent requires SubtypeTrans (mu value)
(var x), but no such constructor exists. See DECISION-LOG.md for
analysis of three possible approaches.
-/

open Expr

def EnvConsistent (γ : Env) (Γ : Env) : Prop :=
  ∀ x τ, Γ.lookup x = some τ → ∃ v, γ.lookup x = some v ∧ SubtypeTrans v τ

/-- Well-typedness: all ascriptions encountered during evaluation are sound. -/
def WellTyped (fuel : Nat) (Γ : Env) (e : Expr) : Prop :=
  match fuel with
  | 0 => True
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
    | .mu x _ann body =>
        -- mu well-typedness: body is well-typed under (x, var x)
        WellTyped fuel ((x, .var x) :: Γ) body
    | .app f a =>
        WellTyped fuel Γ f ∧ WellTyped fuel Γ a ∧
        match absEval fuel Γ f, absEval fuel Γ a with
        | some (.lam x _ body), some aVal => WellTyped fuel ((x, aVal) :: Γ) body
        | _, _ => True

theorem envConsistent_extend {γ Γ : Env} (h : EnvConsistent γ Γ) (x : Name) (v : Expr) :
    EnvConsistent ((x, v) :: γ) ((x, v) :: Γ) := by
  intro y τ h_lookup
  simp only [Env.lookup] at h_lookup ⊢
  split at h_lookup <;> split
  · cases h_lookup; exact ⟨v, rfl, SubtypeTrans.step (Subtype'.refl v)⟩
  · rename_i h1 h2; exact absurd h1 h2
  · rename_i h1 h2; exact absurd h2 h1
  · exact h y τ h_lookup

theorem envConsistent_extend_sub {γ Γ : Env} (h : EnvConsistent γ Γ)
    (x : Name) {v τ : Expr} (hv : SubtypeTrans v τ) :
    EnvConsistent ((x, v) :: γ) ((x, τ) :: Γ) := by
  intro y σ h_lookup
  simp only [Env.lookup] at h_lookup ⊢
  split at h_lookup <;> split
  · cases h_lookup; exact ⟨v, rfl, hv⟩
  · rename_i h1 h2; exact absurd h1 h2
  · rename_i h1 h2; exact absurd h2 h1
  · exact h y σ h_lookup

/-- **Generalized soundness.** Proves that if abstract evaluation gives type `τ`
    and concrete evaluation gives value `v`, then `SubtypeTrans v τ`.

    The proof is generalized over `SubtypeTrans e_c e_a` (not just same expression)
    because the app-beta case produces different bodies from each evaluation mode.

    ## Proved cases
    - var, lam, type, asc: fully proved
    - app with lam in function position: fully proved
    - app with stuck function (var, app, asc): fully proved
    - app with type in function position: fully proved

    ## Sorry'd cases
    - **mu (standalone):** abstract eval binds x to neutral (var x), concrete eval
      binds x to the mu value itself. Cannot establish EnvConsistent for these
      extended envs because there's no SubtypeTrans (mu ...) (var x). Needs either:
      (a) step-indexed logical relation instead of SubtypeTrans, or
      (b) self-intro rule in Subtype'/SubtypeTrans, or
      (c) changed absEval mu semantics.
    - **mu-app:** concEval unrolls the mu then applies; absEval uses the
      annotation or body-unfold. Fundamentally different computation paths.
    - **trans:** needs intermediate expression to evaluate in both modes.
      Similar to the false absEval_succeeds_envsub (see CounterexampleTest.lean).
    - **lam_body/app_cong/mu_body in h_sub:** Same as their refl counterparts. -/
theorem soundness_gen
    (fuel : Nat) (Γ : Env) (γ : Env) (e_a e_c τ v : Expr)
    (h_sub : SubtypeTrans e_c e_a)
    (h_abs : absEval fuel Γ e_a = some τ)
    (h_conc : concEval fuel γ e_c = some v)
    (h_env : EnvConsistent γ Γ)
    (h_wt : WellTyped fuel Γ e_a)
    : SubtypeTrans v τ := by
  induction fuel generalizing Γ γ e_a e_c τ v with
  | zero => simp [absEval] at h_abs
  | succ n ih =>
    cases h_sub with
    | trans _ _ =>
      -- BLOCKED: SubtypeTrans e_c b and SubtypeTrans b e_a.
      -- Need b to evaluate in both modes (abstract and concrete).
      -- Without well-formedness guarantees on intermediate expressions,
      -- this cannot be closed. See CounterexampleTest.lean for why
      -- totality-under-subtyping is false in general.
      sorry
    | step h_step =>
      cases h_step with
      | top e =>
        simp [absEval] at h_abs; rw [← h_abs]; exact .step (.top v)
      | refl =>
        cases e_a with
        | var x =>
          simp [absEval] at h_abs
          simp [concEval] at h_conc
          have ⟨v', hv', hsub⟩ := h_env x τ h_abs
          rw [hv'] at h_conc; cases h_conc; exact hsub
        | type =>
          simp [absEval] at h_abs; simp [concEval] at h_conc
          rw [← h_abs, ← h_conc]; exact .step (.refl .type)
        | lam x dom body =>
          simp only [absEval] at h_abs
          simp only [concEval] at h_conc
          cases hba : absEval n ((x, .var x) :: Γ) body with
          | none => simp [hba] at h_abs
          | some body_a =>
            simp [hba] at h_abs
            cases hbc : concEval n ((x, .var x) :: γ) body with
            | none => simp [hbc] at h_conc
            | some body_c =>
              simp [hbc] at h_conc
              rw [← h_abs, ← h_conc]
              exact SubtypeTrans.lam_body (ih _ _ body body body_a body_c
                (.step (.refl body)) hba hbc
                (envConsistent_extend h_env x (.var x))
                (by simp only [WellTyped] at h_wt; exact h_wt))
        | asc term ty =>
          simp only [absEval] at h_abs
          simp only [concEval] at h_conc
          -- WellTyped gives intermediate type σ with Subtype' σ τ
          simp only [WellTyped] at h_wt
          obtain ⟨h_wt_term, _, σ, τ', h_abs_term, h_abs_ty, h_sub_σ_τ⟩ := h_wt
          rw [h_abs_ty] at h_abs; cases h_abs
          -- IH on term: SubtypeTrans v σ
          exact .trans
            (ih _ _ term term σ v (.step (.refl term)) h_abs_term h_conc h_env h_wt_term)
            (.step h_sub_σ_τ)
        | mu x ann body =>
          -- BLOCKED: env consistency for self-referential binding.
          -- concEval: body with x ↦ mu x ann body (the actual value)
          -- absEval: body with x ↦ var x (neutral), returns mu x ann body'
          -- Need SubtypeTrans (mu x ann body) (var x) which doesn't exist.
          sorry
        | app f a =>
          simp only [absEval] at h_abs
          simp only [concEval] at h_conc
          cases hfa : absEval n Γ f with
          | none => simp [hfa] at h_abs
          | some f_t =>
            cases haa : absEval n Γ a with
            | none => simp [hfa, haa] at h_abs
            | some a_t =>
              rw [hfa, haa] at h_abs
              cases hfc : concEval n γ f with
              | none => simp [hfc] at h_conc
              | some f_v =>
                cases hac : concEval n γ a with
                | none => simp [hfc, hac] at h_conc
                | some a_v =>
                  rw [hfc, hac] at h_conc
                  have hf_sub := ih _ _ f f f_t f_v (.step (.refl f)) hfa hfc h_env
                    (by simp only [WellTyped] at h_wt; exact h_wt.1)
                  have ha_sub := ih _ _ a a a_t a_v (.step (.refl a)) haa hac h_env
                    (by simp only [WellTyped] at h_wt; exact h_wt.2.1)
                  -- Case split on abstract function result
                  cases f_t with
                  | type =>
                    simp only at h_abs; cases h_abs; exact .step (.top v)
                  | lam x dom body_a =>
                    obtain ⟨body_c, hfv_eq, hbody_sub⟩ := SubtypeTrans.lam_target_shape hf_sub
                    subst hfv_eq; simp only at h_abs h_conc
                    have h_wt_body : WellTyped n ((x, a_t) :: Γ) body_a := by
                      simp only [WellTyped] at h_wt
                      obtain ⟨_, _, h3⟩ := h_wt
                      rw [hfa, haa] at h3; exact h3
                    exact ih _ _ body_a body_c τ v hbody_sub h_abs h_conc
                      (envConsistent_extend_sub h_env x ha_sub) h_wt_body
                  | mu _ _ _ => sorry  -- mu-app: see docstring
                  | var v_name =>
                    have := SubtypeTrans.var_target hf_sub; subst this
                    simp only at h_abs h_conc; cases h_abs; cases h_conc
                    exact SubtypeTrans.app_cong hf_sub ha_sub
                  | app f' a' =>
                    obtain ⟨_, _, hfv_eq, _, _⟩ := SubtypeTrans.app_target_shape hf_sub
                    subst hfv_eq; simp only at h_abs h_conc; cases h_abs; cases h_conc
                    exact SubtypeTrans.app_cong hf_sub ha_sub
                  | asc t ty =>
                    have := SubtypeTrans.asc_target hf_sub; subst this
                    simp only at h_abs h_conc; cases h_abs; cases h_conc
                    exact SubtypeTrans.app_cong hf_sub ha_sub
      | lam_body hbody =>
        rename_i x dom body_a body_c
        simp only [absEval] at h_abs
        simp only [concEval] at h_conc
        cases hba : absEval n ((x, .var x) :: Γ) body_a with
        | none => simp [hba] at h_abs
        | some body_a' =>
          simp [hba] at h_abs
          cases hbc : concEval n ((x, .var x) :: γ) body_c with
          | none => simp [hbc] at h_conc
          | some body_c' =>
            simp [hbc] at h_conc
            rw [← h_abs, ← h_conc]
            exact SubtypeTrans.lam_body (ih _ _ body_a body_c body_a' body_c'
              (.step hbody) hba hbc
              (envConsistent_extend h_env x (.var x))
              (by simp only [WellTyped] at h_wt; exact h_wt))
      | app_cong hf ha =>
        rename_i f_a f_c a_a a_c
        simp only [absEval] at h_abs
        simp only [concEval] at h_conc
        cases hfa : absEval n Γ f_a with
        | none => simp [hfa] at h_abs
        | some f_t =>
          cases haa : absEval n Γ a_a with
          | none => simp [hfa, haa] at h_abs
          | some a_t =>
            rw [hfa, haa] at h_abs
            cases hfc : concEval n γ f_c with
            | none => simp [hfc] at h_conc
            | some f_v =>
              cases hac : concEval n γ a_c with
              | none => simp [hfc, hac] at h_conc
              | some a_v =>
                rw [hfc, hac] at h_conc
                have hf_sub := ih _ _ f_a f_c f_t f_v (.step hf) hfa hfc h_env
                  (by simp only [WellTyped] at h_wt; exact h_wt.1)
                have ha_sub := ih _ _ a_a a_c a_t a_v (.step ha) haa hac h_env
                  (by simp only [WellTyped] at h_wt; exact h_wt.2.1)
                -- Case split on abstract function result (same as refl app)
                cases f_t with
                | type =>
                  simp only at h_abs; cases h_abs; exact .step (.top v)
                | lam x dom body_a =>
                  obtain ⟨body_c, hfv_eq, hbody_sub⟩ := SubtypeTrans.lam_target_shape hf_sub
                  subst hfv_eq; simp only at h_abs h_conc
                  have h_wt_body : WellTyped n ((x, a_t) :: Γ) body_a := by
                    simp only [WellTyped] at h_wt
                    obtain ⟨_, _, h3⟩ := h_wt
                    rw [hfa, haa] at h3; exact h3
                  exact ih _ _ body_a body_c τ v hbody_sub h_abs h_conc
                    (envConsistent_extend_sub h_env x ha_sub) h_wt_body
                | mu _ _ _ => sorry  -- mu-app: see docstring
                | var v_name =>
                  have := SubtypeTrans.var_target hf_sub; subst this
                  simp only at h_abs h_conc; cases h_abs; cases h_conc
                  exact SubtypeTrans.app_cong hf_sub ha_sub
                | app f' a' =>
                  obtain ⟨_, _, hfv_eq, _, _⟩ := SubtypeTrans.app_target_shape hf_sub
                  subst hfv_eq; simp only at h_abs h_conc; cases h_abs; cases h_conc
                  exact SubtypeTrans.app_cong hf_sub ha_sub
                | asc t ty =>
                  have := SubtypeTrans.asc_target hf_sub; subst this
                  simp only at h_abs h_conc; cases h_abs; cases h_conc
                  exact SubtypeTrans.app_cong hf_sub ha_sub
      | mu_body _ =>
        -- Same env consistency issue as refl mu case
        sorry

/-- **Soundness theorem.**

    If abstract evaluation gives type `τ` and concrete evaluation gives value `v`,
    then `SubtypeTrans v τ`. -/
theorem soundness
    (Γ : Env) (γ : Env) (e τ v : Expr) (fuel : Nat)
    (h_abs : absEval fuel Γ e = some τ)
    (h_conc : concEval fuel γ e = some v)
    (h_env : EnvConsistent γ Γ)
    (h_wt : WellTyped fuel Γ e)
    : SubtypeTrans v τ :=
  soundness_gen fuel Γ γ e e τ v (SubtypeTrans.step (Subtype'.refl e))
    h_abs h_conc h_env h_wt
