import Och.Syntax
import Och.Eval
import Och.Subtyping
import Och.Monotonicity

/-!
# Soundness

If abstract evaluation says `e` has type `τ`, and concrete evaluation
produces value `v`, then `v ⊑ τ` (in Subtype').

**Architecture:** soundness_gen uses `SubtypeCore` (Subtype' without
self_intro) for both input h_sub and output. This eliminates the
self_intro case entirely — SubtypeCore has no self_intro constructor,
so the case doesn't exist. The main `soundness` theorem converts
the SubtypeCore output to Subtype' via `toSubtype'`.

**Trade-off:** WellTyped's asc case uses SubtypeCore instead of Subtype'.
This means programs with ascriptions like `(e : mu_type)` where the
subtyping proof requires self_intro are not covered. This is acceptable
for now; strengthening to Subtype' requires step-indexed logical relations.

The proof uses a generalized `soundness_gen` that takes `SubtypeCore e_c e_a`
(related expressions) since the app-beta case produces different normalized
bodies from the function IH.

## Status

**SORRY-FREE.** soundness_gen is fully proved.

**Key proof techniques:**
- SubtypeCore (Subtype' without self_intro) for both input and output
- absEval's mu-app uses joint match `(ann, body)`: annotation path only
  when both are lambdas, body-direct path otherwise. This makes absEval
  structurally parallel to concEval for all non-annotation cases.
- Annotation consistency in WellTyped: when both ann and body are lambdas,
  the body's absEval result must SubtypeCore the annotation's return body.
- WellTyped propagation for body-unfold: when body is a lambda (but ann isn't),
  WellTyped requires well-typedness of the body under the argument binding.

**Proved cases:**
- var, lam, type, asc: direct from env consistency / IH / WellTyped
- app-lam: SubtypeCore.lam_rhs_shape inverts concrete function
- app-stuck: direct SubtypeCore case analysis
- mu standalone: mu_body (both evaluators wrap mu results)
- mu_body: mu_body (parallel structure from wrapping)
- lam_body, app_cong: handled via SubtypeCore structure
- mu-app annotation path (ann=lam, body=lam): via annotation consistency
- mu-app body-unfold (ann≠lam or body≠lam): parallel to concEval
-/

open Expr

def EnvConsistent (γ : Env) (Γ : Env) : Prop :=
  ∀ x τ, Γ.lookup x = some τ → ∃ v, γ.lookup x = some v ∧ SubtypeCore v τ

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
                SubtypeCore σ τ'
    | .mu x ann body =>
        WellTyped fuel ((x, .mu x ann body) :: Γ) body
    | .app f a =>
        WellTyped fuel Γ f ∧ WellTyped fuel Γ a ∧
        match absEval fuel Γ f, absEval fuel Γ a with
        | some (.lam x _ body), some aVal => WellTyped fuel ((x, aVal) :: Γ) body
        | some (.mu _x_mu ann body_mu), some aVal =>
          match ann, body_mu with
          | .lam y_ann _dom_ann retBody, .lam y_body _dom_body bodyRes =>
              -- Annotation path: ann and body both lambdas.
              -- Annotation consistency bridges concEval (uses body) and absEval (uses ann).
              y_ann = y_body ∧
              WellTyped fuel ((y_ann, aVal) :: Γ) bodyRes ∧
              WellTyped fuel ((y_ann, aVal) :: Γ) retBody ∧
              ∃ v_body τ_ann,
                absEval fuel ((y_ann, aVal) :: Γ) bodyRes = some v_body ∧
                absEval fuel ((y_ann, aVal) :: Γ) retBody = some τ_ann ∧
                SubtypeCore v_body τ_ann
          | .lam y_ann _dom_ann retBody, _ =>
              -- Annotation path with non-lambda body: absEval uses annotation.
              WellTyped fuel ((y_ann, aVal) :: Γ) retBody
          | _, .lam y_body _dom_body bodyRes =>
              -- Body-unfold path with lambda body: absEval matches body directly.
              WellTyped fuel ((y_body, aVal) :: Γ) bodyRes
          | _, _ => True
        | _, _ => True

theorem envConsistent_extend {γ Γ : Env} (h : EnvConsistent γ Γ) (x : Name) (v : Expr) :
    EnvConsistent ((x, v) :: γ) ((x, v) :: Γ) := by
  intro y τ h_lookup
  simp only [Env.lookup] at h_lookup ⊢
  split at h_lookup <;> split
  · cases h_lookup; exact ⟨v, rfl, SubtypeCore.refl v⟩
  · rename_i h1 h2; exact absurd h1 h2
  · rename_i h1 h2; exact absurd h2 h1
  · exact h y τ h_lookup

theorem envConsistent_extend_sub {γ Γ : Env} (h : EnvConsistent γ Γ)
    (x : Name) {v τ : Expr} (hv : SubtypeCore v τ) :
    EnvConsistent ((x, v) :: γ) ((x, τ) :: Γ) := by
  intro y σ h_lookup
  simp only [Env.lookup] at h_lookup ⊢
  split at h_lookup <;> split
  · cases h_lookup; exact ⟨v, rfl, hv⟩
  · rename_i h1 h2; exact absurd h1 h2
  · rename_i h1 h2; exact absurd h2 h1
  · exact h y σ h_lookup

/-- **Generalized soundness.** Proves that if abstract evaluation gives type `τ`
    and concrete evaluation gives value `v`, then `SubtypeCore v τ`.

    Uses SubtypeCore (Subtype' without self_intro) for both input and output.
    This eliminates the self_intro case entirely — SubtypeCore has no self_intro
    constructor. The main `soundness` theorem converts via `toSubtype'`.

    **SORRY-FREE.** All cases proved. The mu-app case uses the joint
    `match ann, body` structure: annotation path when both are lambdas
    (via annotation consistency), body-direct path otherwise (parallel
    to concEval). -/
theorem soundness_gen
    (fuel : Nat) (Γ : Env) (γ : Env) (e_a e_c τ v : Expr)
    (h_sub : SubtypeCore e_c e_a)
    (h_abs : absEval fuel Γ e_a = some τ)
    (h_conc : concEval fuel γ e_c = some v)
    (h_env : EnvConsistent γ Γ)
    (h_wt : WellTyped fuel Γ e_a)
    : SubtypeCore v τ := by
  induction fuel generalizing Γ γ e_a e_c τ v with
  | zero => simp [absEval] at h_abs
  | succ n ih =>
    cases h_sub with
    | top e =>
      -- e_a = type. absEval type = type.
      simp [absEval] at h_abs; rw [← h_abs]; exact .top v
    | refl =>
      -- e_c = e_a. Standard case: same expression in both modes.
      cases e_a with
      | var x =>
        simp [absEval] at h_abs
        simp [concEval] at h_conc
        have ⟨v', hv', hsub⟩ := h_env x τ h_abs
        rw [hv'] at h_conc; cases h_conc; exact hsub
      | type =>
        simp [absEval] at h_abs; simp [concEval] at h_conc
        rw [← h_abs, ← h_conc]; exact .refl .type
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
            exact .lam_body (ih _ _ body body body_a body_c
              (.refl body) hba hbc
              (envConsistent_extend h_env x (.var x))
              (by simp only [WellTyped] at h_wt; exact h_wt))
      | asc term ty =>
        simp only [absEval] at h_abs
        simp only [concEval] at h_conc
        simp only [WellTyped] at h_wt
        obtain ⟨h_wt_term, _, σ, τ', h_abs_term, h_abs_ty, h_sub_σ_τ⟩ := h_wt
        rw [h_abs_ty] at h_abs; cases h_abs
        exact (ih _ _ term term σ v (.refl term) h_abs_term h_conc h_env h_wt_term).trans h_sub_σ_τ
      | mu x ann body =>
        simp only [absEval] at h_abs
        simp only [concEval] at h_conc
        cases hba : absEval n ((x, .mu x ann body) :: Γ) body with
        | none => simp [hba] at h_abs
        | some body_a =>
          simp [hba] at h_abs
          cases hbc : concEval n ((x, .mu x ann body) :: γ) body with
          | none => simp [hbc] at h_conc
          | some body_c =>
            simp [hbc] at h_conc; rw [← h_abs, ← h_conc]
            exact .mu_body (ih _ _ body body body_a body_c
              (.refl body) hba hbc
              (envConsistent_extend h_env x (.mu x ann body))
              (by simp only [WellTyped] at h_wt; exact h_wt))
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
                have hf_sub := ih _ _ f f f_t f_v (.refl f) hfa hfc h_env
                  (by simp only [WellTyped] at h_wt; exact h_wt.1)
                have ha_sub := ih _ _ a a a_t a_v (.refl a) haa hac h_env
                  (by simp only [WellTyped] at h_wt; exact h_wt.2.1)
                -- Case split on abstract function result
                cases f_t with
                | type =>
                  simp only at h_abs; cases h_abs; exact .top v
                | lam x dom body_a =>
                  obtain ⟨body_c, hfv_eq, hbody_sub⟩ := SubtypeCore.lam_rhs_shape hf_sub
                  subst hfv_eq; simp only at h_abs h_conc
                  have h_wt_body : WellTyped n ((x, a_t) :: Γ) body_a := by
                    simp only [WellTyped] at h_wt
                    obtain ⟨_, _, h3⟩ := h_wt
                    rw [hfa, haa] at h3; exact h3
                  exact ih _ _ body_a body_c τ v hbody_sub h_abs h_conc
                    (envConsistent_extend_sub h_env x ha_sub) h_wt_body
                | mu x_mu ann_mu body_mu =>
                  -- mu-app: absEval matches on (ann, body) jointly.
                  -- Split on body_mu first, then ann_mu, to align with match order.
                  obtain ⟨body_c, hfv_eq, hbody_sub⟩ := SubtypeCore.mu_rhs_shape hf_sub
                  subst hfv_eq
                  have h_wt3 := by
                    simp only [WellTyped] at h_wt; obtain ⟨_, _, h3⟩ := h_wt
                    rw [hfa, haa] at h3; exact h3
                  cases body_mu with
                  | lam y_body dom_body bodyRes =>
                    -- body is lambda. Check ann to determine which match arm.
                    obtain ⟨lamBody, hbc_eq, hlam_sub⟩ := SubtypeCore.lam_rhs_shape hbody_sub
                    subst hbc_eq
                    cases ann_mu with
                    | lam y_ann dom_ann retBody =>
                      -- Both lam: annotation path via annotation consistency
                      simp only at h_wt3
                      obtain ⟨hy_eq, h_wt_bodyRes, h_wt_retBody, v_body, τ_ann,
                        h_abs_body, h_abs_ret, h_sub_body_ann⟩ := h_wt3
                      subst hy_eq
                      simp only at h_abs h_conc
                      have hτ_eq : τ_ann = τ := by
                        rw [h_abs_ret] at h_abs; injection h_abs
                      subst hτ_eq
                      exact (ih _ _ bodyRes lamBody v_body v hlam_sub h_abs_body h_conc
                        (envConsistent_extend_sub h_env y_ann ha_sub)
                        h_wt_bodyRes).trans h_sub_body_ann
                    | _ =>
                      -- Ann not lam, body is lam: body-unfold path
                      simp only at h_abs h_conc
                      have h_wt_body : WellTyped n ((y_body, a_t) :: Γ) bodyRes := by
                        simp only at h_wt3; exact h_wt3
                      exact ih _ _ bodyRes lamBody τ v hlam_sub h_abs h_conc
                        (envConsistent_extend_sub h_env y_body ha_sub) h_wt_body
                  | type =>
                    -- body = type: both evaluators return type (regardless of ann)
                    cases ann_mu with
                    | lam _ _ _ => simp only at h_abs; cases h_abs; exact .top v
                    | _ => simp only at h_abs; cases h_abs; exact .top v
                  | mu _ _ _ =>
                    -- body = mu: stuck application
                    obtain ⟨body₂, hbc_eq, _⟩ := SubtypeCore.mu_rhs_shape hbody_sub
                    subst hbc_eq
                    cases ann_mu with
                    | lam _ _ _ => simp only at h_abs h_conc; cases h_abs; cases h_conc
                                   exact .app_cong hbody_sub ha_sub
                    | _ => simp only at h_abs h_conc; cases h_abs; cases h_conc
                           exact .app_cong hbody_sub ha_sub
                  | var _ =>
                    cases body_c with
                    | lam _ _ _ => cases hbody_sub
                    | type => cases hbody_sub
                    | mu _ _ _ => cases hbody_sub
                    | _ => cases ann_mu with
                           | lam _ _ _ => simp only at h_abs h_conc; cases h_abs; cases h_conc
                                          exact .app_cong hbody_sub ha_sub
                           | _ => simp only at h_abs h_conc; cases h_abs; cases h_conc
                                  exact .app_cong hbody_sub ha_sub
                  | app _ _ =>
                    cases body_c with
                    | lam _ _ _ => cases hbody_sub
                    | type => cases hbody_sub
                    | mu _ _ _ => cases hbody_sub
                    | _ => cases ann_mu with
                           | lam _ _ _ => simp only at h_abs h_conc; cases h_abs; cases h_conc
                                          exact .app_cong hbody_sub ha_sub
                           | _ => simp only at h_abs h_conc; cases h_abs; cases h_conc
                                  exact .app_cong hbody_sub ha_sub
                  | asc _ _ =>
                    cases body_c with
                    | lam _ _ _ => cases hbody_sub
                    | type => cases hbody_sub
                    | mu _ _ _ => cases hbody_sub
                    | _ => cases ann_mu with
                           | lam _ _ _ => simp only at h_abs h_conc; cases h_abs; cases h_conc
                                          exact .app_cong hbody_sub ha_sub
                           | _ => simp only at h_abs h_conc; cases h_abs; cases h_conc
                                  exact .app_cong hbody_sub ha_sub
                | var v_name =>
                  cases hf_sub with
                  | refl => simp only at h_abs h_conc; cases h_abs; cases h_conc
                            exact .app_cong (.refl _) ha_sub
                | app f' a' =>
                  cases hf_sub with
                  | refl => simp only at h_abs h_conc; cases h_abs; cases h_conc
                            exact .app_cong (.refl _) ha_sub
                  | app_cong h1f h1a =>
                    simp only at h_abs h_conc; cases h_abs; cases h_conc
                    exact .app_cong (.app_cong h1f h1a) ha_sub
                | asc t ty =>
                  cases hf_sub with
                  | refl => simp only at h_abs h_conc; cases h_abs; cases h_conc
                            exact .app_cong (.refl _) ha_sub
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
          exact .lam_body (ih _ _ body_a body_c body_a' body_c'
            hbody hba hbc
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
              have hf_sub := ih _ _ f_a f_c f_t f_v hf hfa hfc h_env
                (by simp only [WellTyped] at h_wt; exact h_wt.1)
              have ha_sub := ih _ _ a_a a_c a_t a_v ha haa hac h_env
                (by simp only [WellTyped] at h_wt; exact h_wt.2.1)
              cases f_t with
              | type =>
                simp only at h_abs; cases h_abs; exact .top v
              | lam x dom body_a =>
                obtain ⟨body_c, hfv_eq, hbody_sub⟩ := SubtypeCore.lam_rhs_shape hf_sub
                subst hfv_eq; simp only at h_abs h_conc
                have h_wt_body : WellTyped n ((x, a_t) :: Γ) body_a := by
                  simp only [WellTyped] at h_wt
                  obtain ⟨_, _, h3⟩ := h_wt
                  rw [hfa, haa] at h3; exact h3
                exact ih _ _ body_a body_c τ v hbody_sub h_abs h_conc
                  (envConsistent_extend_sub h_env x ha_sub) h_wt_body
              | mu x_mu ann_mu body_mu =>
                -- mu-app in app_cong: same structure as refl case.
                -- Split on body_mu first (primary discriminant), then ann_mu.
                obtain ⟨body_c, hfv_eq, hbody_sub⟩ := SubtypeCore.mu_rhs_shape hf_sub
                subst hfv_eq
                have h_wt3 := by
                  simp only [WellTyped] at h_wt; obtain ⟨_, _, h3⟩ := h_wt
                  rw [hfa, haa] at h3; exact h3
                cases body_mu with
                | lam y_body dom_body bodyRes =>
                  obtain ⟨lamBody, hbc_eq, hlam_sub⟩ := SubtypeCore.lam_rhs_shape hbody_sub
                  subst hbc_eq
                  cases ann_mu with
                  | lam y_ann dom_ann retBody =>
                    -- Both lam: annotation path via annotation consistency
                    simp only at h_wt3
                    obtain ⟨hy_eq, h_wt_bodyRes, h_wt_retBody, v_body, τ_ann,
                      h_abs_body, h_abs_ret, h_sub_body_ann⟩ := h_wt3
                    subst hy_eq
                    simp only at h_abs h_conc
                    have hτ_eq : τ_ann = τ := by
                      rw [h_abs_ret] at h_abs; injection h_abs
                    subst hτ_eq
                    exact (ih _ _ bodyRes lamBody v_body v hlam_sub h_abs_body h_conc
                      (envConsistent_extend_sub h_env y_ann ha_sub)
                      h_wt_bodyRes).trans h_sub_body_ann
                  | _ =>
                    -- Ann not lam, body is lam: body-unfold path
                    simp only at h_abs h_conc
                    have h_wt_body : WellTyped n ((y_body, a_t) :: Γ) bodyRes := by
                      simp only at h_wt3; exact h_wt3
                    exact ih _ _ bodyRes lamBody τ v hlam_sub h_abs h_conc
                      (envConsistent_extend_sub h_env y_body ha_sub) h_wt_body
                | type =>
                  cases ann_mu with
                  | lam _ _ _ => simp only at h_abs; cases h_abs; exact .top v
                  | _ => simp only at h_abs; cases h_abs; exact .top v
                | mu _ _ _ =>
                  obtain ⟨body₂, hbc_eq, _⟩ := SubtypeCore.mu_rhs_shape hbody_sub
                  subst hbc_eq
                  cases ann_mu with
                  | lam _ _ _ => simp only at h_abs h_conc; cases h_abs; cases h_conc
                                 exact .app_cong hbody_sub ha_sub
                  | _ => simp only at h_abs h_conc; cases h_abs; cases h_conc
                         exact .app_cong hbody_sub ha_sub
                | var _ =>
                  cases body_c with
                  | lam _ _ _ => cases hbody_sub
                  | type => cases hbody_sub
                  | mu _ _ _ => cases hbody_sub
                  | _ => cases ann_mu with
                         | lam _ _ _ => simp only at h_abs h_conc; cases h_abs; cases h_conc
                                        exact .app_cong hbody_sub ha_sub
                         | _ => simp only at h_abs h_conc; cases h_abs; cases h_conc
                                exact .app_cong hbody_sub ha_sub
                | app _ _ =>
                  cases body_c with
                  | lam _ _ _ => cases hbody_sub
                  | type => cases hbody_sub
                  | mu _ _ _ => cases hbody_sub
                  | _ => cases ann_mu with
                         | lam _ _ _ => simp only at h_abs h_conc; cases h_abs; cases h_conc
                                        exact .app_cong hbody_sub ha_sub
                         | _ => simp only at h_abs h_conc; cases h_abs; cases h_conc
                                exact .app_cong hbody_sub ha_sub
                | asc _ _ =>
                  cases body_c with
                  | lam _ _ _ => cases hbody_sub
                  | type => cases hbody_sub
                  | mu _ _ _ => cases hbody_sub
                  | _ => cases ann_mu with
                         | lam _ _ _ => simp only at h_abs h_conc; cases h_abs; cases h_conc
                                        exact .app_cong hbody_sub ha_sub
                         | _ => simp only at h_abs h_conc; cases h_abs; cases h_conc
                                exact .app_cong hbody_sub ha_sub
              | var v_name =>
                cases hf_sub with
                | refl => simp only at h_abs h_conc; cases h_abs; cases h_conc
                          exact .app_cong (.refl _) ha_sub
              | app f' a' =>
                cases hf_sub with
                | refl => simp only at h_abs h_conc; cases h_abs; cases h_conc
                          exact .app_cong (.refl _) ha_sub
                | app_cong h1f h1a =>
                  simp only at h_abs h_conc; cases h_abs; cases h_conc
                  exact .app_cong (.app_cong h1f h1a) ha_sub
              | asc t ty =>
                cases hf_sub with
                | refl => simp only at h_abs h_conc; cases h_abs; cases h_conc
                          exact .app_cong (.refl _) ha_sub
    | mu_body hbody =>
      rename_i x ann body_a body_c
      simp only [absEval] at h_abs
      simp only [concEval] at h_conc
      cases hba : absEval n ((x, .mu x ann body_a) :: Γ) body_a with
      | none => simp [hba] at h_abs
      | some body_a' =>
        simp [hba] at h_abs
        cases hbc : concEval n ((x, .mu x ann body_c) :: γ) body_c with
        | none => simp [hbc] at h_conc
        | some body_c' =>
          simp [hbc] at h_conc; rw [← h_abs, ← h_conc]
          exact .mu_body (ih _ _ body_a body_c body_a' body_c'
            hbody hba hbc
            (envConsistent_extend_sub h_env x (.mu_body hbody))
            (by simp only [WellTyped] at h_wt; exact h_wt))

/-- **Soundness theorem.**

    If abstract evaluation gives type `τ` and concrete evaluation gives value `v`,
    then `Subtype' v τ`.

    Uses SubtypeCore internally (which avoids the self_intro case entirely),
    then converts to Subtype' via toSubtype'. -/
theorem soundness
    (Γ : Env) (γ : Env) (e τ v : Expr) (fuel : Nat)
    (h_abs : absEval fuel Γ e = some τ)
    (h_conc : concEval fuel γ e = some v)
    (h_env : EnvConsistent γ Γ)
    (h_wt : WellTyped fuel Γ e)
    : Subtype' v τ :=
  (soundness_gen fuel Γ γ e e τ v (SubtypeCore.refl e)
    h_abs h_conc h_env h_wt).toSubtype'
