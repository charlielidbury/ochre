import Och.Syntax
import Och.Eval
import Och.Subtyping
import Och.Monotonicity

/-!
# Soundness

If abstract evaluation says `e` has type `τ`, and concrete evaluation
produces value `v`, then `v ⊑ τ` (in Subtype').

## Status

**3 targeted sorrys** in soundness_gen (was 1 blanket sorry). All non-asc,
non-annotation-path cases are fully proved. The sorry'd cases are:

1. **asc case** (line ~193): needs "checker transitivity" bridge
2. **mu-app annotation path** (lines ~252, ~370): needs annotation consistency

## Architecture

WellTyped is **Bool-valued** with `subCheckNF` in the ascription case.
soundness_gen takes SubtypeCore for h_sub and returns SubtypeCore.

## Why SubtypeCore is fundamentally too weak for the remaining sorrys

The asc case needs: `subCheckNF σ τ' = true → SubtypeCore v σ → SubtypeCore v τ'`.
This is FALSE for SubtypeCore because:
- SubtypeCore has no `self_intro` (can't relate a lam to a mu)
- SubtypeCore has no contravariant domain subtyping (`lam_body` requires same domain)
- subCheckNF handles both (equi-recursive self-intro + contra-domain checking)

Subtype' is ALSO too weak:
- Has `self_intro` but WITHOUT substitution (subCheckNF substitutes x := mu)
- Has no contravariant domain subtyping (`lam_body` requires same domain)
- Adding `lam_sub` (contra-domain) breaks `Subtype'.trans` (needs both sides of induction)
- Adding equi-recursive unfolding breaks structural induction

## Viable approaches for the remaining sorrys

(a) **Change soundness output to `subCheckNF`-based.** State soundness as
    `subCheckNF fuel Γ [] v τ = true`. Requires "checker transitivity".
(b) **Coinductive subtyping relation** with lam_sub + equi-recursive rules.
    Lean 4 supports coinductives. Transitivity is coinductive.
(c) **Step-indexed logical relations.** Standard PL approach. Major infra change.
(d) **Prove checker transitivity directly** for subCheckNF. Hard due to
    fuel bounds, inferType, and seen-set interactions.

The mu-app annotation path additionally needs annotation consistency
re-added to WellTyped (using subCheckNF, not SubtypeCore).
-/

open Expr

def EnvConsistent (γ : Env) (Γ : Env) : Prop :=
  ∀ x τ, Γ.lookup x = some τ → ∃ v, γ.lookup x = some v ∧ SubtypeCore v τ

/-- Well-typedness: all ascriptions encountered during evaluation are sound.

    **Bool-valued** for decidability. Uses `subCheckNF` (the decidable subtype
    checker) instead of `SubtypeCore` in the ascription case, so that WellTyped
    is satisfiable for programs with mu types. Previously used `SubtypeCore`,
    which has no `self_intro` constructor and thus was unsatisfiable for any
    program with `(e : mu_type)` ascriptions — making the soundness theorem
    vacuously true.

    The `Γ` parameter serves double duty: it's the absEval environment AND
    the subCheckNF typing context. For lambda-bound variables, Γ maps x to
    `var x` (neutral); for mu-bound variables, Γ maps x to the mu value.
    This works because subCheckNF's inferType uses the context to look up
    variable types, and for neutral variables, it returns the binding itself. -/
def WellTyped (fuel : Nat) (Γ : Env) (e : Expr) : Bool :=
  match fuel with
  | 0 => true
  | fuel + 1 =>
    match e with
    | .var _ => true
    | .lam x _ body => WellTyped fuel ((x, .var x) :: Γ) body
    | .type => true
    | .asc term ty =>
        WellTyped fuel Γ term && WellTyped fuel Γ ty &&
        match absEval fuel Γ term, absEval fuel Γ ty with
        | some σ, some τ' => subCheckNF fuel Γ [] σ τ'
        | _, _ => false
    | .mu x ann body =>
        WellTyped fuel ((x, .mu x ann body) :: Γ) body
    | .app f a =>
        WellTyped fuel Γ f && WellTyped fuel Γ a &&
        match absEval fuel Γ f, absEval fuel Γ a with
        | some (.lam x _ body), some aVal => WellTyped fuel ((x, aVal) :: Γ) body
        | some (.mu _x_mu ann body_mu), some aVal =>
          -- mu-app: absEval uses annotation when both are lambdas,
          -- body otherwise. Check WellTyped of the sub-term that
          -- absEval will actually evaluate (matching absEval's logic).
          match ann, body_mu with
          | .lam y_ann _dom_ann retBody, .lam _y_body _dom_body _bodyRes =>
              -- Both lambdas: absEval uses annotation's return body.
              WellTyped fuel ((y_ann, aVal) :: Γ) retBody
          | .lam y_ann _dom_ann retBody, _ =>
              -- Ann is lam, body isn't: absEval still uses annotation.
              -- (Wait — actually absEval's joint match gives (_, lam) priority
              --  over (lam, _) when body is lam. But here body ISN'T lam.)
              WellTyped fuel ((y_ann, aVal) :: Γ) retBody
          | _, .lam y_body _dom_body bodyRes =>
              -- Body is lam, ann isn't: absEval uses body directly.
              WellTyped fuel ((y_body, aVal) :: Γ) bodyRes
          | _, _ => true
        | _, _ => true

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

/-- **Generalized soundness.** If abstract evaluation gives type `τ`
    and concrete evaluation gives value `v`, then `SubtypeCore v τ`.

    Uses SubtypeCore (Subtype' without self_intro) for both input and output.
    The main `soundness` theorem converts via `toSubtype'`.

    **STATUS: 3 targeted sorrys** (was 1 blanket sorry). All non-asc,
    non-annotation-path cases proved. Remaining sorrys:
    1. **asc case:** WellTyped gives `subCheckNF σ τ' = true` but
       `SubtypeCore v σ → SubtypeCore v τ'` doesn't follow (SubtypeCore
       lacks self_intro and contra-domain lam_sub).
    2. **mu-app annotation path (×2):** absEval uses annotation, concEval
       uses body — different expressions. Needs annotation consistency
       re-added to WellTyped with subCheckNF, plus a checker bridge. -/
theorem soundness_gen
    (fuel : Nat) (Γ : Env) (γ : Env) (e_a e_c τ v : Expr)
    (h_sub : SubtypeCore e_c e_a)
    (h_abs : absEval fuel Γ e_a = some τ)
    (h_conc : concEval fuel γ e_c = some v)
    (h_env : EnvConsistent γ Γ)
    (h_wt : WellTyped fuel Γ e_a = true)
    : SubtypeCore v τ := by
  induction fuel generalizing Γ γ e_a e_c τ v with
  | zero => simp [absEval] at h_abs
  | succ n ih =>
    cases h_sub with
    | top e =>
      simp [absEval] at h_abs; rw [← h_abs]; exact .top v
    | refl =>
      cases e_a with
      | var x =>
        simp [absEval] at h_abs; simp [concEval] at h_conc
        have ⟨v', hv', hsub⟩ := h_env x τ h_abs
        rw [hv'] at h_conc; cases h_conc; exact hsub
      | type =>
        simp [absEval] at h_abs; simp [concEval] at h_conc
        rw [← h_abs, ← h_conc]; exact .refl .type
      | lam x dom body =>
        simp only [absEval] at h_abs; simp only [concEval] at h_conc
        cases hba : absEval n ((x, .var x) :: Γ) body with
        | none => simp [hba] at h_abs
        | some body_a =>
          simp [hba] at h_abs
          cases hbc : concEval n ((x, .var x) :: γ) body with
          | none => simp [hbc] at h_conc
          | some body_c =>
            simp [hbc] at h_conc; rw [← h_abs, ← h_conc]
            exact .lam_body (ih _ _ body body body_a body_c (.refl body) hba hbc
              (envConsistent_extend h_env x (.var x))
              (by simp only [WellTyped] at h_wt; exact h_wt))
      | asc term ty =>
        -- SORRY: asc case needs "checker transitivity" bridge.
        -- WellTyped gives: subCheckNF fuel Γ [] σ τ' = true
        -- IH gives: SubtypeCore v σ
        -- Need: SubtypeCore v τ'
        -- SubtypeCore is too weak: no self_intro, no contra-domain lam_sub.
        -- See PROGRESS.md for analysis of why this is fundamentally hard.
        sorry
      | mu x ann body =>
        simp only [absEval] at h_abs; simp only [concEval] at h_conc
        cases hba : absEval n ((x, .mu x ann body) :: Γ) body with
        | none => simp [hba] at h_abs
        | some body_a =>
          simp [hba] at h_abs
          cases hbc : concEval n ((x, .mu x ann body) :: γ) body with
          | none => simp [hbc] at h_conc
          | some body_c =>
            simp [hbc] at h_conc; rw [← h_abs, ← h_conc]
            exact .mu_body (ih _ _ body body body_a body_c (.refl body) hba hbc
              (envConsistent_extend h_env x (.mu x ann body))
              (by simp only [WellTyped] at h_wt; exact h_wt))
      | app f a =>
        simp only [absEval] at h_abs; simp only [concEval] at h_conc
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
                -- Extract WellTyped: f, a well-typed + match condition
                have h_wt' := h_wt; simp only [WellTyped] at h_wt'
                rw [hfa, haa] at h_wt'
                simp only [Bool.and_eq_true_iff] at h_wt'
                obtain ⟨⟨h_wt_f, h_wt_a⟩, h_wt_rest⟩ := h_wt'
                have hf_sub := ih _ _ f f f_t f_v (.refl f) hfa hfc h_env h_wt_f
                have ha_sub := ih _ _ a a a_t a_v (.refl a) haa hac h_env h_wt_a
                -- Case split on abstract function result
                cases f_t with
                | type =>
                  simp only at h_abs; cases h_abs; exact .top v
                | lam x dom body_a =>
                  obtain ⟨body_c, hfv_eq, hbody_sub⟩ := SubtypeCore.lam_rhs_shape hf_sub
                  subst hfv_eq; simp only at h_abs h_conc
                  exact ih _ _ body_a body_c τ v hbody_sub h_abs h_conc
                    (envConsistent_extend_sub h_env x ha_sub) h_wt_rest
                | mu x_mu ann_mu body_mu =>
                  obtain ⟨body_c, hfv_eq, hbody_sub⟩ := SubtypeCore.mu_rhs_shape hf_sub
                  subst hfv_eq
                  -- mu-app: case split on body_mu shape
                  cases body_mu with
                  | lam y_body dom_body bodyRes =>
                    obtain ⟨lamBody, hbc_eq, hlam_sub⟩ := SubtypeCore.lam_rhs_shape hbody_sub
                    subst hbc_eq
                    cases ann_mu with
                    | lam y_ann dom_ann retBody =>
                      -- ANNOTATION PATH: both ann and body are lambdas.
                      -- absEval uses retBody (annotation), concEval uses lamBody (body).
                      -- SORRY: needs annotation consistency in WellTyped + checker bridge.
                      sorry
                    | _ =>
                      -- Body-unfold: ann ≠ lam, body is lam.
                      simp only at h_abs h_conc
                      exact ih _ _ bodyRes lamBody τ v hlam_sub h_abs h_conc
                        (envConsistent_extend_sub h_env y_body ha_sub) h_wt_rest
                  | type =>
                    cases ann_mu with
                    | lam _ _ _ => simp only at h_abs; cases h_abs; exact .top v
                    | _ => simp only at h_abs; cases h_abs; exact .top v
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
                  | mu _ _ _ =>
                    obtain ⟨body₂, hbc_eq, _⟩ := SubtypeCore.mu_rhs_shape hbody_sub
                    subst hbc_eq
                    cases ann_mu with
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
      simp only [absEval] at h_abs; simp only [concEval] at h_conc
      cases hba : absEval n ((x, .var x) :: Γ) body_a with
      | none => simp [hba] at h_abs
      | some body_a' =>
        simp [hba] at h_abs
        cases hbc : concEval n ((x, .var x) :: γ) body_c with
        | none => simp [hbc] at h_conc
        | some body_c' =>
          simp [hbc] at h_conc; rw [← h_abs, ← h_conc]
          exact .lam_body (ih _ _ body_a body_c body_a' body_c' hbody hba hbc
            (envConsistent_extend h_env x (.var x))
            (by simp only [WellTyped] at h_wt; exact h_wt))
    | app_cong hf ha =>
      rename_i f_a f_c a_a a_c
      simp only [absEval] at h_abs; simp only [concEval] at h_conc
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
              -- Extract WellTyped
              have h_wt' := h_wt; simp only [WellTyped] at h_wt'
              rw [hfa, haa] at h_wt'
              simp only [Bool.and_eq_true_iff] at h_wt'
              obtain ⟨⟨h_wt_f, h_wt_a⟩, h_wt_rest⟩ := h_wt'
              have hf_sub := ih _ _ f_a f_c f_t f_v hf hfa hfc h_env h_wt_f
              have ha_sub := ih _ _ a_a a_c a_t a_v ha haa hac h_env h_wt_a
              cases f_t with
              | type => simp only at h_abs; cases h_abs; exact .top v
              | lam x dom body_a =>
                obtain ⟨body_c, hfv_eq, hbody_sub⟩ := SubtypeCore.lam_rhs_shape hf_sub
                subst hfv_eq; simp only at h_abs h_conc
                exact ih _ _ body_a body_c τ v hbody_sub h_abs h_conc
                  (envConsistent_extend_sub h_env x ha_sub) h_wt_rest
              | mu x_mu ann_mu body_mu =>
                obtain ⟨body_c, hfv_eq, hbody_sub⟩ := SubtypeCore.mu_rhs_shape hf_sub
                subst hfv_eq
                cases body_mu with
                | lam y_body dom_body bodyRes =>
                  obtain ⟨lamBody, hbc_eq, hlam_sub⟩ := SubtypeCore.lam_rhs_shape hbody_sub
                  subst hbc_eq
                  cases ann_mu with
                  | lam y_ann dom_ann retBody =>
                    -- ANNOTATION PATH: same sorry as refl case
                    sorry
                  | _ =>
                    simp only at h_abs h_conc
                    exact ih _ _ bodyRes lamBody τ v hlam_sub h_abs h_conc
                      (envConsistent_extend_sub h_env y_body ha_sub) h_wt_rest
                | type =>
                  cases ann_mu with
                  | lam _ _ _ => simp only at h_abs; cases h_abs; exact .top v
                  | _ => simp only at h_abs; cases h_abs; exact .top v
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
                | mu _ _ _ =>
                  obtain ⟨body₂, hbc_eq, _⟩ := SubtypeCore.mu_rhs_shape hbody_sub
                  subst hbc_eq
                  cases ann_mu with
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
      simp only [absEval] at h_abs; simp only [concEval] at h_conc
      cases hba : absEval n ((x, .mu x ann body_a) :: Γ) body_a with
      | none => simp [hba] at h_abs
      | some body_a' =>
        simp [hba] at h_abs
        cases hbc : concEval n ((x, .mu x ann body_c) :: γ) body_c with
        | none => simp [hbc] at h_conc
        | some body_c' =>
          simp [hbc] at h_conc; rw [← h_abs, ← h_conc]
          exact .mu_body (ih _ _ body_a body_c body_a' body_c' hbody hba hbc
            (envConsistent_extend_sub h_env x (.mu_body hbody))
            (by simp only [WellTyped] at h_wt; exact h_wt))

/-- **Soundness theorem.**

    If abstract evaluation gives type `τ` and concrete evaluation gives value `v`,
    then `Subtype' v τ`.

    Uses SubtypeCore internally (which avoids the self_intro case entirely),
    then converts to Subtype' via toSubtype'.

    **STATUS: 3 sorrys** (depends on sorry'd soundness_gen). -/
theorem soundness
    (Γ : Env) (γ : Env) (e τ v : Expr) (fuel : Nat)
    (h_abs : absEval fuel Γ e = some τ)
    (h_conc : concEval fuel γ e = some v)
    (h_env : EnvConsistent γ Γ)
    (h_wt : WellTyped fuel Γ e = true)
    : Subtype' v τ :=
  (soundness_gen fuel Γ γ e e τ v (SubtypeCore.refl e)
    h_abs h_conc h_env h_wt).toSubtype'
