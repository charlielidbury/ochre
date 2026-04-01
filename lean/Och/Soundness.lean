import Och.Syntax
import Och.Eval
import Och.Subtyping
import Och.Monotonicity

/-!
# Soundness

If abstract evaluation says `e` has type `τ`, and concrete evaluation
produces value `v`, then `v ⊑ τ` (in Subtype').

**Key insight (new):** Subtype' is transitive (Subtype'.trans). This means
SubtypeTrans is unnecessary — soundness uses Subtype' directly. This
eliminates the trans/self_intro cases that were previously sorry'd.

The proof uses a generalized `soundness_gen` that takes `Subtype' e_c e_a`
(related expressions) since the app-beta case produces different normalized
bodies from the function IH.

## Status

soundness_gen has **3 individual sorrys** (was 5).

**Proved cases:**
- var, lam, type, asc: direct from env consistency / IH / WellTyped
- app-lam: Subtype'.lam_rhs_shape inverts concrete function
- app-stuck: direct Subtype' case analysis (no SubtypeTrans needed)
- mu standalone: mu_body (both evaluators now wrap mu results)
- mu_body: mu_body (parallel structure from wrapping)
- lam_body, app_cong: handled via Subtype' structure

**Remaining sorrys (3):**
- mu-app (×2): concEval matches body for lambda; absEval uses annotation
  (lam ann) or body-unfold (non-lam ann). Different computation paths.
- self_intro (×1): fuel/env mismatch. Reachable via asc path (when
  WellTyped has Subtype' σ (mu ...) via self_intro). See case comment.

**Key change:** concEval now wraps mu results (like absEval). This made
the mu standalone and mu_body cases provable via mu_body instead of
self_intro. The app-mu case matches on the mu body directly instead
of re-unrolling.
-/

open Expr

def EnvConsistent (γ : Env) (Γ : Env) : Prop :=
  ∀ x τ, Γ.lookup x = some τ → ∃ v, γ.lookup x = some v ∧ Subtype' v τ

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
    | .mu x ann body =>
        WellTyped fuel ((x, .mu x ann body) :: Γ) body
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
  · cases h_lookup; exact ⟨v, rfl, Subtype'.refl v⟩
  · rename_i h1 h2; exact absurd h1 h2
  · rename_i h1 h2; exact absurd h2 h1
  · exact h y τ h_lookup

theorem envConsistent_extend_sub {γ Γ : Env} (h : EnvConsistent γ Γ)
    (x : Name) {v τ : Expr} (hv : Subtype' v τ) :
    EnvConsistent ((x, v) :: γ) ((x, τ) :: Γ) := by
  intro y σ h_lookup
  simp only [Env.lookup] at h_lookup ⊢
  split at h_lookup <;> split
  · cases h_lookup; exact ⟨v, rfl, hv⟩
  · rename_i h1 h2; exact absurd h1 h2
  · rename_i h1 h2; exact absurd h2 h1
  · exact h y σ h_lookup

/-- **Generalized soundness.** Proves that if abstract evaluation gives type `τ`
    and concrete evaluation gives value `v`, then `Subtype' v τ`.

    Uses Subtype' directly (not SubtypeTrans) since Subtype'.trans is proved.

    ## Sorry'd cases (3)
    - **mu-app (×2):** concEval matches mu body for lambda; absEval uses
      annotation (lam ann) or body-unfold. The annotation is an unrelated
      expression from the mu body, so Subtype' can't bridge them.
    - **self_intro (×1):** fuel/env mismatch. Reachable via asc path when
      WellTyped contains Subtype' σ (mu ...) via self_intro. -/
theorem soundness_gen
    (fuel : Nat) (Γ : Env) (γ : Env) (e_a e_c τ v : Expr)
    (h_sub : Subtype' e_c e_a)
    (h_abs : absEval fuel Γ e_a = some τ)
    (h_conc : concEval fuel γ e_c = some v)
    (h_env : EnvConsistent γ Γ)
    (h_wt : WellTyped fuel Γ e_a)
    : Subtype' v τ := by
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
                  obtain ⟨body_c, hfv_eq, hbody_sub⟩ := Subtype'.lam_rhs_shape hf_sub
                  subst hfv_eq; simp only at h_abs h_conc
                  have h_wt_body : WellTyped n ((x, a_t) :: Γ) body_a := by
                    simp only [WellTyped] at h_wt
                    obtain ⟨_, _, h3⟩ := h_wt
                    rw [hfa, haa] at h3; exact h3
                  exact ih _ _ body_a body_c τ v hbody_sub h_abs h_conc
                    (envConsistent_extend_sub h_env x ha_sub) h_wt_body
                | mu x_mu ann_mu body_mu =>
                  -- mu-app: abstract uses annotation (if lam) or body-unfold,
                  -- concrete matches on body directly.
                  -- From mu_rhs_shape, f_v is either:
                  --   (a) mu x_mu ann_mu body_c with body_c ⊑ body_mu
                  --   (b) Subtype' f_v body_mu (self_intro)
                  -- For (a): annotation consistency — the mu body (concEval
                  --   matches body_c for lam) vs the annotation retBody
                  --   (absEval uses ann_mu directly) are fundamentally
                  --   different expressions. Subtype' can't relate them.
                  -- For (b): different concEval app branch fires, depending
                  --   on f_v's shape (lam, var, etc).
                  sorry
                | var v_name =>
                  -- f_v ⊑ var: f_v must be var (only refl)
                  cases hf_sub with
                  | refl => simp only at h_abs h_conc; cases h_abs; cases h_conc
                            exact .app_cong (.refl _) ha_sub
                | app f' a' =>
                  -- f_v ⊑ app: f_v is refl or app_cong
                  cases hf_sub with
                  | refl => simp only at h_abs h_conc; cases h_abs; cases h_conc
                            exact .app_cong (.refl _) ha_sub
                  | app_cong h1f h1a =>
                    simp only at h_abs h_conc; cases h_abs; cases h_conc
                    exact .app_cong (.app_cong h1f h1a) ha_sub
                | asc t ty =>
                  -- f_v ⊑ asc: f_v must be asc (only refl)
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
                obtain ⟨body_c, hfv_eq, hbody_sub⟩ := Subtype'.lam_rhs_shape hf_sub
                subst hfv_eq; simp only at h_abs h_conc
                have h_wt_body : WellTyped n ((x, a_t) :: Γ) body_a := by
                  simp only [WellTyped] at h_wt
                  obtain ⟨_, _, h3⟩ := h_wt
                  rw [hfa, haa] at h3; exact h3
                exact ih _ _ body_a body_c τ v hbody_sub h_abs h_conc
                  (envConsistent_extend_sub h_env x ha_sub) h_wt_body
              | mu x_mu ann_mu body_mu =>
                -- mu-app in app_cong case (same structure as refl case).
                -- See the refl mu-app case for the detailed analysis.
                sorry
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
    | self_intro h_intro =>
      -- e_a = mu x ann body, h_intro : Subtype' e_c body.
      -- FUEL MISMATCH: absEval uses fuel n (after mu step), but
      -- concEval(e_c) has fuel n+1. The IH requires both to use fuel n.
      -- Also: absEval uses extended env ((x, mu) :: Γ), but concEval
      -- uses the original env γ. These mismatches block the IH.
      --
      -- This case is REACHABLE but only via the asc path: when an
      -- ascription `(term : mu_type)` has WellTyped with Subtype' σ τ'
      -- where τ' is a mu, the asc case returns (IH).trans (self_intro ...)
      -- which is self_intro at the top level. If this is inside a lambda
      -- body that gets applied, lam_rhs_shape decomposes it, producing
      -- self_intro as h_sub for the recursive call.
      --
      -- Previously also reachable from the mu standalone case (which
      -- used self_intro). Now that concEval wraps mu results, the mu
      -- case uses mu_body instead, reducing self_intro's reachability.
      --
      -- Proving this case requires either:
      -- (a) A fuel monotonicity lemma for concEval
      -- (b) Restructuring WellTyped so asc never produces self_intro
      -- (c) A step-indexed/logical-relation approach
      sorry

/-- **Soundness theorem.**

    If abstract evaluation gives type `τ` and concrete evaluation gives value `v`,
    then `Subtype' v τ`. -/
theorem soundness
    (Γ : Env) (γ : Env) (e τ v : Expr) (fuel : Nat)
    (h_abs : absEval fuel Γ e = some τ)
    (h_conc : concEval fuel γ e = some v)
    (h_env : EnvConsistent γ Γ)
    (h_wt : WellTyped fuel Γ e)
    : Subtype' v τ :=
  soundness_gen fuel Γ γ e e τ v (Subtype'.refl e)
    h_abs h_conc h_env h_wt
