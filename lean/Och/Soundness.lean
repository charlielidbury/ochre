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
-/

open Expr

def EnvConsistent (γ : Env) (Γ : Env) : Prop :=
  ∀ x τ, Γ.lookup x = some τ → ∃ v, γ.lookup x = some v ∧ SubtypeTrans v τ

/-- Well-typedness: all ascriptions encountered during evaluation are sound.
    Uses closure-based eval in the app case (matching the evaluator). -/
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

/-- **Generalized soundness.**

    Takes `SubtypeTrans e_c e_a` as input (related expressions) to handle
    the app-beta case where the lambda bodies differ. The result is
    `SubtypeTrans v τ` because the asc case chains IH with well-typedness.

    Standard soundness is the corollary with `SubtypeTrans.step (Subtype'.refl e)`.

    The proof works by induction on fuel, case-splitting on `e_a` (the abstract
    expression). For each shape of `e_a`, SubtypeTrans target shape lemmas
    constrain `e_c` to have the same shape:
    - var → var (var_target)
    - lam → lam (lam_target_shape)
    - app → app (app_target_shape)
    - asc → asc (asc_target)
    - type → anything (trivial via top)
-/
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
    cases e_a with
    | var x =>
      -- SubtypeTrans e_c (var x) → e_c = var x
      have := h_sub.var_target; subst this
      simp [absEval, concEval] at h_abs h_conc
      have ⟨val, h_lv, h_sub'⟩ := h_env x τ h_abs
      rw [h_lv] at h_conc; cases h_conc; exact h_sub'
    | type =>
      -- SubtypeTrans e_c .type → anything; absEval .type = .type
      simp [absEval] at h_abs; rw [← h_abs]
      exact SubtypeTrans.step (Subtype'.top v)
    | lam x dom body_a =>
      -- SubtypeTrans e_c (lam x dom body_a) → e_c = lam x dom body_c
      obtain ⟨body_c, hec_eq, h_body_sub⟩ := h_sub.lam_target_shape
      subst hec_eq
      simp only [absEval, concEval] at h_abs h_conc
      cases hba : absEval n ((x, .var x) :: Γ) body_a with
      | none => simp [hba] at h_abs
      | some body_a' =>
        simp [hba] at h_abs
        cases hbc : concEval n ((x, .var x) :: γ) body_c with
        | none => simp [hbc] at h_conc
        | some body_c' =>
          simp [hbc] at h_conc; rw [← h_abs, ← h_conc]
          have h_env' := envConsistent_extend h_env x (.var x)
          have h_wt' : WellTyped n ((x, .var x) :: Γ) body_a := h_wt
          exact SubtypeTrans.lam_body (ih _ _ body_a body_c _ _ h_body_sub hba hbc h_env' h_wt')
    | asc term ty =>
      -- SubtypeTrans e_c (asc term ty) → e_c = asc term ty
      have := h_sub.asc_target; subst this
      simp only [absEval, concEval] at h_abs h_conc
      have ⟨h_wt_term, _, σ, τ', h_abs_term, h_abs_ty, h_sub_wt⟩ := h_wt
      rw [h_abs] at h_abs_ty; cases h_abs_ty
      have h_vs := ih Γ γ term term σ v (SubtypeTrans.step (Subtype'.refl term))
        h_abs_term h_conc h_env h_wt_term
      exact SubtypeTrans.trans h_vs (SubtypeTrans.step h_sub_wt)
    | app f_a a_a =>
      -- SubtypeTrans e_c (app f_a a_a) → e_c = app f_c a_c
      obtain ⟨f_c, a_c, hec_eq, h_f_sub, h_a_sub⟩ := h_sub.app_target_shape
      subst hec_eq
      simp only [absEval, concEval] at h_abs h_conc
      -- Extract WellTyped components
      have ⟨h_wt_f, h_wt_a, h_wt_body⟩ := h_wt
      -- Evaluate function and argument in both modes
      cases hfa : absEval n Γ f_a with
      | none => simp [hfa] at h_abs
      | some τ_f =>
        cases haa : absEval n Γ a_a with
        | none => simp [hfa, haa] at h_abs
        | some τ_a =>
          cases hfc : concEval n γ f_c with
          | none => simp [hfc] at h_conc
          | some v_f =>
            cases hac : concEval n γ a_c with
            | none => simp [hfc, hac] at h_conc
            | some v_a =>
              -- IH on function and argument
              have ih_f := ih _ _ f_a f_c _ _ h_f_sub hfa hfc h_env h_wt_f
              have ih_a := ih _ _ a_a a_c _ _ h_a_sub haa hac h_env h_wt_a
              -- Now case-split on τ_f (what the abstract evaluator got for the function)
              rw [hfa, haa] at h_abs h_wt_body
              rw [hfc, hac] at h_conc
              cases τ_f with
              | lam x dom body_a =>
                -- Abstract function is a lambda → beta-reduce
                -- Concrete function must also be a lambda (by SubtypeTrans shape)
                obtain ⟨body_c, hvf_eq, h_body_sub⟩ := ih_f.lam_target_shape
                subst hvf_eq
                -- Both sides beta-reduce
                simp only at h_abs h_conc
                -- Body relation: SubtypeTrans body_c body_a
                -- Env relation: EnvConsistent ((x, v_a) :: γ) ((x, τ_a) :: Γ)
                exact ih _ _ body_a body_c _ _ h_body_sub h_abs h_conc
                  (envConsistent_extend_sub h_env x ih_a) h_wt_body
              | type =>
                -- Abstract function is Type → type-app-returns-type
                simp only at h_abs; cases h_abs
                exact SubtypeTrans.step (Subtype'.top v)
              | var v_a_name =>
                -- Stuck: v_f must also be a var (by SubtypeTrans)
                have := ih_f.var_target; subst this
                simp only at h_abs h_conc; cases h_abs; cases h_conc
                exact SubtypeTrans.app_cong ih_f ih_a
              | app f₁' a₁' =>
                -- Stuck: v_f must also be an app
                obtain ⟨f₂', a₂', hvf_eq, _, _⟩ := ih_f.app_target_shape
                subst hvf_eq
                simp only at h_abs h_conc; cases h_abs; cases h_conc
                exact SubtypeTrans.app_cong ih_f ih_a
              | asc t' τ' =>
                -- Stuck: v_f must also be an asc
                have := ih_f.asc_target; subst this
                simp only at h_abs h_conc; cases h_abs; cases h_conc
                exact SubtypeTrans.app_cong ih_f ih_a

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
