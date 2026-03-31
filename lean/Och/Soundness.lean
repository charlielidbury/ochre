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
    | .fix inner =>
        match inner with
        | .lam f dom body =>
            ∃ dom', absEval fuel Γ dom = some dom' ∧
                    WellTyped fuel ((f, dom') :: Γ) body ∧
                    ∃ σ, absEval fuel ((f, dom') :: Γ) body = some σ ∧
                         Subtype' σ dom'
        | _ => False
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

/-- An environment has no `.fix` values. Used to show absEval never
    returns `.fix`, which eliminates an impossible case in soundness. -/
def EnvNoFix (Γ : Env) : Prop :=
  ∀ x inner, Γ.lookup x ≠ some (.fix inner)

theorem envNoFix_nil : EnvNoFix [] := by
  intro x inner; simp [Env.lookup]

theorem envNoFix_extend {Γ : Env} (h : EnvNoFix Γ) (y : Name) {v : Expr}
    (hv : ∀ inner, v ≠ .fix inner) :
    EnvNoFix ((y, v) :: Γ) := by
  intro x inner h_lookup
  simp only [Env.lookup] at h_lookup
  split at h_lookup
  · exact absurd (Option.some.inj h_lookup) (hv inner)
  · exact h x inner h_lookup

/-- absEval never returns `.fix` when the environment is fix-free.
    This is because absEval only produces var (from env), lam, type, app,
    or recursively calls itself — it never constructs a `.fix` node. -/
theorem absEval_not_fix {fuel : Nat} {Γ : Env} {e v : Expr}
    (h_no_fix : EnvNoFix Γ)
    (h_eval : absEval fuel Γ e = some v) :
    ∀ inner, v ≠ .fix inner := by
  induction fuel generalizing Γ e v with
  | zero => simp [absEval] at h_eval
  | succ n ih =>
    cases e with
    | var x =>
      simp only [absEval] at h_eval
      intro inner heq; subst heq; exact absurd h_eval (h_no_fix x inner)
    | type =>
      simp only [absEval] at h_eval
      have h := Option.some.inj h_eval; subst h
      exact fun _ heq => Expr.noConfusion heq
    | lam x dom body =>
      simp only [absEval] at h_eval
      split at h_eval
      · have h := Option.some.inj h_eval; subst h
        exact fun _ heq => Expr.noConfusion heq
      · exact nomatch h_eval
    | asc _ ty =>
      simp only [absEval] at h_eval
      exact ih h_no_fix h_eval
    | fix inner' =>
      simp only [absEval] at h_eval
      cases inner' with
      | lam _ _ _ => exact ih h_no_fix h_eval
      | _ => exact nomatch h_eval
    | app f_e a_e =>
      simp only [absEval] at h_eval
      generalize hf : absEval n Γ f_e = rf at h_eval
      generalize ha : absEval n Γ a_e = ra at h_eval
      cases rf with
      | none => cases ra <;> simp at h_eval
      | some vf =>
        cases ra with
        | none => simp at h_eval
        | some va =>
          cases vf with
          | lam x_l dom_l body_l =>
            simp only at h_eval
            exact ih (envNoFix_extend h_no_fix x_l (ih h_no_fix ha)) h_eval
          | type =>
            simp only at h_eval
            have h := Option.some.inj h_eval; subst h
            exact fun _ heq => Expr.noConfusion heq
          | var x' =>
            simp only at h_eval
            have h := Option.some.inj h_eval; subst h
            exact fun _ heq => Expr.noConfusion heq
          | app f' a' =>
            simp only at h_eval
            have h := Option.some.inj h_eval; subst h
            exact fun _ heq => Expr.noConfusion heq
          | asc t' τ' =>
            simp only at h_eval
            have h := Option.some.inj h_eval; subst h
            exact fun _ heq => Expr.noConfusion heq
          | fix inner' =>
            simp only at h_eval
            have h := Option.some.inj h_eval; subst h
            exact fun _ heq => Expr.noConfusion heq

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
    - fix → fix (fix_target_shape)
    - type → anything (trivial via top)
-/
theorem soundness_gen
    (fuel : Nat) (Γ : Env) (γ : Env) (e_a e_c τ v : Expr)
    (h_sub : SubtypeTrans e_c e_a)
    (h_abs : absEval fuel Γ e_a = some τ)
    (h_conc : concEval fuel γ e_c = some v)
    (h_env : EnvConsistent γ Γ)
    (h_wt : WellTyped fuel Γ e_a)
    (h_no_fix : EnvNoFix Γ)
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
          have h_nf' : EnvNoFix ((x, Expr.var x) :: Γ) := by
            apply envNoFix_extend h_no_fix
            intro inner h
            exact absurd h (by simp [Expr.var, Expr.fix])
          exact SubtypeTrans.lam_body (ih _ _ body_a body_c _ _ h_body_sub hba hbc h_env' h_wt' h_nf')
    | asc term ty =>
      -- SubtypeTrans e_c (asc term ty) → e_c = asc term ty
      have := h_sub.asc_target; subst this
      simp only [absEval, concEval] at h_abs h_conc
      have ⟨h_wt_term, _, σ, τ', h_abs_term, h_abs_ty, h_sub_wt⟩ := h_wt
      rw [h_abs] at h_abs_ty; cases h_abs_ty
      have h_vs := ih Γ γ term term σ v (SubtypeTrans.step (Subtype'.refl term))
        h_abs_term h_conc h_env h_wt_term h_no_fix
      exact SubtypeTrans.trans h_vs (SubtypeTrans.step h_sub_wt)
    | fix inner_a =>
      -- SubtypeTrans e_c (.fix inner_a) → e_c = .fix inner_c
      obtain ⟨inner_c, hec_eq, h_inner_sub⟩ := h_sub.fix_target_shape
      subst hec_eq
      simp only [absEval, concEval] at h_abs h_conc
      -- Abstract: inner_a must be a lam (else absEval returns none)
      -- Concrete: inner_c must also be a lam (by SubtypeTrans shape)
      -- The soundness of fix requires showing that the concrete fixpoint
      -- unrolling produces a value ⊑ the declared type. This requires
      -- EnvConsistent between (f, .fix inner_c) and (f, dom'), which
      -- requires SubtypeTrans (.fix inner_c) dom' — the very property
      -- we're trying to prove. This circularity is broken by fuel induction,
      -- but formalizing it requires a more sophisticated proof strategy.
      sorry
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
              have ih_f := ih _ _ f_a f_c _ _ h_f_sub hfa hfc h_env h_wt_f h_no_fix
              have ih_a := ih _ _ a_a a_c _ _ h_a_sub haa hac h_env h_wt_a h_no_fix
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
                  (envNoFix_extend h_no_fix x (absEval_not_fix h_no_fix haa))
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
              | fix inner' =>
                -- absEval never produces .fix when the env is fix-free
                exact absurd rfl (absEval_not_fix h_no_fix hfa inner')

/-- **Soundness theorem.**

    If abstract evaluation gives type `τ` and concrete evaluation gives value `v`,
    then `SubtypeTrans v τ`. -/
theorem soundness
    (Γ : Env) (γ : Env) (e τ v : Expr) (fuel : Nat)
    (h_abs : absEval fuel Γ e = some τ)
    (h_conc : concEval fuel γ e = some v)
    (h_env : EnvConsistent γ Γ)
    (h_wt : WellTyped fuel Γ e)
    (h_no_fix : EnvNoFix Γ)
    : SubtypeTrans v τ :=
  soundness_gen fuel Γ γ e e τ v (SubtypeTrans.step (Subtype'.refl e))
    h_abs h_conc h_env h_wt h_no_fix
