import PSS.Syntax
import PSS.SyntaxLemmas
import PSS.Reduction
import PSS.Sub
import PSS.Eval

/-!
# Soundness

Och-style soundness proof for PSS (System λ_◁).
-/

open Expr

/-!
## Small-step reduction implies bidirectional subtyping
-/

private theorem step_sub_aux {t t' : Expr} (h : Step t t') :
    ∀ (Γ : Ctx), PSS.Sub Γ t t' ∧ PSS.Sub Γ t' t := by
  induction h with
  | beta => intro Γ; exact ⟨.beta_L, .beta_R⟩
  | app_fun _ ih =>
    intro Γ; have := ih Γ
    exact ⟨.app_cong this.1 (.refl _) (.refl _),
           .app_cong this.2 (.refl _) (.refl _)⟩
  | app_arg _ ih =>
    intro Γ; have := ih Γ
    exact ⟨.app_cong (.refl _) this.1 this.2,
           .app_cong (.refl _) this.2 this.1⟩
  | lam_dom _ ih =>
    intro Γ; have := ih Γ
    exact ⟨.lam this.1 this.2 (.refl _),
           .lam this.2 this.1 (.refl _)⟩
  | @lam_body dom _ _ _ ih =>
    intro Γ; have := ih (dom :: Γ)
    exact ⟨.lam (.refl _) (.refl _) this.1,
           .lam (.refl _) (.refl _) this.2⟩

theorem step_sub {Γ : Ctx} {t t' : Expr} (h : Step t t') :
    PSS.Sub Γ t t' ∧ PSS.Sub Γ t' t :=
  step_sub_aux h Γ

theorem step_preservation {Γ : Ctx} {t t' u : Expr}
    (hsub : PSS.Sub Γ t u) (hstep : Step t t') : PSS.Sub Γ t' u :=
  .trans (step_sub hstep).2 hsub

/-!
## Evaluation preserves closedness
-/

theorem concEval_closedAt {fuel : Nat} {e v : Expr}
    (hcl : e.closedAt 0 = true)
    (hev : concEval fuel e = .ok v) : v.closedAt 0 = true := by
  induction fuel generalizing e v with
  | zero => simp [concEval] at hev
  | succ n ih =>
    unfold concEval at hev
    split at hev
    · -- bvar
      simp only [Expr.closedAt, decide_eq_true_eq] at hcl; omega
    · -- top
      cases hev; rfl
    · -- lam
      cases hev; exact hcl
    · -- app f a
      next f a =>
      simp only [Expr.closedAt, Bool.and_eq_true] at hcl
      split at hev
      · -- .ok (.lam dom body), .ok av => concEval n (body.subst 0 av)
        rename_i dom body av hf ha
        have hclf := ih hcl.1 hf
        have hcla := ih hcl.2 ha
        simp only [Expr.closedAt, Bool.and_eq_true] at hclf
        exact ih (Expr.subst_closedAt_zero hclf.2 hcla) hev
      · -- .ok fv, .ok av (non-lam) => .ok (.app fv av)
        rename_i fv av _ hf ha
        cases hev
        simp only [Expr.closedAt, Bool.and_eq_true]
        exact ⟨ih hcl.1 hf, ih hcl.2 ha⟩
      · cases hev  -- .outOfFuel = .ok v
      · cases hev  -- .outOfFuel = .ok v
      · cases hev  -- .error = .ok v
      · cases hev  -- .error = .ok v

/-!
## Big-step evaluation equivalence
-/

theorem concEval_equiv {fuel : Nat} {e v : Expr}
    (hcl : e.closedAt 0 = true)
    (hev : concEval fuel e = .ok v) :
    PSS.Sub [] v e ∧ PSS.Sub [] e v := by
  induction fuel generalizing e v with
  | zero => simp [concEval] at hev
  | succ n ih =>
    unfold concEval at hev
    split at hev
    · -- bvar
      simp only [Expr.closedAt, decide_eq_true_eq] at hcl; omega
    · -- top
      cases hev; exact ⟨.refl _, .refl _⟩
    · -- lam
      cases hev; exact ⟨.refl _, .refl _⟩
    · -- app f a
      next f a =>
      simp only [Expr.closedAt, Bool.and_eq_true] at hcl
      split at hev
      · -- .ok (.lam dom body), .ok av => beta-reduction
        rename_i dom body av hf ha
        -- closedness of subterms
        have hclf := concEval_closedAt hcl.1 hf
        have hcla := concEval_closedAt hcl.2 ha
        simp only [Expr.closedAt, Bool.and_eq_true] at hclf
        have hcl_subst := Expr.subst_closedAt_zero hclf.2 hcla
        -- IH on all three evaluations
        have ihsub := ih hcl_subst hev
        have ihf := ih hcl.1 hf
        have iha := ih hcl.2 ha
        constructor
        · -- v ≤ app f a
          exact .trans ihsub.1 (.trans .beta_R (.app_cong ihf.1 iha.1 iha.2))
        · -- app f a ≤ v
          exact .trans (.app_cong ihf.2 iha.2 iha.1) (.trans .beta_L ihsub.2)
      · -- .ok fv, .ok av (non-lam) => stuck app
        rename_i fv av _ hf ha
        cases hev
        have ihf := ih hcl.1 hf
        have iha := ih hcl.2 ha
        exact ⟨.app_cong ihf.1 iha.1 iha.2, .app_cong ihf.2 iha.2 iha.1⟩
      · cases hev  -- .outOfFuel = .ok v
      · cases hev  -- .outOfFuel = .ok v
      · cases hev  -- .error = .ok v
      · cases hev  -- .error = .ok v

/-- **Big-step preservation**: one-liner from `concEval_equiv` and `trans`. -/
theorem concEval_preservation {fuel : Nat} {e v τ : Expr}
    (hcl : e.closedAt 0 = true)
    (hsub : PSS.Sub [] e τ)
    (hev : concEval fuel e = .ok v) :
    PSS.Sub [] v τ :=
  .trans (concEval_equiv hcl hev).1 hsub

/-!
## Progress: closed terms never crash
-/

theorem concEval_no_error {fuel : Nat} {e : Expr}
    (hcl : e.closedAt 0 = true) :
    ∀ msg, concEval fuel e ≠ .error msg := by
  induction fuel generalizing e with
  | zero => intro; simp [concEval]
  | succ n ih =>
    intro msg hmsg
    unfold concEval at hmsg
    split at hmsg
    · -- bvar
      simp only [Expr.closedAt, decide_eq_true_eq] at hcl; omega
    · simp at hmsg  -- top
    · simp at hmsg  -- lam
    · -- app f a
      next f a =>
      simp only [Expr.closedAt, Bool.and_eq_true] at hcl
      split at hmsg
      · -- beta: concEval n (body.subst 0 av) = .error msg
        rename_i dom body av hf ha
        have hclf := concEval_closedAt hcl.1 hf
        have hcla := concEval_closedAt hcl.2 ha
        simp only [Expr.closedAt, Bool.and_eq_true] at hclf
        exact ih (Expr.subst_closedAt_zero hclf.2 hcla) msg hmsg
      · -- stuck: .ok (fv.app av) = .error msg — contradiction
        cases hmsg
      · cases hmsg  -- .outOfFuel = .error
      · cases hmsg  -- .outOfFuel = .error
      · -- .error s from f: concEval n f = .error s
        rename_i s hf _
        exact absurd hf (ih hcl.1 s)
      · -- .error s from a: concEval n a = .error s
        rename_i s ha _ _
        exact absurd ha (ih hcl.2 s)

/-!
## Top-level soundness theorems
-/

theorem soundness {fuel : Nat} {e v τ : Expr}
    (hcl : e.closedAt 0 = true) (hsub : PSS.Sub [] e τ)
    (hev : concEval fuel e = .ok v) : PSS.Sub [] v τ :=
  concEval_preservation hcl hsub hev

theorem soundness_no_error {fuel : Nat} {e τ : Expr}
    (hcl : e.closedAt 0 = true) (_hsub : PSS.Sub [] e τ) :
    ∀ msg, concEval fuel e ≠ .error msg :=
  concEval_no_error hcl

theorem soundness_and_progress {fuel : Nat} {e τ : Expr}
    (hcl : e.closedAt 0 = true) (hsub : PSS.Sub [] e τ) :
    (∃ v, concEval fuel e = .ok v ∧ PSS.Sub [] v τ)
    ∨ concEval fuel e = .outOfFuel := by
  match h : concEval fuel e with
  | .ok v => left; exact ⟨v, rfl, concEval_preservation hcl hsub h⟩
  | .outOfFuel => right; rfl
  | .error msg => exact absurd h (concEval_no_error hcl msg)
