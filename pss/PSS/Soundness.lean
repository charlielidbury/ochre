import PSS.Syntax
import PSS.SyntaxLemmas
import PSS.Reduction
import PSS.Sub
import PSS.Eval

/-!
# Soundness

Soundness proof for PSS (System λ_◁) with wf-guarded transitivity.

## What's proved
- `step_sub` — reduction implies bidirectional subtyping (no trans needed)
- `concEval_closedAt` — evaluation preserves closedness

## What's sorry'd (the hard parts)
- `step_preservation` — needs `Wf` for the trans midpoint
- `concEval_equiv` — needs `Wf` preservation through eval
- `concEval_no_error` — needs inversion lemma (the open problem)
- `soundness_and_progress` — depends on all the above
-/

open Expr

/-!
## Small-step reduction implies bidirectional subtyping

Still fully proved — none of these cases use `trans`.
-/

private def step_sub_aux {t t' : Expr} (h : Step t t') :
    ∀ (Γ : Ctx), PSS.Sub Γ t t' × PSS.Sub Γ t' t :=
  match h with
  | .beta => fun _Γ => ⟨.beta_L, .beta_R⟩
  | .app_fun hf =>
    let ih := step_sub_aux hf
    fun Γ => let ⟨l, r⟩ := ih Γ
      ⟨.app_cong l (.refl _) (.refl _), .app_cong r (.refl _) (.refl _)⟩
  | .app_arg ha =>
    let ih := step_sub_aux ha
    fun Γ => let ⟨l, r⟩ := ih Γ
      ⟨.app_cong (.refl _) l r, .app_cong (.refl _) r l⟩
  | .lam_dom hd =>
    let ih := step_sub_aux hd
    fun Γ => let ⟨l, r⟩ := ih Γ
      ⟨.lam l r (.refl _), .lam r l (.refl _)⟩
  | @Step.lam_body dom _ _ hb =>
    let ih := step_sub_aux hb
    fun Γ => let ⟨l, r⟩ := ih (dom :: Γ)
      ⟨.lam (.refl _) (.refl _) l, .lam (.refl _) (.refl _) r⟩

def step_sub {Γ : Ctx} {t t' : Expr} (h : Step t t') :
    PSS.Sub Γ t t' × PSS.Sub Γ t' t :=
  step_sub_aux h Γ

/-!
## Preservation (sorry — needs Wf for trans midpoint)
-/

def step_preservation {Γ : Ctx} {t t' u : Expr}
    (hsub : PSS.Sub Γ t u) (hwf : PSS.Wf Γ t) (hstep : Step t t') :
    PSS.Sub Γ t' u :=
  sorry

/-!
## Evaluation preserves closedness

Still fully proved — doesn't use Sub at all.
-/

theorem concEval_closedAt {fuel : Nat} {e v : Expr}
    (hcl : e.closedAt 0 = true)
    (hev : concEval fuel e = .ok v) : v.closedAt 0 = true := by
  induction fuel generalizing e v with
  | zero => simp [concEval] at hev
  | succ n ih =>
    unfold concEval at hev
    split at hev
    · simp only [Expr.closedAt, decide_eq_true_eq] at hcl; omega
    · cases hev; rfl
    · cases hev; exact hcl
    · next f a =>
      simp only [Expr.closedAt, Bool.and_eq_true] at hcl
      split at hev
      · -- ok fv, ok av
        rename_i fv av hf ha
        split at hev
        · -- fv = lam: beta reduction
          rename_i dom body heq
          have hfcl := ih hcl.1 hf
          have hacl := ih hcl.2 ha
          simp only [Expr.closedAt, Bool.and_eq_true] at hfcl
          exact ih (Expr.subst_closedAt_zero hfcl.2 hacl) hev
        · -- fv ≠ lam: error, contradicts hev
          cases hev
      · cases hev
      · cases hev
      · cases hev
      · cases hev

/-!
## Evaluation equivalence (sorry — needs Wf preservation)
-/

def concEval_equiv {fuel : Nat} {e v : Expr}
    (hcl : e.closedAt 0 = true)
    (hwf : PSS.Wf [] e)
    (hev : concEval fuel e = .ok v) :
    PSS.Sub [] v e × PSS.Sub [] e v :=
  sorry

/-!
## Preservation and progress (sorry — depend on the above)
-/

def concEval_preservation {fuel : Nat} {e v τ : Expr}
    (hcl : e.closedAt 0 = true)
    (hwf : PSS.Wf [] e)
    (hsub : PSS.Sub [] e τ)
    (hev : concEval fuel e = .ok v) :
    PSS.Sub [] v τ :=
  sorry

theorem concEval_no_error {fuel : Nat} {e : Expr}
    (hcl : e.closedAt 0 = true)
    (hwf : PSS.Wf [] e) :
    ∀ msg, concEval fuel e ≠ .error msg :=
  sorry

/-!
## Top-level soundness
-/

theorem soundness_and_progress {fuel : Nat} {e τ : Expr}
    (hcl : e.closedAt 0 = true)
    (hwf : PSS.Wf [] e)
    (hsub : PSS.Sub [] e τ) :
    (∃ v, concEval fuel e = .ok v ∧ Nonempty (PSS.Sub [] v τ))
    ∨ concEval fuel e = .outOfFuel :=
  sorry
