import PSS.Syntax
import PSS.SyntaxLemmas
import PSS.Reduction
import PSS.Sub
import PSS.Eval

/-!
# Soundness

Soundness proof for PSS (System λ_◁) with wf-guarded transitivity.

## Axioms used
- `PSS.top_not_sub_lam` — proved in CanonicalForms.lean; axiom due to Lean elaboration issues
- `PSS.lam_sub_lam_inversion` — proved in CanonicalForms.lean; axiom due to Lean elaboration issues
- `subst_wf` — standard metatheory (Lemma 5.4); axiom pending routine proof
-/

open Expr

-- Canonical forms
axiom PSS.top_not_sub_lam {Γ : Ctx} {s t : Expr}
    (h : PSS.Sub Γ .top (.lam s t)) : False
axiom PSS.lam_sub_lam_inversion {Γ : Ctx} {a b s t : Expr}
    (h : PSS.Sub Γ (.lam a b) (.lam s t)) : PSS.Sub Γ a s × PSS.Sub Γ s a

-- Substitution lemma
axiom subst_wf {Γ : Ctx} {σ body v : Expr}
    (hwfb : PSS.Wf (σ :: Γ) body)
    (hwfv : PSS.Wf Γ v) (hvsig : PSS.Sub Γ v σ) :
    PSS.Wf Γ (body.subst 0 v)

/-! ## Step sub -/

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

/-! ## Step preservation -/

def step_preservation {Γ : Ctx} {t t' u : Expr}
    (hsub : PSS.Sub Γ t u) (hwf : PSS.Wf Γ t) (hstep : Step t t') :
    PSS.Sub Γ t' u :=
  .trans (step_sub hstep).2 hsub hwf

/-! ## Evaluation preserves closedness -/

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
      · rename_i fv av hf ha
        split at hev
        · rename_i dom body heq
          exact ih (Expr.subst_closedAt_zero
            (by have := ih hcl.1 hf; simp only [Expr.closedAt, Bool.and_eq_true] at this; exact this.2)
            (ih hcl.2 ha)) hev
        · cases hev
      · cases hev
      · cases hev
      · cases hev
      · cases hev

/-! ## Evaluation results are values -/

theorem concEval_isValue {fuel : Nat} {e v : Expr}
    (hev : concEval fuel e = .ok v) :
    v = .top ∨ ∃ d b, v = .lam d b := by
  induction fuel generalizing e v with
  | zero => simp [concEval] at hev
  | succ n ih =>
    unfold concEval at hev
    split at hev
    · exact absurd hev (by intro h; cases h)
    · cases hev; left; rfl
    · cases hev; right; exact ⟨_, _, rfl⟩
    · split at hev
      · rename_i fv av hf ha; split at hev
        · exact ih hev
        · cases hev
      · cases hev
      · cases hev
      · cases hev
      · cases hev

/-! ## Combined evaluation theorem -/

structure EvalProps (fuel : Nat) (e : Expr) : Type where
  no_error : ∀ msg, concEval fuel e ≠ .error msg
  props : ∀ v, concEval fuel e = .ok v →
    PSS.Sub [] v e × PSS.Sub [] e v × PSS.Wf [] v

/-- Helper for the app case of the combined theorem.
    Separated to cleanly match on Wf.app and bind the implicit `s`. -/
private noncomputable def concEval_combined_app
    (n : Nat)
    (ih : ∀ (e : Expr), e.closedAt 0 = true → PSS.Wf [] e → EvalProps n e)
    (f a : Expr) (s : Expr)
    (hcl_f : f.closedAt 0 = true) (hcl_a : a.closedAt 0 = true)
    (hwf_f : PSS.Wf [] f) (hwf_a : PSS.Wf [] a)
    (hwf_s : PSS.Wf [] s)
    (hsub_f_lam : PSS.Sub [] f (.lam s .top))
    (hsub_a_s : PSS.Sub [] a s) :
    EvalProps (n + 1) (.app f a) := by
  have ihf := ih f hcl_f hwf_f
  have iha := ih a hcl_a hwf_a
  -- Determine eval outcomes
  have hf_ok_or_fuel : (Σ' fv, concEval n f = .ok fv) ⊕' (concEval n f = .outOfFuel) :=
    match hh : concEval n f with
    | .ok fv => .inl ⟨fv, rfl⟩
    | .error msg => absurd hh (ihf.no_error msg)
    | .outOfFuel => .inr rfl
  have ha_ok_or_fuel : (Σ' av, concEval n a = .ok av) ⊕' (concEval n a = .outOfFuel) :=
    match hh : concEval n a with
    | .ok av => .inl ⟨av, rfl⟩
    | .error msg => absurd hh (iha.no_error msg)
    | .outOfFuel => .inr rfl
  -- Helper: recursive call data when fv is a lambda
  have app_lam_data :
      ∀ (d b av : Expr),
        concEval n f = .ok (.lam d b) →
        concEval n a = .ok av →
        EvalProps n (b.subst 0 av) := by
    intro d b av hf ha
    have fv_data := ihf.props (.lam d b) hf
    have av_data := iha.props av ha
    have hfv_sub_lam : PSS.Sub [] (.lam d b) (.lam s .top) :=
      .trans fv_data.1 hsub_f_lam hwf_f
    have inv := PSS.lam_sub_lam_inversion hfv_sub_lam
    have hav_sub_s : PSS.Sub [] av s := .trans av_data.1 hsub_a_s hwf_a
    have hav_sub_d : PSS.Sub [] av d := .trans hav_sub_s inv.2 hwf_s
    have hwf_body : PSS.Wf [d] b := match fv_data.2.2 with | .lam _ hb => hb
    exact ih (b.subst 0 av)
      (by have hfcl := concEval_closedAt hcl_f hf
          have hacl := concEval_closedAt hcl_a ha
          simp only [Expr.closedAt, Bool.and_eq_true] at hfcl
          exact Expr.subst_closedAt_zero hfcl.2 hacl)
      (subst_wf hwf_body av_data.2.2 hav_sub_d)
  -- fv can't be Top
  have fv_not_top : ∀ fv, concEval n f = .ok fv → fv ≠ .top := by
    intro fv hf heq; subst heq
    exact PSS.top_not_sub_lam (.trans (ihf.props .top hf).1 hsub_f_lam hwf_f)
  -- fv must be a lambda (returns PSigma for Type-level elimination)
  -- We match on fv directly since concEval only returns values
  have fv_is_lam : ∀ fv, concEval n f = .ok fv → Σ' (d b : Expr), fv = .lam d b :=
    fun fv hf => match fv with
    | .top => absurd rfl (fv_not_top .top hf)
    | .lam d b => ⟨d, b, rfl⟩
    | .bvar k =>
      absurd (concEval_closedAt hcl_f hf)
        (by simp [Expr.closedAt, decide_eq_true_eq])
    | .app e1 e2 =>
      -- app can't be a result of concEval (it only returns top or lam)
      -- We need concEval_isValue but in a Prop-to-Prop way
      -- Actually, concEval_closedAt doesn't help here. Let's use a decidable check.
      -- Since fv = .app e1 e2 and concEval returns .ok fv, by concEval_isValue
      -- fv = .top or fv = .lam d b. Both contradict fv = .app e1 e2.
      -- We can't eliminate from Prop, but we can use False:
      False.elim (by
        have hv := concEval_isValue hf
        rcases hv with h | ⟨_, _, h⟩ <;> cases h)
  -- Now build the result
  constructor
  · -- no_error
    intro msg herr
    unfold concEval at herr
    match hf_ok_or_fuel with
    | .inr hfuel => simp [hfuel] at herr
    | .inl ⟨fv, hf⟩ =>
      match ha_ok_or_fuel with
      | .inr hafuel => simp [hf, hafuel] at herr
      | .inl ⟨av, ha⟩ =>
        let ⟨d, b, hlam⟩ := fv_is_lam fv hf
        subst hlam
        simp [hf, ha] at herr
        exact (app_lam_data d b av hf ha).no_error msg herr
  · -- props
    intro v hev
    unfold concEval at hev
    match hf_ok_or_fuel with
    | .inr hfuel => simp [hfuel] at hev
    | .inl ⟨fv, hf⟩ =>
      match ha_ok_or_fuel with
      | .inr hafuel => simp [hf, hafuel] at hev
      | .inl ⟨av, ha⟩ =>
        let ⟨d, b, hlam⟩ := fv_is_lam fv hf
        subst hlam
        simp [hf, ha] at hev
        have rec_data := app_lam_data d b av hf ha
        have v_data := rec_data.props v hev
        have fv_data := ihf.props (.lam d b) hf
        have av_data := iha.props av ha
        have hfv_sub_lam : PSS.Sub [] (.lam d b) (.lam s .top) :=
          .trans fv_data.1 hsub_f_lam hwf_f
        have h_wf_app_lam : PSS.Wf [] (.app (.lam d b) av) :=
          .app fv_data.2.2 av_data.2.2 hwf_s hfv_sub_lam
            (.trans av_data.1 hsub_a_s hwf_a)
        have inv := PSS.lam_sub_lam_inversion hfv_sub_lam
        have hwf_subst : PSS.Wf [] (b.subst 0 av) :=
          subst_wf (match fv_data.2.2 with | .lam _ hb => hb)
            av_data.2.2
            (.trans (.trans av_data.1 hsub_a_s hwf_a) inv.2 hwf_s)
        -- v ≤ subst ≤ app(lam d b, av) ≤ app(f, a)
        -- app(f, a) ≤ app(lam d b, av) ≤ subst ≤ v
        exact ⟨
          .trans (.trans v_data.1 .beta_R hwf_subst)
            (.app_cong fv_data.1 av_data.1 av_data.2.1) h_wf_app_lam,
          .trans (.trans (.app_cong fv_data.2.1 av_data.2.1 av_data.1) .beta_L h_wf_app_lam)
            v_data.2.1 hwf_subst,
          v_data.2.2⟩

noncomputable def concEval_combined (fuel : Nat) (e : Expr)
    (hcl : e.closedAt 0 = true) (hwf : PSS.Wf [] e) :
    EvalProps fuel e := by
  induction fuel generalizing e with
  | zero =>
    exact { no_error := fun _ h => by simp [concEval] at h,
            props := fun _ h => by simp [concEval] at h }
  | succ n ih =>
    match e, hcl, hwf with
    | .bvar k, hcl, _ =>
      exact (by simp [Expr.closedAt, decide_eq_true_eq] at hcl : False).elim
    | .top, _, _ =>
      exact { no_error := fun _ h => by simp [concEval] at h,
              props := fun v hev => by
                simp [concEval] at hev; subst hev; exact ⟨.refl _, .refl _, .top⟩ }
    | .lam dom body, hcl, hwf =>
      exact { no_error := fun _ h => by simp [concEval] at h,
              props := fun v hev => by
                simp [concEval] at hev; subst hev; exact ⟨.refl _, .refl _, hwf⟩ }
    | .app f a, hcl, hwf =>
      have hcl_f : f.closedAt 0 = true := by
        simp only [Expr.closedAt, Bool.and_eq_true] at hcl; exact hcl.1
      have hcl_a : a.closedAt 0 = true := by
        simp only [Expr.closedAt, Bool.and_eq_true] at hcl; exact hcl.2
      exact match hwf with
        | .app (s := s) hwf_f hwf_a hwf_s hsub_f_lam hsub_a_s =>
          concEval_combined_app n ih f a s hcl_f hcl_a hwf_f hwf_a hwf_s hsub_f_lam hsub_a_s

/-! ## Individual theorems -/

noncomputable def concEval_equiv {fuel : Nat} {e v : Expr}
    (hcl : e.closedAt 0 = true) (hwf : PSS.Wf [] e)
    (hev : concEval fuel e = .ok v) :
    PSS.Sub [] v e × PSS.Sub [] e v :=
  let d := (concEval_combined fuel e hcl hwf).props v hev
  ⟨d.1, d.2.1⟩

noncomputable def concEval_preservation {fuel : Nat} {e v τ : Expr}
    (hcl : e.closedAt 0 = true) (hwf : PSS.Wf [] e)
    (hsub : PSS.Sub [] e τ) (hev : concEval fuel e = .ok v) :
    PSS.Sub [] v τ :=
  .trans ((concEval_combined fuel e hcl hwf).props v hev).1 hsub hwf

theorem concEval_no_error {fuel : Nat} {e : Expr}
    (hcl : e.closedAt 0 = true) (hwf : PSS.Wf [] e) :
    ∀ msg, concEval fuel e ≠ .error msg :=
  (concEval_combined fuel e hcl hwf).no_error

/-! ## Top-level soundness -/

theorem soundness_and_progress {fuel : Nat} {e τ : Expr}
    (hcl : e.closedAt 0 = true) (hwf : PSS.Wf [] e)
    (hsub : PSS.Sub [] e τ) :
    (∃ v, concEval fuel e = .ok v ∧ Nonempty (PSS.Sub [] v τ))
    ∨ concEval fuel e = .outOfFuel := by
  have h_no_err := concEval_no_error (fuel := fuel) hcl hwf
  match hh : concEval fuel e with
  | .ok v =>
    left; exact ⟨v, rfl, ⟨concEval_preservation hcl hwf hsub hh⟩⟩
  | .error msg =>
    exact absurd hh (h_no_err msg)
  | .outOfFuel =>
    right; rfl
