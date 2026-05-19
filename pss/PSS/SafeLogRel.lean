import PSS.Sub
import PSS.SubstWf
import PSS.Eval
import PSS.SyntaxLemmas
import PSS.CanonicalForms

/-!
# Type Safety for PSS via Direct Canonical Forms

Uses `PSS.top_not_sub_lam` (Top cannot be a subtype of a lambda type) and
`PSS.lam_sub_lam_inversion` (domain equivalence for lambda-to-lambda subtyping)
from CanonicalForms.lean to prove type safety directly, without a step-indexed
logical relation.

## Architecture

`eval_syntactic` proves that evaluating a well-formed, closed expression:
1. Never produces an error (type safety)
2. Produces a value that is Sub-equivalent to the original and well-formed

The key steps for the application case:
- **Canonical forms**: `top_not_sub_lam` shows fv ≠ Top when f ≤ (λs.⊤)
- **Domain equivalence**: `lam_sub_lam_inversion` extracts Sub [] s d from
  Sub [] (λd.b) (λs.⊤), enabling `subst_wf` for the body substitution
-/

open Expr

namespace PSS.SafeLogRel

/-! ## concEval lemmas -/

private theorem concEval_isVal {fuel : Nat} {e v : Expr}
    (hev : concEval fuel e = .ok v) : v.IsValue := by
  induction fuel generalizing e v with
  | zero => simp [concEval] at hev
  | succ n ih =>
    unfold concEval at hev
    split at hev
    · exact absurd hev (by intro h; cases h)
    · cases hev; exact trivial
    · cases hev; exact trivial
    · split at hev
      · next fv av _ _ =>
        split at hev
        · exact ih hev
        · exact absurd hev (by intro h; cases h)
      · exact absurd hev (by intro h; cases h)
      · exact absurd hev (by intro h; cases h)
      · exact absurd hev (by intro h; cases h)
      · exact absurd hev (by intro h; cases h)

private theorem concEval_closedAt' {fuel : Nat} {e v : Expr}
    (hcl : e.closedAt 0 = true) (hev : concEval fuel e = .ok v) :
    v.closedAt 0 = true := by
  induction fuel generalizing e v with
  | zero => simp [concEval] at hev
  | succ n ih =>
    unfold concEval at hev
    split at hev
    · simp [Expr.closedAt, decide_eq_true_eq] at hcl
    · cases hev; rfl
    · cases hev; exact hcl
    · simp only [Expr.closedAt, Bool.and_eq_true] at hcl
      split at hev
      · next fv av hf ha =>
        split at hev
        · next dom body _ =>
          exact ih (Expr.subst_closedAt_zero
            (by have := ih hcl.1 hf; simp [Expr.closedAt, Bool.and_eq_true] at this; exact this.2)
            (ih hcl.2 ha)) hev
        · exact absurd hev (by intro h; cases h)
      · exact absurd hev (by intro h; cases h)
      · exact absurd hev (by intro h; cases h)
      · exact absurd hev (by intro h; cases h)
      · exact absurd hev (by intro h; cases h)

/-! ## Syntactic eval invariant -/

structure SynEvalProps (fuel : Nat) (e : Expr) : Type where
  no_error : ∀ msg, concEval fuel e ≠ .error msg
  props : ∀ v, concEval fuel e = .ok v →
    PSS.Sub [] v e × PSS.Sub [] e v × PSS.Wf [] v

private noncomputable def eval_syntactic (fuel : Nat) (e : Expr)
    (hcl : e.closedAt 0 = true) (hwf : PSS.Wf [] e) :
    SynEvalProps fuel e := by
  induction fuel generalizing e with
  | zero =>
    exact { no_error := fun _ h => by simp [concEval] at h,
            props := fun _ h => by simp [concEval] at h }
  | succ n ih =>
    match e, hcl, hwf with
    | .bvar _, hcl, _ =>
      exact absurd hcl (by simp [Expr.closedAt, decide_eq_true_eq])
    | .top, _, _ =>
      exact { no_error := fun _ h => by simp [concEval] at h,
              props := fun v hev => by
                simp [concEval] at hev; subst hev; exact ⟨.refl _, .refl _, .top⟩ }
    | .lam _ _, _, hwf =>
      exact { no_error := fun _ h => by simp [concEval] at h,
              props := fun v hev => by
                simp [concEval] at hev; subst hev; exact ⟨.refl _, .refl _, hwf⟩ }
    | .app f a, hcl, hwf =>
      simp only [Expr.closedAt, Bool.and_eq_true] at hcl
      match hwf with
      | .app (s := s) hwf_f hwf_a hwf_s hsub_f_lam hsub_a_s =>
        have ihf := ih f hcl.1 hwf_f
        have iha := ih a hcl.2 hwf_a
        -- fv can't be Top (canonical forms via top_not_sub_lam)
        have fv_not_top : ∀ fv, concEval n f = .ok fv → fv ≠ .top := by
          intro fv hf heq; subst heq
          have fv_data := ihf.props .top hf
          have hsub_top_lam : PSS.Sub [] .top (.lam s .top) :=
            .trans fv_data.1 hsub_f_lam hwf_f
          exact PSS.top_not_sub_lam hsub_top_lam
        -- fv must be a lambda
        have fv_is_lam : ∀ fv, concEval n f = .ok fv → Σ' (d b : Expr), fv = .lam d b := by
          intro fv hf
          match fv, concEval_isVal hf with
          | .top, _ => exact absurd rfl (fv_not_top .top hf)
          | .lam d b, _ => exact ⟨d, b, rfl⟩
          | .bvar _, hval => exact absurd hval id
          | .app _ _, hval => exact absurd hval id
        -- Key: extract domain equivalence directly from Sub
        have app_lam_data : ∀ (d b av : Expr),
            concEval n f = .ok (.lam d b) → concEval n a = .ok av →
            SynEvalProps n (b.subst 0 av) := by
          intro d b av hf ha
          have fv_data := ihf.props (.lam d b) hf
          have av_data := iha.props av ha
          have hwf_fv : PSS.Wf [] (.lam d b) := fv_data.2.2
          have hwf_d : PSS.Wf [] d := match hwf_fv with | .lam hd _ => hd
          have hwf_db : PSS.Wf [d] b := match hwf_fv with | .lam _ hb => hb
          have hwf_av : PSS.Wf [] av := av_data.2.2
          have hcl_av := concEval_closedAt' hcl.2 ha
          have hcl_fv := concEval_closedAt' hcl.1 hf
          -- Extract domain equivalence from Sub [] (.lam d b) (.lam s .top)
          have hfv_sub_lam : PSS.Sub [] (.lam d b) (.lam s .top) :=
            .trans fv_data.1 hsub_f_lam hwf_f
          -- Use lam_sub_lam_inversion to get Sub [] d s × Sub [] s d
          have ⟨hsub_ds, hsub_sd⟩ := PSS.lam_sub_lam_inversion hfv_sub_lam
          -- Now derive Sub [] av d from Sub [] av s + Sub [] s d
          have hsub_av_s : PSS.Sub [] av s := .trans av_data.1 hsub_a_s hwf_a
          have hsub_av_d : PSS.Sub [] av d := .trans hsub_av_s hsub_sd hwf_s
          -- Build Wf for the body substitution
          have hwf_bsubst : PSS.Wf [] (b.subst 0 av) :=
            PSS.subst_wf hwf_db hwf_av hsub_av_d
          have hcl_bsubst : (b.subst 0 av).closedAt 0 = true :=
            Expr.subst_closedAt_zero
              (by simp [Expr.closedAt, Bool.and_eq_true] at hcl_fv; exact hcl_fv.2)
              hcl_av
          -- Use the IH
          exact ih (b.subst 0 av) hcl_bsubst hwf_bsubst
        exact {
          no_error := by
            intro msg herr; unfold concEval at herr
            match hf_eq : concEval n f with
            | .error m => exact ihf.no_error m hf_eq
            | .outOfFuel => simp [hf_eq] at herr
            | .ok fv =>
              match ha_eq : concEval n a with
              | .error m => exact iha.no_error m ha_eq
              | .outOfFuel => simp [hf_eq, ha_eq] at herr
              | .ok av =>
                let ⟨d, b, hlam⟩ := fv_is_lam fv hf_eq
                subst hlam; simp [hf_eq, ha_eq] at herr
                exact (app_lam_data d b av hf_eq ha_eq).no_error msg herr
          props := by
            intro v hev; unfold concEval at hev
            match hf_eq : concEval n f with
            | .error m => exact absurd hf_eq (ihf.no_error m)
            | .outOfFuel => simp [hf_eq] at hev
            | .ok fv =>
              match ha_eq : concEval n a with
              | .error m => exact absurd ha_eq (iha.no_error m)
              | .outOfFuel => simp [hf_eq, ha_eq] at hev
              | .ok av =>
                let ⟨d, b, hlam⟩ := fv_is_lam fv hf_eq
                subst hlam; simp [hf_eq, ha_eq] at hev
                have rec_data := app_lam_data d b av hf_eq ha_eq
                have v_data := rec_data.props v hev
                have fv_data := ihf.props (.lam d b) hf_eq
                have av_data := iha.props av ha_eq
                -- Build the Sub/Wf for the result
                have hwf_fv : PSS.Wf [] (.lam d b) := fv_data.2.2
                have hwf_d : PSS.Wf [] d := match hwf_fv with | .lam hd _ => hd
                have hwf_db : PSS.Wf [d] b := match hwf_fv with | .lam _ hb => hb
                have hwf_av : PSS.Wf [] av := av_data.2.2
                have hfv_sub_lam : PSS.Sub [] (.lam d b) (.lam s .top) :=
                  .trans fv_data.1 hsub_f_lam hwf_f
                have ⟨hsub_ds, hsub_sd⟩ := PSS.lam_sub_lam_inversion hfv_sub_lam
                have hsub_av_s : PSS.Sub [] av s := .trans av_data.1 hsub_a_s hwf_a
                have hsub_av_d : PSS.Sub [] av d := .trans hsub_av_s hsub_sd hwf_s
                have hwf_bsubst : PSS.Wf [] (b.subst 0 av) :=
                  PSS.subst_wf hwf_db hwf_av hsub_av_d
                have h_wf_app_lam : PSS.Wf [] (.app (.lam d b) av) :=
                  .app hwf_fv hwf_av hwf_s hfv_sub_lam hsub_av_s
                exact ⟨
                  .trans (.trans v_data.1 .beta_R hwf_bsubst)
                    (.app_cong fv_data.1 av_data.1 av_data.2.1) h_wf_app_lam,
                  .trans (.trans (.app_cong fv_data.2.1 av_data.2.1 av_data.1) .beta_L h_wf_app_lam)
                    v_data.2.1 hwf_bsubst,
                  v_data.2.2⟩
        }

/-! ## Type Safety -/

theorem type_safety (e : Expr) (hcl : e.closedAt 0 = true) (hwf : PSS.Wf [] e) :
    ∀ (k : Nat) (msg : String), concEval k e ≠ .error msg :=
  fun k msg => (eval_syntactic k e hcl hwf).no_error msg

end PSS.SafeLogRel
