import Och.Syntax
import Och.EvalSubst
import Och.Subtyping
import Och.Soundness.SubtypeSteps
import Och.Soundness.EvalSubstLemmas

/-!
# Bidirectional `evalSubst` equivalence

Mirror of `Och.Soundness.concEval_equiv` for the substitution-based
evaluator `SubstEval.evalSubst`.

```
evalSubst fuel unf e = .ok e' → Subtype' [] [] e' e ∧ Subtype' [] [] e e'
```

In the pure de Bruijn regime, `evalSubst` uses only the standard
`Expr.subst` (no level-var encoding). Under `closedAt 0`, the proof
is straightforward arm-by-arm induction.

## Status

All arms closed. Sorry-free.
-/

namespace Och.Soundness

open SubstEval
open Expr (closedAt)

/-- `evalSubst` preserves `closedAt 0`.  Uses standard `Expr.subst_closedAt`.
    Mirrors `concEval_closedAt`. -/
theorem evalSubst_closedAt {n unf : Nat} {e v : Expr}
    (hcl : e.closedAt 0 = true)
    (h : evalSubst n unf e = .ok v) : v.closedAt 0 = true := by
  induction n generalizing unf e v with
  | zero => rw [evalSubst.eq_1] at h; cases h
  | succ k ih =>
    match e with
    | .bvar j =>
      simp only [closedAt, decide_eq_true_eq] at hcl
      omega
    | .type =>
      rw [evalSubst.eq_3] at h
      simp only [Outcome.ok.injEq] at h; subst h; rfl
    | .bot =>
      rw [evalSubst.eq_4] at h
      simp only [Outcome.ok.injEq] at h; subst h; rfl
    | .lam dom body =>
      rw [evalSubst.eq_5] at h
      simp only [Outcome.ok.injEq] at h; subst h; exact hcl
    | .iota ann body =>
      rw [evalSubst.eq_6] at h
      simp only [Outcome.ok.injEq] at h; subst h; exact hcl
    | .fix ann body =>
      rw [evalSubst.eq_7] at h
      simp only [Outcome.ok.injEq] at h; subst h; exact hcl
    | .asc t ty =>
      simp only [closedAt, Bool.and_eq_true] at hcl
      rw [evalSubst.eq_8] at h
      match ht : evalSubst k unf t with
      | .outOfFuel => rw [ht] at h; cases h
      | .error _ => rw [ht] at h; cases h
      | .ok tv =>
        match hty : evalSubst k unf ty with
        | .outOfFuel => rw [ht, hty] at h; simp only [Outcome.ok_bind] at h; cases h
        | .error _ => rw [ht, hty] at h; simp only [Outcome.ok_bind] at h; cases h
        | .ok tyv =>
          rw [ht, hty] at h
          simp only [Outcome.ok_bind, Outcome.ok.injEq] at h; subst h
          simp only [closedAt, Bool.and_eq_true]
          exact ⟨ih hcl.1 ht, ih hcl.2 hty⟩
    | .app f a =>
      simp only [closedAt, Bool.and_eq_true] at hcl
      rw [evalSubst.eq_9] at h
      match hf : evalSubst k unf f with
      | .outOfFuel => rw [hf] at h; cases h
      | .error _ => rw [hf] at h; cases h
      | .ok fv =>
        have hfcl := ih hcl.1 hf
        match ha : evalSubst k unf a with
        | .outOfFuel => rw [hf, ha] at h; cases h
        | .error _ => rw [hf, ha] at h; cases h
        | .ok av =>
          have hacl := ih hcl.2 ha
          rw [hf, ha] at h
          simp only [Outcome.ok_bind] at h
          cases fv with
          | bvar bk =>
            simp only [closedAt, decide_eq_true_eq] at hfcl
            omega
          | type =>
            simp only at h
            simp only [Outcome.ok.injEq] at h; subst h
            simp only [closedAt, Bool.and_eq_true]
            exact ⟨by simp [closedAt], hacl⟩
          | bot =>
            simp only at h
            simp only [Outcome.ok.injEq] at h; subst h
            simp only [closedAt, Bool.and_eq_true]
            exact ⟨by simp [closedAt], hacl⟩
          | lam _dom body =>
            simp only at h
            simp only [closedAt, Bool.and_eq_true] at hfcl
            have hsub : (body.subst 0 av).closedAt 0 = true :=
              Expr.subst_closedAt (by simpa using hfcl.2) hacl
            exact ih hsub h
          | iota ann body =>
            simp only at h
            split at h
            · simp only [Outcome.ok.injEq] at h
              subst h
              have : (Expr.app (.iota ann body) av).closedAt 0
                  = (closedAt 0 (.iota ann body) && closedAt 0 av) := rfl
              rw [this, Bool.and_eq_true]; exact ⟨hfcl, hacl⟩
            · have hself : (Expr.iota ann body).closedAt 0 = true := hfcl
              simp only [closedAt, Bool.and_eq_true] at hfcl
              have hbody : body.closedAt 1 = true := by simpa using hfcl.2
              have hsub : (body.subst 0 (.iota ann body)).closedAt 0 = true :=
                Expr.subst_closedAt hbody hself
              have hApp : (Expr.app (body.subst 0 (.iota ann body)) av).closedAt 0
                  = true := by
                have : (Expr.app (body.subst 0 (.iota ann body)) av).closedAt 0
                    = (closedAt 0 (body.subst 0 (.iota ann body)) && closedAt 0 av) := rfl
                rw [this, Bool.and_eq_true]; exact ⟨hsub, hacl⟩
              exact ih hApp h
          | fix ann body =>
            simp only at h
            split at h
            · simp only [Outcome.ok.injEq] at h
              subst h
              have : (Expr.app (.fix ann body) av).closedAt 0
                  = (closedAt 0 (.fix ann body) && closedAt 0 av) := rfl
              rw [this, Bool.and_eq_true]; exact ⟨hfcl, hacl⟩
            · have hself : (Expr.fix ann body).closedAt 0 = true := hfcl
              simp only [closedAt, Bool.and_eq_true] at hfcl
              have hbody : body.closedAt 1 = true := by simpa using hfcl.2
              have hsub : (body.subst 0 (.fix ann body)).closedAt 0 = true :=
                Expr.subst_closedAt hbody hself
              have hApp : (Expr.app (body.subst 0 (.fix ann body)) av).closedAt 0
                  = true := by
                have : (Expr.app (body.subst 0 (.fix ann body)) av).closedAt 0
                    = (closedAt 0 (body.subst 0 (.fix ann body)) && closedAt 0 av) := rfl
                rw [this, Bool.and_eq_true]; exact ⟨hsub, hacl⟩
              exact ih hApp h
          | asc inner _ =>
            simp only at h
            have hApp : (Expr.app inner av).closedAt 0 = true := by
              simp only [closedAt, Bool.and_eq_true] at hfcl
              have : (Expr.app inner av).closedAt 0
                  = (inner.closedAt 0 && av.closedAt 0) := rfl
              rw [this, Bool.and_eq_true]; exact ⟨hfcl.1, hacl⟩
            exact ih hApp h
          | app f' a' =>
            simp only at h
            simp only [Outcome.ok.injEq] at h; subst h
            have : (Expr.app (.app f' a') av).closedAt 0
                = (closedAt 0 (.app f' a') && closedAt 0 av) := rfl
            rw [this, Bool.and_eq_true]; exact ⟨hfcl, hacl⟩

/-! ## Main equivalence

We prove the bidirectional equivalence on `closedAt 0` inputs. -/

/-- The two-direction subtype equivalence between an expression and
the result of `evalSubst`.  Mirrors `concEval_equiv`. -/
def evalSubst_equiv {fuel unf : Nat} {e e' : Expr}
    (hcl : e.closedAt 0 = true)
    (hstep : evalSubst fuel unf e = .ok e') :
    Subtype' [] [] e' e × Subtype' [] [] e e' := by
  induction fuel generalizing unf e e' with
  | zero => rw [evalSubst.eq_1] at hstep; cases hstep
  | succ n ih =>
    match e, hcl, hstep with
    | .bvar k, hcl, h =>
      simp only [closedAt, decide_eq_true_eq] at hcl
      omega
    | .type, _, h =>
      rw [evalSubst.eq_3] at h
      simp only [Outcome.ok.injEq] at h; subst h
      exact ⟨.refl _, .refl _⟩
    | .bot, _, h =>
      rw [evalSubst.eq_4] at h
      simp only [Outcome.ok.injEq] at h; subst h
      exact ⟨.refl _, .refl _⟩
    | .lam dom body, _, h =>
      rw [evalSubst.eq_5] at h
      simp only [Outcome.ok.injEq] at h; subst h
      exact ⟨.refl _, .refl _⟩
    | .iota ann body, _, h =>
      rw [evalSubst.eq_6] at h
      simp only [Outcome.ok.injEq] at h; subst h
      exact ⟨.refl _, .refl _⟩
    | .fix ann body, _, h =>
      rw [evalSubst.eq_7] at h
      simp only [Outcome.ok.injEq] at h; subst h
      exact ⟨.refl _, .refl _⟩
    | .asc t ty, hcl, h =>
      simp only [closedAt, Bool.and_eq_true] at hcl
      rw [evalSubst.eq_8] at h
      match ht : evalSubst n unf t with
      | .outOfFuel => rw [ht] at h; cases h
      | .error _ => rw [ht] at h; cases h
      | .ok tv =>
        match hty : evalSubst n unf ty with
        | .outOfFuel => rw [ht, hty] at h; simp only [Outcome.ok_bind] at h; cases h
        | .error _ => rw [ht, hty] at h; simp only [Outcome.ok_bind] at h; cases h
        | .ok tyv =>
          rw [ht, hty] at h
          simp only [Outcome.ok_bind, Outcome.ok.injEq] at h; subst h
          have ⟨ht₁, ht₂⟩ := ih hcl.1 ht
          refine ⟨?_, ?_⟩
          · exact .asc_L (.asc_R ht₁)
          · exact .asc_L (.asc_R ht₂)
    | .app f a, hcl, h =>
      simp only [closedAt, Bool.and_eq_true] at hcl
      rw [evalSubst.eq_9] at h
      match hfEv : evalSubst n unf f with
      | .outOfFuel => rw [hfEv] at h; cases h
      | .error _ => rw [hfEv] at h; cases h
      | .ok fv =>
        have ⟨hf₁, hf₂⟩ := ih hcl.1 hfEv
        match haEv : evalSubst n unf a with
        | .outOfFuel => rw [hfEv, haEv] at h; cases h
        | .error _ => rw [hfEv, haEv] at h; cases h
        | .ok av =>
          have ⟨ha₁, ha₂⟩ := ih hcl.2 haEv
          rw [hfEv, haEv] at h
          simp only [Outcome.ok_bind] at h
          have hfv_cl : fv.closedAt 0 = true := evalSubst_closedAt hcl.1 hfEv
          have hav_cl : av.closedAt 0 = true := evalSubst_closedAt hcl.2 haEv
          cases fv with
          | bvar bk =>
            simp only [closedAt, decide_eq_true_eq] at hfv_cl
            omega
          | type =>
            simp only at h
            simp only [Outcome.ok.injEq] at h; subst h
            exact ⟨.app_cong hf₁ ha₁ ha₂, .app_cong hf₂ ha₂ ha₁⟩
          | bot =>
            simp only at h
            simp only [Outcome.ok.injEq] at h; subst h
            exact ⟨.app_cong hf₁ ha₁ ha₂, .app_cong hf₂ ha₂ ha₁⟩
          | lam dom body =>
            simp only at h
            simp only [closedAt, Bool.and_eq_true] at hfv_cl
            have hbsub_cl : (body.subst 0 av).closedAt 0 = true :=
              Expr.subst_closedAt (by simpa using hfv_cl.2) hav_cl
            have ⟨he₁, he₂⟩ := ih hbsub_cl h
            refine ⟨?_, ?_⟩
            · have step1 : Subtype' [] [] (body.subst 0 av)
                  (.app (.lam dom body) av) := .beta_R (.refl _)
              have step2 : Subtype' [] [] (.app (.lam dom body) av)
                  (.app f a) := .app_cong hf₁ ha₁ ha₂
              exact .trans he₁ (.trans step1 step2)
            · have step1 : Subtype' [] [] (.app f a)
                  (.app (.lam dom body) av) := .app_cong hf₂ ha₂ ha₁
              have step2 : Subtype' [] [] (.app (.lam dom body) av)
                  (body.subst 0 av) := .beta_L (.refl _)
              exact .trans step1 (.trans step2 he₂)
          | iota ann body =>
            simp only at h
            split at h
            · rename_i hcond
              simp only [Outcome.ok.injEq] at h; subst h
              exact ⟨.app_cong hf₁ ha₁ ha₂, .app_cong hf₂ ha₂ ha₁⟩
            · rename_i hcond
              have hself : (Expr.iota ann body).closedAt 0 = true := hfv_cl
              simp only [closedAt, Bool.and_eq_true] at hfv_cl
              have hbody : body.closedAt 1 = true := by simpa using hfv_cl.2
              have hbsub_cl : (body.subst 0 (.iota ann body)).closedAt 0 = true :=
                Expr.subst_closedAt hbody hself
              have hAppCl : (Expr.app (body.subst 0 (.iota ann body)) av).closedAt 0
                  = true := by
                simp only [closedAt, Bool.and_eq_true]; exact ⟨hbsub_cl, hav_cl⟩
              have ⟨he₁, he₂⟩ := ih hAppCl h
              have hUnfoldF : Subtype' [] [] (.iota ann body)
                  (body.subst 0 (.iota ann body)) :=
                .unfold_iota_L (.refl _)
              have hUnfoldB : Subtype' [] [] (body.subst 0 (.iota ann body))
                  (.iota ann body) :=
                .unfold_iota_R (.refl _)
              refine ⟨?_, ?_⟩
              · have step1 : Subtype' [] [] (.app (body.subst 0 (.iota ann body)) av)
                    (.app (.iota ann body) av) :=
                  .app_cong hUnfoldB (.refl _) (.refl _)
                have step2 : Subtype' [] [] (.app (.iota ann body) av)
                    (.app f a) := .app_cong hf₁ ha₁ ha₂
                exact .trans he₁ (.trans step1 step2)
              · have step1 : Subtype' [] [] (.app f a)
                    (.app (.iota ann body) av) := .app_cong hf₂ ha₂ ha₁
                have step2 : Subtype' [] [] (.app (.iota ann body) av)
                    (.app (body.subst 0 (.iota ann body)) av) :=
                  .app_cong hUnfoldF (.refl _) (.refl _)
                exact .trans step1 (.trans step2 he₂)
          | fix ann body =>
            simp only at h
            split at h
            · rename_i hcond
              simp only [Outcome.ok.injEq] at h; subst h
              exact ⟨.app_cong hf₁ ha₁ ha₂, .app_cong hf₂ ha₂ ha₁⟩
            · rename_i hcond
              have hself : (Expr.fix ann body).closedAt 0 = true := hfv_cl
              simp only [closedAt, Bool.and_eq_true] at hfv_cl
              have hbody : body.closedAt 1 = true := by simpa using hfv_cl.2
              have hbsub_cl : (body.subst 0 (.fix ann body)).closedAt 0 = true :=
                Expr.subst_closedAt hbody hself
              have hAppCl : (Expr.app (body.subst 0 (.fix ann body)) av).closedAt 0
                  = true := by
                simp only [closedAt, Bool.and_eq_true]; exact ⟨hbsub_cl, hav_cl⟩
              have ⟨he₁, he₂⟩ := ih hAppCl h
              have hUnfoldF : Subtype' [] [] (.fix ann body)
                  (body.subst 0 (.fix ann body)) :=
                .unfold_fix_L (.refl _)
              have hUnfoldB : Subtype' [] [] (body.subst 0 (.fix ann body))
                  (.fix ann body) :=
                .unfold_fix_R (.refl _)
              refine ⟨?_, ?_⟩
              · have step1 : Subtype' [] [] (.app (body.subst 0 (.fix ann body)) av)
                    (.app (.fix ann body) av) :=
                  .app_cong hUnfoldB (.refl _) (.refl _)
                have step2 : Subtype' [] [] (.app (.fix ann body) av)
                    (.app f a) := .app_cong hf₁ ha₁ ha₂
                exact .trans he₁ (.trans step1 step2)
              · have step1 : Subtype' [] [] (.app f a)
                    (.app (.fix ann body) av) := .app_cong hf₂ ha₂ ha₁
                have step2 : Subtype' [] [] (.app (.fix ann body) av)
                    (.app (body.subst 0 (.fix ann body)) av) :=
                  .app_cong hUnfoldF (.refl _) (.refl _)
                exact .trans step1 (.trans step2 he₂)
          | asc inner _ =>
            simp only at h
            have hApp_cl : (Expr.app inner av).closedAt 0 = true := by
              simp only [closedAt, Bool.and_eq_true] at hfv_cl
              have : (Expr.app inner av).closedAt 0
                  = (inner.closedAt 0 && av.closedAt 0) := rfl
              rw [this, Bool.and_eq_true]; exact ⟨hfv_cl.1, hav_cl⟩
            have ⟨he₁, he₂⟩ := ih hApp_cl h
            have hInner_f : Subtype' [] [] inner f :=
              .trans (.asc_R (.refl _)) hf₁
            have hf_inner : Subtype' [] [] f inner :=
              .trans hf₂ (.asc_L (.refl _))
            refine ⟨?_, ?_⟩
            · exact .trans he₁ (.app_cong hInner_f ha₁ ha₂)
            · exact .trans (.app_cong hf_inner ha₂ ha₁) he₂
          | app f' a' =>
            simp only at h
            simp only [Outcome.ok.injEq] at h; subst h
            exact ⟨.app_cong hf₁ ha₁ ha₂, .app_cong hf₂ ha₂ ha₁⟩

/-- B3-substrate-style preservation, derived from `evalSubst_equiv`. -/
def evalSubst_preservation_aux
    {fuel unf : Nat} {e e' τ : Expr}
    (hcl : e.closedAt 0 = true)
    (hty : Subtype' [] [] e τ)
    (hstep : evalSubst fuel unf e = .ok e') :
    Subtype' [] [] e' τ :=
  let ⟨he', _⟩ := evalSubst_equiv hcl hstep
  he'.trans hty

end Och.Soundness
