import Och.Syntax
import Och.Eval
import Och.Subtyping

/-!
# B3: `concEval` preservation

`concEval` is a CBV evaluator. It β-reduces and unfolds ι/fix/let/asc.
Each individual step is captured by the head-step preservation lemmas
in `Soundness/SubtypeSteps.lean` (B1+B2). What B3 needs in addition is
a way to relate the result of recursively evaluating sub-expressions
back to the source term.

## Strengthening to bidirectional equivalence

A direct attempt to prove `Subtype' [] [] e τ → Subtype' [] [] e' τ`
hits a wall in the `app` case: after evaluating both `f` and `a` to
`fv`/`av`, applying `app_cong` to swap them in/out of the spine
requires *both directions* of `f ≡ fv` (and `a ≡ av`), whereas
single-direction preservation only gives one.

The fix is to strengthen the induction to *bidirectional equivalence*:

```
concEval fuel e = .ok e' → Subtype' [] [] e' e ∧ Subtype' [] [] e e'
```

With both directions in hand, every sub-evaluation can be plugged
into `app_cong` (and `letE_cong`) freely. The single-direction
preservation falls out by `Subtype'.trans` with the user's hypothesis.

The closedness side-condition is needed to (a) rule out free `bvar`
(stuck in `concEval`), and (b) thread `concEval_closedAt` through the
recursive call on the β-redex body.
-/

namespace Och.Soundness

/-- The two-direction subtype equivalence between an expression and
the result of `concEval`. Strictly stronger than B3's
single-direction preservation; closing this also closes B3.

The "bidirectional" form is essential because `app_cong` and
`letE_cong` are not contravariant in their right-hand subterm: to
swap `f`/`a` for `fv`/`av` inside an application or let-binding
we need both `x ⊑ y` and `y ⊑ x` for each pair. -/
def concEval_equiv {fuel : Nat} {e e' : Expr}
    (hcl : e.closedAt 0 = true)
    (hstep : concEval fuel e = .ok e') :
    Subtype' [] [] e' e × Subtype' [] [] e e' := by
  induction fuel generalizing e e' with
  | zero => simp [concEval] at hstep
  | succ n ih =>
    match e, hcl, hstep with
    | .bvar _, _, h => simp [concEval] at h
    | .type, _, h =>
      simp only [concEval, Outcome.ok.injEq] at h
      subst h
      exact ⟨.refl _, .refl _⟩
    | .bot, _, h =>
      simp only [concEval, Outcome.ok.injEq] at h
      subst h
      exact ⟨.refl _, .refl _⟩
    | .lam dom body, _, h =>
      simp only [concEval, Outcome.ok.injEq] at h
      subst h
      exact ⟨.refl _, .refl _⟩
    | .iota ann body, _, h =>
      simp only [concEval, Outcome.ok.injEq] at h
      subst h
      exact ⟨.refl _, .refl _⟩
    | .fix ann body, _, h =>
      simp only [concEval, Outcome.ok.injEq] at h
      subst h
      exact ⟨.refl _, .refl _⟩
    | .asc t ty, hcl, h =>
      simp only [Expr.closedAt, Bool.and_eq_true] at hcl
      simp only [concEval] at h
      have ⟨h₁, h₂⟩ := ih hcl.1 h
      -- h₁ : e' ⊑ t, h₂ : t ⊑ e'
      -- Goal: e' ⊑ asc t ty ∧ asc t ty ⊑ e'
      refine ⟨?_, ?_⟩
      · -- e' ⊑ asc t ty: use asc_R on (e' ⊑ t)
        exact .asc_R h₁
      · -- asc t ty ⊑ e': use asc_L on (t ⊑ e')
        exact .asc_L h₂
    | .letE val body, hcl, h =>
      simp only [Expr.closedAt, Bool.and_eq_true] at hcl
      unfold concEval at h
      match hvEv : concEval n val with
      | .outOfFuel => simp [hvEv] at h
      | .error _ => simp [hvEv] at h
      | .ok vv =>
        simp only [hvEv] at h
        have ⟨hvv₁, hvv₂⟩ := ih hcl.1 hvEv
        -- hvv₁ : vv ⊑ val, hvv₂ : val ⊑ vv
        have hvv_cl : vv.closedAt 0 = true := concEval_closedAt hcl.1 hvEv
        have hbsub_cl : (body.subst 0 vv).closedAt 0 = true := by
          have := Expr.subst_closedAt_gen body 0 0 vv
            (by simpa using hcl.2) (by simpa using hvv_cl)
          simpa using this
        have ⟨he₁, he₂⟩ := ih hbsub_cl h
        -- he₁ : e' ⊑ body.subst 0 vv, he₂ : body.subst 0 vv ⊑ e'
        refine ⟨?_, ?_⟩
        · -- e' ⊑ letE val body
          -- Chain: e' ⊑ body.subst 0 vv ⊑ letE vv body ⊑ letE val body
          have step1 : Subtype' [] [] (body.subst 0 vv) (.letE vv body) :=
            .letE_R (.refl _)
          have step2 : Subtype' [] [] (.letE vv body) (.letE val body) :=
            .letE_cong hvv₁ (.refl _)
          exact .trans he₁ (.trans step1 step2)
        · -- letE val body ⊑ e'
          -- Chain: letE val body ⊑ letE vv body ⊑ body.subst 0 vv ⊑ e'
          have step1 : Subtype' [] [] (.letE val body) (.letE vv body) :=
            .letE_cong hvv₂ (.refl _)
          have step2 : Subtype' [] [] (.letE vv body) (body.subst 0 vv) :=
            .letE_L (.refl _)
          exact .trans step1 (.trans step2 he₂)
    | .app f a, hcl, h =>
      simp only [Expr.closedAt, Bool.and_eq_true] at hcl
      unfold concEval at h
      match hfEv : concEval n f, haEv : concEval n a with
      | .outOfFuel, _ => simp only [hfEv] at h; cases h
      | .error _, .outOfFuel => simp only [hfEv, haEv] at h; cases h
      | .error _, .error _ => simp only [hfEv, haEv] at h; cases h
      | .error _, .ok _ => simp only [hfEv, haEv] at h; cases h
      | .ok _, .outOfFuel => simp only [hfEv, haEv] at h; cases h
      | .ok _, .error _ => simp only [hfEv, haEv] at h; cases h
      | .ok fv, .ok av =>
        simp only [hfEv, haEv] at h
        have ⟨hf₁, hf₂⟩ := ih hcl.1 hfEv
        -- hf₁ : fv ⊑ f, hf₂ : f ⊑ fv
        have ⟨ha₁, ha₂⟩ := ih hcl.2 haEv
        -- ha₁ : av ⊑ a, ha₂ : a ⊑ av
        have hfv_cl : fv.closedAt 0 = true := concEval_closedAt hcl.1 hfEv
        have hav_cl : av.closedAt 0 = true := concEval_closedAt hcl.2 haEv
        match fv, hfv_cl, hf₁, hf₂ with
        | .lam dom body, hfvcl, hf₁, hf₂ =>
          -- β case. e' = concEval n (body.subst 0 av).
          simp only [Expr.closedAt, Bool.and_eq_true] at hfvcl
          have hbsub_cl : (body.subst 0 av).closedAt 0 = true := by
            have := Expr.subst_closedAt_gen body 0 0 av
              (by simpa using hfvcl.2) (by simpa using hav_cl)
            simpa using this
          have ⟨he₁, he₂⟩ := ih hbsub_cl h
          -- he₁ : e' ⊑ body.subst 0 av, he₂ : body.subst 0 av ⊑ e'
          refine ⟨?_, ?_⟩
          · -- e' ⊑ app f a
            -- e' ⊑ body.subst 0 av ⊑ app (lam dom body) av ⊑ app f a
            have step1 : Subtype' [] [] (body.subst 0 av)
                (.app (.lam dom body) av) := .beta_R (.refl _)
            have step2 : Subtype' [] [] (.app (.lam dom body) av)
                (.app f a) := .app_cong hf₁ ha₁ ha₂
            exact .trans he₁ (.trans step1 step2)
          · -- app f a ⊑ e'
            have step1 : Subtype' [] [] (.app f a)
                (.app (.lam dom body) av) := .app_cong hf₂ ha₂ ha₁
            have step2 : Subtype' [] [] (.app (.lam dom body) av)
                (body.subst 0 av) := .beta_L (.refl _)
            exact .trans step1 (.trans step2 he₂)
        | .iota ann body, hfvcl, hf₁, hf₂ =>
          -- iota-unfold case.
          -- e' = concEval n (.app (body.subst 0 (iota ann body)) av).
          simp only [Expr.closedAt, Bool.and_eq_true] at hfvcl
          have hiota_cl : (Expr.iota ann body).closedAt 0 = true := by
            simp only [Expr.closedAt, Bool.and_eq_true]
            exact ⟨hfvcl.1, hfvcl.2⟩
          have hbsub_cl : (body.subst 0 (.iota ann body)).closedAt 0 = true := by
            have := Expr.subst_closedAt_gen body 0 0 (.iota ann body)
              (by simpa using hfvcl.2) (by simpa using hiota_cl)
            simpa using this
          have hAppCl : (Expr.app (body.subst 0 (.iota ann body)) av).closedAt 0 = true := by
            simp only [Expr.closedAt, Bool.and_eq_true]
            exact ⟨hbsub_cl, hav_cl⟩
          have ⟨he₁, he₂⟩ := ih hAppCl h
          -- iota ann body ⊑ body.subst 0 (iota ann body) and reverse
          have hUnfoldF : Subtype' [] [] (.iota ann body)
              (body.subst 0 (.iota ann body)) :=
            .unfold_iota_L (.refl _)
          have hUnfoldB : Subtype' [] [] (body.subst 0 (.iota ann body))
              (.iota ann body) :=
            .unfold_iota_R (.refl _)
          refine ⟨?_, ?_⟩
          · -- e' ⊑ app f a
            -- e' ⊑ app (body.subst …) av ⊑ app (iota …) av ⊑ app f a
            have step1 : Subtype' [] [] (.app (body.subst 0 (.iota ann body)) av)
                (.app (.iota ann body) av) :=
              .app_cong hUnfoldB (.refl _) (.refl _)
            have step2 : Subtype' [] [] (.app (.iota ann body) av)
                (.app f a) := .app_cong hf₁ ha₁ ha₂
            exact .trans he₁ (.trans step1 step2)
          · -- app f a ⊑ e'
            have step1 : Subtype' [] [] (.app f a)
                (.app (.iota ann body) av) := .app_cong hf₂ ha₂ ha₁
            have step2 : Subtype' [] [] (.app (.iota ann body) av)
                (.app (body.subst 0 (.iota ann body)) av) :=
              .app_cong hUnfoldF (.refl _) (.refl _)
            exact .trans step1 (.trans step2 he₂)
        | .fix ann body, hfvcl, hf₁, hf₂ =>
          -- fix-unfold case (mirror of iota).
          simp only [Expr.closedAt, Bool.and_eq_true] at hfvcl
          have hfix_cl : (Expr.fix ann body).closedAt 0 = true := by
            simp only [Expr.closedAt, Bool.and_eq_true]
            exact ⟨hfvcl.1, hfvcl.2⟩
          have hbsub_cl : (body.subst 0 (.fix ann body)).closedAt 0 = true := by
            have := Expr.subst_closedAt_gen body 0 0 (.fix ann body)
              (by simpa using hfvcl.2) (by simpa using hfix_cl)
            simpa using this
          have hAppCl : (Expr.app (body.subst 0 (.fix ann body)) av).closedAt 0 = true := by
            simp only [Expr.closedAt, Bool.and_eq_true]
            exact ⟨hbsub_cl, hav_cl⟩
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
        | .type, _, hf₁, hf₂ =>
          -- Neutral case: e' = app .type av.
          injection h with h
          subst h
          refine ⟨?_, ?_⟩
          · exact .app_cong hf₁ ha₁ ha₂
          · exact .app_cong hf₂ ha₂ ha₁
        | .bot, _, hf₁, hf₂ =>
          injection h with h
          subst h
          refine ⟨?_, ?_⟩
          · exact .app_cong hf₁ ha₁ ha₂
          · exact .app_cong hf₂ ha₂ ha₁
        | .bvar k, hfvcl, _, _ =>
          -- concEval can't produce a bvar from a closed term.
          exact absurd hfEv (fun he => concEval_not_bvar he)
        | .app f' a', _, hf₁, hf₂ =>
          injection h with h
          subst h
          refine ⟨?_, ?_⟩
          · exact .app_cong hf₁ ha₁ ha₂
          · exact .app_cong hf₂ ha₂ ha₁
        | .asc t ty, _, _, _ =>
          exact absurd hfEv (fun he => concEval_not_asc he)
        | .letE vv b, _, _, _ =>
          exact absurd hfEv (fun he => concEval_not_letE he)

/-- B3 — `concEval` preservation. Stated against the substrate-agnostic
declarative `Subtype'`. Falls out of `concEval_equiv` by `trans`. The
public-facing alias is `Och.Soundness.concEval_preservation` in
`lean/Och/Soundness.lean`. -/
def concEval_preservation_aux
    {fuel : Nat} {e e' τ : Expr}
    (hcl : e.closedAt 0 = true)
    (hty : Subtype' [] [] e τ)
    (hstep : concEval fuel e = .ok e') :
    Subtype' [] [] e' τ :=
  let ⟨he', _⟩ := concEval_equiv hcl hstep
  he'.trans hty

end Och.Soundness
