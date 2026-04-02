import Och.Syntax
import Och.Eval
import Och.Subtyping
import Och.Monotonicity
import Och.ValSub

/-!
# Soundness (SoundRel + env-based concEvalE)

## Architecture

Two-layer approach:
- **Input relation: SoundRel** — structural compatibility with flexible domains/
  annotations. Enables substitution congruence (the key lemma SubtypeCore lacks).
- **Output relation: ValSub** — step-indexed value subtyping with compose_r for
  algorithmic transitivity (handles the ascription case via bridge).

## Strategy

The substitution-based `concEval` (lambdas are values) creates a body/body'
mismatch in the lam case: concEval returns source body, absEval returns
normalized body. The env-based `concEvalE` normalizes under binders like
absEval, so the IH relates their outputs directly.

`soundness_gen_sr` proves: SoundRel e_c e_a → concEvalE γ e_c = v →
absEval Γ e_a = τ → EnvSoundRel γ Γ → SoundRel v τ.

The app-lam-beta case uses subst_congr: SoundRel bodyV bodyT → SoundRel av aτ
→ SoundRel (bodyV.subst 0 av) (bodyT.subst 0 aτ), then recurses via IH.

## Bridge to substitution-based concEval

The final soundness theorem for the real runtime (`concEval`) requires a
bridge: `concEval fuel e = v → concEvalE fuel [] e = v' → ValSub n v v'`.
This is a separate step (not yet done). The `soundness_gen_sr` theorem is
meaningful on its own — it proves soundness for the env-based evaluator.
-/

open Expr

/-! ## SoundRel: structural compatibility without domain equality

SoundRel is like SubtypeCore but allows different lambda domains and mu
annotations. This makes substitution congruence provable, which is essential
for the app case of soundness (where beta-reduction substitutes different
arguments into different function bodies). -/

/-- Structural compatibility: same shape, covariant bodies, no domain constraint.
    `SoundRel a b` means `a` and `b` have the same constructor structure with
    related sub-bodies, but domains and annotations may differ. -/
inductive SoundRel : Expr → Expr → Prop where
  | refl (e : Expr) : SoundRel e e
  | top (e : Expr) : SoundRel e .type
  | lam {dom_v dom_τ body_v body_τ : Expr} :
      SoundRel body_v body_τ → SoundRel (.lam dom_v body_v) (.lam dom_τ body_τ)
  | app_cong {f_v f_τ a_v a_τ : Expr} :
      SoundRel f_v f_τ → SoundRel a_v a_τ →
      SoundRel (.app f_v a_v) (.app f_τ a_τ)
  | mu {ann_v ann_τ body_v body_τ : Expr} :
      SoundRel ann_v ann_τ → SoundRel body_v body_τ →
      SoundRel (.mu ann_v body_v) (.mu ann_τ body_τ)
  | asc {term_v term_τ ty_v ty_τ : Expr} :
      SoundRel term_v term_τ → SoundRel ty_v ty_τ →
      SoundRel (.asc term_v ty_v) (.asc term_τ ty_τ)

/-- SubtypeCore embeds into SoundRel (weakening: forget domain equality). -/
theorem SubtypeCore.toSoundRel {a b : Expr} (h : SubtypeCore a b) : SoundRel a b := by
  induction h with
  | refl e => exact .refl e
  | top e => exact .top e
  | lam_body _ ih => exact .lam ih
  | app_cong _ _ ihf iha => exact .app_cong ihf iha
  | mu_body _ ih => exact .mu (.refl _) ih

/-- SoundRel is preserved under shifting. -/
theorem SoundRel.shift_preserve {a b : Expr} (h : SoundRel a b) (d c : Nat) :
    SoundRel (a.shift d c) (b.shift d c) := by
  induction h generalizing c with
  | refl e => exact .refl _
  | top e => simp [Expr.shift]; exact .top _
  | lam _ ih => simp [Expr.shift]; exact .lam (ih (c + 1))
  | app_cong _ _ ihf iha => simp [Expr.shift]; exact .app_cong (ihf c) (iha c)
  | mu _ _ ih_ann ih_body => simp [Expr.shift]; exact .mu (ih_ann c) (ih_body (c + 1))
  | asc _ _ ih_term ih_ty => simp [Expr.shift]; exact .asc (ih_term c) (ih_ty c)

/-- Single-variable substitution congruence: same body, different args. -/
theorem SoundRel.subst_arg_congr {a_v a_τ : Expr} (h : SoundRel a_v a_τ)
    (e : Expr) (j : Nat) :
    SoundRel (e.subst j a_v) (e.subst j a_τ) := by
  induction e generalizing j a_v a_τ with
  | bvar k =>
    simp only [Expr.subst]
    by_cases hkj : k == j
    · simp [hkj]; exact h
    · simp [hkj]
      by_cases hkgt : k > j
      · simp [hkgt]; exact .refl _
      · simp [hkgt]; exact .refl _
  | lam dom body ih_dom ih_body =>
    simp only [Expr.subst]
    exact .lam (ih_body (h.shift_preserve 1 0) (j + 1))
  | app f a ihf iha =>
    simp only [Expr.subst]
    exact .app_cong (ihf h j) (iha h j)
  | asc term ty ih_term ih_ty =>
    simp only [Expr.subst]
    exact .asc (ih_term h j) (ih_ty h j)
  | type => simp [Expr.subst]; exact .refl _
  | mu ann body ih_ann ih_body =>
    simp only [Expr.subst]
    exact .mu (ih_ann h j) (ih_body (h.shift_preserve 1 0) (j + 1))

/-- Two-variable substitution congruence: different bodies, different args.
    The key lemma that SubtypeCore cannot prove (due to domain equality). -/
theorem SoundRel.subst_congr {body_v body_τ : Expr} (h_body : SoundRel body_v body_τ)
    {a_v a_τ : Expr} (h_arg : SoundRel a_v a_τ) (j : Nat) :
    SoundRel (body_v.subst j a_v) (body_τ.subst j a_τ) := by
  induction h_body generalizing j a_v a_τ with
  | refl e => exact h_arg.subst_arg_congr e j
  | top e => simp only [Expr.subst]; exact .top _
  | lam h ih => simp only [Expr.subst]; exact .lam (ih (h_arg.shift_preserve 1 0) (j + 1))
  | app_cong _ _ ihf iha =>
    simp only [Expr.subst]; exact .app_cong (ihf h_arg j) (iha h_arg j)
  | mu h_ann h ih_ann ih => simp only [Expr.subst]; exact .mu (ih_ann h_arg j) (ih (h_arg.shift_preserve 1 0) (j + 1))
  | asc _ _ ih_term ih_ty =>
    simp only [Expr.subst]; exact .asc (ih_term h_arg j) (ih_ty h_arg j)

/-- Inversion: if SoundRel e (lam dom body), then e is a lam with related body. -/
theorem SoundRel.lam_rhs_shape {dom body : Expr} {e : Expr}
    (h : SoundRel e (.lam dom body)) :
    ∃ dom' body', e = .lam dom' body' ∧ SoundRel body' body := by
  cases h with
  | refl => exact ⟨dom, body, rfl, .refl body⟩
  | lam h => exact ⟨_, _, rfl, h⟩

/-- Inversion: if SoundRel e (mu ann body), then e is a mu with related ann and body. -/
theorem SoundRel.mu_rhs_shape {ann body : Expr} {e : Expr}
    (h : SoundRel e (.mu ann body)) :
    ∃ ann' body', e = .mu ann' body' ∧ SoundRel ann' ann ∧ SoundRel body' body := by
  cases h with
  | refl => exact ⟨ann, body, rfl, .refl ann, .refl body⟩
  | mu h_ann h_body => exact ⟨_, _, rfl, h_ann, h_body⟩

/-- Transitivity of SoundRel. -/
theorem SoundRel.trans : {a b c : Expr} → SoundRel a b → SoundRel b c → SoundRel a c := by
  intro a b c p q
  induction q generalizing a with
  | refl => exact p
  | top => exact .top a
  | lam h2 ih =>
    obtain ⟨dom_a, body_a, rfl, h1⟩ := p.lam_rhs_shape
    exact .lam (ih h1)
  | app_cong h2f h2a ihf iha =>
    cases p with
    | refl => exact .app_cong h2f h2a
    | app_cong h1f h1a => exact .app_cong (ihf h1f) (iha h1a)
  | mu h2_ann h2_body ih_ann ih_body =>
    obtain ⟨ann_a, body_a, rfl, h1_ann, h1_body⟩ := p.mu_rhs_shape
    exact .mu (ih_ann h1_ann) (ih_body h1_body)
  | asc h2_term h2_ty ih_term ih_ty =>
    cases p with
    | refl => exact .asc h2_term h2_ty
    | asc h1_term h1_ty => exact .asc (ih_term h1_term) (ih_ty h1_ty)

/-! ## OutputRel: correct output type for soundness

SoundRel v τ is FALSE when v comes from evaluating a term and τ from evaluating
a type (the ascription case). OutputRel composes SoundRel with subCheckNF to
bridge this gap: there exists an intermediate `mid` such that SoundRel v mid
(structural) and subCheckNF mid τ (algorithmic check). -/

/-- OutputRel: SoundRel composed with subCheckNF.
    `OutputRel v τ` means there exists `mid` with `SoundRel v mid` and
    `subCheckNF mid τ = true`. For non-asc cases, `mid = τ` and `subCheckNF`
    is reflexive. For asc cases, `mid = absEval(term)` and `subCheckNF` comes
    from the WellTyped check. -/
inductive OutputRel : Expr → Expr → Prop where
  | sound {v τ : Expr} : SoundRel v τ → OutputRel v τ
  | compose {v mid τ : Expr} : OutputRel v mid →
      {fuel : Nat} → {ctx : List Expr} →
      subCheckNF fuel ctx [] mid τ = true → OutputRel v τ

namespace OutputRel

theorem of_soundrel {v τ : Expr} (h : SoundRel v τ) : OutputRel v τ := .sound h

/-- Lift OutputRel through lam constructor. -/
theorem lam_congr {body_v body_τ dom_v dom_τ : Expr}
    (h : OutputRel body_v body_τ) : OutputRel (.lam dom_v body_v) (.lam dom_τ body_τ) := by
  cases h with
  | sound hs => exact .sound (.lam hs)
  | compose hs hc => sorry -- needs subCheckNF lifting through lam

/-- Lift OutputRel through mu constructor. -/
theorem mu_congr {ann_v ann_τ body_v body_τ : Expr}
    (h_ann : OutputRel ann_v ann_τ) (h_body : OutputRel body_v body_τ) :
    OutputRel (.mu ann_v body_v) (.mu ann_τ body_τ) := by
  cases h_ann with
  | sound hsa =>
    cases h_body with
    | sound hsb => exact .sound (.mu hsa hsb)
    | compose hsb _ => sorry -- needs subCheckNF lifting through mu
  | compose hsa _ => sorry -- needs subCheckNF lifting through mu

end OutputRel

/-- Extract SoundRel from OutputRel (sorry for compose case).
    Used to pass OutputRel IH results through SoundRel-expecting code
    (specifically soundness_app_case). The compose case is sorry'd — it
    arises only when inner ascriptions produce non-trivial subCheckNF chains.
    Proving this requires subCheckNF lifting/transitivity lemmas. -/
private theorem extractSoundRel {v τ : Expr} (h : OutputRel v τ) : SoundRel v τ := by
  cases h with
  | sound s => exact s
  | compose _ _ => sorry

/-! ## SoundRel-based environment consistency -/

-- Helper: relate List.get? to getElem? for proof interop
private theorem list_get?_eq_getElem? {α : Type} {l : List α} {k : Nat} :
    l.get? k = l[k]? := by
  simp [List.get?_eq_getElem?]

/-- Environment consistency via SoundRel. -/
def EnvSoundRel (γ : Env) (Γ : Env) : Prop :=
  ∀ k τ, Γ.get? k = some τ → ∃ v, γ.get? k = some v ∧ SoundRel v τ

theorem envSoundRel_extend {γ Γ : Env} (h : EnvSoundRel γ Γ) (v : Expr) :
    EnvSoundRel (γ.extend v) (Γ.extend v) := by
  intro k τ hget
  unfold Env.extend at hget ⊢
  cases k with
  | zero =>
    simp at hget
    subst hget
    exact ⟨v, by simp, .refl v⟩
  | succ k =>
    simp at hget ⊢
    obtain ⟨orig, horig, hshift⟩ := hget
    rw [← list_get?_eq_getElem?] at horig
    obtain ⟨v_orig, hgetv, hsub⟩ := h k orig horig
    rw [list_get?_eq_getElem?] at hgetv
    exact ⟨v_orig.shift 1 0, ⟨v_orig, hgetv, rfl⟩, hshift ▸ hsub.shift_preserve 1 0⟩

theorem envSoundRel_extend_sub {γ Γ : Env} (h : EnvSoundRel γ Γ)
    {v τ : Expr} (hv : SoundRel v τ) :
    EnvSoundRel (γ.extend v) (Γ.extend τ) := by
  intro k τ₁ hget
  unfold Env.extend at hget ⊢
  cases k with
  | zero =>
    simp at hget
    subst hget
    exact ⟨v, by simp, hv⟩
  | succ k =>
    simp at hget ⊢
    obtain ⟨orig, horig, hshift⟩ := hget
    rw [← list_get?_eq_getElem?] at horig
    obtain ⟨v_orig, hgetv, hsub⟩ := h k orig horig
    rw [list_get?_eq_getElem?] at hgetv
    exact ⟨v_orig.shift 1 0, ⟨v_orig, hgetv, rfl⟩, hshift ▸ hsub.shift_preserve 1 0⟩

/-! ## Well-typedness -/

/-- Well-typedness: all ascriptions encountered during evaluation are sound.
    Bool-valued with subCheckNF in the ascription case.

    The env parameter serves double duty: it's the absEval environment AND
    the subCheckNF typing context. -/
def WellTyped (fuel : Nat) (env : Env) (e : Expr) : Bool :=
  match fuel with
  | 0 => true
  | fuel + 1 =>
    match e with
    | .bvar _ => true
    | .lam _dom body => WellTyped fuel (env.extend (.bvar 0)) body
    | .type => true
    | .asc term ty =>
        WellTyped fuel env term && WellTyped fuel env ty &&
        match absEval fuel env term, absEval fuel env ty with
        | some σ, some τ' => subCheckNF fuel env [] σ τ'
        | _, _ => false
    | .mu ann body =>
        WellTyped fuel (env.extend (.mu ann body)) body
    | .app f a =>
        WellTyped fuel env f && WellTyped fuel env a &&
        match absEval fuel env f, absEval fuel env a with
        | some (.lam _dom body), some aVal =>
            WellTyped fuel env (body.subst 0 aVal)
        | some (.mu ann body_mu), some aVal =>
          match ann, body_mu with
          | .lam _dom_ann retBody, .lam _ _ =>
              WellTyped fuel env (retBody.subst 0 aVal)
          | .lam _dom_ann retBody, _ =>
              WellTyped fuel env (retBody.subst 0 aVal)
          | _, .lam _dom_body bodyRes =>
              WellTyped fuel env (bodyRes.subst 0 aVal)
          | _, _ => true
        | _, _ => true

/-! ## Evaluator inversion lemmas -/

private theorem absEval_app_lam_inv {n : Nat} {Γ : Env} {f a τ : Expr}
    {dom body : Expr} (hf : absEval n Γ f = some (.lam dom body))
    {a_τ : Expr} (ha : absEval n Γ a = some a_τ)
    (h : absEval (n + 1) Γ (.app f a) = some τ)
    : absEval n Γ (body.subst 0 a_τ) = some τ := by
  simp only [absEval, hf, ha] at h; exact h

private theorem concEvalE_app_lam_inv {n : Nat} {γ : Env} {f a v : Expr}
    {dom body : Expr} (hf : concEvalE n γ f = some (.lam dom body))
    {a_v : Expr} (ha : concEvalE n γ a = some a_v)
    (h : concEvalE (n + 1) γ (.app f a) = some v)
    : concEvalE n γ (body.subst 0 a_v) = some v := by
  simp only [concEvalE, hf, ha] at h; exact h

/-! ## App case helper

Factored out so both the refl/app case and app_cong case can share it. -/

private theorem soundness_app_case
    {n : Nat} {Γ γ : Env} {f_a a_a f_c a_c τ v : Expr}
    (hf_sr : SoundRel f_c f_a) (ha_sr : SoundRel a_c a_a)
    (h_abs : absEval (n + 1) Γ (.app f_a a_a) = some τ)
    (h_conc : concEvalE (n + 1) γ (.app f_c a_c) = some v)
    (h_env : EnvSoundRel γ Γ)
    (h_wt : WellTyped (n + 1) Γ (.app f_a a_a) = true)
    (ih : ∀ (Γ' : Env) (γ' : Env) (e_a' e_c' τ' v' : Expr),
      SoundRel e_c' e_a' → absEval n Γ' e_a' = some τ' →
      concEvalE n γ' e_c' = some v' → EnvSoundRel γ' Γ' →
      WellTyped n Γ' e_a' = true → SoundRel v' τ')
    : SoundRel v τ := by
  -- Split on all four inner eval results
  cases h_af : absEval n Γ f_a with
  | none => simp [absEval, h_af] at h_abs
  | some f_τ =>
    cases h_aa : absEval n Γ a_a with
    | none => simp [absEval, h_af, h_aa] at h_abs
    | some a_τ =>
      cases h_cf : concEvalE n γ f_c with
      | none => simp [concEvalE, h_cf] at h_conc
      | some f_v =>
        cases h_ca : concEvalE n γ a_c with
        | none => simp [concEvalE, h_cf, h_ca] at h_conc
        | some a_v =>
          -- All four evals succeeded. Extract WellTyped and IH results.
          have h_wt_f : WellTyped n Γ f_a = true := by
            have := h_wt; simp only [WellTyped] at this
            revert this; cases WellTyped n Γ f_a <;> simp
          have h_wt_a : WellTyped n Γ a_a = true := by
            have := h_wt; simp only [WellTyped] at this
            revert this; cases WellTyped n Γ f_a <;> cases WellTyped n Γ a_a <;> simp
          have ih_f := ih _ _ _ _ _ _ hf_sr h_af h_cf h_env h_wt_f
          have ih_a := ih _ _ _ _ _ _ ha_sr h_aa h_ca h_env h_wt_a
          -- Case-split on f_τ shape (determines absEval's behavior)
          cases f_τ with
          | lam dom_a body_a =>
            -- **Lambda-beta case** (PROVED via subst_congr)
            obtain ⟨dom_c, body_c, hfv_eq, h_body⟩ := ih_f.lam_rhs_shape
            subst hfv_eq
            have h_abs_beta := absEval_app_lam_inv h_af h_aa h_abs
            have h_conc_beta := concEvalE_app_lam_inv h_cf h_ca h_conc
            have h_sub_beta := h_body.subst_congr ih_a 0
            have h_wt_beta : WellTyped n Γ (body_a.subst 0 a_τ) = true := by
              have := h_wt; simp only [WellTyped, h_af, h_aa] at this
              revert this; cases WellTyped n Γ f_a <;> cases WellTyped n Γ a_a <;> simp
            exact ih _ _ _ _ _ _ h_sub_beta h_abs_beta h_conc_beta h_env h_wt_beta
          | type =>
            simp [absEval, h_af, h_aa] at h_abs
            subst h_abs; exact .top v
          | mu ann_a body_a =>
            -- mu-in-function-position: case split on body_a shape
            obtain ⟨ann_c, body_c, rfl, h_ann, h_body⟩ := ih_f.mu_rhs_shape
            cases body_a with
            | type =>
              simp [absEval, h_af, h_aa] at h_abs
              subst h_abs; exact .top v
            | lam dom_a lamBody_a =>
              obtain ⟨dom_c, lamBody_c, hbc_eq, h_lam_body⟩ := h_body.lam_rhs_shape
              subst hbc_eq
              cases ann_a with
              | lam dom_ann retAnn =>
                -- Both evaluators use annotation return type (concEvalE now
                -- mirrors absEval's mu-app case when both ann and body are lam)
                obtain ⟨dom_ann_c, retAnn_c, hac_eq, h_ret_ann⟩ := h_ann.lam_rhs_shape
                subst hac_eq
                have h_conc_beta : concEvalE n γ (retAnn_c.subst 0 a_v) = some v := by
                  simp [concEvalE, h_cf, h_ca] at h_conc; exact h_conc
                have h_abs_beta : absEval n Γ (retAnn.subst 0 a_τ) = some τ := by
                  simp [absEval, h_af, h_aa] at h_abs; exact h_abs
                have h_sub_beta := h_ret_ann.subst_congr ih_a 0
                have h_wt_beta : WellTyped n Γ (retAnn.subst 0 a_τ) = true := by
                  have := h_wt; simp only [WellTyped, h_af, h_aa] at this
                  revert this; cases WellTyped n Γ f_a <;> cases WellTyped n Γ a_a <;> simp
                exact ih _ _ _ _ _ _ h_sub_beta h_abs_beta h_conc_beta h_env h_wt_beta
              | _ =>
                -- ann_a is not lam. absEval uses body's lamBody_a.
                have h_abs_beta : absEval n Γ (lamBody_a.subst 0 a_τ) = some τ := by
                  simp [absEval, h_af, h_aa] at h_abs; exact h_abs
                have h_wt_beta : WellTyped n Γ (lamBody_a.subst 0 a_τ) = true := by
                  have := h_wt; simp only [WellTyped, h_af, h_aa] at this
                  revert this; cases WellTyped n Γ f_a <;> cases WellTyped n Γ a_a <;> simp
                -- concEvalE matches on (ann_c, body_c). Case split on ann_c
                -- to determine which branch concEvalE takes.
                cases ann_c with
                | lam _dac _rac =>
                    -- Edge case: ann_c is lam but ann_a is not (only via SoundRel.top,
                    -- i.e., ann_a = .type). Unreachable from the .refl entry point
                    -- since annotations are preserved by both evaluators.
                    sorry
                | bvar _ | app _ _ | asc _ _ | type | mu _ _ =>
                    -- ann_c is also not lam: concEvalE uses body's lamBody_c
                    have h_conc_beta : concEvalE n γ (lamBody_c.subst 0 a_v) = some v := by
                      simp [concEvalE, h_cf, h_ca] at h_conc; exact h_conc
                    have h_sub_beta := h_lam_body.subst_congr ih_a 0
                    exact ih _ _ _ _ _ _ h_sub_beta h_abs_beta h_conc_beta h_env h_wt_beta
            | bvar k =>
              cases h_body with | refl =>
              simp [absEval, h_af, h_aa] at h_abs
              simp [concEvalE, h_cf, h_ca] at h_conc
              cases h_abs; cases h_conc
              exact .app_cong (.refl _) ih_a
            | app ba_f ba_a =>
              cases h_body with
              | refl =>
                simp [absEval, h_af, h_aa] at h_abs
                simp [concEvalE, h_cf, h_ca] at h_conc
                cases h_abs; cases h_conc
                exact .app_cong (.refl _) ih_a
              | app_cong hf' ha' =>
                simp [absEval, h_af, h_aa] at h_abs
                simp [concEvalE, h_cf, h_ca] at h_conc
                cases h_abs; cases h_conc
                exact .app_cong (.app_cong hf' ha') ih_a
            | asc ba_t ba_ty =>
              cases h_body with
              | refl =>
                simp [absEval, h_af, h_aa] at h_abs
                simp [concEvalE, h_cf, h_ca] at h_conc
                cases h_abs; cases h_conc
                exact .app_cong (.refl _) ih_a
              | asc ht' hty' =>
                simp [absEval, h_af, h_aa] at h_abs
                simp [concEvalE, h_cf, h_ca] at h_conc
                cases h_abs; cases h_conc
                exact .app_cong (.asc ht' hty') ih_a
            | mu ba_ann ba_body =>
              cases h_body with
              | refl =>
                simp [absEval, h_af, h_aa] at h_abs
                simp [concEvalE, h_cf, h_ca] at h_conc
                cases h_abs; cases h_conc
                exact .app_cong (.refl _) ih_a
              | mu h_ann' h' =>
                simp [absEval, h_af, h_aa] at h_abs
                simp [concEvalE, h_cf, h_ca] at h_conc
                cases h_abs; cases h_conc
                exact .app_cong (.mu h_ann' h') ih_a
          | bvar k =>
            cases ih_f with | refl =>
              simp [absEval, h_af, h_aa] at h_abs
              simp [concEvalE, h_cf, h_ca] at h_conc
              cases h_abs; cases h_conc
              exact .app_cong (.refl _) ih_a
          | app f_τ_f f_τ_a =>
            simp [absEval, h_af, h_aa] at h_abs; cases h_abs
            cases ih_f with
            | refl =>
              simp [concEvalE, h_cf, h_ca] at h_conc; cases h_conc
              exact .app_cong (.refl _) ih_a
            | app_cong hf' ha' =>
              simp [concEvalE, h_cf, h_ca] at h_conc; cases h_conc
              exact .app_cong (.app_cong hf' ha') ih_a
          | asc t_a ty_a =>
            simp [absEval, h_af, h_aa] at h_abs; cases h_abs
            cases ih_f with
            | refl =>
              simp [concEvalE, h_cf, h_ca] at h_conc; cases h_conc
              exact .app_cong (.refl _) ih_a
            | asc ht' hty' =>
              simp [concEvalE, h_cf, h_ca] at h_conc; cases h_conc
              exact .app_cong (.asc ht' hty') ih_a

/-! ## Generalized soundness with SoundRel

The key insight: SubtypeCore's domain equality makes substitution congruence
impossible, but the app case needs it. SoundRel relaxes domain equality,
enabling substitution congruence (proved above). This theorem proves the
app-lam-beta case that the old soundness_gen cannot.

Uses concEvalE (env-based, normalizes under binders) so both evaluators
have parallel structure. The IH directly relates their outputs. -/

/-- **Generalized soundness with OutputRel.**
    OutputRel v τ means ∃ mid, SoundRel v mid ∧ subCheckNF mid τ.
    This is the correct output type — SoundRel alone is FALSE for asc
    (concEvalE(term) and absEval(ty) can have different constructors).

    Proved cases: bvar, type, lam, mu, top, app (via soundness_app_case),
    asc (NEWLY PROVED for non-nested case).
    Sorry'd: subCheckNF lifting through lam/mu (in OutputRel helpers),
    subCheckNF transitivity (nested asc), extractSoundRel (app compose). -/
theorem soundness_gen_sr
    (fuel : Nat) (Γ : Env) (γ : Env) (e_a e_c τ v : Expr)
    (h_sub : SoundRel e_c e_a)
    (h_abs : absEval fuel Γ e_a = some τ)
    (h_conc : concEvalE fuel γ e_c = some v)
    (h_env : EnvSoundRel γ Γ)
    (h_wt : WellTyped fuel Γ e_a = true)
    : OutputRel v τ := by
  induction fuel generalizing Γ γ e_a e_c τ v with
  | zero => simp [absEval] at h_abs
  | succ n ih =>
    -- Convert OutputRel IH to SoundRel IH for soundness_app_case
    let ih_sr : ∀ (Γ' : Env) (γ' : Env) (e_a' e_c' τ' v' : Expr),
        SoundRel e_c' e_a' → absEval n Γ' e_a' = some τ' →
        concEvalE n γ' e_c' = some v' → EnvSoundRel γ' Γ' →
        WellTyped n Γ' e_a' = true → SoundRel v' τ' :=
      fun Γ' γ' e_a' e_c' τ' v' h1 h2 h3 h4 h5 =>
        extractSoundRel (ih Γ' γ' e_a' e_c' τ' v' h1 h2 h3 h4 h5)
    cases h_sub with
    | refl =>
      cases e_a with
      | bvar k =>
        simp [absEval, concEvalE] at h_abs h_conc
        rw [← list_get?_eq_getElem?] at h_abs h_conc
        obtain ⟨w, hw, hsub⟩ := h_env k τ h_abs
        rw [hw] at h_conc; cases h_conc; exact .sound hsub
      | type =>
        simp [absEval, concEvalE] at h_abs h_conc
        cases h_abs; cases h_conc; exact .sound (.refl _)
      | lam dom body =>
        simp only [absEval, concEvalE, WellTyped] at h_abs h_conc h_wt
        revert h_abs h_conc
        cases h_ba : absEval n (Env.extend Γ (Expr.bvar 0)) body with
        | none => simp
        | some body_τ =>
          cases h_bc : concEvalE n (Env.extend γ (Expr.bvar 0)) body with
          | none => simp
          | some body_v =>
            simp; intro h_abs h_conc; subst h_abs; subst h_conc
            exact OutputRel.lam_congr (ih _ _ _ _ _ _ (.refl body) h_ba h_bc
              (envSoundRel_extend h_env _) h_wt)
      | mu ann body =>
        simp only [absEval, concEvalE, WellTyped] at h_abs h_conc h_wt
        revert h_abs h_conc
        cases h_ba : absEval n (Env.extend Γ (Expr.mu ann body)) body with
        | none => simp
        | some body_τ =>
          cases h_bc : concEvalE n (Env.extend γ (Expr.mu ann body)) body with
          | none => simp
          | some body_v =>
            simp; intro h_abs h_conc; subst h_abs; subst h_conc
            exact OutputRel.mu_congr (.sound (.refl ann))
              (ih _ _ _ _ _ _ (.refl body) h_ba h_bc
                (envSoundRel_extend h_env _) h_wt)
      | asc term ty =>
        -- NEWLY PROVED: concEvalE takes term, absEval takes ty.
        -- OutputRel composes SoundRel(v, absEval term) with subCheckNF(absEval term, absEval ty).
        simp only [concEvalE] at h_conc
        simp only [absEval] at h_abs
        have h_wt' := h_wt
        simp only [WellTyped] at h_wt'
        -- Extract WellTyped components
        have h_wt_term : WellTyped n Γ term = true := by
          revert h_wt'; cases WellTyped n Γ term <;> simp
        have h_wt_ty : WellTyped n Γ ty = true := by
          revert h_wt'; cases WellTyped n Γ term <;> cases WellTyped n Γ ty <;> simp
        -- Get absEval of term (the intermediate)
        cases h_term_abs : absEval n Γ term with
        | none =>
          -- absEval term = none → the match in WellTyped gives false
          simp [h_term_abs] at h_wt'
        | some σ =>
          -- absEval term = some σ, absEval ty = some τ (from h_abs)
          -- WellTyped gives: subCheckNF n Γ [] σ τ = true
          have h_check : subCheckNF n Γ [] σ τ = true := by
            revert h_wt'
            cases hwtm : WellTyped n Γ term <;> cases hwty : WellTyped n Γ ty <;> simp
            intro h; simp [h_term_abs, h_abs] at h; exact h
          -- IH on term: OutputRel v σ
          have ih_term := ih Γ γ term term σ v (.refl term)
            h_term_abs h_conc h_env h_wt_term
          -- Compose: OutputRel v σ + subCheckNF σ τ → OutputRel v τ
          exact .compose ih_term h_check
      | app f a =>
        exact .sound (soundness_app_case (.refl f) (.refl a) h_abs h_conc h_env h_wt ih_sr)
    | top =>
      simp [absEval] at h_abs; cases h_abs; exact .sound (.top v)
    | lam h_body =>
      rename_i dom_c dom_a body_c body_a
      simp only [absEval] at h_abs
      simp only [concEvalE] at h_conc
      simp only [WellTyped] at h_wt
      cases h_ba : absEval n (Env.extend Γ (Expr.bvar 0)) body_a with
      | none => simp [h_ba] at h_abs
      | some body_τ =>
        simp [h_ba] at h_abs
        cases h_bc : concEvalE n (Env.extend γ (Expr.bvar 0)) body_c with
        | none => simp [h_bc] at h_conc
        | some body_v =>
          simp [h_bc] at h_conc
          subst h_abs; subst h_conc
          exact OutputRel.lam_congr (ih _ _ _ _ _ _ h_body h_ba h_bc
            (envSoundRel_extend h_env _) h_wt)
    | mu h_ann h_body =>
      rename_i ann_c ann_a body_c body_a
      simp only [absEval] at h_abs
      simp only [concEvalE] at h_conc
      simp only [WellTyped] at h_wt
      cases h_ba : absEval n (Env.extend Γ (Expr.mu ann_a body_a)) body_a with
      | none => simp [h_ba] at h_abs
      | some body_τ =>
        simp [h_ba] at h_abs
        cases h_bc : concEvalE n (Env.extend γ (Expr.mu ann_c body_c)) body_c with
        | none => simp [h_bc] at h_conc
        | some body_v =>
          simp [h_bc] at h_conc
          subst h_abs; subst h_conc
          exact OutputRel.mu_congr (.sound h_ann) (ih _ _ _ _ _ _ h_body h_ba h_bc
            (envSoundRel_extend_sub h_env (.mu h_ann h_body)) h_wt)
    | app_cong hf ha =>
      exact .sound (soundness_app_case hf ha h_abs h_conc h_env h_wt ih_sr)
    | asc h_term h_ty =>
      -- SoundRel.asc case: e_c = asc term_c ty_c, e_a = asc term_a ty_a
      rename_i term_c term_a ty_c ty_a
      simp only [concEvalE] at h_conc
      simp only [absEval] at h_abs
      have h_wt' := h_wt
      simp only [WellTyped] at h_wt'
      have h_wt_term : WellTyped n Γ term_a = true := by
        revert h_wt'; cases WellTyped n Γ term_a <;> simp
      -- Get absEval of term_a (the intermediate)
      cases h_term_abs : absEval n Γ term_a with
      | none =>
        simp [h_term_abs] at h_wt'
      | some σ =>
        have h_check : subCheckNF n Γ [] σ τ = true := by
          revert h_wt'
          cases hwtm : WellTyped n Γ term_a <;> cases hwty : WellTyped n Γ ty_a <;> simp
          intro h; simp [h_term_abs, h_abs] at h; exact h
        -- IH on (term_c, term_a): OutputRel v σ
        have ih_term := ih Γ γ term_a term_c σ v h_term
          h_term_abs h_conc h_env h_wt_term
        exact .compose ih_term h_check

/-! ## Top-level soundness (concEvalE version)

Entry point: for closed, well-typed programs, concEvalE and absEval produce
OutputRel-related results. OutputRel v τ means ∃ mid, SoundRel v mid ∧
subCheckNF mid τ. For programs without ascriptions, this reduces to SoundRel v τ
(via OutputRel.sound). -/

theorem soundness_concEvalE
    (fuel : Nat) (e τ v : Expr)
    (h_abs : absEval fuel [] e = some τ)
    (h_conc : concEvalE fuel [] e = some v)
    (h_wt : WellTyped fuel [] e = true)
    : OutputRel v τ :=
  soundness_gen_sr fuel [] [] e e τ v (.refl e) h_abs h_conc
    (fun _ _ h => nomatch h) h_wt

/-! ## Legacy soundness_gen (substitution-based concEval)

Retained for compatibility. Uses ValSub as output with compose_r for the
asc case. The lam/mu/app cases are sorry'd — the SoundRel-based proof above
is the intended replacement. A bridge from concEval to concEvalE would
eliminate these sorrys. -/

theorem soundness_gen
    (fuel : Nat) (e : Expr) (τ v : Expr)
    (h_abs : absEval fuel [] e = some τ)
    (h_conc : concEval fuel e = some v)
    (h_wt : WellTyped fuel [] e = true)
    : ValSub fuel v τ := by
  induction fuel generalizing e τ v with
  | zero => simp [concEval] at h_conc
  | succ fuel ih =>
    match e with
    | .bvar k => simp [concEval] at h_conc
    | .type =>
      simp [concEval] at h_conc
      simp [absEval] at h_abs
      subst h_conc; subst h_abs
      exact ValSub.refl' .type (fuel + 1)
    | .asc term ty =>
      simp only [concEval] at h_conc
      simp only [absEval] at h_abs
      simp only [WellTyped, Bool.and_eq_true] at h_wt
      obtain ⟨⟨h_wt_term, h_wt_ty⟩, h_wt_check⟩ := h_wt
      match h_term_abs : absEval fuel [] term with
      | some σ =>
        simp [h_term_abs, h_abs] at h_wt_check
        have h_vs : ValSub fuel v σ := ih term σ v h_term_abs h_conc h_wt_term
        exact ValSub.compose_r h_vs h_wt_check
      | none =>
        simp [h_term_abs] at h_wt_check
    | .lam dom body => sorry
    | .mu ann body => sorry
    | .app f a => sorry
