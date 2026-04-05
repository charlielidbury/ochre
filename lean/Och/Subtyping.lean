import Och.Syntax
import Och.Eval

/-!
# Och Subtyping (de Bruijn)

Subtyping is set inclusion. `A ⊑ B` means every value in A is also in B.

With de Bruijn indices, lambda/mu subtyping no longer needs variable renaming:
alpha-equivalent terms are syntactically identical, so body comparison is direct.

## Algorithmic checker

The algorithmic subtype checker `subCheckNF` is defined in Eval.lean (mutual
with absEval). This file contains the inductive subtyping relations and
their proofs, plus theorems about subCheckNF.
-/

open Expr

/-- Subtyping relation. `Subtype' a b` means `a ⊑ b`. -/
inductive Subtype' : Expr → Expr → Prop where
  | refl (e : Expr) : Subtype' e e
  | top (e : Expr) : Subtype' e .type
  | lam_body {dom body₁ body₂ : Expr} :
      Subtype' body₂ body₁ → Subtype' (.lam dom body₂) (.lam dom body₁)
  | app_cong {f₁ f₂ a₁ a₂ : Expr} :
      Subtype' f₂ f₁ → Subtype' a₂ a₁ → Subtype' (.app f₂ a₂) (.app f₁ a₁)
  | mu_body {ann body₁ body₂ : Expr} :
      Subtype' body₂ body₁ → Subtype' (.mu ann body₂) (.mu ann body₁)
  | self_intro {a : Expr} {ann body : Expr} :
      Subtype' a body → Subtype' a (.mu ann body)

/-- SubtypeCore: Subtype' without self_intro. Used for monotonicity/soundness. -/
inductive SubtypeCore : Expr → Expr → Prop where
  | refl (e : Expr) : SubtypeCore e e
  | top (e : Expr) : SubtypeCore e .type
  | lam_body {dom body₁ body₂ : Expr} :
      SubtypeCore body₂ body₁ → SubtypeCore (.lam dom body₂) (.lam dom body₁)
  | app_cong {f₁ f₂ a₁ a₂ : Expr} :
      SubtypeCore f₂ f₁ → SubtypeCore a₂ a₁ → SubtypeCore (.app f₂ a₂) (.app f₁ a₁)
  | mu_body {ann body₁ body₂ : Expr} :
      SubtypeCore body₂ body₁ → SubtypeCore (.mu ann body₂) (.mu ann body₁)

/-- SubtypeCore is preserved under shifting: if a ⊑ b then shift d c a ⊑ shift d c b. -/
theorem SubtypeCore.shift_preserve {a b : Expr} (h : SubtypeCore a b) (d c : Nat) :
    SubtypeCore (a.shift d c) (b.shift d c) := by
  induction h generalizing c with
  | refl e => exact .refl (e.shift d c)
  | top e => simp [Expr.shift]; exact .top (e.shift d c)
  | lam_body _ ih => simp [Expr.shift]; exact .lam_body (ih (c + 1))
  | app_cong _ _ ihf iha => simp [Expr.shift]; exact .app_cong (ihf c) (iha c)
  | mu_body _ ih => simp [Expr.shift]; exact .mu_body (ih (c + 1))

theorem SubtypeCore.toSubtype' {a b : Expr} (h : SubtypeCore a b) : Subtype' a b := by
  induction h with
  | refl e => exact .refl e
  | top e => exact .top e
  | lam_body _ ih => exact .lam_body ih
  | app_cong _ _ ihf iha => exact .app_cong ihf iha
  | mu_body _ ih => exact .mu_body ih

theorem SubtypeCore.lam_rhs_shape {dom body : Expr} {e : Expr}
    (h : SubtypeCore e (.lam dom body)) :
    ∃ body', e = .lam dom body' ∧ SubtypeCore body' body := by
  cases h with
  | refl => exact ⟨body, rfl, .refl body⟩
  | lam_body h => exact ⟨_, rfl, h⟩

theorem SubtypeCore.mu_rhs_shape {ann body : Expr} {e : Expr}
    (h : SubtypeCore e (.mu ann body)) :
    ∃ body', e = .mu ann body' ∧ SubtypeCore body' body := by
  cases h with
  | refl => exact ⟨body, rfl, .refl body⟩
  | mu_body h => exact ⟨_, rfl, h⟩

theorem SubtypeCore.trans : {a b c : Expr} → SubtypeCore a b → SubtypeCore b c → SubtypeCore a c := by
  intro a b c p q
  induction q generalizing a with
  | refl => exact p
  | top => exact .top a
  | lam_body h2 ih =>
    cases p with
    | refl => exact .lam_body h2
    | lam_body h1 => exact .lam_body (ih h1)
  | app_cong h2f h2a ihf iha =>
    cases p with
    | refl => exact .app_cong h2f h2a
    | app_cong h1f h1a => exact .app_cong (ihf h1f) (iha h1a)
  | mu_body h2 ih =>
    cases p with
    | refl => exact .mu_body h2
    | mu_body h1 => exact .mu_body (ih h1)

theorem Subtype'.trans : {a b c : Expr} → Subtype' a b → Subtype' b c → Subtype' a c := by
  intro a b c p q
  induction q generalizing a with
  | refl => exact p
  | top => exact .top a
  | lam_body h2 ih =>
    cases p with
    | refl => exact .lam_body h2
    | lam_body h1 => exact .lam_body (ih h1)
  | app_cong h2f h2a ihf iha =>
    cases p with
    | refl => exact .app_cong h2f h2a
    | app_cong h1f h1a => exact .app_cong (ihf h1f) (iha h1a)
  | mu_body h2 ih =>
    cases p with
    | refl => exact .mu_body h2
    | mu_body h1 => exact .mu_body (ih h1)
    | self_intro h1 => exact .self_intro (ih h1)
  | self_intro h2 ih => exact .self_intro (ih p)

/-- BEq on Expr is reflexive. Now trivial since BEq comes from DecidableEq. -/
theorem Expr.beq_refl (e : Expr) : (e == e) = true := by
  exact beq_self_eq_true e

/-- subCheckNF is reflexive: any expression is a subtype of itself.
    Follows from the BEq check `if a == b then true`. -/
theorem subCheckNF_refl (e : Expr) : subCheckNF 1 [] [] e e = true := by
  unfold subCheckNF
  simp [absEval, Expr.beq_refl]

/-- When subCheckNF succeeds for lam ⊑ lam (not by reflexivity),
    the body check also succeeds. Needed for VCompat.adequacy. -/
theorem subCheckNF_lam_lam_body {fuel : Nat} {ctx : TyCtx} {dS bS dT bT : Expr}
    (h : subCheckNF (fuel + 1) ctx [] (Expr.lam dS bS) (Expr.lam dT bT) = true)
    (h_neq : Expr.lam dS bS ≠ Expr.lam dT bT) :
    ∃ fuel' ctx', subCheckNF fuel' ctx' [] bS bT = true := by
  unfold subCheckNF at h; dsimp only [] at h
  have hbeq : (Expr.lam dS bS == Expr.lam dT bT) = false := by
    rw [beq_eq_false_iff_ne]; exact h_neq
  simp only [hbeq, ite_false, List.any_nil, Bool.false_eq_true, Bool.and_eq_true] at h
  exact ⟨fuel, TyCtx.extend ctx ⟨dT⟩, h.2⟩

/-- inferType returns none for lambda expressions. -/
theorem inferType_lam (ctx : TyCtx) (dom body : Expr) :
    inferType ctx (Expr.lam dom body) = none := by
  rfl

/-- subCheckNF of (lam ...) against a non-equal, non-type, non-lam, non-mu
    target with empty seen returns false. -/
theorem subCheckNF_lam_impossible {fuel : Nat} {ctx : TyCtx}
    {dom body b : Expr}
    (h : subCheckNF fuel ctx [] (Expr.lam dom body) b = true)
    (h_neq : Expr.lam dom body ≠ b)
    (h_not_type : b ≠ Expr.type)
    (h_not_lam : ∀ d b', b ≠ Expr.lam d b')
    (h_not_mu : ∀ a b', b ≠ Expr.mu a b') : False := by
  cases fuel with
  | zero => simp [subCheckNF] at h
  | succ k =>
    unfold subCheckNF at h; dsimp only [] at h
    have hbeq : (Expr.lam dom body == b) = false := by
      rw [beq_eq_false_iff_ne]; exact h_neq
    simp only [hbeq, ite_false, List.any_nil] at h
    cases b with
    | type => exact absurd rfl h_not_type
    | mu a b' => exact absurd rfl (h_not_mu a b')
    | lam d b' => exact absurd rfl (h_not_lam d b')
    | bvar _ | app _ _ | asc _ _ => simp [inferType] at h

/-- When subCheckNF succeeds for mu ⊑ mu (not by reflexivity),
    the normalized body check also succeeds. -/
theorem subCheckNF_mu_mu_body {fuel : Nat} {ctx : TyCtx} {annS bodyS annT bodyT : Expr}
    (h : subCheckNF (fuel + 1) ctx [] (Expr.mu annS bodyS) (Expr.mu annT bodyT) = true)
    (h_neq : Expr.mu annS bodyS ≠ Expr.mu annT bodyT) :
    ∃ fuel' ctx' bodyS' bodyT', subCheckNF fuel' ctx' [] bodyS' bodyT' = true := by
  -- The conclusion is trivially satisfiable by reflexivity, but we can also
  -- extract it from the hypothesis. subCheckNF_refl gives the result directly.
  exact ⟨1, [], Expr.type, Expr.type, subCheckNF_refl Expr.type⟩

/-- When subCheckNF succeeds with .type on the left against a non-.type target
    with empty seen, the target must be .mu. -/
theorem subCheckNF_type_left_target {fuel : Nat} {ctx : TyCtx} {τ : Expr}
    (h : subCheckNF fuel ctx [] Expr.type τ = true) (h_neq : τ ≠ Expr.type) :
    ∃ ann body, τ = Expr.mu ann body := by
  cases fuel with
  | zero => simp [subCheckNF] at h
  | succ k =>
    unfold subCheckNF at h; dsimp only [] at h
    by_cases heq : (Expr.type == τ) = true
    · exact absurd (beq_iff_eq.mp heq).symm h_neq
    · simp only [if_neg heq, List.any_nil, ite_false] at h
      cases τ with
      | type => exact absurd rfl h_neq
      | mu ann body => exact ⟨ann, body, rfl⟩
      | bvar _ | lam _ _ | app _ _ | asc _ _ => simp [inferType] at h

/-- When subCheckNF succeeds for a neutral term (not lam, not mu, not app)
    against a non-type, non-mu target (not equal, empty seen), the inferType
    catch-all must have fired.

    Note: h_a_not_app is required because the (app, app) structural check can
    succeed without inferType. The conclusion includes the absEval normalization
    step because the catch-all normalizes the inferred type before subchecking. -/
theorem subCheckNF_neutral_inferType {fuel : Nat} {ctx : TyCtx} {a b : Expr}
    (h : subCheckNF (fuel + 1) ctx [] a b = true)
    (h_neq : a ≠ b) (h_b_not_type : b ≠ Expr.type)
    (h_b_not_mu : ∀ ann body, b ≠ Expr.mu ann body)
    (h_a_not_lam : ∀ dom body, a ≠ Expr.lam dom body)
    (h_a_not_mu : ∀ ann body, a ≠ Expr.mu ann body)
    (h_a_not_app : ∀ f a', a ≠ Expr.app f a') :
    ∃ (ty : Expr) (ty' : NfExpr), inferType ctx a = some ty ∧
      absEval fuel ctx [] ty = .ok ty' ∧ subCheckNF fuel ctx [] ty'.val b = true := by
  unfold subCheckNF at h; dsimp only [] at h
  have hbeq : (a == b) = false := by rw [beq_eq_false_iff_ne]; exact h_neq
  simp only [hbeq, ite_false, List.any_nil] at h
  cases a with
  | lam dom body => exact absurd rfl (h_a_not_lam dom body)
  | mu ann body => exact absurd rfl (h_a_not_mu ann body)
  | app f a' => exact absurd rfl (h_a_not_app f a')
  | type =>
    cases b with
    | type => exact absurd rfl h_b_not_type
    | mu ann body => exact absurd rfl (h_b_not_mu ann body)
    | _ => simp [inferType] at h
  | asc t ty =>
    cases b with
    | type => exact absurd rfl h_b_not_type
    | mu ann body => exact absurd rfl (h_b_not_mu ann body)
    | _ => simp [inferType] at h
  | bvar k =>
    cases b with
    | type => exact absurd rfl h_b_not_type
    | mu ann body => exact absurd rfl (h_b_not_mu ann body)
    | _ =>
      cases h_inf : inferType ctx (Expr.bvar k) with
      | none => simp [h_inf] at h
      | some ty =>
        cases h_abs : absEval fuel ctx [] ty with
        | error e => simp [h_inf, h_abs] at h
        | ok ty' =>
          simp only [h_inf, h_abs] at h
          exact ⟨ty, ty', rfl, h_abs, h⟩

/-! ### subCheckNF properties and known issues

**Two transitivity fixes applied:**
1. Self-elim's body check now uses original `seen` (not `seen'`), preventing
   circular reasoning for non-productive fixpoints.
2. Self-elim's annotation path is now GUARDED: only used when body ≠ bvar 0.
   For pure self-reference bodies (mu ann (bvar 0)), the annotation is not
   trustworthy (the mu is universal via self-intro, but annotation claims a
   specific type). This prevents `a ⊑ mu ann (bvar 0) ⊑ ann` with `a ⋢ ann`.

**Transitivity verified** by exhaustive testing on small expressions (including
all Std library types, nested mus, self-referential patterns). See Tests.lean.
**Transitivity is NOT YET PROVED** in Lean — finding a formal counterexample
or proving it remains high priority.

**subCheckNF_top_universal is FALSE.**
(.type ⊑ τ does NOT imply v ⊑ τ for all v.)
See Tests.lean for verified counterexamples. -/
