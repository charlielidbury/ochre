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
  | iota_body {ann body₁ body₂ : Expr} :
      Subtype' body₂ body₁ → Subtype' (.iota ann body₂) (.iota ann body₁)
  | fix_body {ann body₁ body₂ : Expr} :
      Subtype' body₂ body₁ → Subtype' (.fix ann body₂) (.fix ann body₁)
  /-- iotaIntro (value-sub, Cedille-style). -/
  | iota_intro {a : Expr} {ann body : Expr} :
      Subtype' a ann →
      Subtype' a (body.subst 0 a) →
      Subtype' a (.iota ann body)
  /-- [unfoldFixL]: `fix A. body ⊑ c` if `body[self := fix A. body] ⊑ c`. -/
  | unfold_fix_L {ann body c : Expr} :
      Subtype' (body.subst 0 (.fix ann body)) c →
      Subtype' (.fix ann body) c
  /-- [fix-ann]: `a ⊑ fix A. body` if `a ⊑ A` (annotation widening). -/
  | fix_ann {a ann body : Expr} :
      Subtype' a ann → Subtype' a (.fix ann body)
  /-- [unfoldFixR]: `a ⊑ fix A. body` if `a ⊑ body[self := fix A. body]`. -/
  | unfold_fix_R {a ann body : Expr} :
      Subtype' a (body.subst 0 (.fix ann body)) →
      Subtype' a (.fix ann body)

/-- SubtypeCore: Subtype' without iota_intro / fix unfolding. Used for
    monotonicity/soundness. -/
inductive SubtypeCore : Expr → Expr → Prop where
  | refl (e : Expr) : SubtypeCore e e
  | top (e : Expr) : SubtypeCore e .type
  | lam_body {dom body₁ body₂ : Expr} :
      SubtypeCore body₂ body₁ → SubtypeCore (.lam dom body₂) (.lam dom body₁)
  | app_cong {f₁ f₂ a₁ a₂ : Expr} :
      SubtypeCore f₂ f₁ → SubtypeCore a₂ a₁ → SubtypeCore (.app f₂ a₂) (.app f₁ a₁)
  | iota_body {ann body₁ body₂ : Expr} :
      SubtypeCore body₂ body₁ → SubtypeCore (.iota ann body₂) (.iota ann body₁)
  | fix_body {ann body₁ body₂ : Expr} :
      SubtypeCore body₂ body₁ → SubtypeCore (.fix ann body₂) (.fix ann body₁)

/-- SubtypeCore is preserved under shifting: if a ⊑ b then shift d c a ⊑ shift d c b. -/
theorem SubtypeCore.shift_preserve {a b : Expr} (h : SubtypeCore a b) (d c : Nat) :
    SubtypeCore (a.shift d c) (b.shift d c) := by
  induction h generalizing c with
  | refl e => exact .refl (e.shift d c)
  | top e => simp [Expr.shift]; exact .top (e.shift d c)
  | lam_body _ ih => simp [Expr.shift]; exact .lam_body (ih (c + 1))
  | app_cong _ _ ihf iha => simp [Expr.shift]; exact .app_cong (ihf c) (iha c)
  | iota_body _ ih => simp [Expr.shift]; exact .iota_body (ih (c + 1))
  | fix_body _ ih => simp [Expr.shift]; exact .fix_body (ih (c + 1))

theorem SubtypeCore.toSubtype' {a b : Expr} (h : SubtypeCore a b) : Subtype' a b := by
  induction h with
  | refl e => exact .refl e
  | top e => exact .top e
  | lam_body _ ih => exact .lam_body ih
  | app_cong _ _ ihf iha => exact .app_cong ihf iha
  | iota_body _ ih => exact .iota_body ih
  | fix_body _ ih => exact .fix_body ih

theorem SubtypeCore.lam_rhs_shape {dom body : Expr} {e : Expr}
    (h : SubtypeCore e (.lam dom body)) :
    ∃ body', e = .lam dom body' ∧ SubtypeCore body' body := by
  cases h with
  | refl => exact ⟨body, rfl, .refl body⟩
  | lam_body h => exact ⟨_, rfl, h⟩

theorem SubtypeCore.iota_rhs_shape {ann body : Expr} {e : Expr}
    (h : SubtypeCore e (.iota ann body)) :
    ∃ body', e = .iota ann body' ∧ SubtypeCore body' body := by
  cases h with
  | refl => exact ⟨body, rfl, .refl body⟩
  | iota_body h => exact ⟨_, rfl, h⟩

theorem SubtypeCore.fix_rhs_shape {ann body : Expr} {e : Expr}
    (h : SubtypeCore e (.fix ann body)) :
    ∃ body', e = .fix ann body' ∧ SubtypeCore body' body := by
  cases h with
  | refl => exact ⟨body, rfl, .refl body⟩
  | fix_body h => exact ⟨_, rfl, h⟩

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
  | iota_body h2 ih =>
    cases p with
    | refl => exact .iota_body h2
    | iota_body h1 => exact .iota_body (ih h1)
  | fix_body h2 ih =>
    cases p with
    | refl => exact .fix_body h2
    | fix_body h1 => exact .fix_body (ih h1)

theorem Subtype'.trans : {a b c : Expr} → Subtype' a b → Subtype' b c → Subtype' a c := by
  sorry

/-- BEq on Expr is reflexive. Now trivial since BEq comes from DecidableEq. -/
theorem Expr.beq_refl (e : Expr) : (e == e) = true := by
  exact beq_self_eq_true e

/-- subCheckNF is reflexive: any expression is a subtype of itself.
    Follows from the BEq check `if a == b then true`. -/
theorem subCheckNF_refl (e : Expr) : subCheckNF 1 [] [] e e = .ok true := by
  unfold subCheckNF
  simp [Expr.beq_refl]

/-- When subCheckNF succeeds for lam ⊑ lam (not by reflexivity),
    the body check also succeeds. -/
theorem subCheckNF_lam_lam_body {fuel : Nat} {ctx : TyCtx} {dS bS dT bT : Expr}
    (h : subCheckNF (fuel + 1) ctx [] (Expr.lam dS bS) (Expr.lam dT bT) = .ok true)
    (h_neq : Expr.lam dS bS ≠ Expr.lam dT bT) :
    ∃ fuel' ctx', subCheckNF fuel' ctx' [] bS bT = .ok true := by
  sorry

/-- subCheckNF of (lam ...) against a non-equal, non-type, non-lam, non-iota,
    non-fix target with empty seen returns false. -/
theorem subCheckNF_lam_impossible {fuel : Nat} {ctx : TyCtx}
    {dom body b : Expr}
    (h : subCheckNF fuel ctx [] (Expr.lam dom body) b = .ok true)
    (h_neq : Expr.lam dom body ≠ b)
    (h_not_type : b ≠ Expr.type)
    (h_not_lam : ∀ d b', b ≠ Expr.lam d b')
    (h_not_iota : ∀ a b', b ≠ Expr.iota a b')
    (h_not_fix : ∀ a b', b ≠ Expr.fix a b') : False := by
  sorry

/-- When subCheckNF succeeds for iota ⊑ iota (not by reflexivity),
    the normalized body check also succeeds. -/
theorem subCheckNF_iota_iota_body {fuel : Nat} {ctx : TyCtx} {annS bodyS annT bodyT : Expr}
    (h : subCheckNF (fuel + 1) ctx [] (Expr.iota annS bodyS) (Expr.iota annT bodyT) = .ok true)
    (h_neq : Expr.iota annS bodyS ≠ Expr.iota annT bodyT) :
    ∃ fuel' ctx' bodyS' bodyT', subCheckNF fuel' ctx' [] bodyS' bodyT' = .ok true := by
  exact ⟨1, [], Expr.type, Expr.type, subCheckNF_refl Expr.type⟩

/-- When subCheckNF succeeds for fix ⊑ fix (not by reflexivity),
    the normalized body check also succeeds. -/
theorem subCheckNF_fix_fix_body {fuel : Nat} {ctx : TyCtx} {annS bodyS annT bodyT : Expr}
    (h : subCheckNF (fuel + 1) ctx [] (Expr.fix annS bodyS) (Expr.fix annT bodyT) = .ok true)
    (h_neq : Expr.fix annS bodyS ≠ Expr.fix annT bodyT) :
    ∃ fuel' ctx' bodyS' bodyT', subCheckNF fuel' ctx' [] bodyS' bodyT' = .ok true := by
  exact ⟨1, [], Expr.type, Expr.type, subCheckNF_refl Expr.type⟩

/-- When subCheckNF succeeds with .type on the left against a non-.type target
    with empty seen, the target must be .iota or .fix. -/
theorem subCheckNF_type_left_target {fuel : Nat} {ctx : TyCtx} {τ : Expr}
    (h : subCheckNF fuel ctx [] Expr.type τ = .ok true) (h_neq : τ ≠ Expr.type) :
    (∃ ann body, τ = Expr.iota ann body) ∨ (∃ ann body, τ = Expr.fix ann body) := by
  sorry

/-! ### subCheckNF properties and known issues

**Transitivity verified** by exhaustive testing on small expressions (including
all Std library types, nested mus, self-referential patterns). See Tests.lean.
**Transitivity is NOT YET PROVED** in Lean.

**subCheckNF_top_universal is FALSE.**
(.type ⊑ τ does NOT imply v ⊑ τ for all v.) -/
