import Och.Simple.Syntax
import Och.Simple.Subtype
import Och.Simple.Properties

/-!
# Semantic Substitution (Soundness Part 1)

Proves: if `Γ ⊢ e ⊑ τ` and `γ` is compatible with `Γ`, then
`[] ⊢ closingSubst γ e ⊑ closingSubst γ τ`.

The key insight is defining Compatible so each value is related to its type
*in the remaining context* rather than at empty context.
-/

set_option autoImplicit false

namespace Och.Simple

open Expr

-- ============================================================
-- Closing substitution
-- ============================================================

/-- Apply a list of closed values as a closing substitution.
    If `γ = [v₀, v₁, v₂, ...]`, then `closingSubst γ e` replaces
    `var 0 → v₀`, `var 1 → v₁`, etc. -/
def closingSubst : List Expr → Expr → Expr
  | [], e => e
  | v :: rest, e => closingSubst rest (e.subst 0 v)

-- ============================================================
-- closingSubst lemmas
-- ============================================================

/-- Top is closed under any substitution. -/
theorem closingSubst_top : (γ : List Expr) → closingSubst γ .top = .top
  | [] => rfl
  | _ :: rest => by
    show closingSubst rest (Expr.subst .top 0 _) = .top
    simp [Expr.subst]
    exact closingSubst_top rest

/-- closingSubst distributes over app. -/
theorem closingSubst_app : (γ : List Expr) → (f a : Expr) →
    closingSubst γ (.app f a) = .app (closingSubst γ f) (closingSubst γ a)
  | [], _, _ => rfl
  | v :: rest, f, a => by
    show closingSubst rest (Expr.subst (.app f a) 0 v) = _
    unfold Expr.subst
    exact closingSubst_app rest (f.subst 0 v) (a.subst 0 v)

/-- closingSubst distributes over asc. -/
theorem closingSubst_asc : (γ : List Expr) → (e τ : Expr) →
    closingSubst γ (.asc e τ) = .asc (closingSubst γ e) (closingSubst γ τ)
  | [], _, _ => rfl
  | v :: rest, e, τ => by
    show closingSubst rest (Expr.subst (.asc e τ) 0 v) = _
    unfold Expr.subst
    exact closingSubst_asc rest (e.subst 0 v) (τ.subst 0 v)

/-- closingSubst preserves the lam constructor. -/
theorem closingSubst_lam_is_lam : (γ : List Expr) → (D body : Expr) →
    ∃ D' body', closingSubst γ (.lam D body) = .lam D' body'
  | [], D, body => ⟨D, body, rfl⟩
  | v :: rest, D, body => by
    show ∃ D' body', closingSubst rest ((Expr.lam D body).subst 0 v) = .lam D' body'
    simp only [Expr.subst]
    exact closingSubst_lam_is_lam rest (D.subst 0 v) (body.subst 1 (v.shift 0 1))

-- ============================================================
-- Compatibility (γ ⊨ Γ)
-- ============================================================

/-- A closing substitution `γ` is compatible with context `Γ` if each value
    is Sub-related to its type in the remaining context. -/
inductive Compatible : List Expr → Ctx → Type where
  | nil : Compatible [] []
  | cons {v : Expr} {T : Expr} {γ : List Expr} {Γ : Ctx} :
      Compatible γ Γ →
      Sub Γ v T →
      Compatible (v :: γ) (T :: Γ)

-- ============================================================
-- Semantic substitution theorem
-- ============================================================

/-- **Semantic substitution**: If `Γ ⊢ e ⊑ τ` and `γ` is compatible with `Γ`,
    then `[] ⊢ closingSubst γ e ⊑ closingSubst γ τ`. -/
noncomputable def semanticSubst {Γ : Ctx} {e τ : Expr} {γ : List Expr}
    (hsub : Sub Γ e τ)
    (hcompat : Compatible γ Γ)
    : Sub [] (closingSubst γ e) (closingSubst γ τ) := by
  induction hcompat generalizing e τ with
  | nil =>
    exact hsub
  | @cons v T γ' Γ' hcompat' hv ih =>
    show Sub [] (closingSubst γ' (e.subst 0 v)) (closingSubst γ' (τ.subst 0 v))
    exact ih (Sub.subst_lemma hsub hv)

end Och.Simple
