import Och.Simple.Syntax
import Och.Simple.Subtype
import Och.Simple.Eval

/-!
# Soundness of Simple Och

Framework for proving: if `Γ ⊢ e ⊑ τ` and `γ ⊨ Γ`, then the concrete
evaluation of `e` under `γ` is a subtype of the concrete evaluation of `τ`
under `γ`.
-/

set_option autoImplicit false

namespace Och.Simple

open Expr

-- ============================================================
-- Closing substitution
-- ============================================================

/-- Apply a list of closed values as a closing substitution.
    If `γ = [v₀, v₁, v₂, ...]`, then `closingSubst γ e` replaces
    `var 0 → v₀`, `var 1 → v₁`, etc.

    Implementation: substitute `v₀` at index 0 (which decrements all
    higher indices), then substitute the next value at index 0 again
    (which was formerly index 1), and so on. -/
def closingSubst : List Expr → Expr → Expr
  | [], e => e
  | v :: rest, e => closingSubst rest (e.subst 0 v)

-- ============================================================
-- Compatibility (γ ⊨ Γ)
-- ============================================================

/-- A closing substitution `γ` is compatible with context `Γ` if:
    1. They have the same length.
    2. For each index `i`, the value `γ[i]` is a subtype of the
       closed type `closingSubst γ Γ[i]` in the empty context.

    This is the semantic typing condition from the spec:
    `γ ⊨ Γ` iff for every `x : T ∈ Γ`, we have `∅ ⊢ γ(x) ⊑ T[γ]`.

    Note: Γ stores types with de Bruijn indices relative to the context.
    `Ctx.get?` shifts the looked-up type, but here we use the raw list
    entries and close them with `closingSubst` instead. -/
inductive Compatible : List Expr → Ctx → Prop where
  | nil : Compatible [] []
  | cons (v : Expr) (T : Expr) (γ : List Expr) (Γ : Ctx) :
      Compatible γ Γ →
      Sub [] v (closingSubst (v :: γ) T) →
      Compatible (v :: γ) (T :: Γ)

-- ============================================================
-- Soundness theorem
-- ============================================================

/-- **Soundness**: If the abstract subtype relation accepts `e ⊑ τ` in
    context `Γ`, then for any compatible closing substitution `γ`, the
    concrete value of `e` is a subtype of the concrete value of `τ`
    (both closed under `γ`), provided both evaluations succeed.

    Formally: if `Γ ⊢ e ⊑ τ` and `γ ⊨ Γ`, then for all fuel `n`,
    if `eval n (closingSubst γ e) = some v_e` and
       `eval n (closingSubst γ τ) = some v_τ`,
    then `∅ ⊢ v_e ⊑ v_τ`. -/
theorem soundness
    (Γ : Ctx) (e τ : Expr) (γ : List Expr) (fuel : Nat)
    (hsub : Sub Γ e τ)
    (hcompat : Compatible γ Γ)
    (v_e v_τ : Expr)
    (he : eval fuel (closingSubst γ e) = some v_e)
    (hτ : eval fuel (closingSubst γ τ) = some v_τ) :
    Sub [] v_e v_τ := by
  sorry

-- ============================================================
-- Easy special cases (sketched, using sorry for internals)
-- ============================================================

/-- Special case: [Top] — if `Γ ⊢ e ⊑ ⊤`, then the conclusion is
    `∅ ⊢ v_e ⊑ ⊤`, which holds by `Sub.top`. -/
theorem soundness_top
    (Γ : Ctx) (e : Expr) (γ : List Expr) (fuel : Nat)
    (hcompat : Compatible γ Γ)
    (v_e v_τ : Expr)
    (he : eval fuel (closingSubst γ e) = some v_e)
    (hτ : eval fuel (closingSubst γ .top) = some v_τ) :
    Sub [] v_e v_τ := by
  -- closingSubst γ .top = .top (top has no free variables)
  have htop_closed : closingSubst γ .top = .top := closingSubst_top γ
  rw [htop_closed] at hτ
  -- eval fuel .top = some .top for any fuel > 0
  have hv_τ : v_τ = .top := by
    cases fuel with
    | zero => simp [eval] at hτ
    | succ n => simp [eval] at hτ; exact hτ.symm
  rw [hv_τ]
  exact Sub.top [] v_e
where
  /-- Top is closed under any substitution. -/
  closingSubst_top : (γ : List Expr) → closingSubst γ .top = .top
    | [] => rfl
    | _ :: rest => by
      show closingSubst rest (Expr.subst .top 0 _) = .top
      simp [Expr.subst]
      exact closingSubst_top rest

/-- Special case: [Refl] — if `Γ ⊢ e ⊑ e`, then we need `∅ ⊢ v_e ⊑ v_τ`
    where both `v_e` and `v_τ` come from evaluating the same closed term.
    If both succeed with the same fuel, they produce the same value,
    so the result follows by `Sub.refl`. -/
theorem soundness_refl
    (Γ : Ctx) (e : Expr) (γ : List Expr) (fuel : Nat)
    (hcompat : Compatible γ Γ)
    (v_e v_τ : Expr)
    (he : eval fuel (closingSubst γ e) = some v_e)
    (hτ : eval fuel (closingSubst γ e) = some v_τ) :
    Sub [] v_e v_τ := by
  have : v_e = v_τ := by
    rw [he] at hτ
    exact Option.some.inj hτ
  rw [this]
  exact Sub.refl [] v_τ

end Och.Simple
