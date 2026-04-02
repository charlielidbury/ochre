import Och.Syntax
import Och.Eval
import Och.Subtyping

/-!
# Monotonicity (de Bruijn)

Generalized to `absEval_mono` taking `SubtypeCore e₂ e₁` + `EnvSubCore Γ₂ Γ₁`.

## Status

**SORRY'd** — needs reproving after de Bruijn migration. The proof structure
is the same as before (structural induction on SubtypeCore), but the details
of env extension and substitution-based beta change.
-/

open Expr

/-- Environment subtyping via SubtypeCore. Positional: for each index k,
    if Γ₁[k] exists then Γ₂[k] exists and is ⊑ Γ₁[k]. -/
def EnvSubCore (Γ₂ Γ₁ : Env) : Prop :=
  ∀ k τ₁, Γ₁.get? k = some τ₁ → ∃ τ₂, Γ₂.get? k = some τ₂ ∧ SubtypeCore τ₂ τ₁

-- Helper: relate List.get? to getElem? for proof interop
private theorem list_get?_eq_getElem? {α : Type} {l : List α} {k : Nat} :
    l.get? k = l[k]? := by
  simp [List.get?_eq_getElem?]

theorem envSubCore_extend {Γ₂ Γ₁ : Env} (h : EnvSubCore Γ₂ Γ₁) (v : Expr) :
    EnvSubCore (Γ₂.extend v) (Γ₁.extend v) := by
  intro k τ₁ hget
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
    obtain ⟨τ₂_orig, hget₂, hsub⟩ := h k orig horig
    rw [list_get?_eq_getElem?] at hget₂
    exact ⟨τ₂_orig.shift 1 0, ⟨τ₂_orig, hget₂, rfl⟩, hshift ▸ hsub.shift_preserve 1 0⟩

theorem envSubCore_extend_sub {Γ₂ Γ₁ : Env} (h : EnvSubCore Γ₂ Γ₁)
    {v₂ v₁ : Expr} (hv : SubtypeCore v₂ v₁) :
    EnvSubCore (Γ₂.extend v₂) (Γ₁.extend v₁) := by
  intro k τ₁ hget
  unfold Env.extend at hget ⊢
  cases k with
  | zero =>
    simp at hget
    subst hget
    exact ⟨v₂, by simp, hv⟩
  | succ k =>
    simp at hget ⊢
    obtain ⟨orig, horig, hshift⟩ := hget
    rw [← list_get?_eq_getElem?] at horig
    obtain ⟨τ₂_orig, hget₂, hsub⟩ := h k orig horig
    rw [list_get?_eq_getElem?] at hget₂
    exact ⟨τ₂_orig.shift 1 0, ⟨τ₂_orig, hget₂, rfl⟩, hshift ▸ hsub.shift_preserve 1 0⟩

/-- **Generalized monotonicity.** Sorry'd pending de Bruijn proof update. -/
theorem absEval_mono
    (fuel : Nat) (Γ₁ Γ₂ : Env) (e₁ e₂ τ₁ τ₂ : Expr)
    (h_sub : SubtypeCore e₂ e₁)
    (h_env : EnvSubCore Γ₂ Γ₁)
    (h₁ : absEval fuel Γ₁ e₁ = some τ₁)
    (h₂ : absEval fuel Γ₂ e₂ = some τ₂)
    : SubtypeCore τ₂ τ₁ := by
  sorry

/-- Monotonicity corollary. -/
theorem monotonicity
    (Γ₁ Γ₂ : Env) (e τ₁ τ₂ : Expr) (fuel : Nat)
    (h_env : EnvSubCore Γ₂ Γ₁)
    (h_abs₁ : absEval fuel Γ₁ e = some τ₁)
    (h_abs₂ : absEval fuel Γ₂ e = some τ₂)
    : Subtype' τ₂ τ₁ :=
  (absEval_mono fuel Γ₁ Γ₂ e e τ₁ τ₂ (SubtypeCore.refl e) h_env h_abs₁ h_abs₂).toSubtype'
