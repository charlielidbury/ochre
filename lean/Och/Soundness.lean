import Och.Syntax
import Och.Eval
import Och.Subtyping
import Och.Monotonicity

/-!
# Soundness (de Bruijn)

## Status

**SORRY'd** — needs reproving after de Bruijn migration. The proof structure
is the same (induction on fuel with SubtypeCore), but env extension uses
Env.extend (with shifting) and beta uses substitution.

The 3 pre-existing sorrys (asc case, annotation path ×2) remain. Additional
sorrys from de Bruijn migration.
-/

open Expr

/-- Environment consistency: for each index k, if Γ[k] = τ then
    γ[k] exists and is ⊑ τ via SubtypeCore. -/
def EnvConsistent (γ : Env) (Γ : Env) : Prop :=
  ∀ k τ, Γ.get? k = some τ → ∃ v, γ.get? k = some v ∧ SubtypeCore v τ

-- Helper: relate List.get? to getElem? for proof interop
private theorem list_get?_eq_getElem? {α : Type} {l : List α} {k : Nat} :
    l.get? k = l[k]? := by
  simp [List.get?_eq_getElem?]

theorem envConsistent_extend {γ Γ : Env} (h : EnvConsistent γ Γ) (v : Expr) :
    EnvConsistent (γ.extend v) (Γ.extend v) := by
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

theorem envConsistent_extend_sub {γ Γ : Env} (h : EnvConsistent γ Γ)
    {v τ : Expr} (hv : SubtypeCore v τ) :
    EnvConsistent (γ.extend v) (Γ.extend τ) := by
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

/-- **Generalized soundness.** Sorry'd pending de Bruijn proof update. -/
theorem soundness_gen
    (fuel : Nat) (Γ : Env) (γ : Env) (e_a e_c τ v : Expr)
    (h_sub : SubtypeCore e_c e_a)
    (h_abs : absEval fuel Γ e_a = some τ)
    (h_conc : concEval fuel γ e_c = some v)
    (h_env : EnvConsistent γ Γ)
    (h_wt : WellTyped fuel Γ e_a = true)
    : SubtypeCore v τ := by
  sorry

/-- **Soundness theorem.** Sorry'd (depends on sorry'd soundness_gen). -/
theorem soundness
    (Γ : Env) (γ : Env) (e τ v : Expr) (fuel : Nat)
    (h_abs : absEval fuel Γ e = some τ)
    (h_conc : concEval fuel γ e = some v)
    (h_env : EnvConsistent γ Γ)
    (h_wt : WellTyped fuel Γ e = true)
    : Subtype' v τ :=
  (soundness_gen fuel Γ γ e e τ v (SubtypeCore.refl e)
    h_abs h_conc h_env h_wt).toSubtype'
