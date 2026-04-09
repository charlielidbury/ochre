import Och.Simple.Syntax
import Och.Simple.Subtype
import Och.Simple.Eval
import Och.Simple.Properties

/-!
# Soundness of Simple Och

Two main results:
1. **Semantic substitution**: closing a Sub derivation with a compatible
   substitution yields a closed Sub derivation.
2. **Eval preservation**: if `Sub [] e τ` and both sides evaluate to values,
   then the values are related by Sub.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

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
-- Theorem 1: Semantic substitution
-- ============================================================

/-- A closing substitution `γ` is compatible with context `Γ` if
    each value in `γ` is a subtype of the corresponding type in `Γ`
    in the remaining context. -/
inductive Compatible : List Expr → Ctx → Type where
  | nil : Compatible [] []
  | cons {v T : Expr} {γ : List Expr} {Γ : Ctx} :
      Compatible γ Γ → Sub Γ v T → Compatible (v :: γ) (T :: Γ)

/-- Semantic substitution: if `Γ ⊢ e ⊑ τ` and `γ` is compatible with `Γ`,
    then `[] ⊢ closingSubst γ e ⊑ closingSubst γ τ`. -/
noncomputable def semanticSubst {Γ : Ctx} {e τ : Expr} {γ : List Expr}
    (hsub : Sub Γ e τ) (hcompat : Compatible γ Γ)
    : Sub [] (closingSubst γ e) (closingSubst γ τ) := by
  induction hcompat generalizing e τ with
  | nil =>
    exact hsub
  | @cons v T γ' Γ' hcompat' hvT ih =>
    show Sub [] (closingSubst γ' (e.subst 0 v)) (closingSubst γ' (τ.subst 0 v))
    exact ih (Sub.subst_lemma hsub hvT)

-- ============================================================
-- Theorem 2: Eval preservation
-- ============================================================

-- Helper lemmas for eval

/-- One-step unfolding of eval for app (call-by-name). -/
private theorem eval_app_unfold (fuel : Nat) (f a : Expr) :
    eval (fuel + 1) (Expr.app f a) =
    (do let f' ← eval fuel f
        match f' with
        | .lam _dom body => eval fuel (body.subst 0 a)
        | _ =>
          let a' ← eval fuel a
          some (.app f' a')) := by
  rfl

/-- Fuel monotonicity: if eval succeeds with less fuel, it succeeds with more. -/
theorem eval_mono {e v : Expr} : (fuel : Nat) →
    eval fuel e = some v → eval (fuel + 1) e = some v
  | 0, h => by simp [eval] at h
  | fuel + 1, h => by
    cases e with
    | var k => simp_all [eval]
    | top => simp_all [eval]
    | lam dom body => simp_all [eval]
    | asc e' ty =>
      simp only [eval] at h ⊢
      exact eval_mono fuel h
    | app f a =>
      -- h : eval (fuel+1) (app f a) = some v
      -- Goal: eval (fuel+2) (app f a) = some v
      rw [eval_app_unfold] at h ⊢
      cases hf : eval fuel f with
      | none => rw [hf] at h; simp at h
      | some f' =>
        rw [hf] at h; rw [eval_mono fuel hf]
        cases f' with
        | lam dom body => exact eval_mono fuel h
        | var k =>
          cases ha : eval fuel a with
          | none => rw [ha] at h; simp at h
          | some a' => rw [ha] at h; rw [eval_mono fuel ha]; simpa using h
        | top =>
          cases ha : eval fuel a with
          | none => rw [ha] at h; simp at h
          | some a' => rw [ha] at h; rw [eval_mono fuel ha]; simpa using h
        | app g b =>
          cases ha : eval fuel a with
          | none => rw [ha] at h; simp at h
          | some a' => rw [ha] at h; rw [eval_mono fuel ha]; simpa using h
        | asc e' ty =>
          cases ha : eval fuel a with
          | none => rw [ha] at h; simp at h
          | some a' => rw [ha] at h; rw [eval_mono fuel ha]; simpa using h

/-- Fuel monotonicity generalized: adding any amount of fuel preserves eval results. -/
theorem eval_mono_add {e v : Expr} (fuel extra : Nat)
    (h : eval fuel e = some v) : eval (fuel + extra) e = some v := by
  induction extra with
  | zero => simp; exact h
  | succ n ih => rw [Nat.add_succ]; exact eval_mono _ ih

-- Helper: extract eval of body.subst from CBN eval of app (lam D body) barg.
private theorem eval_betaR_type {D body barg v : Expr} {k : Nat}
    (hτ : eval (k + 2) (.app (.lam D body) barg) = some v)
    : eval (k + 1) (body.subst 0 barg) = some v := by
  rw [eval_app_unfold] at hτ; simp only [eval] at hτ; exact hτ

/-- Eval preservation (inner): structural recursion on `m ≥ fuel + fuel_τ`,
    then case analysis on the Sub derivation. This allows [AscL] to build a
    new Sub.trans derivation and recurse at smaller fuel.

    Proved cases: [Refl], [Top], [Var], [Lam], [BetaR], [Asc-L], [Asc-R].
    Sorry'd: [App] (needs lambda inversion through trans), [Trans] (needs normalization). -/
noncomputable def evalPreservation_go
    (m : Nat) {e τ : Expr}
    (hsub : Sub ([] : Ctx) e τ)
    (fuel fuel_τ : Nat)
    (v_e v_τ : Expr)
    (hm : fuel + fuel_τ ≤ m)
    (he : eval fuel e = some v_e) (hτ : eval fuel_τ τ = some v_τ)
    : Sub [] v_e v_τ :=
  match m with
  | 0 =>
    have : fuel = 0 := by omega
    absurd (this ▸ he) (by simp [eval])
  | m' + 1 =>
    match hsub with
    | .refl _ a =>
      have he' := eval_mono_add fuel fuel_τ he
      have hτ' := eval_mono_add fuel_τ fuel hτ
      have hτ'' : eval (fuel + fuel_τ) a = some v_τ := by rw [Nat.add_comm] at hτ'; exact hτ'
      have heq : v_e = v_τ := by rw [he'] at hτ''; exact Option.some.inj hτ''
      heq ▸ Sub.refl _ _
    | .top _ a =>
      match fuel_τ, hτ with
      | 0, hτ => absurd hτ (by simp [eval])
      | n + 1, hτ =>
        have hvτ : v_τ = .top := by simp [eval] at hτ; exact hτ.symm
        hvτ ▸ Sub.top _ _
    | .var _ x _ T hget _ =>
      absurd hget (by simp [Ctx.get?])
    | .lam _ A B b₁ b₂ hBA hbody =>
      match fuel, fuel_τ, he, hτ with
      | 0, _, he, _ => absurd he (by simp [eval])
      | _, 0, _, hτ => absurd hτ (by simp [eval])
      | n + 1, k + 1, he, hτ =>
        have hve : v_e = .lam A b₁ := by simp [eval] at he; exact he.symm
        have hvτ : v_τ = .lam B b₂ := by simp [eval] at hτ; exact hτ.symm
        hve ▸ hvτ ▸ Sub.lam [] A B b₁ b₂ hBA hbody
    | .app _ f a b D R hfD haD hRb =>
      -- [App]: Requires lambda inversion through trans chains.
      sorry
    | .betaR _ a D body barg hbD habody =>
      match fuel_τ, hτ with
      | 0, hτ => absurd hτ (by simp [eval])
      | 1, hτ => absurd hτ (by simp [eval])
      | k + 2, hτ =>
        have hτ' := eval_betaR_type hτ
        evalPreservation_go m' habody fuel (k + 1) v_e v_τ (by omega) he hτ'
    | .ascL _ ei ti b heTy hTyB =>
      match fuel, he with
      | 0, he => absurd he (by simp [eval])
      | n + 1, he =>
        have he' : eval n ei = some v_e := by simp only [eval] at he; exact he
        evalPreservation_go m' (Sub.trans _ ei ti b heTy hTyB) n fuel_τ v_e v_τ (by omega) he' hτ
    | .ascR _ a ei ti heTy hAE =>
      match fuel_τ, hτ with
      | 0, hτ => absurd hτ (by simp [eval])
      | n + 1, hτ =>
        have hτ' : eval n ei = some v_τ := by simp only [eval] at hτ; exact hτ
        evalPreservation_go m' hAE fuel n v_e v_τ (by omega) he hτ'
    | .trans _ a mid c hab hbc =>
      -- Need eval of intermediate term. Requires normalization theorem.
      sorry

noncomputable def evalPreservation {e τ : Expr}
    (hsub : Sub [] e τ) (fuel fuel_τ : Nat)
    (v_e v_τ : Expr)
    (he : eval fuel e = some v_e) (hτ : eval fuel_τ τ = some v_τ)
    : Sub [] v_e v_τ :=
  evalPreservation_go (fuel + fuel_τ) hsub fuel fuel_τ v_e v_τ (Nat.le_refl _) he hτ

end Och.Simple
