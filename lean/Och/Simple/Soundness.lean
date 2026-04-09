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

/-- Eval preservation: if `Sub [] e τ` and both `e` and `τ` evaluate to values,
    then `Sub [] v_e v_τ`.

    Proved cases:
    - [Refl]: v_e = v_τ since e = τ
    - [Top]: v_τ = top, result by Sub.top
    - [Var]: vacuous (empty context has no variables)
    - [Lam]: both sides are lambda values, eval is identity, use original derivation
    - [Asc-R]: eval erases ascription on τ side, use IH + fuel monotonicity
    - [Beta-R]: call-by-name makes this trivial — eval of app (lam D body) b
      reduces to eval (body.subst 0 b), matching the unevaluated arg in habody

    Sorry'd cases (fundamental difficulties):
    - [App]: requires lambda inversion on Sub [] f' (lam D R), blocked by trans
    - [Asc-L]: intermediate type may not evaluate with available fuel
    - [Trans]: intermediate term may not evaluate (needs normalization theorem) -/
noncomputable def evalPreservation {e τ : Expr}
    (hsub : Sub [] e τ) (fuel : Nat)
    (v_e v_τ : Expr)
    (he : eval fuel e = some v_e) (hτ : eval fuel τ = some v_τ)
    : Sub [] v_e v_τ :=
  evalPreservation_aux hsub rfl fuel v_e v_τ he hτ
where
  /-- Helper with generalized context equality for induction. -/
  evalPreservation_aux {Γ : Ctx} {e τ : Expr}
      (hsub : Sub Γ e τ) (hΓ : Γ = []) (fuel : Nat)
      (v_e v_τ : Expr)
      (he : eval fuel e = some v_e) (hτ : eval fuel τ = some v_τ)
      : Sub [] v_e v_τ := by
    induction hsub generalizing fuel v_e v_τ with
    | refl _ a =>
      have : v_e = v_τ := by rw [he] at hτ; exact Option.some.inj hτ
      subst this; exact Sub.refl _ _
    | top _ a =>
      match fuel with
      | 0 => simp [eval] at hτ
      | n + 1 =>
        simp [eval] at hτ
        rw [← hτ]; exact Sub.top _ _
    | var Γ x b T hget hTb ih =>
      subst hΓ; simp [Ctx.get?] at hget
    | @lam Γ A B b₁ b₂ hBA hbody ihBA ihbody =>
      match fuel with
      | 0 => simp [eval] at he
      | n + 1 =>
        simp [eval] at he hτ
        rw [← he, ← hτ]
        subst hΓ
        exact Sub.lam [] A B b₁ b₂ hBA hbody
    | @app Γ f a b D R hfD haD hRb ihfD ihaD ihRb =>
      -- With call-by-name, eval (app f a) substitutes unevaluated `a`, which matches
      -- the `a` in hRb : Sub Γ (R.subst 0 a) b. However, we still need lambda
      -- inversion on Sub [] f' (lam D R) to extract Sub [D] body' R, which is
      -- blocked by trans as a constructor. A logical-relations approach would be needed.
      sorry
    | @betaR Γ a D body b hbD habody ihbD ihabody =>
      -- τ = app (lam D body) b
      -- With call-by-name: eval (fuel+1) (app (lam D body) b)
      --   = eval fuel (lam D body) >>= match with lam _ body => eval fuel (body.subst 0 b)
      --   = eval fuel (body.subst 0 b)
      -- So hτ gives us eval of body.subst 0 b = some v_τ (after peeling fuel)
      -- IH on habody: Sub [] a (body.subst 0 b) with eval a = v_e, eval (body.subst 0 b) = v_τ
      match fuel with
      | 0 => simp [eval] at hτ
      | n + 1 =>
        -- hτ : eval (n+1) (app (lam D body) b) = some v_τ
        rw [eval_app_unfold] at hτ
        -- After unfolding: eval n (lam D body) >>= ... = some v_τ
        -- eval n (lam D body) = some (lam D body) for n ≥ 1, but we need n ≥ 1
        -- Actually eval 0 (lam D body) = none, so handle that
        cases n with
        | zero => simp [eval] at hτ
        | succ m =>
          simp only [eval] at hτ
          -- Now hτ : eval (m+1) (body.subst 0 b) = some v_τ
          exact ihabody hΓ (m + 2) v_e v_τ he (eval_mono_add (m + 1) 1 hτ)
    | @ascL Γ e' ty b heτ hτb iheτ ihτb =>
      -- e = asc e' ty, so eval strips the ascription: eval fuel e = eval (fuel-1) e'
      -- DIFFICULTY: we'd need eval fuel ty to succeed to use the IH for heτ,
      -- but the intermediate type `ty` may not evaluate with available fuel (or at all).
      sorry
    | @ascR Γ a e' ty heτ hae iheτ ihae =>
      -- τ = asc e' ty, so eval strips the ascription: eval fuel τ = eval (fuel-1) e'
      match fuel with
      | 0 => simp [eval] at hτ
      | n + 1 =>
        simp only [eval] at hτ
        -- hτ : eval n e' = some v_τ
        -- he : eval (n+1) a = some v_e
        -- hae : Sub Γ a e', use IH with fuel monotonicity
        exact ihae hΓ (n + 1) v_e v_τ he (eval_mono n hτ)
    | @trans Γ a b c hab hbc ihab ihbc =>
      -- DIFFICULTY: To chain the two IHs we need eval fuel b = some v_b for some v_b,
      -- i.e., the intermediate term b must evaluate successfully.
      -- This requires a normalization theorem (all well-typed terms evaluate)
      -- which we don't have yet.
      sorry

end Och.Simple
