import Och.Simple.Syntax
import Och.Simple.Subtype
import Och.Simple.Eval
import Och.Simple.Properties

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
theorem closingSubst_app (γ : List Expr) (f a : Expr) :
    closingSubst γ (.app f a) = .app (closingSubst γ f) (closingSubst γ a) := by
  induction γ generalizing f a with
  | nil => rfl
  | v :: rest ih =>
    show closingSubst rest (Expr.subst (.app f a) 0 v) = _
    unfold Expr.subst
    exact ih (f.subst 0 v) (a.subst 0 v)

/-- closingSubst distributes over asc. -/
theorem closingSubst_asc (γ : List Expr) (e τ : Expr) :
    closingSubst γ (.asc e τ) = .asc (closingSubst γ e) (closingSubst γ τ) := by
  induction γ generalizing e τ with
  | nil => rfl
  | v :: rest ih =>
    show closingSubst rest (Expr.subst (.asc e τ) 0 v) = _
    unfold Expr.subst
    exact ih (e.subst 0 v) (τ.subst 0 v)

-- ============================================================
-- Compatibility (γ ⊨ Γ)
-- ============================================================

/-- A closing substitution `γ` is compatible with context `Γ` if:
    1. They have the same length.
    2. For each index `i`, the value `γ[i]` is a subtype of the
       closed type `closingSubst γ Γ[i]` in the empty context. -/
inductive Compatible : List Expr → Ctx → Prop where
  | nil : Compatible [] []
  | cons (v : Expr) (T : Expr) (γ : List Expr) (Γ : Ctx) :
      Compatible γ Γ →
      Sub [] v (closingSubst (v :: γ) T) →
      Compatible (v :: γ) (T :: Γ)

/-- Fuel monotonicity: if eval succeeds with some fuel, it succeeds with more fuel
    and gives the same result. -/
theorem eval_mono (e : Expr) (fuel : Nat) (v : Expr) (h : eval fuel e = some v) :
    eval (fuel + 1) e = some v := by
  induction fuel generalizing e v with
  | zero => simp [eval] at h
  | succ n ih =>
    cases e with
    | var k => simp [eval] at h ⊢; exact h
    | top => simp [eval] at h ⊢; exact h
    | lam D body => simp [eval] at h ⊢; exact h
    | asc e' τ =>
      simp only [eval] at h ⊢
      exact ih e' v h
    | app f a =>
      simp only [eval, bind] at h ⊢
      -- h involves Option.bind
      -- eval (n+1) f >>= ... = some v
      -- Need to show eval (n+2) f >>= ... = some v
      sorry

theorem Compatible.length_eq {γ : List Expr} {Γ : Ctx} (h : Compatible γ Γ) : γ.length = Γ.length := by
  induction h with
  | nil => rfl
  | cons _ _ _ _ _ _ ih => simp [List.length_cons, ih]

-- ============================================================
-- Soundness theorem
-- ============================================================

/-- **Soundness**: If the abstract subtype relation accepts `e ⊑ τ` in
    context `Γ`, then for any compatible closing substitution `γ`, the
    concrete value of `e` is a subtype of the concrete value of `τ`
    (both closed under `γ`), provided both evaluations succeed. -/
noncomputable def soundness
    (Γ : Ctx) (e τ : Expr) (γ : List Expr) (fuel : Nat)
    (hsub : Sub Γ e τ)
    (hcompat : Compatible γ Γ)
    (v_e v_τ : Expr)
    (he : eval fuel (closingSubst γ e) = some v_e)
    (hτ : eval fuel (closingSubst γ τ) = some v_τ) :
    Sub [] v_e v_τ := by
  induction hsub generalizing γ fuel v_e v_τ with
  -- ========== [Refl]: e = τ ==========
  | refl _ a =>
    have : v_e = v_τ := by rw [he] at hτ; exact Option.some.inj hτ
    rw [this]; exact Sub.refl [] v_τ

  -- ========== [Top]: τ = ⊤ ==========
  | top _ a =>
    have htop_closed : closingSubst γ .top = .top := closingSubst_top γ
    rw [htop_closed] at hτ
    have hv_τ : v_τ = .top := by
      cases fuel with
      | zero => simp [eval] at hτ
      | succ n => simp [eval] at hτ; exact hτ.symm
    rw [hv_τ]
    exact Sub.top [] v_e

  -- ========== [Var]: e = var x, Γ(x) = T, Sub Γ T b ==========
  -- This case requires eval(closingSubst γ T) to succeed, which we don't have.
  -- The IH gives us: if eval(closingSubst γ T) = some v_T and eval(closingSubst γ b) = some v_b,
  -- then Sub [] v_T v_b. But we only know eval(closingSubst γ (var x)) succeeds and
  -- eval(closingSubst γ b) succeeds. We'd need a separate argument that if the abstract
  -- judgment holds and γ is compatible, then closingSubst γ T also evaluates.
  | @var Γ' x b T hget _hTb ihTb =>
    sorry

  -- ========== [Lam]: e = lam A b₁, τ = lam B b₂ ==========
  -- closingSubst of a lambda is complex with de Bruijn. The body substitution
  -- creates a closure-like term. To show Sub.lam on the results, we'd need
  -- to show the domains and bodies of the resulting closed lambdas are related.
  -- This requires understanding how closingSubst interacts with lambda binders.
  | @lam Γ' A B b₁ b₂ _hBA _hbody ihBA ihbody =>
    sorry

  -- ========== [App]: e = app f a, Sub Γ f (lam D R), Sub Γ a D, Sub Γ (R.subst 0 a) b ==========
  -- Need to connect eval(app ...) to eval(closingSubst γ (R.subst 0 a)).
  -- This requires deep lemmas about how eval of app relates to the abstract substitution.
  | @app Γ' f a b D R _hfD _haD _hRb ihfD ihaD ihRb =>
    sorry

  -- ========== [Asc-L]: e = asc e' τ', Sub Γ e' τ', Sub Γ τ' b ==========
  -- eval(asc e' τ') = eval(e'). We need eval(closingSubst γ τ') to succeed
  -- to chain the two IHs. Without that, we're stuck.
  | @ascL Γ' e' τ' b _heτ _hτb iheτ ihτb =>
    sorry

  -- ========== [Asc-R]: τ = asc e' τ', Sub Γ e' τ', Sub Γ a e' ==========
  -- eval(asc e' τ') = eval(e'). The IH on a ⊑ e' gives us exactly what we need.
  | @ascR Γ' a e' τ' _heτ _hae iheτ ihae =>
    rw [closingSubst_asc] at hτ
    -- eval (fuel+1) (asc e' τ') = eval fuel e', so we extract that.
    -- But we need eval fuel (closingSubst γ e') = some v_τ where fuel matches he.
    -- After cases on fuel:
    cases fuel with
    | zero => simp [eval] at hτ
    | succ n =>
      -- hτ : eval (n+1) (asc (closingSubst γ e') (closingSubst γ τ')) = some v_τ
      -- which reduces to eval n (closingSubst γ e') = some v_τ
      simp only [eval] at hτ
      -- hτ : eval n (closingSubst γ e') = some v_τ
      -- he : eval (n+1) (closingSubst γ a) = some v_e
      -- IH needs same fuel. We have he at n+1, hτ at n.
      -- We need eval (n+1) (closingSubst γ e') = some v_τ (upward monotonicity).
      -- For now, use eval_mono.
      have hτ_up : eval (n + 1) (closingSubst γ e') = some v_τ := eval_mono _ _ _ hτ
      exact ihae γ (n + 1) hcompat v_e v_τ he hτ_up

end Och.Simple
