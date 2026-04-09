import Och.Simple.Syntax

/-!
# Substitution lemmas for closing substitutions

Lemmas about the interaction of `closingSubst` with the various `Expr`
constructors.  These are building blocks for the soundness proof.
-/

set_option autoImplicit false

namespace Och.Simple

open Expr

-- Re-state closingSubst here so we can use it
-- (It's defined in Soundness.lean, but we want this module to be
--  self-contained and importable *by* Soundness.lean.)

/-- Apply a list of closed values as a closing substitution.
    Replaces `var 0 → v₀`, `var 1 → v₁`, etc. by repeated `subst 0`. -/
def closingSubst : List Expr → Expr → Expr
  | [], e => e
  | v :: rest, e => closingSubst rest (e.subst 0 v)

-- ============================================================
-- Basic subst-constructor distribution
-- ============================================================

@[simp] theorem subst_top (n : Nat) (v : Expr) : Expr.subst .top n v = .top := by
  rfl

@[simp] theorem subst_app (f a : Expr) (n : Nat) (v : Expr) :
    (Expr.app f a).subst n v = .app (f.subst n v) (a.subst n v) := by
  simp [Expr.subst]

@[simp] theorem subst_lam (D b : Expr) (n : Nat) (v : Expr) :
    (Expr.lam D b).subst n v = .lam (D.subst n v) (b.subst (n + 1) (v.shift 0 1)) := by
  simp [Expr.subst]

@[simp] theorem subst_asc (e ty : Expr) (n : Nat) (v : Expr) :
    (Expr.asc e ty).subst n v = .asc (e.subst n v) (ty.subst n v) := by
  simp [Expr.subst]

-- ============================================================
-- closingSubst distributes over constructors
-- ============================================================

-- Lemma 5: closingSubst_top
theorem closingSubst_top (γ : List Expr) : closingSubst γ .top = .top := by
  induction γ with
  | nil => rfl
  | cons v rest ih => exact ih

-- Lemma 2: closingSubst_app
theorem closingSubst_app (γ : List Expr) (f a : Expr) :
    closingSubst γ (.app f a) = .app (closingSubst γ f) (closingSubst γ a) := by
  induction γ generalizing f a with
  | nil => rfl
  | cons v rest ih => exact ih (f.subst 0 v) (a.subst 0 v)

-- Lemma 4: closingSubst_asc
theorem closingSubst_asc (γ : List Expr) (e ty : Expr) :
    closingSubst γ (.asc e ty) = .asc (closingSubst γ e) (closingSubst γ ty) := by
  induction γ generalizing e ty with
  | nil => rfl
  | cons v rest ih => exact ih (e.subst 0 v) (ty.subst 0 v)

-- ============================================================
-- closingSubst_var: looking up a variable
-- ============================================================

/-- Substituting at index 0 into `var 0` yields the replacement. -/
@[simp] theorem subst_var_eq (v : Expr) : (Expr.var 0).subst 0 v = v := by
  simp [Expr.subst]

/-- Substituting at index 0 into `var (k+1)` yields `var k`. -/
@[simp] theorem subst_var_gt (k : Nat) (v : Expr) :
    (Expr.var (k + 1)).subst 0 v = .var k := by
  simp [Expr.subst]

/-- `closingSubst γ (var n) = var (n - γ.length)` when `n ≥ γ.length`. -/
theorem closingSubst_var_ge (γ : List Expr) (n : Nat) (h : n ≥ γ.length) :
    closingSubst γ (.var n) = .var (n - γ.length) := by
  induction γ generalizing n with
  | nil => simp [closingSubst]
  | cons v rest ih =>
    match n with
    | 0 => simp [List.length] at h
    | n + 1 =>
      simp only [closingSubst, subst_var_gt]
      have hk : n ≥ rest.length := by simp [List.length] at h; omega
      rw [ih n hk]
      simp [List.length]

/-- `closingSubst γ (var n)` when `n < γ.length`.
    The result is `closingSubst (γ.drop (n+1)) γ[n]`, because after
    the first n+1 substitutions consume variables 0..n, var n gets
    replaced by γ[n], and then the remaining substitutions act on it. -/
theorem closingSubst_var_lt (γ : List Expr) (n : Nat) (h : n < γ.length) :
    closingSubst γ (.var n) = closingSubst (γ.drop (n + 1)) γ[n] := by
  induction γ generalizing n with
  | nil => exact absurd h (Nat.not_lt_zero n)
  | cons v rest ih =>
    cases n with
    | zero =>
      simp [closingSubst]
    | succ k =>
      simp only [closingSubst]
      simp only [subst_var_gt]
      have hk : k < rest.length := by simp [List.length] at h; omega
      exact ih k hk

-- ============================================================
-- closingSubst_lam
-- ============================================================

-- For the lambda case we need to understand how closingSubst interacts
-- with binders.  The key is that subst 0 v on a lambda shifts v under
-- the binder:
--   (lam D b).subst 0 v = lam (D.subst 0 v) (b.subst 1 (v.shift 0 1))

/-- Shift each entry of γ by 1 at cutoff 0, for use under a binder. -/
def shiftSubst (γ : List Expr) : List Expr :=
  γ.map (Expr.shift 0 1)

/-- Closing a lambda distributes: the domain is closed with γ and the
    body is closed with a shifted γ.  This requires a non-trivial
    commutation between `subst` at different indices.
    Sorry'd — the proof requires showing that repeated subst-at-0
    with shifted values is the same as repeated subst-at-1-then-2-etc. -/
theorem closingSubst_lam (γ : List Expr) (D b : Expr) :
    closingSubst γ (.lam D b) =
      .lam (closingSubst γ D) (closingSubst (shiftSubst γ) b) := by
  sorry

-- ============================================================
-- Lemma 1: closingSubst_subst (the hard commutation lemma)
-- ============================================================

/-- Core commutation lemma:
    Substituting `T` for variable `x` in `M` and then closing with `γ`
    gives the same result as closing `M` directly with `γ`, provided
    that `T` and `var x` close to the same value under `γ`.

    Intuitively: the [Var] rule replaces a variable occurrence with its
    type from the context.  When we close everything with `γ`, the
    variable would have been replaced by `γ[x]` anyway, and `T` (being
    `Γ[x]` shifted) also closes to `γ[x]`.  So the substitution is
    redundant from the perspective of the closed term. -/
theorem closingSubst_subst_of_eq (γ : List Expr) (M : Expr) (x : Nat) (T : Expr)
    (heq : closingSubst γ T = closingSubst γ (.var x)) :
    closingSubst γ (M.subst x T) = closingSubst γ M := by
  sorry

/-- Variant: if `x < γ.length`, substituting `T` for `x` in `M` then
    closing with `γ` gives the same result as closing `M` with `γ`,
    provided the type entry closes correctly. -/
theorem closingSubst_subst (γ : List Expr) (M : Expr) (x : Nat) (T : Expr)
    (_hlen : x < γ.length)
    (heq : closingSubst γ T = closingSubst γ (.var x)) :
    closingSubst γ (M.subst x T) = closingSubst γ M :=
  closingSubst_subst_of_eq γ M x T heq

end Och.Simple
