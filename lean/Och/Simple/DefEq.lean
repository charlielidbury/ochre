import Och.Simple.Syntax

/-!
# Definitional Equality (Experimental)

An experimental definitional-equality relation on `Expr` up to beta and
ascription erasure, developed as one ingredient of the "precise interpretation"
research track for self-types (see `Precise.lean`).

This file is EXPERIMENTAL: sorrys are used freely. It is not imported by
any production file.

## Motivation

When resolving the circularity in `dtrue ⊑ dBool`, two distinct forms of
"precision" are needed:

1.  **Value substitution** (handled by a self-type rule in `Precise.lean`):
    unfolding a self-type by substituting the *value* under test, so that
    positions that mention the self-variable become the same on both sides
    (thus closable by reflexivity).

2.  **Computational equality** (this file): after value substitution, some
    positions on the two sides differ only by an administrative beta step
    or an ascription — e.g. `(λ_. e) a` vs `e[0:=a]`, or `(e : τ)` vs `e`.
    A pure-structural `Refl` cannot close these; we need a `DefEq` rule.

`Precise.lean` combines both ingredients.

## Design

`DefEq` is the least congruence on `Expr` that contains:
- reflexivity (structural);
- beta:           `(λ D. b) a  ≡  b[0 := a]`
- ascription:     `(e : τ)     ≡  e`
- symmetry and transitivity.

We also expose a boolean *normal form* `nf fuel e`, defined by full-reduction
call-by-name evaluation that erases ascriptions and (hopefully) beta-reduces
everywhere. Two terms are then "computationally equal" iff their normal forms
are syntactically equal.

`nf` is not proven sound vs `DefEq` here: we use it only as a
sanity-checking oracle for examples.
-/

set_option autoImplicit false

namespace Och.Simple

open Expr

/-- Definitional equality on `Expr`: congruence closure of beta and
    ascription erasure. -/
inductive DefEq : Expr → Expr → Prop where
  -- equivalence-relation closure
  | refl      : (e : Expr) → DefEq e e
  | symm      : {a b : Expr} → DefEq a b → DefEq b a
  | trans     : {a b c : Expr} → DefEq a b → DefEq b c → DefEq a c
  -- reduction rules
  | beta      : (D b a : Expr) → DefEq (.app (.lam D b) a) (b.subst 0 a)
  | ascErase  : (e τ : Expr) → DefEq (.asc e τ) e
  -- congruence closure
  | lamDom    : {D₁ D₂ b : Expr} → DefEq D₁ D₂ → DefEq (.lam D₁ b) (.lam D₂ b)
  | lamBody   : {D b₁ b₂ : Expr} → DefEq b₁ b₂ → DefEq (.lam D b₁) (.lam D b₂)
  | appFun    : {f₁ f₂ a : Expr} → DefEq f₁ f₂ → DefEq (.app f₁ a) (.app f₂ a)
  | appArg    : {f a₁ a₂ : Expr} → DefEq a₁ a₂ → DefEq (.app f a₁) (.app f a₂)
  | ascTerm   : {e₁ e₂ τ : Expr} → DefEq e₁ e₂ → DefEq (.asc e₁ τ) (.asc e₂ τ)
  | ascTy     : {e τ₁ τ₂ : Expr} → DefEq τ₁ τ₂ → DefEq (.asc e τ₁) (.asc e τ₂)

namespace DefEq

/-- Congruence on the LHS of application, *computed* through many steps. -/
theorem appFunMany {f₁ f₂ a : Expr} (h : DefEq f₁ f₂) :
    DefEq (.app f₁ a) (.app f₂ a) := appFun h

/-- One-step beta rewrite can be composed with an argument rewrite: -/
theorem betaEqArg (D b a₁ a₂ : Expr) (ha : DefEq a₁ a₂) :
    DefEq (.app (.lam D b) a₁) (b.subst 0 a₂) :=
  trans (appArg ha) (beta D b a₂)

/-- Congruence under ascription erasure combined with term equality. -/
theorem ascEraseMany (e₁ e₂ τ : Expr) (h : DefEq e₁ e₂) :
    DefEq (.asc e₁ τ) e₂ :=
  trans (ascTerm h) (ascErase e₂ τ)

end DefEq

/-- A fuel-bounded normal-form function used only for example checking.
    Normalises under lambdas (full reduction), erases ascriptions,
    beta-reduces applications when the function is a lambda.

    Returns `none` on fuel exhaustion. -/
def Expr.nf (fuel : Nat) (e : Expr) : Option Expr :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match e with
    | .var n => some (.var n)
    | .top => some .top
    | .lam D b => do
      let D' ← Expr.nf fuel D
      let b' ← Expr.nf fuel b
      some (.lam D' b')
    | .app f a => do
      let f' ← Expr.nf fuel f
      match f' with
      | .lam _ body =>
        -- beta-reduce, then re-normalise the result
        Expr.nf fuel (body.subst 0 a)
      | _ =>
        let a' ← Expr.nf fuel a
        some (.app f' a')
    | .asc e _τ => Expr.nf fuel e

/-- `nf` agrees with `DefEq`: if both sides normalise to the same thing
    they are def-equal. (We don't prove this; we treat it as a test-only oracle.) -/
theorem defEq_of_nf_eq (fuel : Nat) (a b : Expr)
    (h : Expr.nf fuel a = Expr.nf fuel b) (hne : Expr.nf fuel a ≠ none)
    : DefEq a b := by
  -- Stub: we use this as an oracle only.
  sorry

-- ============================================================
-- Small examples
-- ============================================================

section Examples

/-- Identity applied to something beta-reduces. -/
example : DefEq (.app (.lam .top (.var 0)) .top) .top := by
  have h := DefEq.beta .top (.var 0) .top
  -- h : DefEq (app (lam top (var 0)) top) ((var 0).subst 0 top) = DefEq _ .top
  show DefEq (.app (.lam .top (.var 0)) .top) .top
  -- (var 0).subst 0 top normalises to .top
  have : (Expr.var 0).subst 0 .top = .top := rfl
  rw [← this]; exact h

/-- Ascription erasure: `(e : τ) ≡ e`. -/
example : DefEq (.asc .top .top) .top := DefEq.ascErase .top .top

/-- Combined: `((λ⊤. 0) ⊤ : ⊤) ≡ ⊤`. -/
example : DefEq (.asc (.app (.lam .top (.var 0)) .top) .top) .top := by
  have h1 : DefEq (.app (.lam .top (.var 0)) .top) .top := by
    have := DefEq.beta .top (.var 0) .top
    show DefEq (.app (.lam .top (.var 0)) .top) .top
    exact this
  exact DefEq.trans (DefEq.ascErase _ _) h1

end Examples

end Och.Simple
