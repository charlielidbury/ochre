/-!
# Simple Och Syntax (de Bruijn indices)

A simplified core calculus with five term forms: variables, lambdas,
application, ascription, and top. No μ, no let. Terms and types share
a single syntactic category.
-/

set_option autoImplicit false

namespace Och.Simple

/-- Core syntax of the simplified Och calculus with de Bruijn indices.

    e, τ ::=
      | n              — bound variable (de Bruijn index)
      | λτ. e          — lambda (domain-annotated, bvar 0 = param)
      | e₁ e₂         — application
      | (e : τ)        — ascription
      | ⊤              — top type / universe
      | μA. b          — iota/self-type binder (self = bvar 0 in b)
-/
inductive Expr where
  | var : Nat → Expr
  | lam : (domain : Expr) → (body : Expr) → Expr
  | app : Expr → Expr → Expr
  | asc : (e : Expr) → (ty : Expr) → Expr
  | top : Expr
  /-- `μ A. b` = iota/self-type with annotation `A` and body `b`.
      The binder introduces `self` at de Bruijn index 0 in `b`. -/
  | mu : (ann : Expr) → (body : Expr) → Expr
deriving Inhabited, DecidableEq, Repr

namespace Expr

/-- Shift free variables with index ≥ `cutoff` up by `amount`.
    Used when going under binders to adjust indices for the new binding depth. -/
def shift (cutoff amount : Nat) : Expr → Expr
  | .var k => if k < cutoff then .var k else .var (k + amount)
  | .lam dom body => .lam (shift cutoff amount dom) (shift (cutoff + 1) amount body)
  | .app f a => .app (shift cutoff amount f) (shift cutoff amount a)
  | .asc e ty => .asc (shift cutoff amount e) (shift cutoff amount ty)
  | .top => .top
  | .mu ann body => .mu (shift cutoff amount ann) (shift (cutoff + 1) amount body)

/-- Substitute: replace `var target` with `replacement` in `e`.
    Variables above `target` are decremented by 1 (the binder at `target`
    is being eliminated). `replacement` is shifted when going under binders
    so its free variables stay correct at the new depth. -/
def subst (e : Expr) (target : Nat) (replacement : Expr) : Expr :=
  match e with
  | .var k =>
    if k == target then replacement
    else if k > target then .var (k - 1)
    else .var k
  | .lam dom body =>
    .lam (dom.subst target replacement)
         (body.subst (target + 1) (replacement.shift 0 1))
  | .app f a => .app (f.subst target replacement) (a.subst target replacement)
  | .asc e ty => .asc (e.subst target replacement) (ty.subst target replacement)
  | .top => .top
  | .mu ann body =>
    .mu (ann.subst target replacement)
        (body.subst (target + 1) (replacement.shift 0 1))

/-- Shifting by 0 is the identity. -/
theorem shift_zero (e : Expr) (c : Nat) : e.shift c 0 = e := by
  induction e generalizing c with
  | var k =>
    unfold shift
    split
    · rfl
    · simp
  | lam dom body ih_dom ih_body =>
    unfold shift; congr 1; exact ih_dom c; exact ih_body (c + 1)
  | app f a ih_f ih_a =>
    unfold shift; congr 1; exact ih_f c; exact ih_a c
  | asc e ty ih_e ih_ty =>
    unfold shift; congr 1; exact ih_e c; exact ih_ty c
  | top => rfl
  | mu ann body ih_ann ih_body =>
    unfold shift; congr 1; exact ih_ann c; exact ih_body (c + 1)

/-- Shifting by 1 at cutoff `c` then substituting at `c` cancels out.
    After shifting, there are no `var c`'s in the result, so the
    substitution value is never used. -/
theorem subst_shift_cancel (e : Expr) (c : Nat) (s : Expr)
    : (e.shift c 1).subst c s = e := by
  induction e generalizing c s with
  | var k =>
    unfold shift
    by_cases h : k < c
    · simp [h]
      show Expr.subst (.var k) c s = .var k
      unfold Expr.subst
      have h1 : ¬ k = c := by omega
      have h2 : ¬ c < k := by omega
      simp [beq_iff_eq, h1, h2]
    · simp [h]
      show Expr.subst (.var (k + 1)) c s = .var k
      unfold Expr.subst
      have h1 : ¬ k + 1 = c := by omega
      have h2 : c < k + 1 := by omega
      simp [beq_iff_eq, h1, show k + 1 > c from h2]
  | lam dom body ih_dom ih_body =>
    unfold shift; unfold subst
    simp only [Expr.lam.injEq]
    exact ⟨ih_dom c s, ih_body (c + 1) (s.shift 0 1)⟩
  | app f a ih_f ih_a =>
    unfold shift; unfold subst
    simp only [Expr.app.injEq]
    exact ⟨ih_f c s, ih_a c s⟩
  | asc e ty ih_e ih_ty =>
    unfold shift; unfold subst
    simp only [Expr.asc.injEq]
    exact ⟨ih_e c s, ih_ty c s⟩
  | top => rfl
  | mu ann body ih_ann ih_body =>
    unfold shift; unfold subst
    simp only [Expr.mu.injEq]
    exact ⟨ih_ann c s, ih_body (c + 1) (s.shift 0 1)⟩

/-- Common case: shift by 1 at cutoff 0, then subst at 0 cancels. -/
theorem subst_shift_cancel_zero (e : Expr) (s : Expr)
    : (e.shift 0 1).subst 0 s = e :=
  subst_shift_cancel e 0 s

end Expr
end Och.Simple
