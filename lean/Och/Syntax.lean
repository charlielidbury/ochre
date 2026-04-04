/-!
# Och Syntax (de Bruijn indices)

The core calculus has six term forms. Terms and types share a single syntactic
category — there is no separate type language.

Uses de Bruijn indices for bound variables. This eliminates capture issues in
substitution and makes alpha-equivalent terms syntactically identical.
-/

/-- Core syntax of Och with de Bruijn indices.

    e, τ ::=
      | n              — bound variable (de Bruijn index)
      | λτ. e          — lambda abstraction (domain + body, bvar 0 = param)
      | e₁ e₂         — application
      | (e : τ)        — ascription (precision loss)
      | Type           — universe / top
      | μτ. e          — unified self-reference (bvar 0 = self)
-/
inductive Expr where
  | bvar   : Nat → Expr
  | lam    : (dom : Expr) → (body : Expr) → Expr
  | app    : Expr → Expr → Expr
  | asc    : (term : Expr) → (ty : Expr) → Expr
  | type   : Expr
  | mu     : (ann : Expr) → (body : Expr) → Expr
deriving Inhabited, DecidableEq

namespace Expr

/-- Generate a variable name from a binding depth. -/
private def nameAt (idx : Nat) : String :=
  let letters := #["x", "y", "z", "w", "v", "u"]
  let base := letters[idx % letters.size]!
  if idx < letters.size then base else s!"{base}{idx / letters.size}"

/-- Pretty-print with human-readable variable names (inverse of the `och{…}` macro).
    `names` is the list of bound variable names (innermost-first, like de Bruijn).
    `prec` is the ambient precedence (higher = tighter context). -/
def pretty (e : Expr) (names : List String := []) (prec : Nat := 0) : String :=
  match e with
  | .type => "Type"
  | .bvar k => names.get? k |>.getD s!"?{k}"
  | .asc term ty =>
    s!"({term.pretty names 0} : {ty.pretty names 0})"
  | .lam dom body =>
    let n := nameAt names.length
    let s := s!"λ{n}:{dom.pretty names 10}. {body.pretty (n :: names) 0}"
    if prec > 10 then s!"({s})" else s
  | .mu ann body =>
    let n := nameAt names.length
    let s := s!"μ{n}:{ann.pretty names 10}. {body.pretty (n :: names) 0}"
    if prec > 10 then s!"({s})" else s
  | .app f a =>
    let s := s!"{f.pretty names 50} {a.pretty names 51}"
    if prec > 50 then s!"({s})" else s

instance : Repr Expr where
  reprPrec e _ := e.pretty

instance : ToString Expr where
  toString e := e.pretty

/-- Shift free variables with index ≥ c up by d. Used when going under
    binders to adjust indices for the new binding depth. -/
def shift (d c : Nat) : Expr → Expr
  | .bvar k => if k < c then .bvar k else .bvar (k + d)
  | .lam dom body => .lam (shift d c dom) (shift d (c + 1) body)
  | .app f a => .app (shift d c f) (shift d c a)
  | .asc term ty => .asc (shift d c term) (shift d c ty)
  | .type => .type
  | .mu ann body => .mu (shift d c ann) (shift d (c + 1) body)

/-- Substitute: replace bvar j with s in e. Indices > j are decremented by 1
    (the binder at j is being eliminated). s is shifted when going under
    binders so its free variables stay correct at the new depth. -/
def subst (e : Expr) (j : Nat) (s : Expr) : Expr :=
  match e with
  | .bvar k =>
    if k == j then s
    else if k > j then .bvar (k - 1)
    else .bvar k
  | .lam dom body => .lam (dom.subst j s) (body.subst (j + 1) (s.shift 1 0))
  | .app f a => .app (f.subst j s) (a.subst j s)
  | .asc term ty => .asc (term.subst j s) (ty.subst j s)
  | .type => .type
  | .mu ann body => .mu (ann.subst j s) (body.subst (j + 1) (s.shift 1 0))

/-- Generalized shift-subst cancellation: shifting by 1 at cutoff c then
    substituting at c is the identity, regardless of what value is substituted.
    After shifting, there are no bvar c's in the result, so the substitution
    value is never used. -/
theorem shift_subst_cancel_gen (e : Expr) (c : Nat) (s : Expr)
    : (e.shift 1 c).subst c s = e := by
  induction e generalizing c s with
  | bvar k =>
    unfold shift
    by_cases h : k < c
    · -- k < c: shift leaves bvar k
      simp [h, subst]
      -- Goal: (if k = c then s else if c < k then bvar (k-1) else bvar k) = bvar k
      have h1 : ¬ k = c := by omega
      have h2 : ¬ c < k := by omega
      simp [h1, h2]
    · -- k ≥ c: shift gives bvar (k+1)
      simp [h]
      show Expr.subst (.bvar (k + 1)) c s = .bvar k
      unfold Expr.subst
      -- Goal: (if k+1 = c then s else if c < k+1 then bvar k else bvar (k+1)) = bvar k
      have h1 : ¬ k + 1 = c := by omega
      have h2 : c < k + 1 := by omega
      simp [h1, h2]
  | lam dom body ih_dom ih_body =>
    unfold shift; unfold subst
    simp only [Expr.lam.injEq]
    exact ⟨ih_dom c s, ih_body (c + 1) (s.shift 1 0)⟩
  | app f a ih_f ih_a =>
    unfold shift; unfold subst
    simp only [Expr.app.injEq]
    exact ⟨ih_f c s, ih_a c s⟩
  | asc t y ih_t ih_y =>
    unfold shift; unfold subst
    simp only [Expr.asc.injEq]
    exact ⟨ih_t c s, ih_y c s⟩
  | type => rfl
  | mu ann body ih_ann ih_body =>
    unfold shift; unfold subst
    simp only [Expr.mu.injEq]
    exact ⟨ih_ann c s, ih_body (c + 1) (s.shift 1 0)⟩

/-- Shift-subst cancellation at cutoff 0 (common case). -/
theorem shift_subst_cancel (e : Expr) (s : Expr) : (e.shift 1 0).subst 0 s = e :=
  shift_subst_cancel_gen e 0 s

end Expr

