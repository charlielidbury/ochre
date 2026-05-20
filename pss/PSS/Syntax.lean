/-!
# PSS Syntax (de Bruijn indices)

Mechanisation of System λ_◁ from "Pure Subtype Systems" (Hutchins, POPL 2010).

System λ_◁ has a single syntactic category for terms and types — there is no
separate type language. The only term forms are variables, Top, lambda
abstractions with bounded quantification, and application.

Uses de Bruijn indices for bound variables.
-/

/-- Core syntax of System λ_◁ with de Bruijn indices.

    s, t, u ::=
      | n              — bound variable (de Bruijn index)
      | Top            — universal supertype
      | λt. u          — function (bvar 0 in body = param, bounded by t)
      | t(u)           — application

    Values:
      v, w ::= Top | λt. u
-/
inductive Expr where
  | bvar : Nat → Expr
  | top  : Expr
  | lam  : (dom : Expr) → (body : Expr) → Expr
  | app  : Expr → Expr → Expr
deriving Inhabited, DecidableEq, Repr

namespace Expr

/-- A value is either `Top` or a lambda. -/
def IsValue : Expr → Prop
  | .top => True
  | .lam _ _ => True
  | _ => False

instance : DecidablePred IsValue := fun e =>
  match e with
  | .top => isTrue trivial
  | .lam _ _ => isTrue trivial
  | .bvar _ => isFalse (fun h => h)
  | .app _ _ => isFalse (fun h => h)

/-- Shift free variables with index ≥ c up by d. -/
def shift (d c : Nat) : Expr → Expr
  | .bvar k => if k < c then .bvar k else .bvar (k + d)
  | .top => .top
  | .lam dom body => .lam (shift d c dom) (shift d (c + 1) body)
  | .app f a => .app (shift d c f) (shift d c a)

/-- Substitute: replace bvar j with s in e. Indices > j are decremented
    (the binder at j is being eliminated). s is shifted under binders. -/
def subst (e : Expr) (j : Nat) (s : Expr) : Expr :=
  match e with
  | .bvar k =>
    if k == j then s
    else if k > j then .bvar (k - 1)
    else .bvar k
  | .top => .top
  | .lam dom body => .lam (dom.subst j s) (body.subst (j + 1) (s.shift 1 0))
  | .app f a => .app (f.subst j s) (a.subst j s)

/-- Free-variable check: all bvars in e have index < n. -/
def closedAt (n : Nat) : Expr → Bool
  | .bvar k => k < n
  | .top => true
  | .lam dom body => dom.closedAt n && body.closedAt (n + 1)
  | .app f a => f.closedAt n && a.closedAt n

/-- Pretty-print with human-readable variable names. -/
def pretty (e : Expr) (names : List String := []) (prec : Nat := 0) : String :=
  match e with
  | .top => "Top"
  | .bvar k => names.get? k |>.getD s!"?{k}"
  | .lam dom body =>
    let n := s!"x{names.length}"
    let s := s!"λ{n}≤{dom.pretty names 10}. {body.pretty (n :: names) 0}"
    if prec > 10 then s!"({s})" else s
  | .app f a =>
    let s := s!"{f.pretty names 50}({a.pretty names 0})"
    if prec > 50 then s!"({s})" else s

instance : ToString Expr where
  toString e := e.pretty

/-! ## Shift lemmas -/

/-- Shifting by 0 is the identity. -/
@[simp] theorem shift_zero (e : Expr) (c : Nat) : e.shift 0 c = e := by
  induction e generalizing c with
  | bvar k =>
    simp only [shift]
    split <;> simp_all <;> omega
  | top => rfl
  | lam dom body ih_dom ih_body =>
    show Expr.lam (dom.shift 0 c) (body.shift 0 (c + 1)) = Expr.lam dom body
    rw [ih_dom, ih_body]
  | app f a ih_f ih_a =>
    show Expr.app (f.shift 0 c) (a.shift 0 c) = Expr.app f a
    rw [ih_f, ih_a]

/-- Helper: shift on bvar unfolds to an if-then-else. -/
private theorem shift_bvar (d c k : Nat) :
    (Expr.bvar k).shift d c = if k < c then .bvar k else .bvar (k + d) := rfl

/-- Generalized shift commutation: when c₂ ≤ c₁, shifting at a lower cutoff
    commutes with shifting at a higher cutoff (adjusting the higher cutoff).
    (e.shift d₁ c₁).shift d₂ c₂ = (e.shift d₂ c₂).shift d₁ (c₁ + d₂)  when c₂ ≤ c₁ -/
theorem shift_comm (d₁ d₂ c₁ c₂ : Nat) (e : Expr) (h : c₂ ≤ c₁) :
    (e.shift d₁ c₁).shift d₂ c₂ = (e.shift d₂ c₂).shift d₁ (c₁ + d₂) := by
  induction e generalizing c₁ c₂ with
  | bvar k =>
    simp only [shift_bvar]
    by_cases hkc₁ : k < c₁
    · -- k < c₁: shift d₁ c₁ gives bvar k
      simp only [hkc₁, ite_true, shift_bvar]
      by_cases hkc₂ : k < c₂
      · -- k < c₂: both sides give bvar k
        simp only [hkc₂, ite_true, shift_bvar]
        have : k < c₁ + d₂ := by omega
        simp only [this, ite_true]
      · -- k ≥ c₂: shift d₂ c₂ gives bvar (k + d₂)
        simp only [hkc₂, ite_false, shift_bvar]
        have : k + d₂ < c₁ + d₂ := by omega
        simp only [this, ite_true]
    · -- k ≥ c₁: shift d₁ c₁ gives bvar (k + d₁)
      simp only [hkc₁, ite_false, shift_bvar]
      have hkc₂ : ¬ (k < c₂) := by omega
      simp only [hkc₂, ite_false, shift_bvar]
      -- LHS: shift d₂ c₂ (bvar (k + d₁)): k + d₁ ≥ c₂ (since k ≥ c₁ ≥ c₂)
      have : ¬ (k + d₁ < c₂) := by omega
      simp only [this, ite_false]
      -- RHS: shift d₁ (c₁ + d₂) (bvar (k + d₂)): k + d₂ ≥ c₁ + d₂ (since k ≥ c₁)
      have : ¬ (k + d₂ < c₁ + d₂) := by omega
      simp only [this, ite_false]
      congr 1; omega
  | top => rfl
  | lam dom body ih_dom ih_body =>
    show Expr.lam _ _ = Expr.lam _ _
    congr 1
    · exact ih_dom c₁ c₂ h
    · have := ih_body (c₁ + 1) (c₂ + 1) (by omega)
      rw [show c₁ + 1 + d₂ = c₁ + d₂ + 1 from by omega] at this
      exact this
  | app f a ih_f ih_a =>
    show Expr.app _ _ = Expr.app _ _
    congr 1
    · exact ih_f c₁ c₂ h
    · exact ih_a c₁ c₂ h

/-- Specialization: shift at cutoff 0 commutes with shift at any cutoff c.
    (e.shift d₁ c).shift d₂ 0 = (e.shift d₂ 0).shift d₁ (c + d₂) -/
theorem shift_comm_zero (d₁ d₂ c : Nat) (e : Expr) :
    (e.shift d₁ c).shift d₂ 0 = (e.shift d₂ 0).shift d₁ (c + d₂) :=
  shift_comm d₁ d₂ c 0 e (Nat.zero_le c)

end Expr

/-- Typing context: `Ctx[k]` is the declared bound of `.bvar k`.
    Stored in de Bruijn order (Ctx[0] = innermost binder). -/
abbrev Ctx := List Expr
