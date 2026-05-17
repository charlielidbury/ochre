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

end Expr

/-- Typing context: `Ctx[k]` is the declared bound of `.bvar k`.
    Stored in de Bruijn order (Ctx[0] = innermost binder). -/
abbrev Ctx := List Expr
