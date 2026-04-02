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
deriving Repr, Inhabited, DecidableEq

namespace Expr

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

end Expr

/-!
## Named terms (for test readability)

Named expressions use string variable names (like the old syntax). They
convert to de Bruijn via `toExpr`, which computes indices from a name context.
This lets test terms be written readably while using correct de Bruijn
internally.
-/

/-- Named expression syntax — mirrors old named Expr for writing readable
    test terms. Convert to de Bruijn via `toExpr`. -/
inductive Named where
  | var : String → Named
  | lam : String → Named → Named → Named
  | app : Named → Named → Named
  | asc : Named → Named → Named
  | type : Named
  | mu : String → Named → Named → Named

namespace Named

/-- Find the de Bruijn index for a name in the binding context.
    Returns 999 for unbound variables (will cause test failures). -/
private def indexOf (ctx : List String) (name : String) : Nat :=
  match ctx with
  | [] => 999
  | x :: rest => if x == name then 0 else 1 + indexOf rest name

/-- Convert a named term to a de Bruijn term. ctx lists bound variable names
    from innermost to outermost. -/
def toExpr (ctx : List String := []) : Named → Expr
  | .var name => .bvar (indexOf ctx name)
  | .lam name dom body => .lam (dom.toExpr ctx) (body.toExpr (name :: ctx))
  | .app f a => .app (f.toExpr ctx) (a.toExpr ctx)
  | .asc term ty => .asc (term.toExpr ctx) (ty.toExpr ctx)
  | .type => .type
  | .mu name ann body => .mu (ann.toExpr ctx) (body.toExpr (name :: ctx))

end Named

/-- Shorthand: convert a named term to de Bruijn with empty context. -/
def n (e : Named) : Expr := e.toExpr
