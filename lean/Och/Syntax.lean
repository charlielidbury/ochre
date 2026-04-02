/-!
# Och Syntax

The core calculus has six term forms. Terms and types share a single syntactic
category — there is no separate type language.

Agents: you may change this file. The syntax below is a starting point derived
from the spec (docs/och-spec.md §3). If the proofs require a different
representation (e.g. de Bruijn indices, locally nameless, explicit substitutions),
change it.
-/

/-- Variable names. Using `String` for readability; switch to de Bruijn or
    locally nameless if substitution lemmas become painful. -/
abbrev Name := String

/-- Core syntax of Och. Six forms, no more.

    e, τ ::=
      | x              — variable
      | λ(x: τ). e    — lambda abstraction
      | e₁ e₂         — application
      | (e : τ)        — ascription (precision loss)
      | Type           — universe / top
      | μ(x : τ). e   — unified self-reference (replaces fix + iota)
-/
inductive Expr where
  | var    : Name → Expr
  | lam    : Name → (dom : Expr) → (body : Expr) → Expr
  | app    : Expr → Expr → Expr
  | asc    : (term : Expr) → (ty : Expr) → Expr
  | type   : Expr
  | mu     : Name → (ann : Expr) → (body : Expr) → Expr
deriving Repr, BEq, Inhabited, DecidableEq

namespace Expr

/-- Capture-avoiding substitution. Replace free occurrences of `x` with `s`.

    WARNING: This naive implementation does not handle capture. It is a
    placeholder. Agents should replace it with a correct implementation
    (e.g. de Bruijn, locally nameless, or explicit alpha-renaming). -/
def subst (e : Expr) (x : Name) (s : Expr) : Expr :=
  match e with
  | .var y        => if y == x then s else .var y
  | .lam y dom body =>
    if y == x then .lam y (dom.subst x s) body  -- x is shadowed in body
    else .lam y (dom.subst x s) (body.subst x s)
  | .app f a      => .app (f.subst x s) (a.subst x s)
  | .asc term ty  => .asc (term.subst x s) (ty.subst x s)
  | .type         => .type
  | .mu y ann body =>
    if y == x then .mu y (ann.subst x s) body  -- x is shadowed in body
    else .mu y (ann.subst x s) (body.subst x s)

end Expr
