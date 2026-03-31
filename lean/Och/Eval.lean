import Och.Syntax

/-!
# Och Evaluation

Two evaluation modes that diverge only at ascription:
- **Concrete (runtime):** `(e : τ)` takes the lhs `e`.
- **Abstract (compile-time):** `(e : τ)` takes the rhs `τ`.

Compiling an Och program is just running it in abstract mode. Whether this
dual-interpretation is sound is a central research question.

Agents: you may change everything in this file. The definitions below are
starting points. The evaluation strategy, termination argument, and fuel
mechanism are all open to redesign.
-/

open Expr

/-- Typing environment: maps variable names to their (abstract) types. -/
abbrev Env := List (Name × Expr)

namespace Env

def lookup (Γ : Env) (x : Name) : Option Expr :=
  match Γ with
  | []          => none
  | (y, τ) :: rest => if y == x then some τ else lookup rest x

end Env

/-- Concrete evaluation. Standard beta-reduction with ascription erasure.

    Uses fuel to avoid partiality. Returns `none` on timeout.
    Agents: feel free to replace fuel with a well-founded recursion argument
    if you can find one, or use a different termination strategy. -/
def concEval (fuel : Nat) (e : Expr) : Option Expr :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match e with
    | .var _        => some e
    | .lam _ _ _    => some e  -- lambdas are values
    | .type         => some e
    | .asc term _   => concEval fuel term  -- runtime: take the lhs
    | .app f a      =>
      match concEval fuel f with
      | some (.lam x _dom body) =>
        concEval fuel (body.subst x a)
      | some f' => some (.app f' a)  -- stuck application (neutral term)
      | none    => none

/-- Abstract evaluation (typing) with normalization under binders.
    `Γ ⊢ e ⇝ τ` is computed by `absEval fuel Γ e = some τ`.

    Lambda bodies are normalized under the binder (with the bound variable
    as neutral). This ensures that beta-redexes created by substitution are
    reduced, so e.g. `succ 2` has precise type `3`.

    Domains are NOT normalized, to preserve monotonicity: normalizing
    domains would make them vary with the environment, breaking the
    contravariant domain requirement of function subtyping. -/
def absEval (fuel : Nat) (Γ : Env) (e : Expr) : Option Expr :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match e with
    | .var x        => Γ.lookup x
    | .lam x dom body =>
      -- Normalize body under the binder: x is treated as neutral
      match absEval fuel ((x, .var x) :: Γ) body with
      | some body' => some (.lam x dom body')
      | none => none
    | .type         => some .type
    | .asc _term ty => absEval fuel Γ ty  -- compile-time: take the rhs
    | .app f a      =>
      match absEval fuel Γ f, absEval fuel Γ a with
      | some (.lam x _dom body), some aVal =>
        absEval fuel Γ (body.subst x aVal)
      | some f', some a' => some (.app f' a')  -- stuck
      | _, _ => none
