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

/-- Abstract evaluation (typing). Same as concrete, but ascription takes the rhs.

    `Γ ⊢ e ⇝ τ` is computed by `absEval fuel Γ e = some τ`.

    Agents: this is a placeholder. The real abstract evaluator needs to:
    - Look up variables in the environment
    - Check well-formedness of lambda bodies under extended environments
    - Handle the interaction between substitution and environments
    - Eventually support partitioning for Church-encoded eliminators
    Redesign freely. -/
def absEval (fuel : Nat) (Γ : Env) (e : Expr) : Option Expr :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match e with
    | .var x        => Γ.lookup x
    | .lam _ _ _    => some e  -- a lambda is its own most precise type
    | .type         => some .type
    | .asc _term ty => absEval fuel Γ ty  -- compile-time: take the rhs
    | .app f a      =>
      match absEval fuel Γ f, absEval fuel Γ a with
      | some (.lam x _dom body), some aVal =>
        absEval fuel Γ (body.subst x aVal)
      | some f', some a' => some (.app f' a')  -- stuck
      | _, _ => none
