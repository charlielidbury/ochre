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

/-- Concrete evaluation with environment. Structurally parallel to absEval.

    The ONLY difference from absEval is the ascription case:
    - absEval takes the rhs (type annotation) — compile-time semantics
    - concEval takes the lhs (term value) — runtime semantics

    This parallel structure makes the soundness proof a straightforward induction.

    Uses fuel to avoid partiality. Returns `none` on timeout. -/
def concEval (fuel : Nat) (γ : Env) (e : Expr) : Option Expr :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match e with
    | .var x        => γ.lookup x
    | .lam x dom body =>
      match concEval fuel ((x, .var x) :: γ) body with
      | some body' => some (.lam x dom body')
      | none => none
    | .type         => some .type
    | .asc term _   => concEval fuel γ term  -- runtime: take the lhs
    | .app f a      =>
      match concEval fuel γ f, concEval fuel γ a with
      | some (.lam x _dom body), some aVal =>
        concEval fuel ((x, aVal) :: γ) body
      | some .type, some _ => some .type  -- Type applied = Type (top absorbs)
      | some f', some a' => some (.app f' a')
      | _, _ => none

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
        -- Environment-based beta: extend env instead of substituting.
        -- body was already normalized under [(x, var x) :: Γ_def], so x
        -- appears as (var x). Extending env with (x, aVal) resolves it.
        -- This approach keeps the SAME body in both sides of monotonicity/
        -- soundness proofs, making the IH directly applicable.
        absEval fuel ((x, aVal) :: Γ) body
      | some .type, some _ => some .type  -- Type applied = Type (top absorbs)
      | some f', some a' => some (.app f' a')  -- stuck
      | _, _ => none
