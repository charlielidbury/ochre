import Och.Simple.Syntax

/-!
# Simple Och Concrete Semantics

Fuel-based evaluator implementing the concrete semantics of the simplified
Och calculus. Domain annotations and ascriptions are erased at runtime.
Uses substitution (no separate environment type).
-/

set_option autoImplicit false

namespace Och.Simple

open Expr

/-- Fuel-based evaluator for the concrete semantics.
    Returns `none` when fuel runs out, `some v` on success.

    - `var n`     → stuck (free variable)
    - `top`       → `top`
    - `lam D b`   → `lam D b` (value, domain kept for structure)
    - `app f a`   → evaluate `f`; if `f'` is a lambda then substitute
                     unevaluated `a` and continue (call-by-name);
                     otherwise form stuck application with unevaluated `a`
    - `asc e _`   → evaluate `e` (erase ascription)
-/
def eval (fuel : Nat) (e : Expr) : Option Expr :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match e with
    | .var n => some (.var n)
    | .top => some .top
    | .lam dom body => some (.lam dom body)
    | .app f a => do
      let f' ← eval fuel f
      match f' with
      | .lam _dom body => eval fuel (body.subst 0 a)
      | _ => some (.app f' a)
    | .asc e _ty => eval fuel e
    -- iota: self-type, behaves as a value (annotation + body preserved)
    | .iota ann body => some (.iota ann body)
    -- fix: recursive binder. Equi-recursive — unfold on eval to match
    -- the Sub.unfoldFixL rule (fix is not a value).
    | .fix ann body => eval fuel (body.subst 0 (.fix ann body))

/-- A value is an expression that the evaluator returns as-is
    (i.e., it is in weak head normal form). -/
inductive Value : Expr → Prop where
  | top : Value .top
  | lam : (dom body : Expr) → Value (.lam dom body)
  | var : (n : Nat) → Value (.var n)
  | stuckApp : (f a : Expr) → (¬ ∃ d b, f = .lam d b) → Value (.app f a)
  | iota : (ann body : Expr) → Value (.iota ann body)

-- ============================================================
-- Tests
-- ============================================================

-- Helper: evaluate with generous fuel
private def ev (e : Expr) : Option Expr := eval 100 e

-- top evaluates to top
#eval ev .top  -- some top

-- free variable is stuck
#eval ev (.var 0)  -- some (var 0)

-- lambda is a value
#eval ev (.lam .top (.var 0))  -- some (lam top (var 0))

-- identity applied to top: (λ⊤. 0) ⊤ → ⊤
#eval ev (.app (.lam .top (.var 0)) .top)  -- some top

-- ascription is erased: (⊤ : ⊤) → ⊤
#eval ev (.asc .top .top)  -- some top

-- nested application: (λ⊤. λ⊤. 0) ⊤ ⊤ → ⊤
-- The inner lambda returns var 0, which after substitution of the second arg gives ⊤
#eval ev (.app (.app (.lam .top (.lam .top (.var 0))) .top) .top)  -- some top

-- stuck application: (var 0) applied to top
#eval ev (.app (.var 0) .top)  -- some (app (var 0) top)

-- Church booleans
private def BOOL : Expr := .lam .top (.lam (.var 0) (.lam (.var 1) (.var 2)))
private def TRUE : Expr := .lam .top (.lam (.var 0) (.lam (.var 1) (.var 1)))
private def FALSE : Expr := .lam .top (.lam (.var 0) (.lam (.var 1) (.var 0)))

-- TRUE ⊤ ⊤ ⊤ should give back the "then" branch, which is the second argument
-- TRUE t a b = a
-- We apply TRUE to three arguments: top, top, and (var 42) as a marker
-- Expect: top (the second argument, i.e. the "a")
#eval ev (.app (.app (.app TRUE .top) .top) (.var 42))  -- some top

-- FALSE ⊤ ⊤ (var 42) should give (var 42)
-- FALSE t a b = b
#eval ev (.app (.app (.app FALSE .top) .top) (.var 42))  -- some (var 42)

end Och.Simple
