import PSS.Syntax

/-!
# Big-step Evaluator

Substitution-based CBV big-step evaluator for closed PSS terms,
modelled on Och's `concEval`.

Lambdas and Top are values. Application β-reduces when the function
evaluates to a lambda. Stuck applications (non-function head) are
returned as-is — they are `.ok` but not values.
-/

open Expr

/-- Three-valued outcome: success, error (stuck), or out-of-fuel. -/
inductive Outcome (α : Type) where
  | ok : α → Outcome α
  | error : String → Outcome α
  | outOfFuel : Outcome α
deriving Repr

/-- Big-step evaluator. Only errors on free `bvar` (stuck variable).

    Lambdas and Top are values (returned immediately).
    Application evaluates both sides, then β-reduces if the function
    is a lambda. Non-function applications return `.ok (.app fv av)`. -/
def concEval (fuel : Nat) (e : Expr) : Outcome Expr :=
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
    match e with
    | .bvar k => .error s!"free bvar {k}"
    | .top => .ok .top
    | .lam _ _ => .ok e
    | .app f a =>
      match concEval fuel f, concEval fuel a with
      | .ok (.lam _dom body), .ok av =>
        concEval fuel (body.subst 0 av)
      | .ok fv, .ok av => .ok (.app fv av)
      | .outOfFuel, _ => .outOfFuel
      | _, .outOfFuel => .outOfFuel
      | .error s, _ => .error s
      | _, .error s => .error s
