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

/-- Big-step evaluator. Errors on free `bvar` or application of a non-lambda.

    Lambdas and Top are values (returned immediately).
    Application evaluates both sides, then β-reduces if the function
    is a lambda. Applying a non-lambda (e.g. Top) is an error. -/
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
      | .ok fv, .ok av => match fv with
        | .lam _dom body => concEval fuel (body.subst 0 av)
        | _ => .error "application to non-lambda"
      | .outOfFuel, _ | _, .outOfFuel => .outOfFuel
      | .error s, _ | _, .error s=> .error s
