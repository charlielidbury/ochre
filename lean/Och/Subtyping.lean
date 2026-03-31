import Och.Syntax
import Och.Eval

/-!
# Och Subtyping

Subtyping is set inclusion. `A ⊑ B` means every value in A is also in B.

For lambda terms this is checked pointwise:
  `λ(x: A₁). B₁ ⊑ λ(x: A₂). B₂` if `A₂ ⊑ A₁` (contravariant) and
  `B₁ ⊑ B₂` for all `x ⊑ A₂` (covariant, checked with x as neutral).

Type is top: `τ ⊑ Type` for any τ.
-/

open Expr

/-- Subtyping relation. `Subtype' a b` means `a ⊑ b`. -/
inductive Subtype' : Expr → Expr → Prop where
  /-- Reflexivity: `e ⊑ e` -/
  | refl (e : Expr) : Subtype' e e
  /-- Type is top: `e ⊑ Type` for any `e` -/
  | top (e : Expr) : Subtype' e .type
  /-- Transitivity -/
  | trans {a b c : Expr} : Subtype' a b → Subtype' b c → Subtype' a c

/-- Infer the type of a neutral term from a typing context.
    Variables have their declared type; applications use the function's
    return type (substituting the argument). -/
private def inferType (ctx : List (Name × Expr)) : Expr → Option Expr
  | .var x =>
    match ctx with
    | [] => none
    | (y, ty) :: rest => if y == x then some ty else inferType rest (.var x)
  | .app f a =>
    match inferType ctx f with
    | some (.lam x _dom retTy) => some (retTy.subst x a)
    | _ => none
  | _ => none

/-- Structural subtype check on normalized terms.
    ctx tracks (variable_name, declared_domain) for bound variables.

    Key rules:
    - Syntactic equality → true (reflexivity)
    - b = Type → true (Type is top)
    - Both lambdas → contravariant domains, covariant bodies
    - Otherwise → infer type of a, check type ⊑ b (transitivity through type) -/
private def subCheckNF (fuel : Nat) (ctx : List (Name × Expr)) (a b : Expr) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
    if a == b then true
    else match b with
    | .type => true
    | _ =>
      match a, b with
      | .lam x domA bodyA, .lam y domB bodyB =>
        -- Function subtyping: contravariant domain, covariant body
        let bodyB' := if x == y then bodyB else bodyB.subst y (.var x)
        subCheckNF fuel ctx domB domA
        && subCheckNF fuel ((x, domB) :: ctx) bodyA bodyB'
      | _, _ =>
        match inferType ctx a with
        | some ty => subCheckNF fuel ctx ty b
        | none => false

/-- Decidable subtyping check. Normalizes both sides via absEval, then
    compares structurally with pointwise function subtyping and type
    inference for neutral terms. -/
def subCheck (fuel : Nat) (a b : Expr) : Bool :=
  match absEval fuel [] a, absEval fuel [] b with
  | some a', some b' => subCheckNF fuel [] a' b'
  | _, _ => false
