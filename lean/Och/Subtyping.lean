import Och.Syntax

/-!
# Och Subtyping

Subtyping is set inclusion. `A ⊑ B` means every value in A is also in B.

For lambda terms this is checked pointwise:
  `λ(x: A₁). B₁ ⊑ λ(x: A₂). B₂` if `A₂ ⊑ A₁` (contravariant) and
  `B₁[x] ⊑ B₂[x]` for all `x ⊑ A₂` (covariant).

Type is top: `τ ⊑ Type` for any τ.

Agents: you may change everything in this file. The relation below is a
starting point. You will likely need to:
- Decide between an inductive relation (for proofs) and a decision procedure
  (for testing), or both with a correctness bridge
- Handle the "for all x ⊑ A₂" quantifier in function subtyping — this is
  one of the hardest parts
- Ensure the relation is compatible with beta-equivalence
-/

open Expr

/-- Subtyping relation. `Subtype' a b` means `a ⊑ b`.

    This is a placeholder inductive definition. Agents should extend or
    redesign it. The rules below are incomplete — they don't yet handle
    the covariant body check for functions (which requires quantifying
    over all inhabitants of the domain). -/
inductive Subtype' : Expr → Expr → Prop where
  /-- Reflexivity: `e ⊑ e` -/
  | refl (e : Expr) : Subtype' e e
  /-- Type is top: `e ⊑ Type` for any `e` -/
  | top (e : Expr) : Subtype' e .type
  /-- Transitivity -/
  | trans {a b c : Expr} : Subtype' a b → Subtype' b c → Subtype' a c
  -- Function subtyping placeholder — needs the body/covariance rule
  -- | lam : ...

/-- Decidable subtyping check (for testing). Uses fuel.

    Agents: this is a very incomplete placeholder. It only handles
    syntactic equality and the Type-is-top rule. The real implementation
    needs beta-reduction, pointwise function comparison, etc. -/
def subCheck (fuel : Nat) (a b : Expr) : Bool :=
  match fuel with
  | 0 => false
  | _fuel + 1 =>
    if a == b then true
    else match b with
    | .type => true  -- anything ⊑ Type
    | _ => false     -- placeholder: extend this
