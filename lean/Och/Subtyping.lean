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

/-- Subtyping relation (trans-free). `Subtype' a b` means `a ⊑ b`.

    Trans is deliberately excluded so that lambda inversion is possible:
    `Subtype' (lam x d b₂) (lam x d b₁)` can only arise from `refl` or
    `lam_body`, both of which give `b₂ ⊑ b₁`. This is essential for the
    monotonicity proof's app case. -/
inductive Subtype' : Expr → Expr → Prop where
  /-- Reflexivity: `e ⊑ e` -/
  | refl (e : Expr) : Subtype' e e
  /-- Type is top: `e ⊑ Type` for any `e` -/
  | top (e : Expr) : Subtype' e .type
  /-- Lambda body covariance (same name and domain).
      If body₂ ⊑ body₁ then λx:dom. body₂ ⊑ λx:dom. body₁.
      Used in the monotonicity proof for the lambda case. -/
  | lam_body {x : Name} {dom body₁ body₂ : Expr} :
      Subtype' body₂ body₁ → Subtype' (.lam x dom body₂) (.lam x dom body₁)
  /-- Neutral application congruence.
      If f₂ ⊑ f₁ and a₂ ⊑ a₁ then (f₂ a₂) ⊑ (f₁ a₁).
      Used in the monotonicity proof for stuck applications. -/
  | app_cong {f₁ f₂ a₁ a₂ : Expr} :
      Subtype' f₂ f₁ → Subtype' a₂ a₁ → Subtype' (.app f₂ a₂) (.app f₁ a₁)

/-- Transitive closure of Subtype'. Used in soundness where transitivity
    is needed (the asc case chains IH result with the well-typedness hyp). -/
inductive SubtypeTrans : Expr → Expr → Prop where
  /-- Lift a single-step subtyping into the transitive closure. -/
  | step {a b : Expr} : Subtype' a b → SubtypeTrans a b
  /-- Transitivity. -/
  | trans {a b c : Expr} : SubtypeTrans a b → SubtypeTrans b c → SubtypeTrans a c

/-- Lift lam_body through SubtypeTrans: if bodies are related transitively,
    then the lambdas are related transitively. -/
theorem SubtypeTrans.lam_body {x : Name} {dom body₁ body₂ : Expr}
    (h : SubtypeTrans body₂ body₁) :
    SubtypeTrans (.lam x dom body₂) (.lam x dom body₁) := by
  induction h with
  | step h => exact .step (.lam_body h)
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

/-- Lambda inversion: if `Subtype' (lam x d b₂) (lam x d b₁)` then `Subtype' b₂ b₁`.
    This is the key lemma enabled by removing trans from Subtype'. -/
theorem Subtype'.lam_inv {x : Name} {dom body₁ body₂ : Expr}
    (h : Subtype' (.lam x dom body₂) (.lam x dom body₁)) : Subtype' body₂ body₁ := by
  cases h with
  | refl => exact Subtype'.refl body₁
  | lam_body h => exact h

/-- If `Subtype' e (lam x d b)` then `e` must be a lam with same name and domain.
    Essential for eliminating mixed lam/non-lam cases in proofs. -/
theorem Subtype'.lam_rhs_shape {x : Name} {dom body : Expr} {e : Expr}
    (h : Subtype' e (.lam x dom body)) :
    ∃ body', e = .lam x dom body' ∧ Subtype' body' body := by
  cases h with
  | refl => exact ⟨body, rfl, Subtype'.refl body⟩
  | lam_body h => exact ⟨_, rfl, h⟩

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
