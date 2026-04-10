import Och.Simple.Syntax

/-!
# Subtype relation for Simple Och

Formalizes the relation `Γ ⊢ a ⊑ b` from the simplified Och calculus spec.
-/

set_option autoImplicit false

namespace Och.Simple

open Expr

/-- A context is a list of types, with index 0 being the most recent binding. -/
abbrev Ctx := List Expr

namespace Ctx

/-- Look up the type at de Bruijn index `n` in the context.
    Returns the type shifted up by `n + 1` so that its free variables
    refer to the correct binders at the usage site. -/
def get? (Γ : Ctx) (n : Nat) : Option Expr :=
  match List.get? Γ n with
  | some T => some (T.shift 0 (n + 1))
  | none   => none

end Ctx

/-- The subtype relation: `Sub Γ a b` means `Γ ⊢ a ⊑ b`. -/
inductive Sub : Ctx → Expr → Expr → Type where
  /-- [Refl]: `Γ ⊢ a ⊑ a` -/
  | refl (Γ : Ctx) (a : Expr) :
      Sub Γ a a
  /-- [Top]: `Γ ⊢ a ⊑ ⊤` -/
  | top (Γ : Ctx) (a : Expr) :
      Sub Γ a .top
  /-- [Var]: `Γ ⊢ x ⊑ b` if `Γ(x) = T` and `Γ ⊢ T ⊑ b`. -/
  | var (Γ : Ctx) (x : Nat) (b T : Expr) :
      Γ.get? x = some T →
      Sub Γ T b →
      Sub Γ (.var x) b
  /-- [Lam]: `Γ ⊢ λA. b₁ ⊑ λB. b₂` if `Γ ⊢ B ⊑ A` and `B :: Γ ⊢ b₁ ⊑ b₂`. -/
  | lam (Γ : Ctx) (A B b₁ b₂ : Expr) :
      Sub Γ B A →
      Sub (B :: Γ) b₁ b₂ →
      Sub Γ (.lam A b₁) (.lam B b₂)
  /-- [App]: `Γ ⊢ f a ⊑ b` if `f` is callable with domain `D` and return `R`,
      `a ⊑ D`, and `R[0 := a] ⊑ b`. -/
  | app (Γ : Ctx) (f a b D R : Expr) :
      Sub Γ f (.lam D R) →
      Sub Γ a D →
      Sub Γ (R.subst 0 a) b →
      Sub Γ (.app f a) b
  /-- [Asc-L]: `Γ ⊢ (e : τ) ⊑ b` if `e ⊑ τ` and `τ ⊑ b`. -/
  | ascL (Γ : Ctx) (e τ b : Expr) :
      Sub Γ e τ →
      Sub Γ τ b →
      Sub Γ (.asc e τ) b
  /-- [Asc-R]: `Γ ⊢ a ⊑ (e : τ)` if `e ⊑ τ` and `a ⊑ e`. -/
  | ascR (Γ : Ctx) (a e τ : Expr) :
      Sub Γ e τ →
      Sub Γ a e →
      Sub Γ a (.asc e τ)
  /-- [Iota-Intro]: `Γ ⊢ a ⊑ μA.b` if `a ⊑ A` and `a ⊑ b[0 := μA.b]`.
      Uses the "fixed self-reference" formulation where the self-binder is
      instantiated with the self-type itself. This formulation is the one
      that admits a clean inductive transitivity proof for covariant
      self-types (see Precise.lean for discussion). -/
  | iotaIntro (Γ : Ctx) (a A b : Expr) :
      Sub Γ a A →
      Sub Γ a (b.subst 0 (.mu A b)) →
      Sub Γ a (.mu A b)

end Och.Simple
