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
  /-- [Beta-R]: `Γ ⊢ a ⊑ (λD. body) b` if `b ⊑ D` and `a ⊑ body[0 := b]`. -/
  | betaR (Γ : Ctx) (a D body b : Expr) :
      Sub Γ b D →
      Sub Γ a (body.subst 0 b) →
      Sub Γ a (.app (.lam D body) b)
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
  /-- [Trans]: transitivity -/
  | trans (Γ : Ctx) (a b c : Expr) :
      Sub Γ a b → Sub Γ b c → Sub Γ a c

end Och.Simple
