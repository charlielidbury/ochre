import PSS.Syntax

/-!
# Och-style Subtyping for PSS

An Och-inspired declarative subtyping relation for System λ_◁.

Key differences from the paper's formulation (`DeclRel` in `Declarative.lean`):
- `trans` does NOT require the middle term to be well-formed
- Explicit `beta_L`/`beta_R` constructors for β-reduction equivalence
- `app_cong` requires bidirectional argument equivalence (like Och)
- No seen-set parameter (PSS has no recursive types)

These changes break the circularity between well-formedness and subtyping,
making preservation provable without transitivity elimination.
-/

open Expr

/-- Och-style declarative subtyping for PSS.

    `PSS.Sub Γ a b` means `a` is a subtype of `b` in context `Γ`.
    Modelled on Och's `Subtype'` but without the seen-set parameter
    (PSS has no equirecursive types). -/
inductive PSS.Sub : Ctx → Expr → Expr → Prop where
  /-- Reflexivity. -/
  | refl {Γ : Ctx} (e : Expr) : PSS.Sub Γ e e
  /-- Everything is a subtype of Top. -/
  | top {Γ : Ctx} (e : Expr) : PSS.Sub Γ e .top
  /-- Transitivity (NO well-formedness requirement on the middle term). -/
  | trans {Γ : Ctx} {a b c : Expr} :
      PSS.Sub Γ a b → PSS.Sub Γ b c → PSS.Sub Γ a c
  /-- Variable promotion: `x ≤ t ∈ Γ ⊢ x ≤ t`. -/
  | bvar {Γ : Ctx} {k : Nat} {t : Expr} :
      Γ.get? k = some t →
      PSS.Sub Γ (.bvar k) (t.shift (k + 1) 0)
  /-- Function subtyping with invariant domain:
      `dom ≡ dom'` (both directions) and `body ≤ body'` under the left domain. -/
  | lam {Γ : Ctx} {dom dom' body body' : Expr} :
      PSS.Sub Γ dom dom' → PSS.Sub Γ dom' dom →
      Sub (dom :: Γ) body body' →
      PSS.Sub Γ (.lam dom body) (.lam dom' body')
  /-- Application congruence with bidirectional argument equivalence.
      Needed because a neutral head can use its argument at any variance. -/
  | app_cong {Γ : Ctx} {f f' a a' : Expr} :
      PSS.Sub Γ f f' → PSS.Sub Γ a a' → PSS.Sub Γ a' a →
      PSS.Sub Γ (.app f a) (.app f' a')
  /-- β-reduction forward: redex ≤ reduct. -/
  | beta_L {Γ : Ctx} {dom body arg : Expr} :
      PSS.Sub Γ (.app (.lam dom body) arg) (body.subst 0 arg)
  /-- β-reduction backward: reduct ≤ redex. -/
  | beta_R {Γ : Ctx} {dom body arg : Expr} :
      PSS.Sub Γ (body.subst 0 arg) (.app (.lam dom body) arg)
