import PSS.Syntax

/-!
# Subtyping and Well-Formedness (mutual)

Declarative subtyping for System λ_◁ with the paper's well-formedness
guard on transitivity.

`Sub` and `Wf` are mutually defined:
- `trans` requires the middle term to be well-formed
- `Wf`'s W-APP rule requires subtyping witnesses

This coupling is the source of the paper's proof difficulties, but
dropping it (as we showed with the counterexample) makes the relation
unsound.
-/

open Expr

namespace PSS

mutual

inductive Sub : Ctx → Expr → Expr → Prop where
  | refl {Γ : Ctx} (e : Expr) : Sub Γ e e
  | top {Γ : Ctx} (e : Expr) : Sub Γ e .top
  /-- Transitivity with well-formedness guard on the middle term. -/
  | trans {Γ : Ctx} {a b c : Expr} :
      Sub Γ a b → Sub Γ b c → Wf Γ b → Sub Γ a c
  | bvar {Γ : Ctx} {k : Nat} {t : Expr} :
      Γ.get? k = some t →
      Sub Γ (.bvar k) (t.shift (k + 1) 0)
  /-- Function subtyping with invariant domain. -/
  | lam {Γ : Ctx} {dom dom' body body' : Expr} :
      Sub Γ dom dom' → Sub Γ dom' dom →
      Sub (dom :: Γ) body body' →
      Sub Γ (.lam dom body) (.lam dom' body')
  /-- Application congruence with bidirectional argument equivalence. -/
  | app_cong {Γ : Ctx} {f f' a a' : Expr} :
      Sub Γ f f' → Sub Γ a a' → Sub Γ a' a →
      Sub Γ (.app f a) (.app f' a')
  /-- β-reduction forward: redex ≤ reduct. -/
  | beta_L {Γ : Ctx} {dom body arg : Expr} :
      Sub Γ (.app (.lam dom body) arg) (body.subst 0 arg)
  /-- β-reduction backward: reduct ≤ redex. -/
  | beta_R {Γ : Ctx} {dom body arg : Expr} :
      Sub Γ (body.subst 0 arg) (.app (.lam dom body) arg)

/-- Well-formedness judgment. -/
inductive Wf : Ctx → Expr → Prop where
  | var {Γ : Ctx} {k : Nat} :
      k < Γ.length → Wf Γ (.bvar k)
  | top {Γ : Ctx} : Wf Γ .top
  | lam {Γ : Ctx} {dom body : Expr} :
      Wf Γ dom → Wf (dom :: Γ) body →
      Wf Γ (.lam dom body)
  | app {Γ : Ctx} {f a s : Expr} :
      Wf Γ f → Wf Γ a → Wf Γ s →
      Sub Γ f (.lam s .top) → Sub Γ a s →
      Wf Γ (.app f a)

end

end PSS
