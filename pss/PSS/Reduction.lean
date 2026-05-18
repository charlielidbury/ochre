import PSS.Syntax

/-!
# Operational Semantics

Small-step reduction for System λ_◁ (Figure 1, left column).

Two rules:
- E-APP: `(λx ≤ t. u)(s) ⟶ [x ↦ s]u`
- E-CONG: `t ⟶ t'` implies `C[t] ⟶ C[t']`

Evaluation contexts `C` are defined as:
  C ::= [] | C(t) | t(C) | λx ≤ C. t | λx ≤ t. C
-/

open Expr

/-- One-step reduction: `Step t t'` means `t ⟶ t'`. -/
inductive Step : Expr → Expr → Type where
  /-- E-APP: β-reduction. `(λx ≤ t. u)(s) ⟶ [x ↦ s]u` -/
  | beta {dom body arg} :
      Step (.app (.lam dom body) arg) (body.subst 0 arg)
  /-- E-CONG: reduce in function position of application. -/
  | app_fun {f f' a} :
      Step f f' → Step (.app f a) (.app f' a)
  /-- E-CONG: reduce in argument position of application. -/
  | app_arg {f a a'} :
      Step a a' → Step (.app f a) (.app f a')
  /-- E-CONG: reduce in domain of lambda. -/
  | lam_dom {dom dom' body} :
      Step dom dom' → Step (.lam dom body) (.lam dom' body)
  /-- E-CONG: reduce in body of lambda. -/
  | lam_body {dom body body'} :
      Step body body' → Step (.lam dom body) (.lam dom body')

/-- Reflexive-transitive closure of Step. -/
inductive Steps : Expr → Expr → Type where
  | refl {t : Expr} : Steps t t
  | step {t t' u : Expr} : Step t t' → Steps t' u → Steps t u
