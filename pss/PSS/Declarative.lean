import PSS.Syntax
import PSS.Reduction

/-!
# Declarative Subtyping and Well-Formedness

Mechanisation of Figure 1 (right and middle columns) from the PSS paper.

The paper uses `◁` as a metavariable ranging over the subtype relation `≤`
and the type equivalence relation `≡`. We model this with a `Rel` parameter.
Each rule given in terms of `◁` defines two rules (one per mode).

Well-formedness and subtyping are mutually dependent:
- DS-TRANS requires `t wf`
- W-APP requires `t ≤ (λs.Top)` and `u ≤ s`

They are defined in a single `mutual` block.
-/

open Expr

/-- The two declarative relations: subtyping (≤) and equivalence (≡). -/
inductive Rel where
  | sub   -- ≤
  | equiv -- ≡
deriving DecidableEq

/-!
## Declarative subtyping and well-formedness (mutual)

`DeclRel r Γ a b` is the declarative judgment `Γ ⊢ a ◁ b` where `◁` is
determined by `r : Rel`.

`Wf Γ t` is the well-formedness judgment `Γ ⊢ t wf`.

`CtxWf Γ` is the context well-formedness judgment `Γ wf`.
-/

mutual

/-- `DeclRel r Γ a b` — declarative `Γ ⊢ a ◁ b`.

    When `r = .sub`:  this is `Γ ⊢ a ≤ b`.
    When `r = .equiv`: this is `Γ ⊢ a ≡ b`.
-/
inductive DeclRel : Rel → Ctx → Expr → Expr → Prop where
  /-- DS-TRANS: `s ◁ t, t ◁ u, t wf ⊢ s ◁ u` -/
  | trans {r : Rel} {Γ : Ctx} {s t u : Expr} :
      DeclRel r Γ s t → DeclRel r Γ t u → Wf Γ t →
      DeclRel r Γ s u
  /-- DS-SYM (≡ only): `u ≡ t ⊢ t ≡ u` -/
  | sym {Γ : Ctx} {t u : Expr} :
      DeclRel .equiv Γ u t → DeclRel .equiv Γ t u
  /-- DS-EQ: `t ≡ u ⊢ t ≤ u` -/
  | eq {Γ : Ctx} {t u : Expr} :
      DeclRel .equiv Γ t u → DeclRel .sub Γ t u
  /-- DS-VAR (≡ only): `x ≡ x` -/
  | var {Γ : Ctx} {k : Nat} :
      DeclRel .equiv Γ (.bvar k) (.bvar k)
  /-- DS-TOP (≡ only): `Top ≡ Top` -/
  | top_ {Γ : Ctx} :
      DeclRel .equiv Γ .top .top
  /-- DS-FUN: `t ≡ t', Γ,x≤t ⊢ u ◁ u' ⊢ (λt.u) ◁ (λt'.u')`

      Domain must be equivalent; body compared under the left domain. -/
  | fun_ {r : Rel} {Γ : Ctx} {dom dom' body body' : Expr} :
      DeclRel .equiv Γ dom dom' →
      DeclRel r (dom :: Γ) body body' →
      DeclRel r Γ (.lam dom body) (.lam dom' body')
  /-- DS-APP: `t ◁ t', u ≡ u' ⊢ t(u) ◁ t'(u')` -/
  | app {r : Rel} {Γ : Ctx} {f f' a a' : Expr} :
      DeclRel r Γ f f' →
      DeclRel .equiv Γ a a' →
      DeclRel r Γ (.app f a) (.app f' a')
  /-- DS-EAPP (≡ only): `(λt.u)(s) ≡ [x ↦ s]u` -/
  | eapp {Γ : Ctx} {dom body arg : Expr} :
      DeclRel .equiv Γ (.app (.lam dom body) arg) (body.subst 0 arg)
  /-- DS-ETOP (≤ only): `t ≤ Top` -/
  | etop {Γ : Ctx} {t : Expr} :
      DeclRel .sub Γ t .top
  /-- DS-EVAR (≤ only): `x ≤ t ∈ Γ ⊢ x ≤ t`

      In de Bruijn: looking up bvar k yields Γ[k], shifted to current depth. -/
  | evar {Γ : Ctx} {k : Nat} {t : Expr} :
      Γ.get? k = some t →
      DeclRel .sub Γ (.bvar k) (t.shift (k + 1) 0)

/-- `Wf Γ t` — well-formedness: `Γ ⊢ t wf`.

    Ensures that every subterm is well-scoped and that applications
    are applied to appropriate arguments (W-APP). -/
inductive Wf : Ctx → Expr → Prop where
  /-- W-VAR: `x ∈ dom(Γ) ⊢ x wf` -/
  | var {Γ : Ctx} {k : Nat} :
      k < Γ.length → Wf Γ (.bvar k)
  /-- W-TOP: `Top wf` -/
  | top_ {Γ : Ctx} : Wf Γ .top
  /-- W-FUN: `t wf, Γ,x≤t ⊢ u wf ⊢ (λt.u) wf` -/
  | fun_ {Γ : Ctx} {dom body : Expr} :
      Wf Γ dom → Wf (dom :: Γ) body →
      Wf Γ (.lam dom body)
  /-- W-APP: `t ≤_wf (λs.Top), u ≤_wf s ⊢ t(u) wf`

      The existential `s` is the inferred domain — `t` must behave as a
      function from `s`, and `u` must be a subtype of `s`. -/
  | app {Γ : Ctx} {f a s : Expr} :
      Wf Γ f → Wf Γ a → Wf Γ s →
      DeclRel .sub Γ f (.lam s .top) →
      DeclRel .sub Γ a s →
      Wf Γ (.app f a)

end

/-- Context well-formedness: every entry is well-formed in its prefix. -/
inductive CtxWf : Ctx → Prop where
  /-- W-GAM1: `∅ wf` -/
  | nil : CtxWf []
  /-- W-GAM2: `Γ wf, Γ ⊢ t wf ⊢ (Γ, x ≤ t) wf` -/
  | cons {Γ : Ctx} {t : Expr} :
      CtxWf Γ → Wf Γ t → CtxWf (t :: Γ)

/-- Well-formed subtyping: `Γ ⊢ t ≤_wf u` iff both sides are wf and `t ≤ u`. -/
structure WfSub (Γ : Ctx) (t u : Expr) : Prop where
  wf_left : Wf Γ t
  wf_right : Wf Γ u
  sub : DeclRel .sub Γ t u

/-- Well-formed equivalence: `Γ ⊢ t ≡_wf u`. -/
structure WfEquiv (Γ : Ctx) (t u : Expr) : Prop where
  wf_left : Wf Γ t
  wf_right : Wf Γ u
  equiv : DeclRel .equiv Γ t u
