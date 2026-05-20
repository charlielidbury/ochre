import Och.Syntax
import Och.Subtyping

/-!
# Well-formedness (declarative)

`WellFormed Γ e` is the declarative well-formedness judgment: under
context `Γ`, expression `e` is well-formed.

In Och's "values are types" world, a separate type assignment is
unnecessary — every value IS its own most-precise type (by
`Subtype'.refl`), and all type-comparison questions are handled by
the subtyping relation. Well-formedness just validates structural
conditions: annotations are types, binders are in scope, applications
have Π-typed functions with domain-inhabiting arguments.

## Relationship to other definitions

This is the declarative counterpart of the algorithmic `Och.check`
(`API.lean`), analogous to how `Subtype'` (`Subtyping.lean`) is the
declarative counterpart of `subCheckSubst` (`EvalSubst.lean`).

```
Subtype'     ←  subCheckSubst     (subtype-check soundness)
WellFormed   ←  Och.check          (well-formedness soundness)
```

## Soundness target

  `Och.check e fuel Γ = .ok () → WellFormed Γ e`
-/

open Expr

/-- Declarative well-formedness judgment.

`WellFormed Γ e` means: under context `Γ`, term `e` is well-formed.

No type witness is returned — in Och, a value IS its own type
(`Subtype'.refl`), and subtyping handles all type comparisons.

The `Subtype'` premises always use the empty seen-set `[]`,
matching the "real" subtyping judgment `∅; Γ ⊢ a ⊑ b`. -/
inductive WellFormed : Ctx → Expr → Prop where
  | type {Γ : Ctx} :
      WellFormed Γ .type
  | bot {Γ : Ctx} :
      WellFormed Γ .bot
  | bvar {Γ : Ctx} {k : Nat} :
      k < Γ.length →
      WellFormed Γ (.bvar k)
  | lam {Γ : Ctx} {dom body : Expr} :
      WellFormed Γ dom →
      WellFormed (dom :: Γ) body →
      WellFormed Γ (.lam dom body)
  | iota {Γ : Ctx} {ann body : Expr} :
      WellFormed Γ ann →
      WellFormed (ann :: Γ) body →
      WellFormed Γ (.iota ann body)
  | fix {Γ : Ctx} {body : Expr} :
      WellFormed ((.fix body) :: Γ) body →
      WellFormed Γ (.fix body)
  /-- Application: function and argument must be well-formed,
      function must subtype a Π (possibly after fix/iota unfolding
      via `Subtype'`), and argument must subtype the domain.

      The existentially quantified `dom` and `body` are the Π's
      domain and codomain — they may not appear directly in `f`
      (e.g. when `f` is a fix that unfolds to a lambda). -/
  | app {Γ : Ctx} {f a dom body : Expr} :
      WellFormed Γ f →
      WellFormed Γ a →
      Subtype' [] Γ f (.lam dom body) →
      Subtype' [] Γ a dom →
      WellFormed Γ (.app f a)
