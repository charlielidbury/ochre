import Och.Syntax
import Och.Subtyping

/-!
# Well-formed WHNF (declarative typing)

`WfWhnf Γ e v` is the declarative typing judgment: under context `Γ`,
expression `e` is well-formed, and `v` is its type-witness.

For canonical forms (lam, iota, fix, type, bot, bvar), the type-witness
is the expression itself — this is Och's refl-typing convention where a
value IS its own most-precise type.

For elimination forms (app, let, asc), the type-witness is determined
structurally: application produces the instantiated codomain, let
produces itself, and ascription strips to the inner expression's witness.

## Relationship to other definitions

This is the declarative counterpart of the algorithmic `Och.check`
(`API.lean`), analogous to how `Subtype'` (`Subtyping.lean`) is the
declarative counterpart of `subCheckSubst` (`EvalSubst.lean`).

```
Subtype'  ←  subCheckSubst     (subtype-check soundness)
WfWhnf    ←  Och.check          (synthesis soundness, target)
```

## Soundness target

  `Och.check fuel Γ e = ok v → WfWhnf Γ e v`
-/

open Expr

/-- Declarative typing / well-formedness judgment.

`WfWhnf Γ e v` means: under context `Γ`, term `e` is well-formed,
and `v` is its type-witness (most-precise type).

The `Subtype'` premises always use the empty seen-set `[]`,
matching the "real" subtyping judgment `∅; Γ ⊢ a ⊑ b`. -/
inductive WfWhnf : Ctx → Expr → Expr → Type where
  /-- `⊤` is self-typing: `Γ ⊢ ⊤ ⇝ ⊤`. -/
  | type {Γ : Ctx} :
      WfWhnf Γ .type .type
  /-- `⊥` is self-typing: `Γ ⊢ ⊥ ⇝ ⊥`. -/
  | bot {Γ : Ctx} :
      WfWhnf Γ .bot .bot
  /-- A bound variable is well-formed if in scope. Self-typing. -/
  | bvar {Γ : Ctx} {k : Nat} :
      k < Γ.length →
      WfWhnf Γ (.bvar k) (.bvar k)
  /-- Lambda: domain must be a type, body well-formed under extended
      context. Self-typing (a lambda IS its own Π-type in Och). -/
  | lam {Γ : Ctx} {dom body bodyV : Expr} :
      Subtype' [] Γ dom .type →
      WfWhnf (dom :: Γ) body bodyV →
      WfWhnf Γ (.lam dom body) (.lam dom body)
  /-- Iota: annotation must be a type, body well-formed under extended
      context. Self-typing. -/
  | iota {Γ : Ctx} {ann body bodyV : Expr} :
      Subtype' [] Γ ann .type →
      WfWhnf (ann :: Γ) body bodyV →
      WfWhnf Γ (.iota ann body) (.iota ann body)
  /-- Fix: annotation must be a type, body well-formed under extended
      context. Self-typing. -/
  | fix {Γ : Ctx} {ann body bodyV : Expr} :
      Subtype' [] Γ ann .type →
      WfWhnf (ann :: Γ) body bodyV →
      WfWhnf Γ (.fix ann body) (.fix ann body)
  /-- Ascription: annotation must be a type, inner must be well-formed,
      and inner's type-witness must subtype the annotation.
      Output is the inner's type-witness (ascription stripped),
      matching `Och.check`'s behavior and the runtime erasure of
      ascriptions. -/
  | asc {Γ : Ctx} {e τ eV : Expr} :
      Subtype' [] Γ τ .type →
      WfWhnf Γ e eV →
      Subtype' [] Γ eV τ →
      WfWhnf Γ (.asc e τ) eV
  /-- Application: function and argument must be well-formed,
      function's type-witness must subtype a Π (possibly after
      fix/iota unfolding via `Subtype'`), and argument must subtype
      the domain. Output is the codomain with the argument substituted.

      The existentially quantified `dom` and `body` are the Π's
      domain and codomain — they may not appear directly in `fV`
      (e.g. when `fV` is a fix that unfolds to a lambda). -/
  | app {Γ : Ctx} {f a fV aV dom body : Expr} :
      WfWhnf Γ f fV →
      WfWhnf Γ a aV →
      Subtype' [] Γ fV (.lam dom body) →
      Subtype' [] Γ aV dom →
      WfWhnf Γ (.app f a) (body.subst 0 a)
