import Pss.Syntax

/-!
# Declarative subtyping and well-formedness for System λ⊲

Figure 1 of Hutchins, *Pure Subtype Systems* (POPL 2010): context
well-formedness `Γ wf`, term well-formedness `Γ ⊢ t wf`, well-subtyping
`Γ ⊢ t ⊲wf u`, and declarative subtyping `Γ ⊢ t ⊲ u`.

The four judgments are mutually inductive: subtyping mentions
well-formedness in DS-TRANS, well-formedness mentions well-subtyping in
W-APP, and well-subtyping packages well-formedness with subtyping (W-SUB).

The metavariable `⊲` ranges over `≤` and `≡` (`Rel.le`, `Rel.eq`); a rule
stated with `⊲` is two rules, exactly as in §3.1 of the paper.

De Bruijn conventions (formalization tweaks, cf. `Pss.Syntax`):
* `x ∈ dom(Γ)` becomes `x < Γ.length`;
* the freshness premise `x ∉ dom(Γ)` of W-GAM2 is vacuous and disappears;
* `x ≤ t ∈ Γ` is `Ctx.Bound Γ x t`, which shifts the bound into the scope
  of the full context.
-/
namespace Pss

mutual

/-- `Γ wf` — context well-formedness (Figure 1). -/
inductive CtxWf : Ctx → Prop where
  /-- `∅ wf` (W-GAM1). -/
  | nil : CtxWf []
  /-- `Γ wf, Γ ⊢ t wf ⟹ Γ, x ≤ t wf` (W-GAM2; freshness of `x` is implicit
  in de Bruijn style). -/
  | cons {Γ : Ctx} {t : Term} : CtxWf Γ → Wf Γ t → CtxWf (t :: Γ)

/-- `Γ ⊢ t wf` — well-formedness (Figure 1). -/
inductive Wf : Ctx → Term → Prop where
  /-- `Γ wf, x ∈ dom(Γ) ⟹ Γ ⊢ x wf` (W-VAR). -/
  | var {Γ : Ctx} {x : Nat} : CtxWf Γ → x < Γ.length → Wf Γ (.var x)
  /-- `Γ wf ⟹ Γ ⊢ Top wf` (W-TOP). -/
  | top {Γ : Ctx} : CtxWf Γ → Wf Γ .top
  /-- `Γ, x ≤ t ⊢ u wf ⟹ Γ ⊢ λx ≤ t. u wf` (W-FUN). -/
  | fn {Γ : Ctx} {t u : Term} : Wf (t :: Γ) u → Wf Γ (.lam t u)
  /-- `Γ ⊢ t ≤wf λx ≤ s. Top, Γ ⊢ u ≤wf s ⟹ Γ ⊢ t(u) wf` (W-APP). -/
  | app {Γ : Ctx} {t u s : Term} :
      WellSub Γ t .le (.lam s .top) → WellSub Γ u .le s → Wf Γ (.app t u)

/-- `Γ ⊢ t ⊲wf u` — well-subtyping (Figure 1): subtyping between terms that
are themselves well-formed. Written `t ≤wf u` / `t ≡wf u` in the paper. -/
inductive WellSub : Ctx → Term → Rel → Term → Prop where
  /-- `Γ ⊢ t wf, u wf, Γ ⊢ t ⊲ u ⟹ Γ ⊢ t ⊲wf u` (W-SUB). -/
  | sub {Γ : Ctx} {t u : Term} {r : Rel} :
      Wf Γ t → Wf Γ u → Sub Γ t r u → WellSub Γ t r u

/-- `Γ ⊢ t ⊲ u` — declarative subtyping (Figure 1), defined syntactically
over *all* terms (well-formedness checks live in `WellSub`, cf. §3.4). -/
inductive Sub : Ctx → Term → Rel → Term → Prop where
  /-- `Γ ⊢ s ⊲ t, t ⊲ u, t wf ⟹ Γ ⊢ s ⊲ u` (DS-TRANS). -/
  | trans {Γ : Ctx} {s t u : Term} {r : Rel} :
      Sub Γ s r t → Sub Γ t r u → Wf Γ t → Sub Γ s r u
  /-- `Γ ⊢ u ≡ t ⟹ Γ ⊢ t ≡ u` (DS-SYM). -/
  | symm {Γ : Ctx} {t u : Term} : Sub Γ u .eq t → Sub Γ t .eq u
  /-- `Γ ⊢ t ≡ u ⟹ Γ ⊢ t ≤ u` (DS-EQ). -/
  | eq {Γ : Ctx} {t u : Term} : Sub Γ t .eq u → Sub Γ t .le u
  /-- `Γ ⊢ x ≡ x` (DS-VAR). -/
  | var {Γ : Ctx} {x : Nat} : Sub Γ (.var x) .eq (.var x)
  /-- `Γ ⊢ Top ≡ Top` (DS-TOP). -/
  | top {Γ : Ctx} : Sub Γ .top .eq .top
  /-- `Γ ⊢ t ≡ t', Γ, x ≤ t ⊢ u ⊲ u' ⟹ Γ ⊢ λx ≤ t. u ⊲ λx ≤ t'. u'`
  (DS-FUN). Note the *invariant* bound (§3.3: no contravariance). -/
  | fn {Γ : Ctx} {t t' u u' : Term} {r : Rel} :
      Sub Γ t .eq t' → Sub (t :: Γ) u r u' →
      Sub Γ (.lam t u) r (.lam t' u')
  /-- `Γ ⊢ t ⊲ t', u ≡ u' ⟹ Γ ⊢ t(u) ⊲ t'(u')` (DS-APP): point-wise
  subtyping, covariant in the function, invariant in the argument. -/
  | app {Γ : Ctx} {t t' u u' : Term} {r : Rel} :
      Sub Γ t r t' → Sub Γ u .eq u' →
      Sub Γ (.app t u) r (.app t' u')
  /-- `Γ ⊢ (λx ≤ t. u)(s) ≡ [x ↦ s]u` (DS-EAPP): β-reduction as equivalence. -/
  | eapp {Γ : Ctx} {t u s : Term} :
      Sub Γ (.app (.lam t u) s) .eq (u.subst1 s)
  /-- `Γ ⊢ t ≤ Top` (DS-ETOP). -/
  | etop {Γ : Ctx} {t : Term} : Sub Γ t .le .top
  /-- `x ≤ t ∈ Γ ⟹ Γ ⊢ x ≤ t` (DS-EVAR): variable promotion. -/
  | evar {Γ : Ctx} {x : Nat} {t : Term} :
      Ctx.Bound Γ x t → Sub Γ (.var x) .le t

end

end Pss
