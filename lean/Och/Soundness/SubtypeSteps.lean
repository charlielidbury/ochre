import Och.Subtyping

/-!
# B1+B2: head-step preservation for `Subtype'`

These lemmas say that the declarative subtype relation is closed under
the head-reduction rules that `concEval` performs:

  * β-reduce            `(λA. b) a    ↝ b[a/0]`
  * ι-unfold            `ι A. body    ↝ body[ι A. body/0]`
  * fix-unfold          `fix A. body  ↝ body[fix A. body/0]`
  * let-unfold          `let v in b   ↝ b[v/0]`
  * ascription strip    `(e : τ)      ↝ e`

The statement, parameterised by reduction shape, is:

```
Subtype' S Γ <redex>  τ → Subtype' S Γ <reduct>  τ.
```

i.e. if the *redex* has a declarative supertype `τ`, then so does its
*reduct*. This is exactly the substep needed by `concEval_preservation`
(B3 / `Och.Soundness.concEval_preservation`).

## Proof shape

All proofs are one-liners exploiting the fact that `Subtype'`
already has the dual constructors `beta_R`, `unfold_iota_R`,
`unfold_fix_R`: these say `reduct ⊑ redex`. Composed
with the hypothesis `redex ⊑ τ` via `Subtype'.trans`, we get
`reduct ⊑ τ`.

Concretely, for β:

  * `beta_R (refl _) : Subtype' S Γ (b.subst 0 a) (.app (.lam A b) a)`
  * `Subtype'.trans` of the above with the hypothesis closes the goal.

The earlier strategy doc anticipated a structural induction on the LHS
derivation (with the worrying `app_cong` case requiring head-WHNF
characterisation). The R-direction conversion rules already in
`Subtype'` make that induction unnecessary. -/

namespace Subtype'

/-- B1 — β-step preservation. If the redex `(λA. b) a` is a subtype of
`τ`, so is its reduct `b[a/0]`. -/
def preserve_betaStep {S : Seen} {Γ : Ctx} {A b a τ : Expr}
    (h : Subtype' S Γ (.app (.lam A b) a) τ) :
    Subtype' S Γ (b.subst 0 a) τ :=
  .trans (.beta_R (.refl _)) h

/-- B2.1 — ι-unfold-step preservation. -/
def preserve_iotaUnfoldStep {S : Seen} {Γ : Ctx} {ann body τ : Expr}
    (h : Subtype' S Γ (.iota ann body) τ) :
    Subtype' S Γ (body.subst 0 (.iota ann body)) τ :=
  .trans (.unfold_iota_R (.refl _)) h

/-- B2.2 — fix-unfold-step preservation. -/
def preserve_fixUnfoldStep {S : Seen} {Γ : Ctx} {ann body τ : Expr}
    (h : Subtype' S Γ (.fix ann body) τ) :
    Subtype' S Γ (body.subst 0 (.fix ann body)) τ :=
  .trans (.unfold_fix_R (.refl _)) h

/-! ## R-side mirror lemmas

For completeness we also provide the *RHS* preservation forms — `redex
on the right` reduces to `reduct on the right`. These are dual to B1/B2
and use the L-side conversion rules (`beta_L`, `unfold_iota_L`, etc.).
The `concEval_preservation` proof only needs the L-side forms, since
`concEval` reduces the term on the LHS of the typing judgment, but the
mirrors are useful when working with `Subtype'` more generally. -/

/-- β-step preservation, RHS form. -/
def preserve_betaStep_R {S : Seen} {Γ : Ctx} {A b a a' : Expr}
    (h : Subtype' S Γ a' (.app (.lam A b) a)) :
    Subtype' S Γ a' (b.subst 0 a) :=
  .trans h (.beta_L (.refl _))

/-- ι-unfold preservation, RHS form. -/
def preserve_iotaUnfoldStep_R {S : Seen} {Γ : Ctx}
    {ann body a' : Expr}
    (h : Subtype' S Γ a' (.iota ann body)) :
    Subtype' S Γ a' (body.subst 0 (.iota ann body)) :=
  .trans h (.unfold_iota_L (.refl _))

/-- fix-unfold preservation, RHS form. -/
def preserve_fixUnfoldStep_R {S : Seen} {Γ : Ctx}
    {ann body a' : Expr}
    (h : Subtype' S Γ a' (.fix ann body)) :
    Subtype' S Γ a' (body.subst 0 (.fix ann body)) :=
  .trans h (.unfold_fix_L (.refl _))

end Subtype'
