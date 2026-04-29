import Pss.Mpss.Diamond
import Pss.Mpss.Substitution
import Pss.Mpss.Weakening
import Pss.Mpss.Narrowing
import Pss.Mpss.ContextRed

set_option linter.unusedVariables false

/-! # `Pss.Mpss.Commutation` — Lemma 1 (Strong Commutativity)

Pasquale & García-Pérez 2024 (CSL 2026), §3 (statement) and Appendix A
(proof). The single hardest theorem of the formalization.

The headline result `Lemma_1_StrongCommutativity` says that the MPSS
equivalence reduction `⟶^≡` and subtype reduction `⟶^≤` strongly commute
modulo a context-stepping discipline `↣*`. Diagrammatically:

```
    t₂ ──≡──→ t₃              (closing equiv:   in Γ₁; s₁)
    ↑         ↑
    ≡         ≤              (closing subtype: in Γ₂; s₂)
    ↑         ↑
    t₀ ──≤──→ t₁              (input solid arrows in Γ₀; s₀)
```

with `t₂` obtained by an equivalence step from `t₀` (left vertical
solid) and `t₁` obtained by a subtype step from `t₀` (bottom solid).
The closing equivalence step from `t₁` lives in `(Γ₁, s₁)` and the
closing subtype step from `t₂` lives in `(Γ₂, s₂)`, where both
`(Γ₁, s₁)` and `(Γ₂, s₂)` are reachable from `(Γ₀, s₀)` via the
extended-context reduction `↣*`.

The "context-evolution" premises are a key MPSS innovation versus
traditional commutativity statements: they let the closing context
differ from the starting context, which is what permits the inductive
proof to descend under binders (Me-FOp / Ms-FOp on a stack head).

## Proof strategy in the paper

The paper's proof (Appendix p. 17-20) is by induction on the **term
structure of t₀**, then by case analysis on the last two rules used in
the two solid edges (the bottom subtype edge and the vertical
equivalence edge). For each `(MSubRed.constructor, MEqRed.constructor)`
pair, the closing diagram is constructed by either:

  1. A direct re-application of MEqRed/MSubRed rules (when both edges
     decompose disjoint sub-terms — the IH applies pointwise).
  2. An appeal to Lemma 2 (`Diamond` of `⟶^≡`) — when the subtype side
     is `Ms-Equ` (i.e. it's secretly an equivalence step).
  3. An appeal to substitution lemmas (`Lemma 30`/`Lemma 31`) — when
     both edges fire on the same redex (`Me-Bet` cases).
  4. An appeal to weakening (`Lemma 21`/`Lemma 22`) — when an FOp step
     extends the context with an `≡`-binding that the other side then
     needs to lift past.
  5. An appeal to Lemma 36 to extract `Γ₀; nil ↣ Γ′; nil` from
     `Γ₀; s₀ ↣ Γ′; s′` (used in the Ms-Pro case).

## Mechanization status (this file)

The full formalization of every case is the largest open obligation in
the formalization (estimated 600-1500 lines, see `PLAN.md` §5 Risk 3).

Per `PLAN.md` §6.3 we are permitted **escape-hatch axioms** for cases
that don't yield within bounded effort. We mechanize:

  - The full case-grid enumeration (§1, comment block).
  - The discharged cases that follow directly from existing infrastructure
    (notably the `Ms-Top` arm via `Proposition_18`, and the vacuous
    `pro × pro` case via prevalidity).
  - The headline theorem `Lemma_1_StrongCommutativity` is **AXIOMATIZED
    as a whole** with the precise paper-level statement. The discharge
    plan is documented per case in §1; each non-trivial case has a
    paper line citation for the discharger to follow.

This is the same strategy used for `Lemma_2_DiamondMEqRed` (Wave 5C)
and `Lemma_24_NarrowingMSubRed` (Wave 5B), which are also axiomatized
pending Wave 7-8 polish — Lemma 1 mirrors their treatment so the
cross-referenced theorem statements line up.

The `Pss.Mpss.TransitivityElim` agent (Wave 7A) consumes
`Lemma_1_StrongCommutativity` (and `Lemma_2_DiamondMEqRed`) to derive
`Theorem_3_TransitivityIsAdmissible`. With the axiom in place, the
downstream chain will type-check; once Wave 7-8 dischargers replace
the Lemma 1/Lemma 2 axioms with proofs, `Theorem 3` will reduce to
those standard three (`propext`, `Quot.sound`, `Classical.choice`).
-/

/-! # Lemma 1 case grid

We are case-splitting on the pair `(MSubRed.constructor, MEqRed.constructor)`
of the two solid edges. `MSubRed` has 6 constructors, `MEqRed` has 8,
giving 6×8 = 48 cells. Many are vacuous (term-shape mismatches).

   MSubRed \ MEqRed:    pro    bet    top    app    var    fun_   tAp    fOp
   ──────────────────────────────────────────────────────────────────────────
   pro     (.fvar x)  : V/imp  V      V      V      P*     V      V      V
   top     (any u)    : P      P      P      P      P      P      P      P
   equ     (any u)    : E      E      E      E      E      E      E      E
   app     (.app)     : V      P      V      P      V      V      P      V
   fun_    (.abs)     : V      V      V      V      V      P      V      V
   fOp     (.abs/α::s): V      V      V      V      V      V      V      P*

Status legend:
  V   = vacuous (term shapes can't unify)
  P   = paper-covered (appendix gives a concrete diagram chase)
  P*  = paper-covered with non-trivial side condition (e.g. need Lemma 36
        + multi-Ct-Ann to find the moved annotation; Me-Pro avoidance
        for fOp)
  E   = `Ms-Equ` arm: the subtype side is secretly an `MEqRed` step,
        so this collapses to a `(MEqRed, MEqRed)` instance — discharged
        by `Lemma_2_DiamondMEqRed_bare`. All 8 columns under `equ`
        share this discharge.
  V/imp = vacuous by impossibility of a context having two distinct
        annotations for the same `x` (paper, p. 17 first case): the
        `pro` row needs `x ≤ t ∈ Γ` while the `pro` column needs
        `x ≡ α ∈ Γ`, which contradicts prevalidity.

## Detailed per-cell paper citations

Cell (pro, var)        — paper p. 17 "Case Me-Var with Ms-Pro"
Cell (pro, pro)        — paper p. 17 "Case Me-Pro with Ms-Pro" (vacuous)
Row (top, *)           — paper p. 17 ("If [missing] is Ms-Top ...")
Row (equ, *)           — paper p. 17 ("If the vertical edge is Ms-Equ ...")
Cell (app, app)        — paper p. 18 "Case Me-App with Ms-App"
Cell (app, bet)        — paper p. 19 "Case Me-Bet with Ms-App" (uses Lemma 30)
Cell (app, tAp)        — paper p. 17 "If bottom rule is ... Me-TAp ..."
Cell (fun_, fun_)      — paper p. 18 "Case Me-Fun with Ms-Fun"
Cell (fOp, fOp)        — paper p. 19 "Case Me-FOp with Ms-FOp"

## Approximate line counts (per discharged case in this file)

  `Lemma_1_case_top`           — ~10 lines  (PROVED)
  `Lemma_1_case_pro_pro_vacuous` — ~30 lines (PROVED)
  Headline `Lemma_1_StrongCommutativity` — AXIOMATIZED

The vacuous-by-shape cases (28 cells) will, in the eventual full proof,
be discharged en bloc by the term-structure induction's case analysis:
each `MSubRed` constructor uniquely determines `t₀`'s top-level shape
(`fvar`, `app`, `abs`, etc.), as does each `MEqRed` constructor that
descends into a specific shape. The cells where the shapes don't agree
are skipped by `cases` automatically.
-/

namespace Pss

/-! ## §1. Headline theorem (axiomatized escape hatch) -/

/-- **Lemma 1 (Strong Commutativity, Pasquale & García-Pérez 2024 §3,
appendix A).** The MPSS equivalence reduction `⟶^≡` and subtype
reduction `⟶^≤` strongly commute, modulo the extended-context-stepping
discipline `↣*`.

Diagrammatically:
```
    t₂ ──≡──→ t₃              (closing equiv:   in Γ₁; s₁)
    ↑         ↑
    ≡         ≤              (closing subtype: in Γ₂; s₂)
    ↑         ↑
    t₀ ──≤──→ t₁              (input solid arrows in Γ₀; s₀)
```

The closing context `(Γ₁, s₁)` for the top edge can be ANY extended
context reachable from `(Γ₀, s₀)` via `↣*`. Likewise `(Γ₂, s₂)` for
the right edge. This freedom is what permits the inductive proof to
descend under `Me-FOp` / `Ms-FOp` binders that extend the context with
an `≡`-binding (paper p. 7 "The generalisation over all possible
resulting contexts ... is crucial for the inductive proof").

**Mechanization:** AXIOMATIZED here per Plan §6.3 escape hatch,
mirroring the treatment of `Lemma_2_DiamondMEqRed` (Wave 5C, single
escape hatch) and `Lemma_24_NarrowingMSubRed` (Wave 5B, single escape
hatch). The case-grid comment block above documents what was confronted;
the per-case paper citations point the discharger to the right paragraphs
in Appendix A.

The discharge is by induction on the term structure of `t₀`, with case
analysis on the last rules of `hsub` and `heq`. Across all
`(MSubRed.constructor, MEqRed.constructor)` pairs:

  - **Vacuous-by-shape** (term-tag mismatch): 28 cells, no work.
  - **Vacuous-by-prevalidity** (`pro × pro`): 1 cell, immediate.
  - **Ms-Equ row** (`equ × *`): 8 cells, dispatches to
    `Lemma_2_DiamondMEqRed_bare` plus a `Prevalid` preservation lemma
    along `↣*`.
  - **Ms-Top row** (`top × *`): 8 cells, dispatches to
    `Proposition_18_ReflexivityMSubRed` + `MEqRed.top` re-application.
  - **Diagonal cases** (`app×app`, `fun_×fun_`, `fOp×fOp`): 3 cells,
    use IH on each sub-derivation pointwise + reconstruct the
    constructor on each closing edge.
  - **`pro × var`** (paper p. 17 "Me-Var with Ms-Pro"): 1 cell, uses
    Lemma 36 + multi-`Ct-Ann` + `Lemma_22_WeakeningMEqRed`.
  - **`app × bet`** (paper p. 19 "Me-Bet with Ms-App"): 1 cell, uses
    `Lemma_30_ReductionUnderSubst_Sub` (the substitution-and-reduction
    commutation lemma).
  - **`app × tAp`** (paper p. 17 first paragraph): collapses via
    `Me-TAp` reflexivity.

The full mechanization is estimated at 600-1500 lines.

TODO: discharge in Wave 8 polish. -/
axiom Lemma_1_StrongCommutativity
    {Γ₀ : Ctx} {s₀ : Stack} {t₀ t₁ t₂ : Term}
    (hsub : MSubRed Γ₀ s₀ t₀ t₁)
    (heq  : MEqRed  Γ₀ s₀ t₀ t₂)
    {Γ₁ : Ctx} {s₁ : Stack} {Γ₂ : Ctx} {s₂ : Stack}
    (hCt₁ : ExtCtxRedStar (Γ₀, s₀) (Γ₁, s₁))
    (hCt₂ : ExtCtxRedStar (Γ₀, s₀) (Γ₂, s₂)) :
    Σ' t₃,
      MEqRed  Γ₁ s₁ t₁ t₃ ×
      MSubRed Γ₂ s₂ t₂ t₃

/-! ## §2. Same-context corollary

The most common application of Lemma 1 takes `(Γ₁, s₁) = (Γ₂, s₂) =
(Γ₀, s₀)` (reflexive `↣*`), which is the standard "strong commutativity"
form. Used by `TransitivityElim`. -/

/-- Same-context corollary: take `Γ₁; s₁ = Γ₂; s₂ = Γ₀; s₀` (no
context evolution). -/
noncomputable def Lemma_1_StrongCommutativity_sameCtx
    {Γ : Ctx} {s : Stack} {t₀ t₁ t₂ : Term}
    (hsub : MSubRed Γ s t₀ t₁)
    (heq  : MEqRed  Γ s t₀ t₂) :
    Σ' t₃, MEqRed Γ s t₁ t₃ × MSubRed Γ s t₂ t₃ :=
  Lemma_1_StrongCommutativity hsub heq
    Relation.ReflTransGen.refl Relation.ReflTransGen.refl

/-! ## §3. Discharged sub-cases

Some of the case-grid cells admit short, self-contained proofs from
the existing infrastructure. We expose them as named lemmas. They
serve as:

  - sanity checks that the supporting infrastructure is correctly wired,
  - building blocks for the eventual full discharge,
  - a partial demonstration that the case grid above is internally
    consistent.
-/

/-! ### §3.1. Sub-case `Ms-Top × *`

When the subtype side is `Ms-Top`, the right closing edge is also
`Ms-Top` (anything is below `Top`), and the top closing edge is
`Me-Top` (Top reduces to itself). This case is fully discharged. -/

/-- **Sub-case `top × *`** (paper p. 17 "If the vertical edge is
Ms-Top..."): the closing top edge is `Me-Top` and the closing right
edge is `Ms-Top`. Fully discharged. -/
def Lemma_1_case_top
    {Γ₁ : Ctx} {s₁ : Stack} {Γ₂ : Ctx} {s₂ : Stack} {t₂ : Term}
    (hpv₁ : PrevalidExt Γ₁ s₁) (hpv₂ : PrevalidExt Γ₂ s₂)
    (hLCt₂ : Term.LC t₂)
    (hfv₂ : Term.fv t₂ ⊆ Γ₂.dom) :
    Σ' t₃, MEqRed Γ₁ s₁ Term.top t₃ × MSubRed Γ₂ s₂ t₂ t₃ :=
  -- Take t₃ = Top. The top edge is Me-Top in Γ₁; s₁; the right edge
  -- is Ms-Top of t₂ in Γ₂; s₂.
  ⟨.top, MEqRed.top hpv₁, MSubRed.top hpv₂ hLCt₂ hfv₂⟩

/-! ### §3.2. Vacuous case: `pro × pro`

Paper p. 17 "Case Me-Pro with Ms-Pro": impossible by prevalidity (a
single `x` cannot have both a `≤` and a `≡` annotation). -/

/-- A `subBinds` lookup that succeeds implies the variable is in the
domain. (Local helper; private versions live in `Pss/Mpss/Weakening.lean`,
re-derived here as a public theorem so the vacuity argument can use it.) -/
private theorem _comm_lookupSub_some_dom
    {Γ : Ctx} {x : String} {t : Term} (h : Γ.subBinds x t) : x ∈ Γ.dom := by
  induction Γ with
  | nil => simp [Ctx.subBinds, Ctx.lookupSub] at h
  | cons e rest ih =>
    rw [Ctx.subBinds, Ctx.lookupSub_cons] at h
    by_cases hex : e.name = x
    · simp [Ctx.dom_cons, hex]
    · simp [hex] at h
      simp [Ctx.dom_cons]
      exact Or.inr (ih h)

private theorem _comm_lookupEqu_some_dom
    {Γ : Ctx} {x : String} {α : Term} (h : Γ.equBinds x α) : x ∈ Γ.dom := by
  induction Γ with
  | nil => simp [Ctx.equBinds, Ctx.lookupEqu] at h
  | cons e rest ih =>
    rw [Ctx.equBinds, Ctx.lookupEqu_cons] at h
    by_cases hex : e.name = x
    · simp [Ctx.dom_cons, hex]
    · simp [hex] at h
      simp [Ctx.dom_cons]
      exact Or.inr (ih h)

/-- **Sub-case `pro × pro`** (paper p. 17): vacuous by prevalidity.
Given a context with both `x ≤ t` and `x ≡ α`, we derive `False`. -/
theorem Lemma_1_case_pro_pro_vacuous
    {Γ : Ctx} {x : String} {t α : Term}
    (hpv : Prevalid Γ)
    (hsub : Γ.subBinds x t) (hequ : Γ.equBinds x α) :
    False := by
  induction Γ with
  | nil =>
    simp [Ctx.subBinds, Ctx.lookupSub] at hsub
  | cons e rest ih =>
    have hpv_norm : Prevalid (e :: rest) := hpv
    by_cases hex : e.name = x
    · cases he_kind : e.kind with
      | sub =>
        -- e is .sub for x. equBinds at the head returns none when kind=.sub,
        -- so the lookup `Ctx.equBinds (⟨x, _, .sub⟩ :: rest) x = some α`
        -- reduces to `none = some α`, which is False. Close via Option.noConfusion.
        have hequ' : Ctx.equBinds (e :: rest) x α := hequ
        rw [Ctx.equBinds, Ctx.lookupEqu_cons] at hequ'
        rw [if_pos hex, he_kind] at hequ'
        -- hequ' : none = some α
        exact Option.noConfusion hequ'
      | equ =>
        have hsub' : Ctx.subBinds (e :: rest) x t := hsub
        rw [Ctx.subBinds, Ctx.lookupSub_cons] at hsub'
        rw [if_pos hex, he_kind] at hsub'
        exact Option.noConfusion hsub'
    · -- e is not for x; recurse on rest.
      have hsub' : Ctx.subBinds (e :: rest) x t := hsub
      have hequ' : Ctx.equBinds (e :: rest) x α := hequ
      rw [Ctx.subBinds, Ctx.lookupSub_cons] at hsub'
      rw [Ctx.equBinds, Ctx.lookupEqu_cons] at hequ'
      simp [hex] at hsub' hequ'
      exact ih hpv_norm.tail hsub' hequ'

end Pss
