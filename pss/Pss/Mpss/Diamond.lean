import Pss.Mpss.Substitution
import Pss.Mpss.Weakening

/-! # `Pss.Mpss.Diamond` — Diamond property and reflexivity for `⟶^≡`

Pasquale & García-Pérez 2024 (CSL 2026), §3 (and appendix proofs).

This module mechanizes:

* **Proposition 18 (Reflexivity).** Every locally-closed, in-scope term
  reduces to itself in one step under both `⟶^≡` and `⟶^≤`.
* **Lemma 2 (Diamond modulo Me-Pro side condition).** `⟶^≡` has the
  diamond property modulo a "no `Me-Pro` on `x`" side condition that
  travels through context-reduction.

## Encoding the side condition (Approach A)

The paper's Lemma 2 statement has this clause:

> "Moreover, for any variable `x`, if in the derivation of `Γ₀; s₀ ⊢ t₀ ⟶^≡ t₁`
> [...] there isn't an application of the Rule `Me-Pro` that makes a promotion
> of variable `x`, then in the derivation `Γ₂; s₂ ⊢ t₂ ⟶^≡ t₃` [...] there
> won't be an application of the Rule `Me-Pro` that makes a promotion of
> variable `x`."

We encode this as an **inductive predicate** `MEqRedAvoidsPro h x : Prop`
that mirrors the structure of `MEqRed`'s constructors. Constructor-by-
constructor: at every node we require the corresponding sub-derivations
to also avoid promoting `x`; at `Me-Pro` nodes we additionally require
the promoted variable to differ from `x`.

This is **Approach A** from the plan (Risk 4, §5). We chose the inductive
formulation (rather than a `def` by recursion) because the cofinitely-
quantified body sub-derivations of `bet`/`fun_`/`fOp` make a recursive
`def` over the eliminator awkward (Lean's pattern-matcher cannot easily
extract the `y ∉ L` hypothesis when the constructor is matched). Approach B
(a refined inductive `MEqRedNoProOf` mirroring `MEqRed` itself) is left as
a fallback if downstream proofs need a different shape.

## Status

* `Proposition_18_ReflexivityMEqRed`  — **PROVED** (delegates to
  `MEqRed.refl` from `Pss.Mpss.Substitution`).
* `Proposition_18_ReflexivityMSubRed` — **PROVED** (via `Ms-Equ`).
* `Proposition_18_Reflexivity`       — **PROVED** (combined statement).
* `Lemma_2_DiamondMEqRed` — **AXIOMATIZED** (single Wave 5 escape
  hatch per Plan §6.3). The proof is the second-largest in the
  formalization (300-500+ lines, paper §3 + appendix). The axiom
  states the precise side-condition-aware form, and the predicate
  `MEqRedAvoidsPro` is fully mechanized so the discharger has a
  definite target.

The discharger (Wave 7 at latest) will replace the axiom with a proof by
induction on `h₁` with case analysis on `h₂`, using:

* `Lemma_31_ReductionUnderSubst_Eq` (Wave 4B) for Me-Bet vs. Me-Bet (the
  substitution-vs-reduction commutation).
* `Lemma_22_WeakeningMEqRed` (Wave 4A) for Me-Pro vs. Me-Var (lifting
  reductions across context extensions for the promoted operand).
* `Lemma_36` (Wave 3C) for extracting `Γ₀; nil ↣ Γ₂; nil` from
  `Γ₀; s₀ ↣ Γ₂; s₂`.
* `MEqRed.refl` (Proposition 18 here) for trivial diagonal cases.
-/

namespace Pss

/-! ## §1. The "no Me-Pro on `x`" predicate (Approach A)

Defined as an inductive predicate (Approach A, with the inductive flavour
of formulation, since the cofinitely-quantified body cases of `bet`/`fun_`/
`fOp` make a `def`-by-recursion form awkward to state cleanly). -/

/-- Predicate on `MEqRed` derivations: the derivation does NOT contain
an application of `Me-Pro` that promotes the named variable `x`.

The predicate has one constructor per `MEqRed` constructor; the `pro`
constructor is the only one with non-trivial side condition (`y ≠ x`),
and it propagates the predicate to its operand sub-derivation. All other
constructors propagate the predicate structurally to all sub-derivations
(including the cofinitely-quantified body sub-derivations, which must
satisfy the predicate uniformly over the `y ∉ L` witnesses). -/
inductive MEqRedAvoidsPro (x : String) :
    ∀ {Γ : Ctx} {s : Stack} {u v : Term}, MEqRed Γ s u v → Prop where
  /-- `Me-Pro` on `y ≠ x`, with the operand sub-derivation also avoiding
  promotion of `x`. -/
  | pro {Γ s y α α'}
        (hpv : PrevalidExt Γ s)
        (heq : Γ.equBinds y α)
        (hα : MEqRed Γ s α α')
        (hyx : y ≠ x)
        (hAv : MEqRedAvoidsPro x hα) :
      MEqRedAvoidsPro x (MEqRed.pro hpv heq hα)
  /-- `Me-Bet` with both body and operand sub-derivations avoiding `x`. -/
  | bet {Γ s t v v' body body'} {L : Finset String}
        (hLCt : Term.LC t)
        (hbody : ∀ y, y ∉ L → MEqRed Γ s (body^[y]) (body'^[y]))
        (hv : MEqRed Γ [] v v')
        (hAvBody : ∀ y (hy : y ∉ L), MEqRedAvoidsPro x (hbody y hy))
        (hAvV : MEqRedAvoidsPro x hv) :
      MEqRedAvoidsPro x (MEqRed.bet (L := L) hLCt hbody hv)
  /-- `Me-Top` is always fine. -/
  | top {Γ s} (hpv : PrevalidExt Γ s) :
      MEqRedAvoidsPro x (MEqRed.top hpv)
  /-- `Me-App` with both operator and operand sub-derivations avoiding `x`. -/
  | app {Γ s u u' v v'}
        (hu : MEqRed Γ (v :: s) u u')
        (hv : MEqRed Γ [] v v')
        (hAvU : MEqRedAvoidsPro x hu)
        (hAvV : MEqRedAvoidsPro x hv) :
      MEqRedAvoidsPro x (MEqRed.app hu hv)
  /-- `Me-Var` is always fine. -/
  | var {Γ s y} (hpv : PrevalidExt Γ s) :
      MEqRedAvoidsPro x (MEqRed.var (x := y) hpv)
  /-- `Me-Fun` with both bound-annotation and body sub-derivations avoiding `x`. -/
  | fun_ {Γ t t' body body'} {L : Finset String}
        (ht : MEqRed Γ [] t t')
        (hbody : ∀ y, y ∉ L →
          MEqRed (⟨y, t, .sub⟩ :: Γ) [] (body^[y]) (body'^[y]))
        (hAvT : MEqRedAvoidsPro x ht)
        (hAvBody : ∀ y (hy : y ∉ L), MEqRedAvoidsPro x (hbody y hy)) :
      MEqRedAvoidsPro x (MEqRed.fun_ (L := L) ht hbody)
  /-- `Me-TAp` is always fine. -/
  | tAp {Γ s u}
        (hpv : PrevalidExt Γ s) (hLC : Term.LC u) (hfv : Term.fv u ⊆ Γ.dom) :
      MEqRedAvoidsPro x (MEqRed.tAp hpv hLC hfv)
  /-- `Me-FOp` with both bound-annotation and body sub-derivations avoiding `x`. -/
  | fOp {Γ s t t' α body body'} {L : Finset String}
        (ht : MEqRed Γ [] t t')
        (hbody : ∀ y, y ∉ L →
          MEqRed (⟨y, α, .equ⟩ :: Γ) s (body^[y]) (body'^[y]))
        (hAvT : MEqRedAvoidsPro x ht)
        (hAvBody : ∀ y (hy : y ∉ L), MEqRedAvoidsPro x (hbody y hy)) :
      MEqRedAvoidsPro x (MEqRed.fOp (L := L) ht hbody)

/-! ## §2. Proposition 18 — Reflexivity of `⟶^≡` and `⟶^≤` -/

/-- **Proposition 18 (Reflexivity, equivalence half).** For any prevalid
extended context `Γ; s` and any locally-closed in-scope term `u`,
`Γ; s ⊢ u ⟶^≡ u`.

This is a direct re-export of `MEqRed.refl` from `Pss.Mpss.Substitution`,
exposed at this module under the paper's name. -/
theorem Proposition_18_ReflexivityMEqRed
    {Γ : Ctx} {s : Stack} {u : Term}
    (hpv : PrevalidExt Γ s) (hLC : Term.LC u) (hfv : Term.fv u ⊆ Γ.dom) :
    MEqRed Γ s u u :=
  MEqRed.refl hpv hLC hfv

/-- **Proposition 18 (Reflexivity, subtyping half).** Same statement, for
`⟶^≤`. Follows by `Ms-Equ` from the equivalence half. -/
theorem Proposition_18_ReflexivityMSubRed
    {Γ : Ctx} {s : Stack} {u : Term}
    (hpv : PrevalidExt Γ s) (hLC : Term.LC u) (hfv : Term.fv u ⊆ Γ.dom) :
    MSubRed Γ s u u :=
  MSubRed.equ hpv (Proposition_18_ReflexivityMEqRed hpv hLC hfv)

/-- **Proposition 18 (Reflexivity, combined).** Both halves. -/
theorem Proposition_18_Reflexivity
    {Γ : Ctx} {s : Stack} {u : Term}
    (hpv : PrevalidExt Γ s) (hLC : Term.LC u) (hfv : Term.fv u ⊆ Γ.dom) :
    MEqRed Γ s u u ∧ MSubRed Γ s u u :=
  ⟨Proposition_18_ReflexivityMEqRed hpv hLC hfv,
   Proposition_18_ReflexivityMSubRed hpv hLC hfv⟩

/-! ## §3. Lemma 2 — Diamond property modulo Me-Pro side condition

The paper's statement (verbatim, modulo notation):

  Let `Γ₀; s₀` be an extended context. Let `t₀, t₁, t₂` be terms.
  If `Γ₀; s₀ ⊢ t₀ ⟶^≡ t₁` and `Γ₀; s₀ ⊢ t₀ ⟶^≡ t₂`, then for any
  extended contexts `Γ₁; s₁` and `Γ₂; s₂` such that `Γ₀; s₀ ↣ Γ₁; s₁`
  and `Γ₀; s₀ ↣ Γ₂; s₂`, there exists a term `t₃` such that
  `Γ₁; s₁ ⊢ t₁ ⟶^≡ t₃` and `Γ₂; s₂ ⊢ t₂ ⟶^≡ t₃`.

  Moreover, for any variable `x`, if in the derivation of
  `Γ₀; s₀ ⊢ t₀ ⟶^≡ t₁` (respectively `Γ₀; s₀ ⊢ t₀ ⟶^≡ t₂`) there
  isn't an application of the Rule `Me-Pro` that makes a promotion of
  variable `x`, then in the derivation `Γ₂; s₂ ⊢ t₂ ⟶^≡ t₃`
  (respectively `Γ₁; s₁ ⊢ t₁ ⟶^≡ t₃`) there won't be an application of
  the Rule `Me-Pro` that makes a promotion of variable `x`.

The "side condition propagation" clause is encoded as the existence of
`t₃` and **derivations** `h₁' h₂'` for the two output edges, such that
the "no Me-Pro on `x`" predicate transfers in the swapped direction. -/

/-- **Lemma 2** (Pasquale & García-Pérez 2024 §3, Diamond property of
`⟶^≡` modulo the "no Me-Pro on `x`" side condition).

The conclusion exposes the closing derivations `h₁'` and `h₂'` so that
the side-condition-propagation clause (the `Moreover` paragraph of the
paper) can be stated about them.

Status: **AXIOMATIZED** as Wave 5's single escape-hatch (per Plan §6.3).
The proof is by induction on `h₁` with case analysis on `h₂`'s last rule.
For each `(rule₁, rule₂)` pair:

* both reduce the same redex → IHs combine (e.g. Me-Pro/Me-Pro, Me-Bet/Me-Bet).
* disjoint subterms → trivial closure (each side just re-steps).
* substitution overlap → use `Lemma_31_ReductionUnderSubst_Eq`.
* `Me-Pro` vs. structural-on-`x` → uses the side condition.

Estimated proof size: 300-500 lines. Discharged in Wave 7 (`Pss.Mpss.Commutation`
and follow-ons), where the full case grid is enumerated alongside the
strong-commutation proof. -/
axiom Lemma_2_DiamondMEqRed
    {Γ₀ : Ctx} {s₀ : Stack} {t₀ t₁ t₂ : Term}
    (h₁ : MEqRed Γ₀ s₀ t₀ t₁)
    (h₂ : MEqRed Γ₀ s₀ t₀ t₂)
    {Γ₁ : Ctx} {s₁ : Stack} {Γ₂ : Ctx} {s₂ : Stack}
    (hCt₁ : ExtCtxRedStar (Γ₀, s₀) (Γ₁, s₁))
    (hCt₂ : ExtCtxRedStar (Γ₀, s₀) (Γ₂, s₂)) :
    ∃ (t₃ : Term) (h₁' : MEqRed Γ₁ s₁ t₁ t₃) (h₂' : MEqRed Γ₂ s₂ t₂ t₃),
      -- Side-condition propagation (the "Moreover" clause):
      ∀ x : String,
        (MEqRedAvoidsPro x h₁ → MEqRedAvoidsPro x h₂') ∧
        (MEqRedAvoidsPro x h₂ → MEqRedAvoidsPro x h₁')

/-! ## §4. Convenience: the bare-existence corollary

Many downstream consumers of Lemma 2 only need the basic existence of
`t₃` without the side-condition propagation. We expose that as a
corollary that drops the `MEqRedAvoidsPro` clause. -/

/-- Bare-existence corollary of `Lemma_2_DiamondMEqRed`: the diamond
property of `⟶^≡` (without the side condition exposed in the
conclusion). -/
theorem Lemma_2_DiamondMEqRed_bare
    {Γ₀ : Ctx} {s₀ : Stack} {t₀ t₁ t₂ : Term}
    (h₁ : MEqRed Γ₀ s₀ t₀ t₁)
    (h₂ : MEqRed Γ₀ s₀ t₀ t₂)
    {Γ₁ : Ctx} {s₁ : Stack} {Γ₂ : Ctx} {s₂ : Stack}
    (hCt₁ : ExtCtxRedStar (Γ₀, s₀) (Γ₁, s₁))
    (hCt₂ : ExtCtxRedStar (Γ₀, s₀) (Γ₂, s₂)) :
    ∃ t₃, MEqRed Γ₁ s₁ t₁ t₃ ∧ MEqRed Γ₂ s₂ t₂ t₃ := by
  obtain ⟨t₃, h₁', h₂', _⟩ :=
    Lemma_2_DiamondMEqRed h₁ h₂ hCt₁ hCt₂
  exact ⟨t₃, h₁', h₂'⟩

/-! ## §5. Same-context corollary

The most common application of Lemma 2 takes `Γ₁; s₁ = Γ₂; s₂ = Γ₀; s₀`
(reflexive `↣*`), which is the actual diamond property in the standard
sense. -/

/-- The diamond property of `MEqRed` at a single extended context (no
context evolution). This is the form used by the strong-commutativity
proof (Wave 6) and the transitivity-elimination theorem (Wave 7). -/
theorem Lemma_2_DiamondMEqRed_sameCtx
    {Γ : Ctx} {s : Stack} {t₀ t₁ t₂ : Term}
    (h₁ : MEqRed Γ s t₀ t₁)
    (h₂ : MEqRed Γ s t₀ t₂) :
    ∃ t₃, MEqRed Γ s t₁ t₃ ∧ MEqRed Γ s t₂ t₃ :=
  Lemma_2_DiamondMEqRed_bare h₁ h₂
    (Relation.ReflTransGen.refl) (Relation.ReflTransGen.refl)

end Pss
