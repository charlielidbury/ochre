# `MEqRed.bet` Audit — Paper Faithfulness vs Wave 3B Mistranslation

**Status:** READ-ONLY investigation. No code changed. No commits.

**Question:** Is our `MEqRed.bet`'s "no context extension" body premise
faithful to Pasquale & García-Pérez 2024 (CSL 2026), Figure 2's Me-Bet
rule, or is it a Wave 3B mistranslation?

**Answer:** Our rule is **paper-faithful**. The structural obstructions
that have stalled multiple discharge attempts (commits `5d9d0c4`,
`b83bccd`) are **mechanization-induced** by the locally-nameless
encoding interacting with our auxiliary lemma library — they are NOT
present in the paper, because the paper proves Lemma 6 / 7 via a
different chain that never needs an "MEqRed-preserves-WfM" lemma.

---

## 1. Paper's exact Me-Bet rule

From **Figure 2, "Equivalence reduction" panel, p. 9:5** of
`papers/pasquale-garcia-perez-2024-mpss.pdf`:

```
Γ; s ⊢ u  ─≡→ u'      Γ; nil ⊢ v ─≡→ v'
─────────────────────────────────────────  Me-Bet
Γ; s ⊢ (λx ≤ t.u) v ─≡→ u'[x\v']
```

**Critical observation**: the body subderivation `Γ; s ⊢ u ─≡→ u'`
lives at the **same context `Γ`** as the conclusion (and at the same
stack `s`). There is NO `Γ, x ≤ t` or `Γ, x ≡ v'` extension. The bound
name `x` from the abstraction is treated as a meta-variable that names
a hole in `u`, eliminated in the conclusion via the named substitution
`u'[x\v']`. The paper uses ordinary named binders with α-equivalence
glossed (§2 paragraph "We assume the usual notions … α-equivalence is
applied at will").

For comparison, the paper's other binder-introducing rules (same panel)
**do** extend the context:

* **Me-Fun** at empty stack: body premise is `Γ, x ≤ t; nil ⊢ u ─≡→ u'`
  — extends with `≤` annotation.
* **Me-FOp** at non-empty stack `α::s`: body premise is
  `Γ, x ≡ α; s ⊢ u ─≡→ u'` — extends with `≡` annotation pointing at
  the popped operand.

So the paper's `Me-Bet` is the unique exception: it does *not* extend
the context to record any binding for `x`.

## 2. Our mechanization's Me-Bet rule

From `pss/Pss/Mpss/Reductions.lean`, lines 69–73:

```lean
| bet {Γ : Ctx} {s : Stack} {t v v' body body' : Term} (L : Finset String) :
    Term.LC t →
    (∀ x, x ∉ L → MEqRed Γ s (body^[x]) (body'^[x])) →
    MEqRed Γ [] v v' →
    MEqRed Γ s (.app (.abs t body) v) (Term.opening v' body')
```

The cofinite-quantified body premise `∀ x ∉ L, MEqRed Γ s body^[x]
body'^[x]` lives at the same context `Γ` and same stack `s` as the
conclusion. The fresh `x` opens the de Bruijn body `body` to a named
form `body^[x]` but does NOT enter `Γ`.

For comparison, our `fun_` extends with `.sub`:

```lean
| fun_ {Γ : Ctx} {t t' body body' : Term} (L : Finset String) :
    MEqRed Γ [] t t' →
    (∀ x, x ∉ L →
      MEqRed (⟨x, t, .sub⟩ :: Γ) [] (body^[x]) (body'^[x])) →
    MEqRed Γ [] (.abs t body) (.abs t' body')
```

and our `fOp` extends with `.equ` annotation pointing at the popped
operand:

```lean
| fOp {Γ : Ctx} {s : Stack} {t t' α body body' : Term} (L : Finset String) :
    MEqRed Γ [] t t' →
    (∀ x, x ∉ L →
      MEqRed (⟨x, α, .equ⟩ :: Γ) s (body^[x]) (body'^[x])) →
    MEqRed Γ (α :: s) (.abs t body) (.abs t' body')
```

## 3. Comparison: do they match?

**Yes — they match exactly.** The cofinite locally-nameless encoding
of "x is a fresh name for the body hole" with the body subderivation
at the unextended `Γ` is the standard LN translation of the paper's
named binder + α-conversion + meta-variable convention. There is no
divergence between the paper's Me-Bet and our `MEqRed.bet`.

The match is consistent with all our other Me-* rules:

| Paper rule       | Body context      | Lean encoding                                        |
| ---------------- | ----------------- | ---------------------------------------------------- |
| Me-Bet           | `Γ` (no extension)| `MEqRed Γ s (body^[x]) (body'^[x])`                  |
| Me-Fun (nil)     | `Γ, x ≤ t`        | `MEqRed (⟨x,t,.sub⟩ :: Γ) [] (body^[x]) (body'^[x])` |
| Me-FOp (α::s)    | `Γ, x ≡ α`        | `MEqRed (⟨x,α,.equ⟩ :: Γ) s (body^[x]) (body'^[x])`  |

## 4. Why our proofs nonetheless stall — and why the paper does not

The structural obstructions catalogued in commit `5d9d0c4` are real
*mechanization* problems but are **not paper proof obligations**. The
paper's proofs simply do not need the lemmas we have been trying to
build. Concretely:

### 4.1 `WfM.preservation_MEqRed` is NOT a paper lemma

The paper never states or uses anything of the form "`WfM Γ t` is
preserved under `Γ; s ⊢ t ─≡→ t'`". It is a Lean-only auxiliary we
introduced (see `Pss/Mpss/TypeSafety.lean` lines 1317–1361,
`WfM.preservation_MEqRed`) to try to discharge `Lemma_10_Inversion`.
The paper's preservation argument (Lemma 6, p. 9:27) for the **Os-Bet**
case never invokes such a lemma:

> **Case `t = (λx ≤ u.v)w` and `t' = v[x\w]` by rule Os-Bet.** By the
> assumption `Γ ⊢ (λx ≤ u.v)w wf` and by rule `WfApp` we have
> `Γ ⊢ λx ≤ u.v ≤*_wf λx ≤ z.Top` and `Γ ⊢ w ≤*_wf z`. By inversion
> (Lemma 10), we obtain `Γ ⊢ u ≡_wf z`. By Lemma 15, we obtain
> `Γ ⊢ z ≤_wf u`. By Lemma 16 `Γ ⊢ z ≤_wf u`. Because both `z` and `u`
> are well-formed in `Γ`, we have `Γ ⊢ z ≤*_wf u` by rule Ws-Sub. By
> transitivity, we now have `Γ ⊢ w ≤*_wf u`.
> From `Γ ⊢ λx ≤ u.v ≤*_wf λx ≤ z.Top` and Proposition 12, we obtain
> `Γ ⊢ λx ≤ u.v wf`. Hence by rule WfFun, we obtain `Γ, x ≤ u ⊢ v wf`.
>
> Now, by **Lemma 7** on `Γ, x ≤ u ⊢ v wf` and `Γ ⊢ w ≤*_wf u`, we
> obtain `Γ ⊢ v[x\w] wf`.

Note the body's well-formedness `Γ, x ≤ u ⊢ v wf` is sourced from
**Wf-Fun inversion on the abstraction**, which produces it in the
`.sub`-extended context. This has *nothing to do* with `MEqRed.bet`'s
body context. Our chain has been trying to push WfM through the body's
MEqRed — but the paper's Os-Bet preservation never reduces `v` to `v'`
under MEqRed at all. The MEqRed-bet reduction is what `Step.beta`
embeds *into*, but the preservation chain proves WfM of the
*substituted* body, not the *MEqRed-reduced* body.

### 4.2 What `MEqRed.bet`'s body context IS used for in the paper

The paper's actual use of the unextended-Γ body subderivation is in
**Lemma 1** (Strong Commutativity), specifically the
**Case Me-Bet with Ms-App** subcase (p. 9:19–9:20). There the proof:

1. Inverts the Ms-App side via Ms-FOp to obtain
   `Γ, x ≡ v₀; s ⊢ u₀ ─≤→ u₂`.
2. Uses the "no Me-Pro on `x`" `moreover` clause to drop the Pro from
   that derivation and re-cast it as `Γ; s ⊢ u₀ ─≤→ u₂` — i.e. it
   *erases* the `x ≡ v₀` extension.
3. Applies the IH at the unextended Γ.
4. Uses **Lemma 30** to push the substitution `[x\v₁]` through the
   resulting `─≤→ u₃`.

That entire chain *requires* the body subderivation to be at the
unextended `Γ` — if `MEqRed.bet`'s body lived at `Γ, x ≡ v` (a
hypothetical "fix"), the paper's Lemma 1 proof would not type-check:
the IH would produce a derivation in the wrong context, and the
substitution-application step would have nothing to substitute (the
`x ≡ v` annotation already records the binding).

So the rule is structured the way it is for a positive reason: the
paper's commutativity proof needs the bound variable to be a true
meta-variable that *can* be substituted away via Lemma 30, not a
context entry that would have to be deleted.

### 4.3 Lemma 32 (the asymmetric substitution lemma)

The Diamond proof's **Case Me-App with Me-Bet** (p. 9:23) uses
**Lemma 32** to push a substitution `[x\v₂]` through a derivation
`Γ₂, x ≡ v₂; s₂ ⊢ u₂ ─≡→ u₃`, producing `Γ₂; s₂ ⊢ u₂[x\v₂] ─≡→ u₃[x\v₂]`.
Lemma 32 is the *substitution* lemma whose hypothesis derivation lives
in the **extended** context `Γ, x ≡ v ::` and whose conclusion lives
in the **unextended** `Γ` (with the substitution applied). Lemma 32 is
invoked in a context where the body of the *Me-Bet* came in via
`MEqRed.bet`'s premise (unextended Γ) and was then *converted* into the
extended form by an Me-FOp step coming from the Ms-App side.

This asymmetry — Lemma 32's signature, the unextended-Γ Me-Bet body,
and the extended-Γ Me-FOp body — is internally consistent in the paper
and is what enables the Lemma 1 commutativity proof.

### 4.4 What our mechanization is doing wrong

Our axiom `WfM.preservation_MEqRed_bet_axiom` (TypeSafety.lean,
lines 1265–1279) and its sibling `Proposition_17_beta_axiom`
(OperationalSem.lean, lines 81–87) are byproducts of trying to prove
auxiliary lemmas that the paper neither states nor needs. The Wave 3B
direction of "preserve WfM through MEqRed" diverges from the paper's
strategy of "build WfM of the substituted body directly via Lemma 7
on the inverted Wf-Fun premise".

The Diamond.lean Bet-residual axioms (`Lemma_2_inline_app_bet_residual_axiom`,
`Lemma_2_inline_bet_residual_axiom`, see Diamond.lean lines 73–74) are
a separate but related issue: they correspond to Lemma 1 / Lemma 2
cases that the paper proves using the dropped "no Me-Pro on x" Bool
side condition. Those obstructions are about the missing
`avoidsPro` mechanism, not about Me-Bet's body context.

## 5. Recommendation

**Recommendation (a) — keep the rule as-is and find another way through.**

Concretely:

1. **Do not** modify `MEqRed.bet` to extend the context with `.equ x ≡ v`
   (or any other binding). Doing so would break paper-faithfulness and
   would kill the path to `Lemma_1_StrongCommutativity` Case Me-Bet ×
   Ms-App, which crucially relies on the body derivation living at the
   unextended Γ so that the IH can be applied there and Lemma 30/32
   can substitute `x` away afterwards.

2. **Drop** `WfM.preservation_MEqRed` and the per-arm
   `WfM.preservation_MEqRed_bet_axiom` /
   `WfM.preservation_MEqRed_app_axiom` /
   `WfM.preservation_MEqRed_fOp_axiom`. The paper's Os-Bet preservation
   case (Lemma 6) does not need it. Re-attempt `Lemma_6_EvaluationPreservesWf`
   following the paper's chain literally:
   * Wf-App inversion of `Γ ⊢ (λ ≤ u.v) w wf` → both subterms wf,
     `Γ ⊢ w ≤*_wf z` and `Γ ⊢ λ ≤ u.v ≤*_wf λ ≤ z.Top`.
   * Lemma 10 (inversion) → `Γ ⊢ u ≡_wf z`.
   * Lemma 15/16/Ws-Sub/Ws-Trs → `Γ ⊢ w ≤*_wf u`.
   * Wf-Fun inversion → `Γ, x ≤ u ⊢ v wf`.
   * Lemma 7 (substitution) → `Γ ⊢ v[x\w] wf`.

   None of those steps requires "WfM preserves under MEqRed".

3. For `Proposition_17_beta_axiom` (the Step.beta → MEqRed.bet
   embedding): this is a separate LN-encoding obstacle (constructing
   `MEqRed Γ s body^[x] body^[x]` for fresh `x` whose
   `MEqRed.refl`-style construction wants `fv body^[x] ⊆ Γ.dom`). The
   right discharge is a custom `MEqRed.refl_open` helper that walks LC
   structure and uses `MEqRed.var` (no fv-scope requirement) at fvars.
   This is documented in the OperationalSem.lean axiom comment (lines
   77–80) and is independent of `MEqRed.bet`'s rule shape.

4. The Diamond Bet-residual axioms remain blocked on `avoidsPro` /
   term-size induction (see Diamond.lean lines 86–91) and are likewise
   independent of `MEqRed.bet`'s rule shape.

**Rationale (TL;DR):** `MEqRed.bet` is paper-faithful and is structured
precisely to make Lemma 1 Case Me-Bet × Ms-App work; changing it would
break the commutativity proof we ultimately need. The proofs that have
stalled are stalled because they were trying to establish a lemma
(`WfM.preservation_MEqRed`) that the paper does not use — the paper
goes through Wf-Fun inversion + Lemma 7, not through MEqRed
preservation. Refactor away the `WfM.preservation_MEqRed` lemma family
and replay Lemma 6 along the paper's Wf-Fun-inversion chain.
