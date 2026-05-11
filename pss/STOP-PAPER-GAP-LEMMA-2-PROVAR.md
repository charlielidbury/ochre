# PROVISIONAL — Lemma 2 Moreover clause at ProVar may have a paper gap

**Status:** Provisional Verdict B with strong Verdict C salvage path
recommendation. The agent that introduced
`MoreoverDiamondGeneral_ProVarVarPro_Payload` and
`MoreoverDiamondGeneral_VarPro_Payload` (commits `e24961f`, `be86b75`)
diagnosed a wall at general-context Moreover propagation through the
Me-Pro × Me-Var case. This dispatch confirms the wall is real **as
predicated** but suggests the predicate may be re-formulable.

**Hard caveat — historical false alarm:** The previous paper-bug
diagnosis at Lemma 32 (commit `e5d2096`) was WRONG (revert in commit
`bb3b441`, STOP file `STOP-PAPER-BUG-LEMMA-32.md`). That diagnosis
missed a structural rescue lemma (`MEqRed.sub_to_equ_head_replace`).
**A similar rescue may exist for ProVar that this dispatch hasn't
identified.** Do NOT email the authors based on this file alone — first
attempt the Verdict C re-formulation described below.

## The claim being verified

The agent shipped two residual payloads:

```lean
def MoreoverDiamondGeneral_ProVarVarPro_Payload : Prop :=
  ∀ {Γ₀ : Ctx} {s₀ : Stack} {i : Nat} {α₀ α_1 : Term}
    (hpv₁ : PrevalidExt Γ₀ s₀) (hb : Γ₀.equBinds i α₀)
    (hα : MEqRed Γ₀ s₀ α₀ α_1)
    (hpv₂ : PrevalidExt Γ₀ s₀) (hi : i < Γ₀.depth),
    MoreoverDiamondGeneral
      (MEqRed.pro hpv₁ hb hα) (MEqRed.var hpv₂ hi)
```

with claim: "The paper's bidirectional Moreover clause for the Me-Pro
× Me-Var case (p. 9:21) requires NP-x of the lifted reduction `α₀ →
α_evolved` (built via `equBinds_evolve + lift_empty_to_stack`) for all
variable indices x. The lifted reduction can inherit Me-Pro steps from
`ctAnn`'s arbitrary `hbound : MEqRed Γ_inner [] t t'` carrier, so
unconditional NP cannot be established."

## What the paper actually says

**Paper Lemma 2 statement (p. 9:9):**

> *Moreover, for any variable x, if in the derivation of `Γ₀; s₀ ⊢ t₀ →ᵉᵠᵘ t₁`
> (respectively `Γ₀; s₀ ⊢ t₀ →ᵉᵠᵘ t₂`) there isn't an application of the
> Rule Me-Pro that makes a promotion of variable x, then in the
> derivation `Γ₂; s₂ ⊢ t₂ →ᵉᵠᵘ t₃` (respectively `Γ₁; s₁ ⊢ t₁ →ᵉᵠᵘ t₃`)
> there won't be an application of the Rule Me-Pro that makes a
> promotion of variable x.*

The clause is universally quantified over `x` and stated at general
evolutions `Γ₀; s₀ ↣ Γ₂; s₂`.

**Paper Lemma 2 proof of Me-Pro × Me-Var case (p. 9:21):** builds the
diamond via `equBinds_evolve` (multiple Ct-Ann) + Lemma 19 (weakening),
gets bound diamond α₃, rebuilds Me-Pro on Γ₂. **NEVER mentions or
traces the Moreover witness through the case.**

## The structural obstacle

For the Me-Pro × Me-Var pair, h₂ = Me-Var has `h₂.NoPromotionOf x = True`
for all `x`. The paper's Moreover then requires `d₁.NoPromotionOf x = True`
for all `x`, where `d₁ : MEqRed Γ₁ s₁ α₁ α₃` is the bound diamond's
LHS output.

`d₁` is obtained from the **bound IH** applied to `(hα, hLifted)`, where
`hLifted : MEqRed Γ₀ s₀ α₀ α₂` is the "evolved bound" reduction built
via `equBinds_evolve` (extracting from `he₂`) plus `lift_empty_to_stack`.

The bound IH's Moreover delivers `hLifted.NoPromotionOf x → d₁.NoPromotionOf x`.
**To conclude `d₁.NoPromotionOf x` for all `x`, we need `hLifted.NoPromotionOf x`
for all `x`.**

`equBinds_evolve` at a `ContextEvolution.ctAnn` step extracts the
constructor's `hbound : MEqRed Γ_inner [] t t'` field weakened by
`weaken_head`. **This `hbound` is an arbitrary MEqRed derivation that
can contain `Me-Pro` steps**. So `hLifted` inherits arbitrary `Me-Pro`,
and `hLifted.NoPromotionOf x` is NOT free for all `x`.

## Where the bundle recursion meets non-trivial evolutions

The top-level downstream consumer is `UniformEqDiamonds`, which
specializes the bundle to `ctRefl/ctRefl` (same-context). At ctRefl,
`hLifted` is reflexive, has no `Me-Pro`, and the wall vanishes.

But the bundle's recursion builds new evolutions internally via:

* `fun_fun`: body IH at `ContextEvolution.ctAnn he hT` (hT is the
  abstraction's bound reduction — can contain Me-Pro).
* `bet_bet`/`app_bet`/`bet_app`: body IH at `cons_evolve(he, hArg)`
  (= ctAnn with hArg = operand reduction — can contain Me-Pro).
* `fOp_fOp`: body IH at `cons_evolve(he, hStripHead)` (head reduction
  from `stripStackHeadWithReduction` — can contain Me-Pro).

So inside the bundle's recursion, ProVar cells DO face non-trivial
evolutions containing Me-Pro, and the wall applies.

## Why this isn't trivially Verdict B (Verdict C salvage path)

Critically, **the paper's actual USE of the Moreover clause is more
restricted than its stated UNIVERSAL form**. Examining the paper's
recursive usage in Lemma 2's Me-App × Me-Bet case (p. 9:22-23):

> "By induction hypothesis on `Γ₀, x ≡ v₀; s₀ ⊢ u₀ →= u₂`, there exists
> u₃ such that:
> * Γ₁, x ≡ v₁; s₁ ⊢ u₁ →= u₃
> * Γ₂, x ≡ v₂; s₂ ⊢ u₂ →= u₃
> Because the derivation `Γ₀, x ≡ v₀; s₀ ⊢ u₀ →= u₂` do not make any
> promotion of `x` to `v₀`, then the induction process ensures that
> the derivation `Γ₁, x ≡ v₁; s₁ ⊢ u₁ →= u₃` do not make any promotion
> of `x` to `v₁`."

Here the paper uses Moreover at **one specific `x`** (the body-fresh
binder), not for arbitrary `x`. And the source `u₀ →= u₂` is a
*weakening* of an outer derivation that doesn't mention `x` — the NP-x
of `u₀ →= u₂` at body-fresh x is free.

In the body recursion's ProVar case, when the body's `bvar 0` is
promoted on one side, the lifted reduction is `hArg₂` (the outer
operand reduction) weakened to body context. **At body-fresh slot 0,
this weakened hLifted has NP-0 trivially** (weakening doesn't introduce
Me-Pro on the new head's slot).

**This suggests the predicate could be re-formulated to track NP only
at "structurally protected" indices** (body-fresh slots whose lifted
reductions come from weakening), and the wall would not apply.

## Verdict C salvage path — recommended next dispatch

**Re-formulate `MoreoverDiamondGeneral`** to require NP-tracking only
at indices for which the source derivation's path through the context
evolution is Me-Pro-free. Specifically:

* Add a side condition on `MoreoverDiamondGeneral` that the evolution
  is "Me-Pro-free at index x" (or use a different surface — e.g.,
  track NP only at the body-fresh slot in body-context recursions).
* The downstream consumer `UniformEqDiamonds` requires Moreover only
  at `ctRefl/ctRefl`, where all NP indices are vacuously free.
* The bundle's recursive use (AppBet body IH) requires Moreover only
  at body-fresh index 0, and the relevant lifted reduction is a
  weakening, so NP-0 is free.

This re-formulation is **substantial architectural work** (the
predicate, all 14 cells, and the bundle recursion all need updating).
Roughly 6-10 dispatches per `Lemma_2_DiamondGeneral.lean`'s scale.

## Verdict C alternative — drop ProVar's reverse direction

Another path: drop the reverse-direction Moreover (`h₂.NP-x → d₁.NP-x`)
from `MoreoverDiamondGeneral`, keeping only the forward direction
(`h₁.NP-x → d₂.NP-x`). The paper's recursive use at AppBet's body IH
needs BOTH directions (the paper's hypothesis is on h₂, conclusion on
d₁), so this doesn't directly work — but a careful audit may show
that the BetApp side covers one direction and AppBet covers the other,
so a single-direction predicate plus a symmetry argument could suffice.

## What to do if Verdict C doesn't pan out

Before declaring Verdict B and emailing authors:

1. **Re-audit `equBinds_evolve` and `lift_empty_to_stack`** for any
   structural lemma the agent (and this dispatch) missed. The Lemma 32
   false alarm was rescued by `sub_to_equ_head_replace`; a similar
   rescue may exist for ProVar.
2. **Try a concrete Lean counterexample.** Construct a specific
   `Γ₀, s₀, i, α₀, α₁, he₂` where `hLifted.NoPromotionOf x` is FALSE
   for some specific `x` that the bundle's outer caller demands. If
   no counterexample can be constructed, the wall may be in the
   predicate, not the proof.
3. **Check whether the paper's own recursive use at AppBet/BetApp
   actually demands universal-x Moreover or just specific-x Moreover.**
   This dispatch's reading suggests specific-x, but a more careful
   audit is warranted.

## Files touched

None. This is a diagnostic report only. The two residual payloads
`MoreoverDiamondGeneral_ProVarVarPro_Payload` and
`MoreoverDiamondGeneral_VarPro_Payload` remain as the bundle's
explicit residuals in
`Pss/Paper/Lemma_2_DiamondGeneral.lean`.

## Cross-references

* `Pss/Paper/Lemma_2_DiamondGeneral.lean` — predicate + payload
  definitions, bundle assembly.
* `Pss/Paper/Lemma_2_DiamondClosure.lean:185-215` — same-context
  ProVar discharge (uses `equBinds_evolve` + `lift_empty_to_stack`
  WITHOUT Moreover tracking — works because non-Moreover diamond is
  weaker).
* `Pss/Paper/Aux/EvolutionTransport.lean:247` — `equBinds_evolve`'s
  ctAnn case, the structural site of the lifted reduction's Me-Pro
  inheritance.
* `Pss/Paper/Lemma_2_EqDiamondsWithMoreover.lean` — same-context
  Moreover formulation (different angle on the same problem;
  walled separately).
* Paper Lemma 2 statement: p. 9:9.
* Paper Lemma 2 proof appendix: p. 9:21-25.
* Paper recursive use of Moreover: p. 9:23 (Me-App × Me-Bet case).

## Lessons (in case this is also a false alarm)

If a future dispatch resolves this with a structural lemma (as Lemma 32
was resolved), this file should be archived/renamed with a "FALSE
ALARM" header per the `STOP-PAPER-BUG-LEMMA-32.md` template.
