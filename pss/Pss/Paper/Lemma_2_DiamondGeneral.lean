import Pss.Mpss.DeBruijnTypeSafety
import Pss.Paper.Lemma_2_Diamond
import Pss.Paper.Lemma_2_DiamondClosure
import Pss.Paper.Lemma_2_NoPromotion
import Pss.Paper.Lemma_2_BundleProof
import Pss.Paper.Lemma_2_EqDiamondsWithMoreover
import Pss.Paper.Aux.EvolutionTransport
import Pss.Paper.Aux.CommutativityWeakening
import Pss.Paper.Investigation.Lemma_32_EquHead

/-! # `Pss.Paper.Lemma_2_DiamondGeneral` — paper Lemma 2's general-context
diamond, paper-faithful AppBet/BetApp inlines, and `UniformEqDiamonds`
closure.

This file ships the **general-context Moreover-tracked diamond** that
mirrors paper Lemma 2 (Pasquale & García-Pérez 2024, p. 9:9 statement;
proof p. 9:21-25):

> *Statement.* Let `Γ_0; s_0` be an extended context. Let `t_0, t_1, t_2`
> be terms. If `Γ_0; s_0 ⊢ t_0 →ᵉᵠᵘ t_1` and `Γ_0; s_0 ⊢ t_0 →ᵉᵠᵘ t_2`,
> then for any extended contexts `Γ_1; s_1` and `Γ_2; s_2` such that
> `Γ_0; s_0 ↣ Γ_1; s_1` and `Γ_0; s_0 ↣ Γ_2; s_2`, there exists a term
> `t_3` such that `Γ_1; s_1 ⊢ t_1 →ᵉᵠᵘ t_3` and `Γ_2; s_2 ⊢ t_2 →ᵉᵠᵘ t_3`.
>
> Moreover (paper p. 9:9), for any variable `x`, if in the derivation
> `t_0 → t_1` there isn't an application of `Me-Pro` that makes a
> promotion of `x`, then in the derivation `t_2 → t_3` there won't be
> an application of `Me-Pro` that makes a promotion of `x`
> (respectively, `t_0 → t_2`'s `NP-x` propagates to `t_1 → t_3`).

The diamond is captured as `MoreoverDiamondGeneral` (asymmetric crossed
Moreover, paper-faithful), and `UniformMoreoverDiamondGeneral` is the
universal closure. Projection theorems deliver the plain general-context
diamond and the same-context `UniformEqDiamonds`.

## Strategy

The diamond is proved by **structural induction on `h_1`** with
case-split on `h_2`, dispatching to per-cell discharges. The cross-β
cases (App×Bet, Bet×App) are **inlined paper-faithfully** using
`Lemma_32_EquHead_proved_closed` + `cons_evolve` for body context
evolution. Non-cross-β cells (TopTop, VarVar, TApTAp, ProPro, ProVar,
AppTAp, FunFun, FOpFOp, BetBet, AppApp) invoke the per-cell theorems in
`Pss.Paper.Lemma_2_DiamondClosure`.

## Status: Phase 1 — predicate definitions and trivial cells

This phase ships:
* `MoreoverDiamondGeneral` (the Moreover-tracked general-context
  predicate, asymmetric crossed form per paper p. 9:9).
* `UniformMoreoverDiamondGeneral` (universal closure target).
* Projection `MoreoverDiamondGeneral.toLemma_2_Diamond_Plain` (drops the
  Moreover witness).
* `UniformMoreoverDiamondGeneral.toUniformEqDiamonds` (specializes
  general-context to same-context via `ctRefl`, drops Moreover).
* Trivial-cell discharges (TopTop, VarVar, TApTAp).

Subsequent phases will ship the per-case dispatch, paper-faithful
AppBet/BetApp inlines, and the full bundle recursion.

No `sorry`. No new axioms.
-/

namespace Pss
namespace DeBruijn
namespace Paper

open Investigation

/-! ## Predicate definitions -/

/-- **Paper Lemma 2 conclusion with Moreover NP-tracking** (asymmetric
crossed form, paper p. 9:9).

Given two equivalence-reduction steps from a common source at `Γ_0; s_0`,
plus any two evolved extended contexts `Γ_1; s_1` and `Γ_2; s_2`, this
delivers a common reduct `t_3` joined by `MEqRed` derivations `d_1, d_2`
on both sides, plus the asymmetric Moreover witness: `h_i.NP-x` of
either source crosses to `d_j.NP-x` of the OTHER output (`i ≠ j`).

The asymmetric crossed form mirrors the paper text exactly: NP of
*one* input propagates to the *other* output (the diagonal direction
through the diamond). -/
def MoreoverDiamondGeneral
    {Γ₀ : Ctx} {s₀ : Stack} {t₀ t₁ t₂ : Term}
    (h₁ : MEqRed Γ₀ s₀ t₀ t₁) (h₂ : MEqRed Γ₀ s₀ t₀ t₂) : Prop :=
  ∀ {Γ₁ s₁ Γ₂ s₂ : _},
    ContextEvolution Γ₀ s₀ Γ₁ s₁ →
    ContextEvolution Γ₀ s₀ Γ₂ s₂ →
    ∃ (t₃ : Term) (d₁ : MEqRed Γ₁ s₁ t₁ t₃) (d₂ : MEqRed Γ₂ s₂ t₂ t₃),
      ∀ (x : Nat),
        (h₁.NoPromotionOf x → d₂.NoPromotionOf x) ∧
        (h₂.NoPromotionOf x → d₁.NoPromotionOf x)

/-- Universal closure of the general-context Moreover diamond at every
extended context, over every source pair. -/
def UniformMoreoverDiamondGeneral : Prop :=
  ∀ {Γ₀ : Ctx} {s₀ : Stack} {t₀ t₁ t₂ : Term}
    (h₁ : MEqRed Γ₀ s₀ t₀ t₁) (h₂ : MEqRed Γ₀ s₀ t₀ t₂),
    MoreoverDiamondGeneral h₁ h₂

/-! ## Projections -/

/-- Drop the Moreover NP witness from a general-context Moreover
diamond, yielding the plain general-context diamond conclusion
(`Lemma_2_DiamondMEqRed_Conclusion`). -/
theorem MoreoverDiamondGeneral.toLemma_2_DiamondMEqRed_Conclusion
    {Γ₀ : Ctx} {s₀ : Stack} {t₀ t₁ t₂ : Term}
    {h₁ : MEqRed Γ₀ s₀ t₀ t₁} {h₂ : MEqRed Γ₀ s₀ t₀ t₂}
    (h : MoreoverDiamondGeneral h₁ h₂) :
    Lemma_2_DiamondMEqRed_Conclusion h₁ h₂ := by
  intro Γ₁ s₁ Γ₂ s₂ he₁ he₂
  obtain ⟨t₃, d₁, d₂, _⟩ := h he₁ he₂
  exact ⟨t₃, ⟨d₁⟩, ⟨d₂⟩⟩

/-- The general-context Moreover diamond's universal closure specializes
to the same-context `UniformEqDiamonds` via `ctRefl/ctRefl`. -/
theorem UniformMoreoverDiamondGeneral.toUniformEqDiamonds
    (h : UniformMoreoverDiamondGeneral) : UniformEqDiamonds := by
  intro Γ s t₀ t₁ t₂ h₁ h₂
  obtain ⟨t₃, d₁, d₂, _⟩ :=
    (h h₁ h₂) ContextEvolution.ctRefl ContextEvolution.ctRefl
  exact ⟨t₃, ⟨d₁⟩, ⟨d₂⟩⟩

/-! ## Trivial-cell discharges

The trivial source-shape cases (Me-Top × Me-Top, Me-Var × Me-Var,
Me-TAp × Me-TAp) close immediately by reflexivity/transport, with
trivial Moreover witnesses (the outputs are themselves `MEqRed`
identities or transport-images that admit `NoPromotionOf x` for all
`x`).

These take only the `MEqRedTransportAcrossEvolution` payload, but since
the trivial sources never use `Me-Pro` (the outputs are `.top` or
`.bvar i`), the NP witness for the outputs is trivially `True`. -/

/-- Me-Top × Me-Top: source `.top`, both targets `.top`, output `.top`
on both evolved contexts. Moreover witness trivial since neither source
uses `Me-Pro`. -/
theorem MoreoverDiamondGeneral_top_top {Γ₀ : Ctx} {s₀ : Stack}
    (hpv : PrevalidExt Γ₀ s₀) :
    MoreoverDiamondGeneral (MEqRed.top hpv) (MEqRed.top hpv) := by
  intro Γ₁ s₁ Γ₂ s₂ he₁ he₂
  have hpv₁ : PrevalidExt Γ₁ s₁ :=
    Classical.choice (he₁.preservesNonemptyPrevalidExt ⟨hpv⟩)
  have hpv₂ : PrevalidExt Γ₂ s₂ :=
    Classical.choice (he₂.preservesNonemptyPrevalidExt ⟨hpv⟩)
  refine ⟨.top, MEqRed.top hpv₁, MEqRed.top hpv₂, ?_⟩
  intro x
  exact ⟨fun _ => trivial, fun _ => trivial⟩

/-- Me-Var × Me-Var: source `.bvar i`, both targets `.bvar i`, output
`.bvar i` on both evolved contexts. Moreover trivial. -/
theorem MoreoverDiamondGeneral_var_var {Γ₀ : Ctx} {s₀ : Stack} {i : Nat}
    (hpv : PrevalidExt Γ₀ s₀) (hi : i < Γ₀.depth) :
    MoreoverDiamondGeneral (MEqRed.var hpv hi) (MEqRed.var hpv hi) := by
  intro Γ₁ s₁ Γ₂ s₂ he₁ he₂
  have hpv₁ : PrevalidExt Γ₁ s₁ :=
    Classical.choice (he₁.preservesNonemptyPrevalidExt ⟨hpv⟩)
  have hpv₂ : PrevalidExt Γ₂ s₂ :=
    Classical.choice (he₂.preservesNonemptyPrevalidExt ⟨hpv⟩)
  have hdepth₁ : Γ₀.depth = Γ₁.depth := he₁.preserves_ctx_depth
  have hdepth₂ : Γ₀.depth = Γ₂.depth := he₂.preserves_ctx_depth
  have hi₁ : i < Γ₁.depth := by rw [← hdepth₁]; exact hi
  have hi₂ : i < Γ₂.depth := by rw [← hdepth₂]; exact hi
  refine ⟨.bvar i, MEqRed.var hpv₁ hi₁, MEqRed.var hpv₂ hi₂, ?_⟩
  intro x
  exact ⟨fun _ => trivial, fun _ => trivial⟩

/-- Me-TAp × Me-TAp: source `.app .top u`, both targets `.top`, output
`.top` on both evolved contexts. Moreover trivial. -/
theorem MoreoverDiamondGeneral_tAp_tAp {Γ₀ : Ctx} {s₀ : Stack} {u : Term}
    (hpv : PrevalidExt Γ₀ s₀) (hu : Term.Scoped Γ₀.depth u) :
    MoreoverDiamondGeneral (MEqRed.tAp hpv hu) (MEqRed.tAp hpv hu) := by
  intro Γ₁ s₁ Γ₂ s₂ he₁ he₂
  have hpv₁ : PrevalidExt Γ₁ s₁ :=
    Classical.choice (he₁.preservesNonemptyPrevalidExt ⟨hpv⟩)
  have hpv₂ : PrevalidExt Γ₂ s₂ :=
    Classical.choice (he₂.preservesNonemptyPrevalidExt ⟨hpv⟩)
  refine ⟨.top, MEqRed.top hpv₁, MEqRed.top hpv₂, ?_⟩
  intro x
  exact ⟨fun _ => trivial, fun _ => trivial⟩

end Paper
end DeBruijn
end Pss
