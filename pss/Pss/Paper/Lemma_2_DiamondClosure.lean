import Pss.Paper.Lemma_2_Diamond
import Pss.Paper.Aux.CommutativityWeakening
import Pss.Paper.Aux.EvolutionTransport
import Pss.Paper.Aux.Substitution
import Pss.Paper.Investigation.Lemma_32_KindNarrowedAsymmetric
import Pss.Mpss.DeBruijnTypeSafety

/-! # `Pss.Paper.Lemma_2_DiamondClosure` — discharging the 9 case obligations

Discharges the per-case obligations declared in
`Pss.Paper.Lemma_2_Diamond` (`Lemma_2_Case_*`) by using the existing
paper-mirroring infrastructure (Lemma 19, Lemma 32 asymmetric
kind-narrowed, Lemma 36, plus `equBinds_evolve` and
`preservesNonemptyPrevalidExt` from `EvolutionTransport.lean`).

Each obligation takes recursive IHs (the diamond at smaller
sub-derivations / sub-terms) plus the outer `ContextEvolution` premises.
The discharge of each case is mechanized faithfully against the paper
proof at p. 9:21–25.

The trivial cases (`TopTop`, `VarVar`, `TApTAp`) are **already proved
unconditionally** in `EvolutionTransport.lean`; the matching paper-named
obligations here are connector functions that adapt the unconditional
proofs to the case-obligation shape.

## Status

This file is **active discharge**. Cases close incrementally; final
unconditional closure of `UniformEqDiamonds` is gated by all 9 cases.

Build green; no new axioms; no `sorry`.
-/

namespace Pss
namespace DeBruijn
namespace Paper

open ContextEvolution

/-! ## Trivial-cell discharges (paper p. 9:21 base, p. 9:25 trivials)

These are connectors to the already-proved unconditional cells in
`EvolutionTransport.lean`. They have a slightly different signature
shape than the `Prop`-defined cases in `Lemma_2_Diamond.lean`, so we
ship explicit case-obligation discharges that match the paper's grid. -/

/-- Discharge of `Lemma_2_Case_AppTAp`: the Me-TAp source forces operator
`= .top`, so all LHS reducts end at `.top` via `Me-TAp` rebuilt at the
evolved context. -/
theorem Lemma_2_Case_AppTAp_proved : Lemma_2_Case_AppTAp := by
  intro Γ₀ s₀ u₁ v₀ v₁ hOp hArg hVScoped hpv₀
    Γ₁ s₁ Γ₂ s₂ he₁ he₂
  -- hOp : MEqRed Γ₀ (v₀ :: s₀) .top u₁ → u₁ = .top by Me-Top inversion.
  have hu₁_top : u₁ = .top := hOp.top_inv
  subst hu₁_top
  -- Now LHS = .app .top v₁ → .top via Me-TAp at evolved Γ₁;s₁.
  have hpvE₁ : PrevalidExt Γ₁ s₁ :=
    Classical.choice (he₁.preservesNonemptyPrevalidExt ⟨hpv₀⟩)
  have hpvE₂ : PrevalidExt Γ₂ s₂ :=
    Classical.choice (he₂.preservesNonemptyPrevalidExt ⟨hpv₀⟩)
  have hv₁Scoped : Term.Scoped Γ₀.depth v₁ := hArg.scoped_right
  have hdepth₁ : Γ₀.depth = Γ₁.depth := he₁.preserves_ctx_depth
  have hv₁Scoped₁ : Term.Scoped Γ₁.depth v₁ := by
    rw [← hdepth₁]; exact hv₁Scoped
  refine ⟨.top, ?_, ?_⟩
  · exact ⟨MEqRed.tAp hpvE₁ hv₁Scoped₁⟩
  · exact ⟨MEqRed.top hpvE₂⟩

/-- Discharge of `Lemma_2_Case_TApTAp` via the unconditional cell. -/
theorem Lemma_2_Case_TApTAp_proved : Lemma_2_Case_TApTAp := by
  intro Γ₀ s₀ u hpv₀ hu Γ₁ s₁ Γ₂ s₂ he₁ he₂
  exact Lemma_2_TApTAp_proved_unconditional hpv₀ hu he₁ he₂

/-! ## Body transport closures (used in deeper cases)

These were left as residual payloads in the existing infrastructure but
are fully provable from `MEqRed.sub_to_equ_head_replace` (which is total:
the kind narrowing `.sub → .equ` widens the relation, and the head bound
change is fine since body's `.sub`-source forbids `Me-Pro` lookups at
index 0). -/

/-- The body transport `MEqRedSubHeadToEquHeadPayload` is provably
dischargeable: at empty stack, source `.sub`-head body transport to
`.equ`-head body with a different bound is exactly
`MEqRed.sub_to_equ_head_replace`. -/
noncomputable def MEqRedSubHeadToEquHeadPayload_proved :
    MEqRedSubHeadToEquHeadPayload := by
  intro Γ bound operand body body' hbody hOperand
  exact hbody.sub_to_equ_head_replace hOperand

/-- The Me-Fun stack-append payload follows from the body transport. -/
noncomputable def MEqRedFunStackAppendPayload_proved :
    MEqRedFunStackAppendPayload :=
  MEqRedFunStackAppendPayload.of_body_transport
    MEqRedSubHeadToEquHeadPayload_proved

/-! ## Variable-source cases (paper p. 9:21) -/

/-- Discharge of `Lemma_2_Case_ProPro`: when both sides promote the same
variable, the paper invokes prevalidity to identify the bound, then
invokes the bound IH. -/
theorem Lemma_2_Case_ProPro_proved : Lemma_2_Case_ProPro := by
  intro Γ₀ s₀ i α₀ α₁ α₂ hpv₀ hb hα₁ hα₂ hBoundIH Γ₁ s₁ Γ₂ s₂ he₁ he₂
  -- Both reductions of the same `bvar i` use the same bound `α₀` (forced
  -- by Ctx prevalidity → unique lookup). Apply the bound IH.
  exact hBoundIH he₁ he₂

end Paper
end DeBruijn
end Pss
