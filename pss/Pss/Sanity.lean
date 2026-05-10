import Pss.Mpss.DeBruijnTypeSafety
import Pss.Paper.Aux.CommutativityWeakening
import Pss.Paper.Aux.Congruence
import Pss.Paper.Aux.EvolutionTransport
import Pss.Paper.Aux.PrevalidityUnderSubst
import Pss.Paper.Aux.Propositions
import Pss.Paper.Aux.Substitution
import Pss.Paper.Aux.Weakening
import Pss.Paper.Lemma_2_Diamond

/-! # `Pss.Sanity` — `#print axioms` audit

Pure audit module. Lists the axiom dependencies of the headline
theorems so reviewers can verify (a) which paper-level axioms each
theorem depends on, and (b) that no stray Lean axioms have crept in.

The expected baseline for every theorem is the standard three:
`propext`, `Quot.sound`, `Classical.choice`. Plus the paper-level
axioms documented in `AXIOMS.md`.

## Audit layer — De Bruijn primary headlines

The `_proved` endpoints in `Pss/Mpss/DeBruijnTypeSafety.lean`. Each
depends only on kernel axioms (`propext`, `Quot.sound`,
`Classical.choice`) plus named Prop / Type residual hypotheses
(`UniformStrongCommutes`, `UniformEqDiamonds`,
`BetaInstantiationPreservesWfM`, `AbsFunctionBoundInversion`,
`WfMSubHeadReplaceOfNewWf`) which represent the open
transitivity-elimination + paper-conjecture problems and are
documented as Prop residuals, NOT custom axioms. These are the
endpoints reviewers should consult for the actual current proof
status of the headline theorems.

The locally-nameless audit layer (`Lemma_10_InversionRestricted` and
`Lemma_32_AsymmetricEqu`) was retired together with the LN
`WellFormed.lean` and `AvoidsPro.lean` modules during Phase B of the
de Bruijn refactor; the de Bruijn `_proved` endpoints below carry the
actual current proof status. With those deletions all of the original
LN β-residual axioms (`Lemma_1_*`, `Lemma_2_*`,
`Lemma_10_InversionRestricted`, `Lemma_32_AsymmetricEqu`) are gone
from the codebase.
-/

namespace Pss

/-! ## De Bruijn primary headlines (the actual proven endpoints)

These are the `_proved` wrappers shipped to
`Pss/Mpss/DeBruijnTypeSafety.lean`. Each depends only on kernel axioms
+ named Prop / Type residual hypotheses
(`UniformEqDiamonds`, `UniformStrongCommutes`,
`BetaInstantiationPreservesWfM`, `AbsFunctionBoundInversion`,
`WfMSubHeadReplaceOfNewWf`, plus `MEqRedArgTransportPayload` /
`MEqRedOpStackHeadTransportPayload` / `MEqRedSubBridgePayload` for the
diamond closures) which represent the open transitivity-elimination +
paper-conjecture problems and are documented as Prop / Type residuals,
NOT custom axioms.
-/

#print axioms Pss.DeBruijn.Lemma_1_DeBruijn_StrongCommutativityStar_proved
#print axioms Pss.DeBruijn.Lemma_1_DeBruijn_StrongCommutativityChain_proved
#print axioms Pss.DeBruijn.Lemma_2_DeBruijn_DiamondMEqRedStar_proved
#print axioms Pss.DeBruijn.Lemma_2_DeBruijn_DiamondMEqRedChain_proved
#print axioms Pss.DeBruijn.Theorem_3_DeBruijn_TransitivityIsAdmissible_proved
#print axioms Pss.DeBruijn.Theorem_4_DeBruijn_Progress_proved
#print axioms Pss.DeBruijn.Theorem_5_DeBruijn_Preservation_proved
#print axioms Pss.DeBruijn.Theorem_5_DeBruijn_ClosedPreservation_proved

/-! ### v4 partial surface

The v4 partial surface absorbs the universal-Γ NoBinders-restricted
bet residual `hBetNoBindersResidual` via `hBetNoBindersResidual_of_wsubmstar`.
Surface arity drops by one parameter relative to v3; the remaining
`hNoBindersAtBet` is still exposed as a hypothesis. -/

#print axioms Pss.DeBruijn.Theorem_5_DeBruijn_Preservation_partial_v4_proved
#print axioms Pss.DeBruijn.Theorem_5_DeBruijn_ClosedPreservation_partial_v4_proved

/-! ### v5 partial surface

The v5 partial surface absorbs v4's universal-shape `hNoBindersAtBet`
premise (false in general) by switching to a concrete outer-source
`hSourceNoBinders : Term.NoBinders t` premise. Under that invariant,
the operational reduction path is fully discharged without recourse to
the chain-shape inversion pipeline: every Step from a `NoBinders`
source either propagates `NoBinders` to a subterm (`appL`/`appR`) or
is structurally absurd (`beta`/`absBound`/`absBody`).

The supporting `_aux_NoBinders` recursion structure demonstrates the
parallel collapse on the `MEqRed` side: bet/fun_/fOp/var/pro arms are
all absurd via case-elim on `Term.NoBinders`, leaving only top/tAp/app
— discharged with `hOpFun` alone (no `hFunBound`, no `h_bet`). -/

#print axioms Pss.DeBruijn.Theorem_5_DeBruijn_Preservation_partial_v5_proved
#print axioms Pss.DeBruijn.Theorem_5_DeBruijn_ClosedPreservation_partial_v5_proved

-- Theorem 5 partial v6: drops the v5 typed-payload premises that were
-- retained for closure-tracking parity. v6's surface needs only the outer
-- `WfCtxEqu Γ` and the source `Term.NoBinders` premise. The closed-term
-- v6 discharges WfCtxEqu via `WfCtxEqu.empty`, leaving `hSourceNoBinders`
-- as the sole non-standard premise. Both depend only on the kernel three.
#print axioms Pss.DeBruijn.Theorem_5_DeBruijn_Preservation_partial_v6_proved
#print axioms Pss.DeBruijn.Theorem_5_DeBruijn_ClosedPreservation_partial_v6_proved

/-! ### Paper-mirroring layer

These are the `Pss.Paper.*` artifacts established as the paper-faithful
counterpart to the existing de Bruijn working development. The numbers
match the paper (Pasquale & García-Pérez 2024). -/

#print axioms
  Pss.DeBruijn.Paper.ContextEvolution.Lemma_36_CommutativityContextWeakening

#print axioms Pss.DeBruijn.Paper.Lemma_19_Weakening.proved
#print axioms Pss.DeBruijn.Paper.Lemma_20_Weakening_Aux.proved
#print axioms Pss.DeBruijn.Paper.Lemma_21_Weakening_SubtypingReduction
#print axioms Pss.DeBruijn.Paper.Lemma_22_Weakening_EquivalenceReduction

-- Paper Lemma 28 (Substitution preserves prevalidity), p. 9:40.
#print axioms
  Pss.DeBruijn.Paper.Lemma_28_SubstitutionPreservesPrevalidity_extended
#print axioms
  Pss.DeBruijn.Paper.Lemma_28_SubstitutionPreservesPrevalidity_logical

#print axioms Pss.DeBruijn.Paper.Lemma_31_ReductionUnderSubstitution
#print axioms Pss.DeBruijn.Paper.Lemma_31_ReductionUnderSubstitution_J
#print axioms
  Pss.DeBruijn.Paper.Lemma_32_ReductionUnderSubstitution_AuxForCommutation
#print axioms
  Pss.DeBruijn.Paper.Lemma_32_ReductionUnderSubstitution_AuxForCommutation_J
-- Paper-faithful asymmetric form of Lemma 32 (LHS by `arg`, RHS by `arg'`).
-- Discharged via `MEqRedStackExtensionWall_proved`; see
-- `Pss/Paper/Investigation/Lemma_32_Asymmetric.lean`.
#print axioms
  Pss.DeBruijn.Paper.Lemma_32_ReductionUnderSubstitution_AuxForCommutation_Asymmetric
#print axioms
  Pss.DeBruijn.Paper.Lemma_32_ReductionUnderSubstitution_AuxForCommutation_Asymmetric_J
#print axioms
  Pss.DeBruijn.Paper.Investigation.MEqRedStackExtensionWall_proved
#print axioms
  Pss.DeBruijn.Paper.Investigation.Lemma_32_Asymmetric_proved
#print axioms
  Pss.DeBruijn.Paper.Investigation.Lemma_32_Asymmetric_proved_closed

-- Paper Theorem 11 (No supertype of `Top` is a function), p. 9:31. Conditional
-- on `StrongCommutes` (de Bruijn analogue of Theorem 3 at the empty stack).
#print axioms Pss.DeBruijn.Paper.Theorem_11_NoTopAbstractionSupertypes_of
#print axioms Pss.DeBruijn.Paper.Theorem_11_NoTopFunctionSupertypes_of
#print axioms Pss.DeBruijn.Paper.Theorem_11_NoTopFunctionSupertypes_closed_of

-- Paper Proposition 12 (Well-formedness extraction), p. 9:32.
#print axioms Pss.DeBruijn.Paper.Proposition_12_WfMExtraction_left
#print axioms Pss.DeBruijn.Paper.Proposition_12_WfMExtraction_right
#print axioms Pss.DeBruijn.Paper.Proposition_12_WfMExtraction

-- Paper Proposition 13 (From well-subtyping to subtyping), p. 9:32.
#print axioms Pss.DeBruijn.Paper.Proposition_13_FromWellSubtypingToSubtyping
#print axioms
  Pss.DeBruijn.Paper.Proposition_13_FromWellSubtypingToSubtyping_star

-- Paper Proposition 14 (From well-equivalence to equivalence), p. 9:32.
#print axioms
  Pss.DeBruijn.Paper.Proposition_14_FromWellEquivalenceToEquivalence
#print axioms
  Pss.DeBruijn.Paper.Proposition_14_FromWellEquivalenceToEquivalence_star

-- Paper Lemma 15 (Symmetry of `≡_wf`), p. 9:33.
#print axioms Pss.DeBruijn.Paper.Lemma_15_WEquMSymmetry
#print axioms Pss.DeBruijn.Paper.Lemma_15_WEquMSymmetry_star

-- Paper Lemma 16 (`≡_wf` ⊆ `≤_wf`), p. 9:33.
#print axioms Pss.DeBruijn.Paper.Lemma_16_WEquMToWSubM
#print axioms Pss.DeBruijn.Paper.Lemma_16_WEquMToWSubM_star

-- Paper Proposition 17 (From reduction semantics to equivalence reduction),
-- p. 9:33. Unconditional in de Bruijn (the LN `Proposition_17_beta_axiom` is
-- retired).
#print axioms
  Pss.DeBruijn.Paper.Proposition_17_FromReductionToEquivalenceReduction
#print axioms
  Pss.DeBruijn.Paper.Proposition_17_FromReductionToEquivalenceReduction_closed
#print axioms
  Pss.DeBruijn.Paper.Proposition_17_FromReductionToEquivalenceReduction_J

-- Paper Proposition 18 (Reflexivity of equivalence reduction), p. 9:33.
#print axioms Pss.DeBruijn.Paper.Proposition_18_MEqRedReflexivity
#print axioms Pss.DeBruijn.Paper.Proposition_18_MSubRedReflexivity
#print axioms Pss.DeBruijn.Paper.Proposition_18_MEqRedReflexivity_J
#print axioms Pss.DeBruijn.Paper.Proposition_18_MSubRedReflexivity_J

-- Paper Lemma 33 (Congruence of `≤`), p. 9:45. Six conjuncts (single-step
-- and chain variants for app, fun, fOp shapes).
#print axioms Pss.DeBruijn.Paper.Lemma_33_Congruence_MSub.proved

-- Paper Lemma 34 (Congruence of `↦ˢᵘᵇ`), p. 9:45–46. Three conjuncts
-- (app/fun/fOp). Dispatches to the single-step `MSubRedStar` lifters in
-- `Pss/Mpss/DeBruijnReductions.lean`.
#print axioms Pss.DeBruijn.Paper.Lemma_34_Congruence_MSubRedStar.proved

-- Paper Lemma 35 (Congruence of `↦ᵉᵠᵘ`), p. 9:46. Three conjuncts. The
-- equivalence-side chain lifters are introduced in this file (no prior
-- `MEqRedStar.app_*`/`fun_*`/`fOp_*` siblings existed in the working
-- development).
#print axioms Pss.DeBruijn.Paper.Lemma_35_Congruence_MEqRedStar.proved

-- Paper Lemma 2 (Diamond property of `→ᵉᵠᵘ`), p. 9:9 statement / p. 9:21–25
-- proof. Trivial-source-shape cells (Top × Top, Var × Var, TAp × TAp) close
-- conditionally on `MEqRedTransportAcrossEvolution` (the de Bruijn analogue of
-- paper Lemma 19's `↣` invocation pattern). The non-trivial cases are exposed
-- as named per-case obligations bundled in `Lemma_2_CaseGrid`. See file
-- `Pss/Paper/Lemma_2_Diamond.lean` and `STOP-LEMMA-2-STRUCTURAL.md` for the
-- dispatch sequence to discharge each.
#print axioms Pss.DeBruijn.Paper.Lemma_2_TopTop_proved
#print axioms Pss.DeBruijn.Paper.Lemma_2_VarVar_proved
#print axioms Pss.DeBruijn.Paper.Lemma_2_TApTAp_proved

-- Paper Lemma 2 trivial cells, UNCONDITIONAL discharge. The original
-- `MEqRedTransportAcrossEvolution` auxiliary that wrapped these cells was
-- shown to be structurally circular (its Me-Pro case requires diamond
-- itself); see `Pss/Paper/Aux/EvolutionTransport.lean` docstring. The
-- unconditional cells use only `ContextEvolution.preservesNonemptyPrevalidExt`
-- and `preserves_ctx_depth`.
#print axioms Pss.DeBruijn.Paper.ContextEvolution.preservesNonemptyPrevalid
#print axioms Pss.DeBruijn.Paper.ContextEvolution.preservesNonemptyPrevalidExt
#print axioms Pss.DeBruijn.Paper.Lemma_2_TopTop_proved_unconditional
#print axioms Pss.DeBruijn.Paper.Lemma_2_VarVar_proved_unconditional
#print axioms Pss.DeBruijn.Paper.Lemma_2_TApTAp_proved_unconditional

end Pss
