import Pss.Mpss.DeBruijnTypeSafety
import Pss.Paper.Aux.CommutativityWeakening
import Pss.Paper.Aux.Congruence
import Pss.Paper.Aux.EvolutionTransport
import Pss.Paper.Aux.Narrowing
import Pss.Paper.Aux.PrevalidityUnderSubst
import Pss.Paper.Aux.PromotionUnderSubst
import Pss.Paper.Aux.Propositions
import Pss.Paper.Aux.Substitution
import Pss.Paper.Aux.Weakening
import Pss.Paper.Conjecture8
import Pss.Paper.Investigation.Lemma_32_KindNarrowedAsymmetric
import Pss.Paper.Lemma_2_Diamond
import Pss.Paper.Lemma_7_SubstPreservesWfM

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

-- Paper Lemma 29 (Promotion under substitution outside of covariant
-- contexts), p. 9:41–42. Direct constructor recursion on `Co`.
#print axioms Pss.DeBruijn.Paper.Lemma_29_PromotionUnderSubst_OutsideCovariant
#print axioms
  Pss.DeBruijn.Paper.Lemma_29_PromotionUnderSubst_OutsideCovariant_closed
#print axioms
  Pss.DeBruijn.Paper.Lemma_29_PromotionUnderSubst_OutsideCovariant_J

-- Paper Lemma 30 (Promotion under substitution inside of covariant
-- contexts), p. 9:42–43. Closed-prefix form; conditional on the
-- `MSubStarStackAppendPayload` residual (the codebase's Ms-Pro head
-- bridge for substitution preservation). The conclusion targets
-- `MSubStar` (chain) rather than the paper's single `→ˢᵘᵇ`; see file
-- docstring for the rationale.
#print axioms Pss.DeBruijn.Paper.Lemma_30_PromotionUnderSubst_InsideCovariant
#print axioms
  Pss.DeBruijn.Paper.Lemma_30_PromotionUnderSubst_InsideCovariant_nilStack

-- Paper Lemma 9 covariant-context branch (paper p. 9:31): combines
-- Lemma 29 with Conjecture 8 to bridge `→ˢᵘᵇ` to `≤*_wf`. Surfaces
-- Conjecture 8 in `#print axioms`.
#print axioms Pss.DeBruijn.Paper.Lemma_9_Bridge_via_Conjecture8

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

-- Paper Lemma 23 (Narrowing of context in well-formedness), p. 9:37–38.
-- Conditional on `WfMSubHeadReplaceOfNewWf` (residual; see file docstring).
#print axioms Pss.DeBruijn.Paper.Lemma_23_Narrowing_WfM_of
#print axioms Pss.DeBruijn.Paper.Lemma_23_Narrowing_WfM_under_of

-- Paper Lemma 24 (Narrowing of context in subtyping reductions), p. 9:38–39.
-- Closed unconditionally modulo caller-supplied paper-faithful payloads
-- (changed-slot Ms-Pro bridge, recursive Ms-Fun/Ms-FOp body cases).
#print axioms Pss.DeBruijn.Paper.Lemma_24_Narrowing_MSubRed
#print axioms Pss.DeBruijn.Paper.Lemma_24_Narrowing_MSubRed_general

-- Paper Lemma 25 (Narrowing of context in equivalence reductions), p. 9:39.
-- Direct match: `MEqRed.sub_head_replace` is `Lemma_25_Narrowing_MEqRed`.
#print axioms Pss.DeBruijn.Paper.Lemma_25_Narrowing_MEqRed
#print axioms Pss.DeBruijn.Paper.Lemma_25_Narrowing_MEqRed_star
#print axioms Pss.DeBruijn.Paper.Lemma_25_Narrowing_MEqRed_general
#print axioms Pss.DeBruijn.Paper.Lemma_25_Narrowing_MEqRed_J

-- Paper Lemma 26 (Narrowing prevalidity), p. 9:39–41. Direct match:
-- `Prevalid.sub_head_replace` is the head form.
#print axioms Pss.DeBruijn.Paper.Lemma_26_Narrowing_Prevalidity_sub
#print axioms Pss.DeBruijn.Paper.Lemma_26_Narrowing_Prevalidity_equ
#print axioms Pss.DeBruijn.Paper.Lemma_26_Narrowing_Prevalidity
#print axioms Pss.DeBruijn.Paper.Lemma_26_Narrowing_Prevalidity_general

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

-- Conjecture 8 (paper p. 9:13). Open in the paper. Surfaces in the
-- `#print axioms` of any theorem that depends on it.
#print axioms Pss.DeBruijn.Paper.Conjecture_8_WellSubtypingContextIndependent

-- Paper Lemma 7 (Substitution preserves well-formedness), p. 9:12 statement;
-- proof p. 9:27–30. Paper-faithful aliased entry of the de Bruijn
-- `BetaInstantiationPreservesWfM` Type. The closed discharge requires the
-- multi-page Wf-App sub-induction (paper p. 9:28–30) which depends on
-- Conjecture 8 via Lemma 9; that discharge is a campaign-level open
-- obligation. The `_proved` form below takes
-- `BetaInstantiationPreservesWfM` as a hypothesis (the same residual
-- consumed by `Theorem_5_DeBruijn_Preservation_proved`), so Lemma 7 inherits
-- exactly the residual surface of the underlying Type. The `_top`, `_var`,
-- `_fun` specialisations are closed (kernel three only); `_app` consumes
-- only the chain-substitution residual `BetaInstantiationPreservesWSubMStar`.
#print axioms Pss.DeBruijn.Paper.Lemma_7_SubstitutionPreservesWfM_proved
#print axioms Pss.DeBruijn.Paper.Lemma_7_SubstitutionPreservesWfM_top
#print axioms Pss.DeBruijn.Paper.Lemma_7_SubstitutionPreservesWfM_var
#print axioms Pss.DeBruijn.Paper.Lemma_7_SubstitutionPreservesWfM_fun
#print axioms Pss.DeBruijn.Paper.Lemma_7_SubstitutionPreservesWfM_app
#print axioms
  Pss.DeBruijn.Paper.Lemma_7_SubstitutionPreservesWfM_eq_BetaInstantiationPreservesWfM

-- Kind-narrowed asymmetric Lemma 32. Combines the decoupling of the
-- symmetric kind-narrowed `MEqRedFusedKindNarrowedBetaSubstStack_proved`
-- with the asymmetric LHS/RHS substitutions of
-- `Lemma_32_Asymmetric_proved`. Source's `.sub` head bound `t` is
-- decoupled from the LHS substitution arg `arg`. This is the lemma
-- consumed by Lemma 2's bet × bet, app × bet, bet × app cells for
-- single-step output.
#print axioms Pss.DeBruijn.Paper.Investigation.Lemma_32_KindNarrowedAsymmetric_proved
#print axioms Pss.DeBruijn.Paper.Investigation.Lemma_32_KindNarrowedAsymmetric_proved_closed

-- equBinds preservation across ContextEvolution. Unblocks paper Lemma 2's
-- Me-Pro × Me-Var case (paper p. 9:21): given Γ ↣ Γ' and Γ.equBinds i α₀,
-- finds the new bound α₂ in Γ' and a reduction `α₀ →ᵉᵠᵘ α₂` at Γ; [].
#print axioms Pss.DeBruijn.Paper.ContextEvolution.equBinds_evolve

end Pss
