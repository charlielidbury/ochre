import Pss.Mpss.TransitivityElim
import Pss.Mpss.SubstitutionNoPro
import Pss.Mpss.AvoidsPro
import Pss.Mpss.DeBruijnTypeSafety

/-! # `Pss.Sanity` — `#print axioms` audit

Pure audit module. Lists the axiom dependencies of the headline
theorems so reviewers can verify (a) which paper-level axioms each
theorem depends on, and (b) that no stray Lean axioms have crept in.

The expected baseline for every theorem is the standard three:
`propext`, `Quot.sound`, `Classical.choice`. Plus the paper-level
axioms documented in `AXIOMS.md`.

## Audit layers

This module audits the axiom dependencies in two layers:

* **De Bruijn primary headlines** (PRIMARY, post-iter pss-20260506-*).
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

* **Locally-nameless headlines** (DOCUMENTATION-ONLY / paper-faithfulness
  reference). The original LN-encoded `Theorem_3_*` / `Lemma_1_*` /
  `Lemma_2_*` endpoints that survive the LN-cleanup. These remain in
  the audit so the LN-side residual cluster
  (`Lemma_1_ctx_axiom`, `Lemma_1_inline_app_bet_residual`,
  `Lemma_2_DiamondMEqRed_ctx_axiom`,
  `Lemma_2_inline_app_bet_residual_axiom`,
  `Lemma_2_inline_bet_residual_axiom`) and the Wf-inversion residuals
  (`Lemma_10_Inversion`, `Lemma_24_NarrowingMSubRed`,
  `Lemma_30_msPro_x_axiom`) remain visible
  in the audit during the de Bruijn refactor. The LN type-safety
  endpoints (`Theorem_4_Progress`, `Theorem_5_Preservation`,
  `Lemma_30_ReductionUnderSubst_Sub_noProOn`,
  `Lemma7.lf2_case_noProOn`, `Conjecture_8_*`) were retired together
  with `Pss/Mpss/TypeSafety.lean` during Phase B of the de Bruijn
  refactor (the de Bruijn `_proved` endpoints carry the proofs). The
  remaining LN endpoints are retained as paper-faithful textual
  statements alongside the de Bruijn endpoints above.
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

/-! ## Locally-nameless headlines (documentation-only / paper-faithful)

The remaining LN-side endpoints are retained as a paper-faithfulness
reference (textual statements match Pasquale & García-Pérez 2024).
Their proofs still consume the LN β-residual axioms
(`Lemma_1_ctx_axiom`, `Lemma_1_inline_app_bet_residual`,
`Lemma_2_DiamondMEqRed_ctx_axiom`,
`Lemma_2_inline_app_bet_residual_axiom`,
`Lemma_2_inline_bet_residual_axiom`) and the Wf-inversion family
(`Lemma_10_Inversion`, `Lemma_24_NarrowingMSubRed`,
`Lemma_30_msPro_x_axiom`); the de Bruijn
`_proved` endpoints above carry the actual current proof status. The
LN type-safety endpoints (`Theorem_4_Progress`,
`Theorem_5_Preservation`, `Lemma_30_ReductionUnderSubst_Sub_noProOn`,
`Lemma7.lf2_case_noProOn`, `Conjecture_8_*`) were retired with
`Pss/Mpss/TypeSafety.lean` during Phase B of the de Bruijn refactor.
-/

#print axioms Theorem_3_TransitivityIsAdmissible
#print axioms Lemma_1_StrongCommutativity
#print axioms Lemma_2_DiamondMEqRed
#print axioms Lemma_10_InversionRestricted
#print axioms Lemma_32_AsymmetricEqu

end Pss
