import Pss.Mpss.WellFormed
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
  reference). The original LN-encoded `Lemma_1_*` / `Lemma_2_*` endpoints
  that survive the LN-cleanup. These remain in
  the audit so the Wf-inversion residuals
  (`Lemma_10_Inversion`, `Lemma_24_NarrowingMSubRed`,
  `Lemma_30_msPro_x_axiom`) remain visible
  in the audit during the de Bruijn refactor. The LN type-safety
  endpoints (`Theorem_4_Progress`, `Theorem_5_Preservation`,
  `Lemma_30_ReductionUnderSubst_Sub_noProOn`,
  `Lemma7.lf2_case_noProOn`, `Conjecture_8_*`) were retired together
  with `Pss/Mpss/TypeSafety.lean` during Phase B of the de Bruijn
  refactor (the de Bruijn `_proved` endpoints carry the proofs); the
  LN `Theorem_3_TransitivityIsAdmissible` endpoint was retired with
  `Pss/Mpss/TransitivityElim.lean` later in the same Phase B; the
  LN `Lemma_1_StrongCommutativity` endpoint was retired with
  `Pss/Mpss/Commutation.lean` (killing the
  `Lemma_1_ctx_axiom` and `Lemma_1_inline_app_bet_residual` axioms)
  later in the same Phase B; and the
  LN `Lemma_2_DiamondMEqRed` endpoint was retired with
  `Pss/Mpss/Diamond.lean` (killing the
  `Lemma_2_DiamondMEqRed_ctx_axiom`,
  `Lemma_2_inline_app_bet_residual_axiom`, and
  `Lemma_2_inline_bet_residual_axiom` axioms) later still in the same
  Phase B. With this last deletion all 5 of the original LN
  β-residual axioms are gone from the codebase. The
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
Their proofs consume only the Wf-inversion family
(`Lemma_10_Inversion`, `Lemma_24_NarrowingMSubRed`,
`Lemma_30_msPro_x_axiom`); the de Bruijn
`_proved` endpoints above carry the actual current proof status. The
LN type-safety endpoints (`Theorem_4_Progress`,
`Theorem_5_Preservation`, `Lemma_30_ReductionUnderSubst_Sub_noProOn`,
`Lemma7.lf2_case_noProOn`, `Conjecture_8_*`) were retired with
`Pss/Mpss/TypeSafety.lean` during Phase B of the de Bruijn refactor;
the LN `Lemma_1_StrongCommutativity` endpoint was retired with
`Pss/Mpss/Commutation.lean` (killing `Lemma_1_ctx_axiom` and
`Lemma_1_inline_app_bet_residual`) later in the same Phase B; the
LN `Lemma_2_DiamondMEqRed` endpoint was retired with
`Pss/Mpss/Diamond.lean` (killing the three
`Lemma_2_*` β-residual axioms) later still in the same Phase B,
removing the last of the original 5 LN β-residual axioms from the
codebase.
-/

#print axioms Lemma_10_InversionRestricted
#print axioms Lemma_32_AsymmetricEqu

end Pss
