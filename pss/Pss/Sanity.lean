import Pss.Mpss.DeBruijnTypeSafety

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

end Pss
