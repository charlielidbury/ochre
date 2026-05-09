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

end Pss
