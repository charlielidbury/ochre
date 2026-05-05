import Pss.Mpss.DeBruijnTypeSafety

/-! # `Pss.DeBruijnSanity` — de Bruijn `#print axioms` audit

This audit module tracks the new de Bruijn endpoints separately from
`Pss.Sanity`, which still reports the locally-nameless headline closures until
the branch switches over atomically.
-/

namespace Pss
namespace DeBruijn

#print axioms Lemma_2_DeBruijn_DiamondMEqRedStar_of
#print axioms Lemma_2_DeBruijn_DiamondMEqRedChain_of
#print axioms Lemma_1_DeBruijn_StrongCommutativityStar_of
#print axioms Lemma_1_DeBruijn_StrongCommutativityChain_of
#print axioms Theorem_3_DeBruijn_TransitivityIsAdmissible_of
#print axioms Theorem_4_DeBruijn_Progress_of_StrongCommutativity
#print axioms Theorem_5_DeBruijn_ClosedPreservation_of
#print axioms Theorem_5_DeBruijn_ClosedPreservation_of_components
#print axioms Theorem_5_DeBruijn_ClosedPreservation_of_diagram_components
#print axioms Theorem_5_DeBruijn_ClosedPreservation_of_chain_diagram_components
#print axioms Theorem_5_DeBruijn_ClosedPreservation_of_chain_shape_components
#print axioms Theorem_5_DeBruijn_ClosedPreservation_of_chain_shape_meq_components

end DeBruijn
end Pss
