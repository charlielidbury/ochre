import Pss.Mpss.TypeSafety
import Pss.Mpss.TransitivityElim

/-! # `Pss.Sanity` — `#print axioms` audit

Pure audit module. Lists the axiom dependencies of the headline
theorems so reviewers can verify (a) which paper-level axioms each
theorem depends on, and (b) that no stray Lean axioms have crept in.

The expected baseline for every theorem is the standard three:
`propext`, `Quot.sound`, `Classical.choice`. Plus the paper-level
axioms documented in `AXIOMS.md`.
-/

namespace Pss

#print axioms Theorem_3_TransitivityIsAdmissible
#print axioms Theorem_4_Progress
#print axioms Theorem_5_Preservation
#print axioms Lemma_1_StrongCommutativity
#print axioms Lemma_2_DiamondMEqRed

end Pss
