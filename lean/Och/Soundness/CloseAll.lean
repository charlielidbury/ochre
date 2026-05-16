import Och.Subtyping
import Och.EvalSubst
import Och.Soundness.EvalSubstLemmas
import Och.Soundness.EvalSubstEquiv

/-!
# `closeAll` — OBSOLETE (gutted by de Bruijn refactor)

This module previously implemented the `closeAll` translation from
level-var indices to de Bruijn indices. In the pure de Bruijn regime,
the algorithmic and declarative representations share the same variable
encoding, making `closeAll` the identity. The entire module has been
replaced with trivial stubs.

The downstream soundness modules (`SubCheckSubstStructural`,
`SubCheckSubstFallback`, `SubCheckSubstNeutral`,
`SubCheckSubstSoundness`) still import this file for compilation
purposes but their proofs need complete rewriting for the new regime.
-/

namespace SubstEval

/-- In the pure de Bruijn regime, `closeAll` is the identity.
    Retained as a compatibility stub for downstream modules. -/
def closeAll (_d : Nat) (e : Expr) : Expr := e

/-- In the pure de Bruijn regime, `closeAllAt` is the identity.
    Retained as a compatibility stub for downstream modules. -/
def closeAllAt (_c _d : Nat) (e : Expr) : Expr := e

theorem closeAll_zero (e : Expr) : closeAll 0 e = e := rfl

theorem closeAllAt_zero (_c : Nat) (e : Expr) : closeAllAt _c 0 e = e := rfl

end SubstEval
