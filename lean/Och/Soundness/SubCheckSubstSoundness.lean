import Och.Subtyping
import Och.EvalSubst
import Och.API
import Och.Soundness.EvalSubstLemmas
import Och.Soundness.CloseAll
import Och.Soundness.SubCheckSubstNeutral
import Och.Soundness.SubCheckSubstStructural
import Och.Soundness.SubCheckSubstFallback

/-!
# `subCheckSubst_sound` — the main soundness theorem

Assembles the per-arm lemmas into the engine-level soundness theorem:

```
subCheck fuel a b = .ok true → Subtype' [] [] a b
```

## Status (post de Bruijn refactor)

Sorry'd. In the pure de Bruijn regime the proof should be simpler
(no closeAll translation layer), but needs a rewrite against the
new engine shape.
-/

namespace Och.Soundness

open SubstEval

/-- The main soundness theorem for the structural subtype checker.
    Sorry'd pending proof for pure de Bruijn indices. -/
noncomputable def subCheckSubst_sound
    {fuel : Nat} {a b : Expr}
    (h : SubstEval.subCheck fuel a b = .ok true) :
    Subtype' [] [] a b := by
  sorry

/-- Surface-level soundness: `Och.subCheck a b fuel = .ok true →
    Subtype' [] [] a.whnf b.whnf`. -/
noncomputable def Och_subCheck_sound
    {a b : Och.WTValue} {fuel : Nat}
    (_h : Och.subCheck a b fuel = .ok true) :
    Subtype' [] [] a.whnf b.whnf := by
  sorry

end Och.Soundness
