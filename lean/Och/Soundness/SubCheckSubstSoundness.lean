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

Assembles the per-arm lemmas from `SubCheckSubstStructural`,
`SubCheckSubstNeutral`, and `SubCheckSubstFallback` into the
engine-level soundness theorem:

```
subCheckSubst fuel tyCtx seen a b = .ok true →
  Subtype' S Γ a b
```

## Status (post de Bruijn refactor)

Sorry'd. The entire module used the old `closeAll`/`closedAtLvl`/
`lvarLT`/`substL` infrastructure which has been removed. In the
pure de Bruijn regime the proof should be simpler (no translation
layer), but needs a complete rewrite.
-/

namespace Och.Soundness

open SubstEval

/-- The main soundness theorem for the structural subtype checker.
    Sorry'd pending rewrite for pure de Bruijn indices. -/
theorem subCheckSubst_sound
    {fuel : Nat} {a b : Expr}
    (h : SubstEval.subCheck fuel a b = .ok true) :
    Subtype' [] [] a b := by
  sorry

/-- Surface-level soundness: `Och.subCheck a b fuel = .ok true →
    Subtype' [] [] a.whnf b.whnf`. -/
theorem Och_subCheck_sound
    {a b : Och.WTValue} {fuel : Nat}
    (_h : Och.subCheck a b fuel = .ok true) :
    Subtype' [] [] a.whnf b.whnf := by
  sorry

end Och.Soundness
