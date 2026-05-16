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

## Status (post intrinsic-derivation refactor)

With the refactored `subCheckSubst` returning `Outcome (Subtype' S Γ a b)`
intrinsically, soundness becomes trivial: the derivation is carried by the
return value. The per-arm lemmas in `SubCheckSubstStructural`,
`SubCheckSubstNeutral`, and `SubCheckSubstFallback` are obsoleted — each
arm's soundness is now the arm's own sorry obligation inside
`subCheckSubstMatch`.

The old theorem `subCheckSubst_sound` is replaced by `subCheckDeriv_sound`
which extracts the derivation from the `Outcome`. The sorry's in this
module are inherited from the sorry's in `subCheckSubst`/`subCheckSubstMatch`.

The Bool-returning `subCheck` soundness (`subCheck_sound`) is still sorry'd
because it uses `subCheckBool` (the Bool version), not `subCheckSubst`
(the derivation version). Once the derivation version is fully closed,
`subCheck` can be defined in terms of it and soundness follows.
-/

namespace Och.Soundness

open SubstEval

/-- Soundness of the derivation-returning subtype checker: if
    `subCheckDeriv` succeeds, the `Outcome` payload is the proof.
    This is trivially true by construction (the payload IS the
    derivation). -/
noncomputable def subCheckDeriv_sound
    {fuel : Nat} {a b : Expr} {deriv : Subtype' [] [] a b}
    (_h : SubstEval.subCheckDeriv fuel a b = .ok deriv) :
    Subtype' [] [] a b :=
  deriv

/-- The main soundness theorem for the Bool-returning checker.
    Sorry'd — the Bool version (`subCheckBool`) doesn't carry
    derivations. Once all arms of `subCheckSubstMatch` are closed,
    `subCheck` can be redefined via `subCheckDeriv` and this
    theorem becomes trivial. -/
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
