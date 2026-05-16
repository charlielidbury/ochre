import Och.Subtyping
import Och.EvalSubst
import Och.Soundness.EvalSubstLemmas
import Och.Soundness.CloseAll
import Och.Soundness.SubtypeSteps
import Och.Soundness.SubCheckSubstNeutral
import Och.Soundness.SubCheckSubstStructural

/-!
# Fallback arm lemmas for `subCheckSubst` soundness

These lemmas handle the fallback (non-structural) arms of the
subtype checker: iotaIntro, unfoldFixR, unfoldFixL, unfoldIotaL.

## Status (post de Bruijn refactor)

All sorry'd. In the old level-var regime these required complex
`closeAll`/`substL` bridges. In the pure de Bruijn regime, the
bridge is trivial (closeAll = id, engine uses Expr.subst directly),
but the proofs need to be rewritten against the new engine shape.
-/

namespace Och.Soundness

open SubstEval

/-- `closeAll 0 e = e` (compatibility shim). -/
theorem closeAll_zero' (e : Expr) : closeAll 0 e = e := rfl

/-- iotaIntro fallback: if the engine accepts `a ⊑ ι ann. body` via
    iotaIntro, then declaratively `Subtype' S Γ a (ι ann body)`. -/
theorem iota_intro_arm
    {S : Seen} {Γ : Ctx} {fuel : Nat}
    {a ann body : Expr} {bodyV : Expr}
    (_h_eval : evalSubst fuel unfBound (body.subst 0 a) = .ok bodyV)
    (_hcl : True) (_hlv : True) :
    Subtype' S Γ a (.iota ann body) := by
  sorry

/-- unfoldFixR fallback. -/
theorem unfold_fix_R_arm
    {S : Seen} {Γ : Ctx} {fuel : Nat}
    {a ann body : Expr} {unfoldedV : Expr}
    (_h_eval : evalSubst fuel unfBound (body.subst 0 (.fix ann body)) = .ok unfoldedV)
    (_hcl : True) (_hlv : True) :
    Subtype' S Γ a (.fix ann body) := by
  sorry

/-- unfoldFixL fallback. -/
theorem unfold_fix_L_arm
    {S : Seen} {Γ : Ctx} {fuel : Nat}
    {ann body b : Expr} {unfoldedV : Expr}
    (_h_eval : evalSubst fuel unfBound (body.subst 0 (.fix ann body)) = .ok unfoldedV)
    (_hcl : True) (_hlv : True) :
    Subtype' S Γ (.fix ann body) b := by
  sorry

/-- unfoldIotaL fallback. -/
theorem unfold_iota_L_arm
    {S : Seen} {Γ : Ctx} {fuel : Nat}
    {ann body b : Expr} {unfoldedV : Expr}
    (_h_eval : evalSubst fuel unfBound (body.subst 0 (.iota ann body)) = .ok unfoldedV)
    (_hcl : True) (_hlv : True) :
    Subtype' S Γ (.iota ann body) b := by
  sorry

end Och.Soundness
