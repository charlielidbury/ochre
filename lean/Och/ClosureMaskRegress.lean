import Och.Macro
import Och.Eval
import Och.SubCheckVal

/-!
# Closure-env masking regression

`subCheckValMatch`'s lam-lam arm pushes the *target* domain
`domB` (SoundnessAudit A6). When the RHS comes from `dNat`'s
body, `domB` for the `s` parameter is `λpred:N. P (dsucc_local
pred)`, where `dsucc_local` is the `let`-bound inner fix. That
fix's closure env is `[dzero_val, fresh_self@d, vNat]` even
though its body never references `self` (only `N`). Each
structural ι-open at depth `d` thus produced a *distinct*
`dsucc_local` Val, the seen-set never hit, and the algorithm
went exponential — `NbE.subCheck 200 dtwo dNat` did not
terminate in 90 s.

`Closure.mk'` now masks env slots the body cannot reach
(`Expr.usesBvar`), so `dsucc_local` is the same Val regardless
of `self@d`. The checks below complete in seconds.

These defs are inlined (not imported from `Och.Std.DNat`) so
this file builds independently of the heavyweight `dthree ⊑
dNat` `native_decide` examples there.
-/

namespace ClosureMaskRegress

def dNat := och{
  fix N:Type. ι self:N.
    let dzero : N = ι dzero:N. λP:(dzero → Type). λz:(P dzero). λs:Type. z in
    let dsucc : (N → N) = fix dsucc:(N → N).
      λm:N. λP:((dsucc m) → Type). λz:Type. λs:(λpred:N. P (dsucc pred)). s m in
    λP:(N → Type). λz:(P dzero). λs:(λpred:N. P (dsucc pred)). P self
}
def dzero := och{
  ι dzero:dNat. λP:(dzero → Type). λz:(P dzero). λs:Type. z
}
def dsucc := och{
  fix dsucc:(dNat → dNat).
    λm:dNat. λP:((dsucc m) → Type). λz:Type. λs:(λpred:dNat. P (dsucc pred)). s m
}
def done_  := och{ dsucc dzero }
def dtwo   := och{ dsucc done_ }
def dthree := och{ dsucc dtwo }

-- Pre-mask: hung at fuel ≥ 170. Post-mask: instant.
example : NbE.subCheck 200 dtwo  dNat = .ok true := by native_decide
example : NbE.subCheck 400 done_ dNat = .ok true := by native_decide

-- The masking is conservative (never changes a referenced
-- slot), so the negative cases are unchanged.
example : NbE.subCheck 400 dNat dzero = .ok false := by native_decide
example : NbE.subCheck 400 dzero done_ = .ok false := by native_decide

end ClosureMaskRegress
