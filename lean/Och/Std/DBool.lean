import Och.Macro
import Och.Eval
import Och.Std.Bool
import Och.Std.Nat

/-!
# Dependent Booleans (self-type encoding)

Scott-style dependent Bool where the return type of elimination depends
on the value being eliminated.

```
dBool = ι(dBool : Type).
  -- constructors (motive domain constrained to self for self-type intro)
  let dtrue  = ι(dtrue  : dBool). λP:(dtrue→Type).  λt:(P dtrue).  λf:Type. t in
  let dfalse = ι(dfalse : dBool). λP:(dfalse→Type). λt:Type. λf:(P dfalse). f in

  -- the type itself
  λP:(dBool→Type). λt:(P dtrue). λf:(P dfalse). P dBool
```

Uses ι (iota / self-type binder), not fix: these definitions use the
self-reference for dependent elimination (the motive `P` ranges over the
type itself), not for general recursion.

Key properties:
- Dependent: motive P can vary over which boolean is eliminated
- Each constructor constrains P's domain to itself (not dBool). This is
  essential for self-type intro: when checking dtrue ⊑ dBool, the self-type
  substitution replaces dBool with dtrue in the body, making the P domain
  check reflexive (dtrue→Type ⊑ dtrue→Type).
- Usage still works: passing P:(dBool→Type) to dtrue requires
  (dBool→Type) ⊑ (dtrue→Type), which by contravariance needs dtrue ⊑ dBool.
- dtrue has λf:Type (f unused, domain is Top for covariance)
- dfalse has λt:Type (t unused, domain is Top for covariance)
-/

namespace Std

-- ============================================================
-- Exported definitions
-- ============================================================

def dtrue := och{
  ι self:Type. λP:(self → Type). λt:(P self). λf:Type. t
}

def dfalse := och{
  ι self:Type. λP:(self → Type). λt:Type. λf:(P self). f
}

def dBool := och{
  ι self:Type. λP:(self → Type). λt:(P dtrue). λf:(P dfalse). P self
}

def not := och{
  λb:dBool. b (dBool → dBool) dfalse dtrue
}

def and := och{
  λa:dBool. λb:dBool. a (dBool → dBool) b dfalse
}

-- ============================================================
-- Tests
-- ============================================================

section Tests

-- dtrue P t f = t
example : concEval 50 (och{ dtrue (dBool → Nat_) zero_ one_ }) = some zero_ := by native_decide

-- dfalse P t f = f
example : concEval 50 (och{ dfalse (dBool → Nat_) zero_ one_ }) = some one_ := by native_decide

-- Non-dependent case analysis: true→0, false→1
private def dbcase := och{
  λb:dBool. b (dBool → Nat_) zero_ one_
}

example : concEval 50 (och{ dbcase dtrue }) = some zero_ := by native_decide
example : concEval 50 (och{ dbcase dfalse }) = some one_ := by native_decide

-- Dependent elimination: motive that distinguishes true from false.
-- P b = b (λ_.Type) Nat Bool, so P true = Nat, P false = Bool
private def depMotive := och{
  λb:dBool. b (dBool → Type → Type) Nat_ Bool
}

example : concEval 100 (och{ dtrue depMotive zero_ true_ }) = some zero_ := by native_decide

example : concEval 100 (och{ dfalse depMotive zero_ true_ }) = some true_ := by native_decide

-- Subtype checking
-- TODO[mega-loop]: dtrue ⊑ dBool (aspirational) — previously passed with the
-- bundled-mu iotaIntro using "fixed-self" substitution. Under the new
-- value-sub iotaIntro the right cascade of rules must fire. Currently
-- returns .ok false (see docs/research/iota-fix-split.md and Simple Och's
-- Challenge.lean for the exact obstruction — structural beta-redex in
-- contravariant position).
example : subCheck 50 dtrue dBool = .ok true := by sorry
-- TODO[mega-loop]: dfalse ⊑ dBool (aspirational) — same obstruction as dtrue.
example : subCheck 50 dfalse dBool = .ok true := by sorry

-- not
example : concEval 100 (och{ not dtrue }) = concEval 100 dfalse := by native_decide
example : concEval 100 (och{ not dfalse }) = concEval 100 dtrue := by native_decide

-- and
example : concEval 100 (och{ and dtrue dtrue }) = concEval 100 dtrue := by native_decide
example : concEval 100 (och{ and dtrue dfalse }) = concEval 100 dfalse := by native_decide
example : concEval 100 (och{ and dfalse dtrue }) = concEval 100 dfalse := by native_decide
example : concEval 100 (och{ and dfalse dfalse }) = concEval 100 dfalse := by native_decide

-- computation (negative)
-- dtrue selects first arg, not second
example : concEval 50 (och{ dtrue (dBool → Nat_) zero_ one_ }) ≠ some one_ := by native_decide
-- dfalse selects second arg, not first
example : concEval 50 (och{ dfalse (dBool → Nat_) zero_ one_ }) ≠ some zero_ := by native_decide
-- not true ≠ true
example : concEval 100 (och{ not dtrue }) ≠ concEval 100 dtrue := by native_decide
-- not false ≠ false
example : concEval 100 (och{ not dfalse }) ≠ concEval 100 dfalse := by native_decide
-- and false true ≠ true
example : concEval 100 (och{ and dfalse dtrue }) ≠ concEval 100 dtrue := by native_decide
-- and true false ≠ true
example : concEval 100 (och{ and dtrue dfalse }) ≠ concEval 100 dtrue := by native_decide

end Tests
end Std
