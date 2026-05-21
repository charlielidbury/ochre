import Och.Macro
import Och.Eval
import Och.EvalSubst
import Och.Std.Bool
import Och.Std.DNat
import Och.API

/-!
# Dependent Booleans

Scott-style dependent Bool where the motive's domain is the value
itself, `P : (self → Type)`. The constructors are plain lambdas
(no ι/fix wrapper) and don't reference `DBool`, so there is no
forward-reference cycle: `true_`/`false_` are defined first (in
`Bool.lean`), `DBool` references them.

```
true_  = λP:Type. λt:Type. λf:Type. t
false_ = λP:Type. λt:Type. λf:Type. f
DBool  = fix B:Type. ι self:B. λP:(B → Type). λt:(P true_). λf:(P false_). P self
```

## How `true_ ⊑ DBool` closes

When checking `true_ ⊑ DBool`:

  1. `_, .fix` unfolds DBool, extending `seen` with `(true_, DBool)`.
  2. `iotaIntro`'s `okAnn` check (`true_ ⊑ B = DBool`) hits `seen` ✓.
     RHS body opens with `self ↦ true_`.
  3. `.lam,.lam` on `P`: contravariant `(DBool → Type) ⊑ Type`
     → `.top` ✓.
  4. `t`-domain `(P true_) ⊑ Type`: top. `f`-domain
     `(P false_) ⊑ Type`: top. Body `t ⊑ P true_`: ascent via
     `tyCtx[t] = P true_` (domA), refl. ✓

Since the constructors are plain lambdas with `Type` domains,
all contravariant domain checks are trivially `.top` — no
coinductive hypothesis from the seen-set is needed for the
domain comparisons (only for the annotation check in step 2).
-/

namespace Std

-- ============================================================
-- Exported definitions
-- ============================================================

def DBool := och{
  fix B. ι self:B. λP:(B → Type). λt:(P true_). λf:(P false_). P self
}

def not := och{
  λb:DBool. b (λ_:DBool. DBool) false_ true_
}

def and := och{
  λa:DBool. λb:DBool. a (λ_:DBool. DBool) b false_
}

-- ============================================================
-- Tests
-- ============================================================

section Tests

-- -----------------------------------------------------------
-- Computation (concEval): fix/ι wrappers unfold transparently
-- in head position so the Church-style bodies reduce as before.
-- -----------------------------------------------------------

example : concEval 100 (och{ true_ (λ_:DBool. Nat_) zero_ one_ }) = concEval 100 zero_ := by
  native_decide
example : concEval 100 (och{ false_ (λ_:DBool. Nat_) zero_ one_ }) = concEval 100 one_ := by
  native_decide

private def dbcase := och{
  λb:DBool. b (λ_:DBool. Nat_) zero_ one_
}

example : concEval 100 (och{ dbcase true_ }) = concEval 100 zero_ := by native_decide
example : concEval 100 (och{ dbcase false_ }) = concEval 100 one_ := by native_decide

-- Dependent elimination. depMotive picks Nat for true, Bool for false.
private def depMotive := och{
  λb:DBool. b (λ_:DBool. Type) Nat_ Bool
}

example : concEval 100 (och{ true_ depMotive zero_ true_ }) = .ok zero_ := by native_decide
example : concEval 100 (och{ false_ depMotive zero_ true_ }) = .ok true_ := by native_decide

-- -----------------------------------------------------------
-- Subtyping: the central aspirational tests. Closed via the
-- coinductive seen-set discipline (productive unfolds extend
-- the assumption set, ann-widening does not).
-- -----------------------------------------------------------

example : Och.checkSubtype 50 true_ DBool = .ok true := by native_decide
example : Och.checkSubtype 50 false_ DBool = .ok true := by native_decide

-- DBool ⋢ true_: DBool's motive demands both P(true_) and P(false_)
-- but true_ only demands P(self), so the body check fails at
-- `Type ⊑ P false_`.
example : Och.checkSubtype 50 DBool true_ = .ok false := by native_decide

-- The constructors are pairwise unrelated.
example : Och.checkSubtype 50 true_ false_ = .ok false := by native_decide
example : Och.checkSubtype 50 false_ true_ = .ok false := by native_decide

-- -----------------------------------------------------------
-- Operations (not / and).
-- -----------------------------------------------------------

example : concEval 100 (och{ not true_ }) = concEval 100 false_ := by native_decide
example : concEval 100 (och{ not false_ }) = concEval 100 true_ := by native_decide

example : concEval 100 (och{ and true_ true_ }) = concEval 100 true_ := by native_decide
example : concEval 100 (och{ and true_ false_ }) = concEval 100 false_ := by native_decide
example : concEval 100 (och{ and false_ true_ }) = concEval 100 false_ := by native_decide
example : concEval 100 (och{ and false_ false_ }) = concEval 100 false_ := by native_decide

-- -----------------------------------------------------------
-- Negative / sanity checks
-- -----------------------------------------------------------

example : concEval 100 (och{ true_ (λ_:DBool. Nat_) zero_ one_ }) ≠ .ok one_ := by native_decide
example : concEval 100 (och{ false_ (λ_:DBool. Nat_) zero_ one_ }) ≠ .ok zero_ := by native_decide
example : concEval 100 (och{ not true_ }) ≠ concEval 100 true_ := by native_decide
example : concEval 100 (och{ not false_ }) ≠ concEval 100 false_ := by native_decide
example : concEval 100 (och{ and false_ true_ }) ≠ concEval 100 true_ := by native_decide
example : concEval 100 (och{ and true_ false_ }) ≠ concEval 100 true_ := by native_decide

end Tests
end Std
