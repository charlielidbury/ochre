import Och.Macro
import Och.Eval
import Och.EvalSubst
import Och.Std.Bool
import Och.Std.DNat
import Och.API

/-!
# Dependent Booleans (very-dependent ι encoding)

Scott-style dependent Bool where the motive's domain is the value
itself, `P : (self → Type)`. The constructors carry no per-value
`fix` wrapper and don't reference `dBool`, so there is no
forward-reference cycle: `dtrue`/`dfalse` are defined first,
`dBool` references them.

```
dtrue  = ι self:Type. λP:(self → Type). λt:(P self). λf:Type.     t
dfalse = ι self:Type. λP:(self → Type). λt:Type.     λf:(P self). f
dBool  = fix B:Type. ι self:B. λP:(B → Type). λt:(P dtrue). λf:(P dfalse). P self
```

## How `dtrue ⊑ dBool` closes

The constructor's ι annotation is `Type` (a placeholder — the motive
uses `self`, not the annotation, so any annotation works). When
checking `dtrue ⊑ dBool`:

  1. `_, .fix` unfolds dBool, extending `seen` with `(dtrue, dBool)`.
  2. `.iota,.iota` structural fails the annotation check
     (`Type ⊑ dBool` is false), falls to `iotaIntro`.
  3. `iotaIntro`'s `okAnn` check (`dtrue ⊑ B = dBool`) hits `seen` ✓.
     RHS body opens with `self ↦ dtrue`.
  4. `.iota,_` unfolds the LHS with `self ↦ dtrue`, giving
     `λP:(dtrue → Type). λt:(P dtrue). λf:Type. t`.
  5. `.lam,.lam` on `P`: contravariant `(dBool → Type) ⊑ (dtrue → Type)`
     → contravariant `dtrue ⊑ dBool` → hits `seen` ✓.
  6. `t`-domain `(P dtrue) ⊑ (P dtrue)`: refl. `f`-domain
     `(P dfalse) ⊑ Type`: top. Body `t ⊑ P dtrue`: ascent via
     `tyCtx[t] = P dtrue` (domA), refl. ✓

The earlier `fix B:Type` per-constructor wrapper (commit `e08bce9`)
worked around step 5 not closing — at the time, the seen-set was
reset under binders (pre-A4). With the seen-indexed `Subtype'` and
the iotaIntro/seen-thread fixes (A4/A5/A7), the very-dependent form
goes through directly. The constructors are now half the size and
don't mention any external type.

## On the ι annotation

`ι` syntactically requires an annotation. For constructors, `Type`
is the natural choice: it makes the structural-path annotation check
fail fast (so iotaIntro takes over), and it carries no information
the algorithm needs. For the *type* `dBool`, the annotation is the
fix-binder `B`, which is the standard `μ`-pattern.
-/

namespace Std

-- ============================================================
-- Exported definitions
-- ============================================================

def dtrue := och{
  ι self. λP:(self → Type). λt:(P self). λf:Type. t
}

def dfalse := och{
  ι self. λP:(self → Type). λt:Type. λf:(P self). f
}

def dBool := och{
  fix B. ι self:B. λP:(B → Type). λt:(P dtrue). λf:(P dfalse). P self
}

def not := och{
  λb:dBool. b (λ_:dBool. dBool) dfalse dtrue
}

def and := och{
  λa:dBool. λb:dBool. a (λ_:dBool. dBool) b dfalse
}

-- ============================================================
-- Tests
-- ============================================================

section Tests

-- -----------------------------------------------------------
-- Computation (concEval): fix/ι wrappers unfold transparently
-- in head position so the Church-style bodies reduce as before.
-- -----------------------------------------------------------

example : concEval 100 (och{ dtrue (λ_:dBool. Nat_) zero_ one_ }) = concEval 100 zero_ := by
  native_decide
example : concEval 100 (och{ dfalse (λ_:dBool. Nat_) zero_ one_ }) = concEval 100 one_ := by
  native_decide

private def dbcase := och{
  λb:dBool. b (λ_:dBool. Nat_) zero_ one_
}

example : concEval 100 (och{ dbcase dtrue }) = concEval 100 zero_ := by native_decide
example : concEval 100 (och{ dbcase dfalse }) = concEval 100 one_ := by native_decide

-- Dependent elimination. depMotive picks Nat for true, Bool for false.
private def depMotive := och{
  λb:dBool. b (λ_:dBool. Type) Nat_ Bool
}

example : concEval 100 (och{ dtrue depMotive zero_ true_ }) = .ok zero_ := by native_decide
example : concEval 100 (och{ dfalse depMotive zero_ true_ }) = .ok true_ := by native_decide

-- -----------------------------------------------------------
-- Subtyping: the central aspirational tests. Closed via the
-- coinductive seen-set discipline (productive unfolds extend
-- the assumption set, ann-widening does not).
-- -----------------------------------------------------------

example : Och.subCheckE 50 dtrue dBool = .ok true := by native_decide
example : Och.subCheckE 50 dfalse dBool = .ok true := by native_decide

-- dBool ⋢ dtrue: dBool's motive demands both P(dtrue) and P(dfalse)
-- but dtrue only demands P(self), so the body check fails at
-- `Type ⊑ P dfalse`.
example : Och.subCheckE 50 dBool dtrue = .ok false := by native_decide

-- The constructors are pairwise unrelated.
example : Och.subCheckE 50 dtrue dfalse = .ok false := by native_decide
example : Och.subCheckE 50 dfalse dtrue = .ok false := by native_decide

-- -----------------------------------------------------------
-- Operations (not / and).
-- -----------------------------------------------------------

example : concEval 100 (och{ not dtrue }) = concEval 100 dfalse := by native_decide
example : concEval 100 (och{ not dfalse }) = concEval 100 dtrue := by native_decide

example : concEval 100 (och{ and dtrue dtrue }) = concEval 100 dtrue := by native_decide
example : concEval 100 (och{ and dtrue dfalse }) = concEval 100 dfalse := by native_decide
example : concEval 100 (och{ and dfalse dtrue }) = concEval 100 dfalse := by native_decide
example : concEval 100 (och{ and dfalse dfalse }) = concEval 100 dfalse := by native_decide

-- -----------------------------------------------------------
-- Negative / sanity checks
-- -----------------------------------------------------------

example : concEval 100 (och{ dtrue (λ_:dBool. Nat_) zero_ one_ }) ≠ .ok one_ := by native_decide
example : concEval 100 (och{ dfalse (λ_:dBool. Nat_) zero_ one_ }) ≠ .ok zero_ := by native_decide
example : concEval 100 (och{ not dtrue }) ≠ concEval 100 dtrue := by native_decide
example : concEval 100 (och{ not dfalse }) ≠ concEval 100 dfalse := by native_decide
example : concEval 100 (och{ and dfalse dtrue }) ≠ concEval 100 dtrue := by native_decide
example : concEval 100 (och{ and dtrue dfalse }) ≠ concEval 100 dtrue := by native_decide

end Tests
end Std
