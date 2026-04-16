import Och.Macro
import Och.Eval
import Och.Std.Bool
import Och.Std.Nat

/-!
# Dependent Booleans (fix + ι encoding)

Scott-style dependent Bool where the motive's domain is pinned via `fix`
(recursion binder) and the argument in `P self` comes from `ι` (self-type
binder). Splitting the two self-reference jobs between the two binders is
what gives this encoding its structural properties.

```
dtrue  = fix B:Type. ι self:B. λP:(B → Type). λt:(P self). λf:Type.     t
dfalse = fix B:Type. ι self:B. λP:(B → Type). λt:Type.     λf:(P self). f
dBool  = fix B:Type. ι self:B. λP:(B → Type). λt:(P dtrue). λf:(P dfalse). P self
```

## Why this shape

The previous encoding put `self` in the motive's domain (`P:(self → Type)`)
which made the domain check during `[Lam]` descent contravariantly
problematic — the self-reference there produced the wall documented in
`docs/research-graveyard.md` (covariant self closable, contravariant
impossible).

This encoding moves the recursive reference used in `P`'s domain into the
`fix` binder. During subtyping:
  - structural `fix-body` rule compares bodies with both `B`s as the same
    variable (bvar 0 after fix descent) — refl-equal, no productive cycle
  - structural `ι-body` rule compares bodies with both `self`s bound to
    the same variable
  - `[Lam]` on the motive gives contravariant `(B → Type) ⊑ (B → Type)` →
    refl via the bound variable, not a productive cycle

This is strictly more than the previous `ι self:Type. λP:(self → Type). ...`
version could do. The OUTER wall dissolves.

## What closed it

The inner `(P dtrue) ⊑ (P self)` wall dissolves once the coinductive
assumption set (`seen`) is threaded through `lam`/`app` instead of being
reset to `[]` at every binder. After `iotaIntro` substitutes the LHS for
`self` on the right and `unfoldFixL`/`unfoldIotaL` peel the LHS, the
residual `dtrue ⊑ dBool` subgoal in contravariant domain position is
discharged directly from the assumption set, and the structural
`app-app` rule lines up the `(P dtrue)` arguments. The body comparison
that *should* fail for, e.g., `dBool ⊑ dtrue` does fail at the leaf
`Type ⊑ P dfalse`, so the discipline is not vacuous.

## Note on self-substitution semantics

When the rules fire in different orders different things happen to `self`:
  - `iotaIntro` (value-sub) fires when the LHS is NOT an ι — it substitutes
    the LHS value for `self` in the RHS body. After this, `self` is no
    longer a bound variable in the resulting subtyping goal.
  - Structural `ι-body` fires when both sides are ι — it compares bodies
    with `self` remaining as bvar 0 on both sides.

Agents attacking these markers: DO NOT assume `self` is always bvar 0 in
the body of an ι — after iotaIntro it's been fully substituted and is
whatever the LHS term is.

## Use site

Usage is `b M t f : M b` where `M : B → Type`. This requires passing `M`
at type `(B → Type)`, which the subtype system must accept against the
constructor's declared `(B → Type)` domain via structural fix-unfold
mechanics.
-/

namespace Std

-- ============================================================
-- Exported definitions
-- ============================================================

def dtrue := och{
  fix B:Type. ι self:B. λP:(B → Type). λt:(P self). λf:Type. t
}

def dfalse := och{
  fix B:Type. ι self:B. λP:(B → Type). λt:Type. λf:(P self). f
}

def dBool := och{
  fix B:Type. ι self:B. λP:(B → Type). λt:(P dtrue). λf:(P dfalse). P self
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

example : concEval 50 (och{ dtrue (λ_:dBool. Nat_) zero_ one_ }) = some zero_ := by native_decide
example : concEval 50 (och{ dfalse (λ_:dBool. Nat_) zero_ one_ }) = some one_ := by native_decide

private def dbcase := och{
  λb:dBool. b (λ_:dBool. Nat_) zero_ one_
}

example : concEval 50 (och{ dbcase dtrue }) = some zero_ := by native_decide
example : concEval 50 (och{ dbcase dfalse }) = some one_ := by native_decide

-- Dependent elimination. depMotive picks Nat for true, Bool for false.
private def depMotive := och{
  λb:dBool. b (λ_:dBool. Type) Nat_ Bool
}

example : concEval 100 (och{ dtrue depMotive zero_ true_ }) = some zero_ := by native_decide
example : concEval 100 (och{ dfalse depMotive zero_ true_ }) = some true_ := by native_decide

-- -----------------------------------------------------------
-- Subtyping: the central aspirational tests. Closed via the
-- coinductive seen-set discipline (productive unfolds extend
-- the assumption set, ann-widening does not).
-- -----------------------------------------------------------

example : subCheck 50 dtrue dBool = .ok true := by native_decide
example : subCheck 50 dfalse dBool = .ok true := by native_decide

-- dBool ⋢ dtrue: dBool's motive demands both P(dtrue) and P(dfalse)
-- but dtrue only demands P(self), so the body check fails at
-- `Type ⊑ P dfalse`.
example : subCheck 50 dBool dtrue = .ok false := by native_decide

-- The constructors are pairwise unrelated.
example : subCheck 50 dtrue dfalse = .ok false := by native_decide
example : subCheck 50 dfalse dtrue = .ok false := by native_decide

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

example : concEval 50 (och{ dtrue (λ_:dBool. Nat_) zero_ one_ }) ≠ some one_ := by native_decide
example : concEval 50 (och{ dfalse (λ_:dBool. Nat_) zero_ one_ }) ≠ some zero_ := by native_decide
example : concEval 100 (och{ not dtrue }) ≠ concEval 100 dtrue := by native_decide
example : concEval 100 (och{ not dfalse }) ≠ concEval 100 dfalse := by native_decide
example : concEval 100 (och{ and dfalse dtrue }) ≠ concEval 100 dtrue := by native_decide
example : concEval 100 (och{ and dtrue dfalse }) ≠ concEval 100 dtrue := by native_decide

end Tests
end Std
