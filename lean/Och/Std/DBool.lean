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

## What doesn't dissolve

An INNER wall remains at the body's `[Lam]` descent, where the
contravariant check becomes `(P dtrue) ⊑ (P self)` (or similar depending
on which side of the λt binder). `P` is a bound variable; its applications
to different specific terms cannot be compared structurally by the current
rule set. This is a β-convertibility gap, not a self-type gap — it would
be resolved by a local rule letting stuck apps reduce or compare
extensionally when the function side matches.

Making `dtrue ⊑ dBool` close under this encoding is a `TODO[mega-loop]`
target. It should require strictly less machinery than closing the old
encoding did — a β-conversion / DefEq rule on applied bound variables,
plus the split-binder structure that's already in place.

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
-- Computation (concEval): independent of typing, should still
-- work because fix/ι wrappers don't change runtime reduction.
-- -----------------------------------------------------------

-- TODO[mega-loop]: dtrue P t f = t. If concEval doesn't yet unfold fix/ι
-- at the head of an application, this will need the runtime semantics
-- to handle the new binders correctly.
example : concEval 50 (och{ dtrue (λ_:dBool. Nat_) zero_ one_ }) = some zero_ := by sorry

-- TODO[mega-loop]: dfalse P t f = f
example : concEval 50 (och{ dfalse (λ_:dBool. Nat_) zero_ one_ }) = some one_ := by sorry

-- TODO[mega-loop]: non-dependent case analysis via dbcase
private def dbcase := och{
  λb:dBool. b (λ_:dBool. Nat_) zero_ one_
}

example : concEval 50 (och{ dbcase dtrue }) = some zero_ := by sorry
example : concEval 50 (och{ dbcase dfalse }) = some one_ := by sorry

-- TODO[mega-loop]: dependent elimination. depMotive picks Nat for true, Bool for false.
private def depMotive := och{
  λb:dBool. b (λ_:dBool. Type) Nat_ Bool
}

example : concEval 100 (och{ dtrue depMotive zero_ true_ }) = some zero_ := by sorry
example : concEval 100 (och{ dfalse depMotive zero_ true_ }) = some true_ := by sorry

-- -----------------------------------------------------------
-- Subtyping: the aspirational core. All sorried until the
-- mega-loop closes the β-convertibility obstruction.
-- -----------------------------------------------------------

-- TODO[mega-loop]: dtrue ⊑ dBool. Outer motive-domain contravariance is
-- now structural (fix-body); the remaining obstruction is the inner
-- contravariant `(P dtrue) ⊑ (P self)` check on applied bound variables.
example : subCheck 50 dtrue dBool = .ok true := by sorry

-- TODO[mega-loop]: dfalse ⊑ dBool. Same obstruction, mirror of dtrue.
example : subCheck 50 dfalse dBool = .ok true := by sorry

-- TODO[mega-loop]: dBool ⋢ dtrue (narrowing going the wrong direction
-- should NOT succeed — dBool's motive demands both P(dtrue) and P(dfalse)
-- but dtrue only demands P(dtrue)). This is a negative test; closing it
-- means the checker correctly rejects.
example : subCheck 50 dBool dtrue = .ok false := by sorry

-- -----------------------------------------------------------
-- Operations (not / and). Depend on the subtyping above.
-- -----------------------------------------------------------

-- TODO[mega-loop]: not dtrue = dfalse (computationally)
example : concEval 100 (och{ not dtrue }) = concEval 100 dfalse := by sorry
example : concEval 100 (och{ not dfalse }) = concEval 100 dtrue := by sorry

-- TODO[mega-loop]: and table
example : concEval 100 (och{ and dtrue dtrue }) = concEval 100 dtrue := by sorry
example : concEval 100 (och{ and dtrue dfalse }) = concEval 100 dfalse := by sorry
example : concEval 100 (och{ and dfalse dtrue }) = concEval 100 dfalse := by sorry
example : concEval 100 (och{ and dfalse dfalse }) = concEval 100 dfalse := by sorry

-- -----------------------------------------------------------
-- Negative / sanity checks
-- -----------------------------------------------------------

-- TODO[mega-loop]: dtrue selects first arg, not second
example : concEval 50 (och{ dtrue (λ_:dBool. Nat_) zero_ one_ }) ≠ some one_ := by sorry
-- TODO[mega-loop]: dfalse selects second arg, not first
example : concEval 50 (och{ dfalse (λ_:dBool. Nat_) zero_ one_ }) ≠ some zero_ := by sorry
-- TODO[mega-loop]: not is an involution, so not true ≠ true
example : concEval 100 (och{ not dtrue }) ≠ concEval 100 dtrue := by sorry
-- TODO[mega-loop]: not dfalse ≠ dfalse
example : concEval 100 (och{ not dfalse }) ≠ concEval 100 dfalse := by sorry
-- TODO[mega-loop]: and is not commutative-on-false
example : concEval 100 (och{ and dfalse dtrue }) ≠ concEval 100 dtrue := by sorry
example : concEval 100 (och{ and dtrue dfalse }) ≠ concEval 100 dtrue := by sorry

end Tests
end Std
