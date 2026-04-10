import Och.Simple.Macro
import Och.Simple.Subtype
import Och.Simple.Eval
import Och.Simple.Bidir
import Och.Simple.Std.Bool
import Och.Simple.Std.Nat
import Och.Simple.Std.Pair
import Och.Simple.Std.Unit
import Och.Simple.Std.DBool
import Och.Simple.Std.DNat
import Och.Simple.Std.Mu

/-!
# Aspirational Tests for Simple Och

Tests organized by the feature that would make them pass.
Each aspirational test is commented out with:
  1. What it tests
  2. Why it fails
  3. What "flip condition" would make it pass

## Test Categories

- **Category A**: Self-type intro (needs Sub.muR)
- **Category B**: BetaR (type-level computation on RHS)
- **Category C**: CBV (call-by-value evaluation)
- **Category D**: Recursive types/functions
- **Category E**: Larger programs (composition of features)

## Metric

Count of aspirational tests that pass = progress measure.
Current: 0 aspirational tests pass.
-/

set_option autoImplicit false

namespace Och.Simple.Std.Aspirational

open Och.Simple Expr

private def ev (e : Expr) : Option Expr := eval 200 e

-- Free variable markers (soch{} cannot contain .var literals)
private def x1 : Expr := .var 1
private def x2 : Expr := .var 2
private def x3 : Expr := .var 3
private def x42 : Expr := .var 42
private def x99 : Expr := .var 99

-- ============================================================
-- Category A: Self-type intro (needs Sub.muR)
-- ============================================================
-- The current Sub.mu rule only handles mu on the LEFT: mu(A).b <= c.
-- There is NO rule for a <= mu(A).b (self-type intro on the RIGHT).
-- Adding Sub.muR would enable these.

-- A1: dtrue <= dBool — FLIPPED via bidirectional checker (muR + seen set)
example : check 200 [] dtrue dBool = true := by native_decide

-- A2: dfalse <= dBool — FLIPPED
example : check 200 [] dfalse dBool = true := by native_decide

-- A3: dzero <= dNat — FLIPPED
example : check 200 [] dzero dNat = true := by native_decide

-- A4: done_ <= dNat — STILL ASPIRATIONAL
-- `done_ = dsucc dzero` is an application of a recursive function to a recursive value.
-- The current bidirectional checker's app strategies (synth + beta) cannot yet
-- reduce `dsucc dzero` far enough to match `dNat`'s structure.
-- Flip condition: stronger beta reduction in subCheck for app-of-mu, or a
-- normalization pass before subCheck.
-- example : check 500 [] done_ dNat = true := by native_decide

-- A5: dtwo <= dNat — STILL ASPIRATIONAL (same reason as A4)
-- example : check 500 [] dtwo dNat = true := by native_decide

-- A6: dnot : dBool -> dBool — STILL ASPIRATIONAL
-- dnot's body is a dependent elimination of a variable of type dBool, which
-- requires unfolding the variable's mu via its type in the context.
-- The current algorithm doesn't do this unfolding.
-- Flip condition: ctx-aware beta reduction (unfold var's type's mu)
-- example : check 500 [] dnot (soch{ dBool → dBool }) = true := by native_decide

-- A7: dand : dBool -> dBool -> dBool — STILL ASPIRATIONAL (same as A6)
-- example : check 500 [] dand (soch{ dBool → dBool → dBool }) = true := by native_decide

-- A8: disZero : dNat -> BOOL — STILL ASPIRATIONAL (same reason as A6)
-- example : check 500 [] disZero (soch{ dNat → BOOL }) = true := by native_decide

-- ============================================================
-- Category B: BetaR (type-level computation on RHS)
-- ============================================================
-- The subtype checker does not beta-reduce on the RHS of <=.
-- Sub.app gives R[0:=a] on the LHS but cannot reduce apps on the RHS.

-- B1: SUCC ZERO <= NAT — FLIPPED via bidirectional checker (app beta-reduction)
example : ev (.app (.app (.app (.app SUCC ZERO) .top) x99) (soch{ λ(x : ⊤). x }))
  = some x99 := rfl
example : check 100 [] (soch{ SUCC ZERO }) NAT = true := by native_decide

-- B2: ADD ONE TWO <= NAT — FLIPPED
example : check 100 [] (soch{ ADD ONE TWO }) NAT = true := by native_decide

-- B3: Type-level function application: (λa:T. a -> a) BOOL <= BOOL -> BOOL
-- FLIPPED via bidirectional checker (lam beta-reduction)
example : check 100 [] (soch{ (λ(a : ⊤). a → a) BOOL }) (soch{ BOOL → BOOL }) = true := by native_decide

-- B4: ISZERO ZERO <= BOOL (result of applying ISZERO) — FLIPPED
example : check 100 [] (soch{ ISZERO ZERO }) BOOL = true := by native_decide

-- B5: MUL TWO THREE <= NAT — STILL ASPIRATIONAL
-- MUL TWO THREE evaluates to Church-encoded 6, which has O(6) structure in
-- applications. The current subCheck loop doesn't progress through it within
-- the fuel budget.
-- Flip condition: stronger normalization or caching in subCheck
-- example : check 1000 [] (soch{ MUL TWO THREE }) NAT = true := by native_decide

-- ============================================================
-- Category C: CBV (call-by-value evaluation)
-- ============================================================
-- Current evaluator is call-by-name. CBV would reduce arguments before
-- passing them, which matters for some programs.

-- C1: SUCC ZERO with stuck successor evaluates differently in CBN vs CBV
-- In CBN: f (ZERO T z f) -- the ZERO app stays unevaluated
-- In CBV: f z -- the inner application would be reduced first
-- This test documents the CBN behavior:
example : ev (.app (.app (.app (.app SUCC ZERO) .top) x99) x42)
  = some (.app x42 (.app (.app (.app ZERO .top) x99) x42)) := rfl
-- ASPIRATIONAL (CBV): the inner ZERO application would reduce
-- def ev_cbv := ... -- hypothetical CBV evaluator
-- example : ev_cbv (SUCC ZERO applied) = some (app x42 x99)

-- C2: ADD ONE ONE with stuck args
-- CBN leaves inner applications unreduced
-- CBV would reduce them
-- ASPIRATIONAL: CBV evaluator that matches CBN on total programs

-- C3: toZero_bad diverges in CBN because both branches are evaluated
-- In a CBV language with proper if-then-else, only one branch would execute
-- ASPIRATIONAL: CBV with proper conditionals
-- example : ev_cbv (toZero_bad ZERO) = some ZERO

-- ============================================================
-- Category D: Recursive types/functions
-- ============================================================

-- D1: LIST encoding — defined, well-formedness checks
def LIST : Expr := soch{
  μ(list : ⊤). λ(a : ⊤). λ(r : ⊤).
    λ(cons : λ(hd : a). λ(tl : list a). r). λ(nil : r). r
}

-- LIST synthesizes successfully (it's well-formed)
example : (synth 200 [] LIST).isSome = true := by native_decide

-- LIST <= T trivially
example : check 100 [] LIST .top = true := by native_decide

-- D2: MAP over lists
-- ASPIRATIONAL: needs LIST + recursive function typing
-- Flip condition: LIST + Sub.muR

-- D3: Factorial
-- ASPIRATIONAL: needs MUL + PRED + thunking
-- Flip condition: Full arithmetic + thunking strategy

-- D4: TREE encoding — defined, well-formedness checks
def TREE : Expr := soch{
  μ(tree : ⊤). λ(a : ⊤). λ(r : ⊤).
    λ(leaf : λ(x : a). r). λ(node : λ(l : tree a). λ(r' : tree a). r). r
}

example : (synth 200 [] TREE).isSome = true := by native_decide
example : check 100 [] TREE .top = true := by native_decide

-- ============================================================
-- Category E: Larger programs (composition of features)
-- ============================================================

-- E1: Boolean logic circuit: half adder
-- sum = XOR a b, carry = AND a b
-- This WORKS at the eval level:
private def halfAdderSum : Expr := soch{ λ(a : BOOL). λ(b : BOOL). XOR a b }
private def halfAdderCarry : Expr := soch{ λ(a : BOOL). λ(b : BOOL). AND a b }

-- Half adder evaluation tests (these PASS)
-- 0 + 0 = (sum=0, carry=0)
example : ev (.app (.app (.app (.app (.app halfAdderSum FALSE) FALSE) .top) x42) x99)
  = some x99 := rfl
example : ev (.app (.app (.app (.app (.app halfAdderCarry FALSE) FALSE) .top) x42) x99)
  = some x99 := rfl
-- 1 + 0 = (sum=1, carry=0)
example : ev (.app (.app (.app (.app (.app halfAdderSum TRUE) FALSE) .top) x42) x99)
  = some x42 := rfl
example : ev (.app (.app (.app (.app (.app halfAdderCarry TRUE) FALSE) .top) x42) x99)
  = some x99 := rfl
-- 0 + 1 = (sum=1, carry=0)
example : ev (.app (.app (.app (.app (.app halfAdderSum FALSE) TRUE) .top) x42) x99)
  = some x42 := rfl
example : ev (.app (.app (.app (.app (.app halfAdderCarry FALSE) TRUE) .top) x42) x99)
  = some x99 := rfl
-- 1 + 1 = (sum=0, carry=1)
example : ev (.app (.app (.app (.app (.app halfAdderSum TRUE) TRUE) .top) x42) x99)
  = some x99 := rfl
example : ev (.app (.app (.app (.app (.app halfAdderCarry TRUE) TRUE) .top) x42) x99)
  = some x42 := rfl

-- E1 ASPIRATIONAL: halfAdderSum : BOOL -> BOOL -> BOOL — FLIPPED
example : check 500 [] halfAdderSum (soch{ BOOL → BOOL → BOOL }) = true := by native_decide

-- E1b: halfAdderCarry : BOOL -> BOOL -> BOOL — FLIPPED
example : check 500 [] halfAdderCarry (soch{ BOOL → BOOL → BOOL }) = true := by native_decide

-- E2: Composition: COMPOSE f g x = f (g x)
private def COMPOSE : Expr :=
  soch{ λ(a : ⊤). λ(b : ⊤). λ(c : ⊤).
    λ(f : b → c). λ(g : a → b). λ(x : a). f (g x) }

-- Compose id id = id (PASSES)
private def idFnE : Expr := soch{ λ(x : ⊤). x }
example : ev (.app (.app (.app (.app (.app (.app COMPOSE .top) .top) .top) idFnE) idFnE) x42)
  = some x42 := rfl

-- Compose NOT NOT = id on booleans (PASSES)
example : ev (.app (.app (.app (.app (.app (.app (.app (.app (.app COMPOSE BOOL) BOOL) BOOL) NOT) NOT) TRUE) .top) x42) x99)
  = some x42 := rfl
example : ev (.app (.app (.app (.app (.app (.app (.app (.app (.app COMPOSE BOOL) BOOL) BOOL) NOT) NOT) FALSE) .top) x42) x99)
  = some x99 := rfl

-- E3: SWAP works at value level (PASSES)
private def swapped : Expr := .app (.app (.app SWAP .top) .top) (.app (.app (.app (.app MkPair .top) .top) x42) x99)
example : ev (.app (.app (.app FST .top) .top) swapped) = some x99 := rfl
example : ev (.app (.app (.app SND .top) .top) swapped) = some x42 := rfl

-- E4: Triple via nested pairs (PASSES)
private def TRIPLE_VAL : Expr :=
  soch{ λ(a : ⊤). λ(b : ⊤). λ(c : ⊤). λ(x : a). λ(y : b). λ(z : c).
    MkPair ⊤ ⊤ x (MkPair ⊤ ⊤ y z) }

private def tripleTest : Expr :=
  .app (.app (.app (.app (.app (.app TRIPLE_VAL .top) .top) .top) x1) x2) x3

example : ev (.app (.app (.app FST .top) .top) tripleTest)
  = some x1 := rfl

-- E5: Natural number arithmetic pipeline (PASSES at eval level)
-- ADD (ADD ONE ONE) (ADD ONE ONE) with identity successor
-- This should give 4 applications of id to z, i.e. z
private def idFn2 : Expr := soch{ λ(x : ⊤). x }
example : ev (.app (.app (.app (.app (.app ADD (.app (.app ADD ONE) ONE)) (.app (.app ADD ONE) ONE)) .top) x99) idFn2)
  = some x99 := rfl

-- E5 ASPIRATIONAL: ADD (ADD ONE ONE) (ADD ONE ONE) <= NAT — STILL ASPIRATIONAL
-- Same issue as B5: nested additions build up complexity beyond the fuel bound.
-- example : check 1000 [] (soch{ ADD (ADD ONE ONE) (ADD ONE ONE) }) NAT = true := by native_decide

-- E6: Church encoding of maybe/option type (PASSES at eval level)
private def MAYBE : Expr := soch{ λ(a : ⊤). λ(r : ⊤). λ(just : a → r). λ(nothing : r). r }
private def JUST : Expr := soch{ λ(a : ⊤). λ(x : a). λ(r : ⊤). λ(just : a → r). λ(nothing : r). just x }
private def NOTHING : Expr := soch{ λ(a : ⊤). λ(r : ⊤). λ(just : a → r). λ(nothing : r). nothing }

-- JUST T (var 42) with an extractor -> var 42
private def idExtractor : Expr := soch{ λ(x : ⊤). x }
example : ev (.app (.app (.app (.app (.app JUST .top) x42) .top) idExtractor) x99) = some x42 := rfl
-- NOTHING T with an extractor -> var 99
example : ev (.app (.app (.app (.app NOTHING .top) .top) idExtractor) x99) = some x99 := rfl

-- E6 ASPIRATIONAL: JUST <= MAYBE — STILL ASPIRATIONAL
-- Requires complex lambda body reasoning across the JUST lambda (which
-- takes additional arguments before becoming a maybe-like value).
-- example : check 1000 [] (soch{ JUST ⊤ }) (soch{ MAYBE ⊤ }) = true := by native_decide

-- E7: Leibniz equality
private def EQ : Expr := soch{ λ(a : ⊤). λ(x : a). λ(y : a). λ(P : a → ⊤). P x → P y }
private def REFL_EQ : Expr := soch{ λ(a : ⊤). λ(x : a). λ(P : a → ⊤). λ(px : P x). px }

-- REFL_EQ T (var 42) returns the identity on P (var 42)
-- Applied to a motive and proof: REFL_EQ T x P px = px
example : ev (.app (.app (.app (.app REFL_EQ .top) x42) (soch{ λ(_ : ⊤). ⊤ })) .top) = some .top := rfl

-- ASPIRATIONAL: REFL_EQ a x : EQ a x x
-- Needs the lambda proof to check against the EQ type
-- Flip condition: careful Sub derivation
-- example : Sub [] (REFL_EQ applied) (EQ applied) := ...

-- ============================================================
-- Summary of aspirational test counts by category (as of Bidir.lean)
-- ============================================================
-- Category A (self-type intro — muR):
--     FLIPPED: A1 (dtrue ⊑ dBool), A2 (dfalse ⊑ dBool), A3 (dzero ⊑ dNat)
--     STILL ASPIRATIONAL: A4 (done_ ⊑ dNat), A5 (dtwo ⊑ dNat),
--                         A6 (dnot ⊑ dBool → dBool), A7 (dand), A8 (disZero)
-- Category B (BetaR on RHS):
--     FLIPPED: B1, B2, B3, B4
--     STILL ASPIRATIONAL: B5 (MUL TWO THREE)
-- Category C (CBV):       3 tests — out of scope (CBV deferred)
-- Category D (Recursive types):
--     D1: LIST encoding DEFINED and well-formedness CHECKED.
--     D2-D4: STILL ASPIRATIONAL
-- Category E:
--     FLIPPED: E1 (halfAdderSum ⊑ BOOL → BOOL → BOOL)
--     STILL ASPIRATIONAL: E5 (nested ADD), E6 (JUST ⊑ MAYBE), E7 (REFL_EQ)
-- Total FLIPPED: 8 tests + LIST well-formedness
-- Total STILL ASPIRATIONAL: ~14 tests (many behind shared "dependent elim" gap)

end Och.Simple.Std.Aspirational
