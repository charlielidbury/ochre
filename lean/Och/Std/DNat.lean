import Och.Macro
import Och.Eval
import Och.Std.Bool
import Och.Std.Nat

/-!
# Dependent Naturals (self-type encoding)

Scott-style dependent Nat where the return type of elimination depends
on the value being eliminated.

```
dNat = μ(dNat : Type).
  let dzero = μ(dzero : dNat). λP:(dNat→Type). λz:(P dzero). λs:Type. z in
  λP:(dNat→Type). λz:(P dzero). λs:(λpred:dNat. λself:dNat. P self). P dNat

dzero = μ(dzero : dNat). λP:(dNat→Type). λz:(P dzero). λs:Type. z

dsucc = λm:dNat. μ(sn : dNat). λP:(dNat→Type). λz:Type.
  λs:(λpred:dNat. λself:dNat. P self). s m sn
```

Key design:
- The succ branch `s` receives both the predecessor and the successor
  value (via mu self-reference `sn`), with return type `P self`.
- This makes the `s` annotation identical in the type and constructor,
  so the contravariant domain check succeeds trivially.
- The body `s m sn` has type `P sn = P (dsucc m)` — fully dependent.
- dzero has `λs:Type` (s unused, domain is Top for covariance).
-/

namespace Std

-- ============================================================
-- Type and constructors
-- ============================================================

def dNat := och{
  μ dNat:Type.
    let dzero : dNat = μ dzero:dNat. λP:(dNat → Type). λz:(P dzero). λs:Type. z in
    λP:(dNat → Type). λz:(P dzero). λs:(λpred:dNat. λself:dNat. P self). P dNat
}

def dzero := och{
  μ dzero:dNat. λP:(dNat → Type). λz:(P dzero). λs:Type. z
}

def dsucc := och{
  λm:dNat. μ sn:dNat. λP:(dNat → Type). λz:Type. λs:(λpred:dNat. λself:dNat. P self). s m sn
}

def done   := och{ dsucc dzero }
def dtwo   := och{ dsucc done }
def dthree := och{ dsucc dtwo }

-- ============================================================
-- Operations
-- ============================================================

-- isZero: non-dependent case analysis
def disZero := och{
  λn:dNat. n (λself:dNat. Std.Bool) Std.true_ (λpred:dNat. λself:dNat. Std.false_)
}

-- predecessor (Scott-style: direct access, no recursion needed)
def dpred := och{
  λn:dNat. n (λself:dNat. dNat) dzero (λpred:dNat. λself:dNat. pred)
}

-- ============================================================
-- Tests
-- ============================================================

section Tests

-- ── Positive computation tests (concEval) ───────────────────

-- isZero dzero = true
example : concEval 200 (och{ disZero dzero }) = some Std.true_ := by native_decide

-- isZero (dsucc dzero) = false
example : concEval 200 (och{ disZero done }) = some Std.false_ := by native_decide

-- isZero (dsucc (dsucc dzero)) = false
example : concEval 200 (och{ disZero dtwo }) = some Std.false_ := by native_decide

-- pred dzero = dzero
example : concEval 200 (och{ dpred dzero }) = concEval 200 dzero := by native_decide

-- pred (dsucc dzero) = dzero
example : concEval 200 (och{ dpred done }) = concEval 200 dzero := by native_decide

-- pred (dsucc (dsucc dzero)) = dsucc dzero
example : concEval 200 (och{ dpred dtwo }) = concEval 200 done := by native_decide

-- ── Dependent elimination ───────────────────────────────────

-- depMotive: dzero → Nat_, dsucc _ → Bool
-- Uses dNat's own eliminator for type-level computation
private def depMotive := och{
  λn:dNat. n (λself:dNat. Type) Nat_ (λpred:dNat. λself:dNat. Std.Bool)
}

-- depMotive dzero = Nat_
example : concEval 200 (och{ depMotive dzero })
  = concEval 200 Nat_ := by native_decide

-- depMotive (dsucc dzero) = Bool
example : concEval 200 (och{ depMotive done })
  = concEval 200 Std.Bool := by native_decide

-- Dependent elimination: f dzero = zero_ : Nat_, f (dsucc _) = true_ : Bool
-- Different branches return values of DIFFERENT types!
private def depElim := och{
  λn:dNat. n depMotive zero_ (λpred:dNat. λself:dNat. Std.true_)
}

example : concEval 200 (och{ depElim dzero }) = some zero_ := by native_decide
example : concEval 200 (och{ depElim done }) = some Std.true_ := by native_decide

-- ── Positive subtype checks ─────────────────────────────────

-- constructors are subtypes of dNat
example : subCheck 200 dzero dNat = true := by native_decide
example : subCheck 200 done dNat = true := by native_decide
example : subCheck 200 dtwo dNat = true := by native_decide
example : subCheck 200 dthree dNat = true := by native_decide

-- ── Negative computation tests ──────────────────────────────

-- isZero dzero ≠ false
example : concEval 200 (och{ disZero dzero }) ≠ some Std.false_ := by native_decide

-- isZero done ≠ true
example : concEval 200 (och{ disZero done }) ≠ some Std.true_ := by native_decide

-- pred dtwo ≠ dzero (pred 2 = 1, not 0)
example : concEval 200 (och{ dpred dtwo }) ≠ concEval 200 dzero := by native_decide

-- depElim dzero ≠ true (it's zero_, a Nat)
example : concEval 200 (och{ depElim dzero }) ≠ some Std.true_ := by native_decide

-- depElim done ≠ zero_ (it's true_, a Bool)
example : concEval 200 (och{ depElim done }) ≠ some zero_ := by native_decide

-- ── Negative subtype checks ─────────────────────────────────

-- dNat is not a subtype of dzero (it's wider)
example : subCheck 200 dNat dzero = false := by native_decide

-- dzero is not done
example : subCheck 200 dzero done = false := by native_decide

-- a Church Bool is not a dNat
example : subCheck 200 Std.true_ dNat = false := by native_decide

end Tests
end Std
