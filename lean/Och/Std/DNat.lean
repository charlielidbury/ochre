import Och.Macro
import Och.Eval
import Och.SubCheckVal
import Och.Std.Bool
import Och.Std.Nat

/-!
# Dependent Naturals (self-type encoding)

Scott-style dependent Nat where the return type of elimination depends
on the value being eliminated.

```
dNat = ι(dNat : Type).
  let dzero = ι(dzero : dNat). λP:(dzero→Type). λz:(P dzero). λs:Type. z in
  let dsucc = fix(dsucc : dNat→dNat).
    λm:dNat. λP:((dsucc m)→Type). λz:Type. λs:(λpred:dNat. P (dsucc pred)). s m in
  λP:(dNat→Type). λz:(P dzero). λs:(λpred:dNat. P (dsucc pred)). P dNat
```

Split rationale:
- `dNat` uses `fix N:Type. ι self:N. …` (matching dBool, e08bce9). The
  outer `fix` binds the *type* `N`, used in every type ascription
  (`λm:N`, `λpred:N`, `dsucc:(N→N)`); the inner `ι` binds the *value*
  `self`, used only in the final `P self`. iotaIntro substitutes `self`
  (so `P self` becomes `P done_` when checking `done_ ⊑ dNat`), but `N`
  stays `N` (= dNat after fix-unfold), so `λpred:N` doesn't
  over-specialise. Under the previous ι-only encoding, `λpred:bvar0`
  became `λpred:done_` after iotaIntro and the contravariant check
  required `dNat ⊑ done_` — making `done_ ⊑ dNat` unsatisfiable.
- `dzero` uses `ι` alone — its self-reference is for the motive domain
  (`λP:(dzero→Type)`), not type ascriptions on other binders.
- `dsucc` uses `fix` — genuine recursion on the constructor term.

Key design:
- Each constructor constrains P's domain to ITSELF (not dNat). This is
  essential for self-type intro: when checking dzero ⊑ dNat, the self-type
  substitution replaces dNat with dzero in the body, making the P domain
  check reflexive (dzero→Type ⊑ dzero→Type).
- dsucc's body references `dsucc` via `fix`-style unfolding so that
  `P (dsucc pred)` expresses "motive applied to the successor of pred".
- Usage still works: passing P:(dNat→Type) needs (dNat→Type) ⊑ (dzero→Type),
  which by contravariance needs dzero ⊑ dNat — exactly what we just proved.
- dzero has `λs:Type` (s unused, domain is Top for covariance).
- The body `s m` has type `P (dsucc m)` — fully dependent.
-/

namespace Std

-- ============================================================
-- Type and constructors
-- ============================================================

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

def done_ := och{ dsucc dzero }
def dtwo  := och{ dsucc done_ }
def dthree := och{ dsucc dtwo }

-- ============================================================
-- Operations
-- ============================================================

-- isZero: non-dependent case analysis
def disZero := och{
  λn:dNat. n (λ_:dNat. Std.Bool) Std.true_ (λpred:dNat. Std.false_)
}

-- predecessor (Scott-style: direct access, no recursion needed)
def dpred := och{
  λn:dNat. n (λ_:dNat. dNat) dzero (λpred:dNat. pred)
}

-- ============================================================
-- Tests
-- ============================================================

section Tests

-- ── Positive computation tests (concEval) ───────────────────

example : concEval 200 (och{ disZero dzero }) = some Std.true_ := by native_decide
example : concEval 200 (och{ disZero done_ }) = some Std.false_ := by native_decide
example : concEval 200 (och{ disZero dtwo }) = some Std.false_ := by native_decide

example : concEval 200 (och{ dpred dzero }) = concEval 200 dzero := by native_decide
example : concEval 200 (och{ dpred done_ }) = concEval 200 dzero := by native_decide
example : concEval 200 (och{ dpred dtwo }) = concEval 200 done_ := by native_decide

-- ── Dependent elimination ───────────────────────────────────

-- depMotive: dzero → Nat_, dsucc _ → Bool
private def depMotive := och{
  λn:dNat. n (λ_:dNat. Type) Nat_ (λpred:dNat. Std.Bool)
}

example : concEval 200 (och{ depMotive dzero }) = concEval 200 Nat_ := by native_decide
example : concEval 200 (och{ depMotive done_ }) = concEval 200 Std.Bool := by native_decide

-- Different branches return values of DIFFERENT types
private def depElim := och{
  λn:dNat. n depMotive zero_ (λpred:dNat. Std.true_)
}

example : concEval 200 (och{ depElim dzero }) = some zero_ := by native_decide
example : concEval 200 (och{ depElim done_ }) = some Std.true_ := by native_decide

-- ── Positive subtype checks ─────────────────────────────────

-- dzero ⊑ dNat: the direct analogue of dtrue ⊑ dBool.
example : subCheck 200 dzero dNat = .ok true := by native_decide

-- done_ ⊑ dNat. Closed by wrapping dNat in `fix N:Type. ι self:N.
-- …` (matching dBool's e08bce9 pattern): the *type* binder N is
-- stable under iotaIntro, so `λpred:N` stays `λpred:dNat` after
-- substituting `self := done_`, and the contravariant check is
-- reflexive. Under the previous ι-only encoding, `λpred:bvar0`
-- became `λpred:done_` and the contra needed `dNat ⊑ done_`,
-- which is correctly false — done_ would call `s dzero` but the
-- caller's `s` would expect `pred:done_`, and `dzero ⊄ done_`.
example : subCheck 200 done_ dNat = .ok true := by native_decide

-- dtwo/dthree ⊑ dNat. subCheckNF (Expr-domain) fans out here:
-- each dsucc layer copies the closed-`dNat` substituend into the
-- unfold path, so the term grows polynomially per fuel step. The
-- Val-domain checker (NbE.subCheckVal) shares substituends via
-- closure environments instead of copying, and with the
-- stuckRec-stuckRec structural arm it now closes both.
--
-- These assert against `NbE.subCheck` directly. Once subCheckNF
-- is retired in favour of subCheckVal (Phase 2 cleanup), all
-- assertions in this file move uniformly.
example : NbE.subCheck 800 dtwo dNat = .ok true := by native_decide
example : NbE.subCheck 1600 dthree dNat = .ok true := by native_decide
-- And under the same checker the earlier numerals + negatives
-- agree with subCheckNF, so no regression in semantics:
example : NbE.subCheck 400 dzero dNat = .ok true := by native_decide
example : NbE.subCheck 400 done_ dNat = .ok true := by native_decide
example : NbE.subCheck 400 dNat dzero = .ok false := by native_decide
example : NbE.subCheck 400 dzero done_ = .ok false := by native_decide

-- ── Negative subtype checks ─────────────────────────────────

-- dNat ⊄ dzero: dNat's eliminator demands both branches, dzero only
-- the zero branch.
example : subCheck 200 dNat dzero = .ok false := by native_decide

-- true_ ⊄ dNat: the Church boolean has the wrong shape.
example : subCheck 200 Std.true_ dNat = .ok false := by native_decide

-- dzero ⊄ done_. Previously returned `.ok true` because absEval's
-- muSeen cycle check compared (fix, arg) pairs and the de-Bruijn
-- shifted argument never matched, so dsucc' kept unfolding until
-- both sides looked identical. With the length-based muSeen cutoff
-- this is now correctly rejected.
example : subCheck 200 dzero done_ = .ok false := by native_decide

-- ── Negative computation tests ──────────────────────────────

example : concEval 200 (och{ disZero dzero }) ≠ some Std.false_ := by native_decide
example : concEval 200 (och{ disZero done_ }) ≠ some Std.true_ := by native_decide
example : concEval 200 (och{ dpred dtwo }) ≠ concEval 200 dzero := by native_decide
example : concEval 200 (och{ depElim dzero }) ≠ some Std.true_ := by native_decide
example : concEval 200 (och{ depElim done_ }) ≠ some zero_ := by native_decide

end Tests
end Std
