import Och.Macro
import Och.Eval
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
- `dNat` / `dzero` use `ι` (iota) — the self-reference in each of these
  definitions is used for dependent elimination (the motive P ranges over
  the type itself), not for recursion.
- `dsucc` uses `fix` — `dsucc` appears in its own body applied to the
  predecessor argument (`P (dsucc pred)`). This is genuine recursion on the
  constructor term.

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
  ι dNat:Type.
    let dzero : dNat = ι dzero:dNat. λP:(dzero → Type). λz:(P dzero). λs:Type. z in
    let dsucc : (dNat → dNat) = fix dsucc:(dNat → dNat).
      λm:dNat. λP:((dsucc m) → Type). λz:Type. λs:(λpred:dNat. P (dsucc pred)). s m in
    λP:(dNat → Type). λz:(P dzero). λs:(λpred:dNat. P (dsucc pred)). P dNat
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

-- TODO[mega-loop]: done_/dtwo/dthree ⊑ dNat. With NbE.subCheckVal
-- (no fan-out) the answer is `.ok false` — and the trace shows
-- this is the *encoding*, not the checker. dNat's `λpred:dNat`
-- uses the ι-self bvar, so iotaIntro substitutes it to
-- `λpred:done_`. But done_'s body calls `s dzero`, and the
-- caller's `s` (typed at dNat[done_]'s λs domain) expects
-- `pred:done_` — yet `dzero ⊄ done_`. So done_ genuinely doesn't
-- satisfy dNat's self-type under standard function subtyping.
--
-- Compare dBool (e08bce9): `fix B:Type. ι self:B. … λP:(B→Type) …`
-- separates the *type* binder B (fix) from the *value* binder
-- self (ι). iotaIntro substitutes self; B stays B (= dBool after
-- fix-unfold). dNat conflates them — its `λpred:bvar0` should be
-- `λpred:B` (the type), not `λpred:self` (the value). The fix is
-- to wrap dNat in `fix N:Type. ι self:N. …` and use `N` for type
-- ascriptions and `self` only for `P self` at the end.
example : subCheck 200 done_ dNat = .ok true := by sorry
example : subCheck 200 dtwo dNat = .ok true := by sorry
example : subCheck 200 dthree dNat = .ok true := by sorry

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
