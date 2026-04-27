import Och.Macro
import Och.Eval
import Och.SubCheckVal
import Och.Std.Bool
import Och.TypedNbE
import Och.EvalSubst

/-!
# Unified Natural Numbers (self-type encoding with singleton-tightened succ)

Scott-style dependent Nat where the return type of elimination depends on
the value being eliminated. This is the single Nat in Och — the previous
Church-style `Std.Nat` has been retired. All downstream consumers
(`Std.Bool`, `Std.Pair`, `Std.Sigma`, `Std.Mu`, `Std.Id`, `Std.DBool`,
`Std.Array`, `Std.Vec`) use this `Nat_`.

```
zero_ = ι self:Type. λP:(self→Type). λz:(P self). λs:Type. z
Nat_  = fix N:Type. ι self:N.
  let succ_ = fix(succ_ : N→N).
    λm:N. λP:((succ_ m)→Type). λz:Type. λs:(λpred:m. P (succ_ pred)). s m in
  λP:(N→Type). λz:(P zero_). λs:(λpred:N. P (succ_ pred)). P self
succ_ = fix succ_:(Nat_→Nat_). λm:Nat_. … (same body, with Nat_ for N)
```

## Encoding choices

- `zero_` is defined *before* `Nat_` with the very-dependent motive
  `P:(self → Type)` and placeholder annotation `Type`.
- `Nat_` uses `fix N:Type. ι self:N. …`. The outer `fix` binds the *type*
  `N`, used in `λm:N`, `λpred:N`, `succ_:(N→N)`; the inner `ι` binds the
  *value* `self`. `iotaIntro` substitutes `self` but `N` stays `N`
  (= Nat_ after fix-unfold), so `λpred:N` doesn't over-specialise.
- `succ_` keeps a local-let copy inside `Nat_`. Its body uses `λpred:N`
  (the fix-binder); the top-level `succ_` uses `λpred:Nat_` instead.
  Semantically equal but structurally distinct closures (DECISION-LOG
  2026-04-18, A6).
- **Option A singleton tightening** (the key ingredient for Option F
  DFin): `succ_`'s `s`-branch has domain `pred:m` (singleton) rather
  than `pred:Nat_` (any Nat). Honest — the body calls `s m` with that
  exact value. See `Std.Fin` for why this matters.

## Key design

- Each constructor's motive domain is ITSELF (`self → Type`). When
  checking `zero_ ⊑ Nat_`, after iotaIntro substitutes `self ↦ zero_`
  on both sides, the P-domain check becomes `(N → Type) ⊑ (zero_ →
  Type)` → contravariant `zero_ ⊑ N` → closes via `.hyp`.
- `zero_` has `λs:Type` (s unused; domain is Top for covariance).
- `succ_ m` returns the raw λ-spine (no ι-wrap).
- The body `s m` has type `P (succ_ m)` — fully dependent.
-/

namespace Std

-- ============================================================
-- Type and constructors
-- ============================================================

/-- Zero. Very-dependent: motive domain is `self` (not `Nat_`),
annotation is the placeholder `Type`. Defined before `Nat_` so it
can be referenced directly from Nat_'s body. -/
def zero_ := och{
  λP:Type. λz:Type. λs:Type. z
}

def succ_ := och{
  λpred:Type. λP:Type. λz:Type. λs:(pred → Type). s pred
}

/-- Unified natural numbers. Singleton-tightened inner `succ_` (the
`s`-branch domain is `pred:m` instead of `pred:N`). This is the key
change that enables `Std.Fin`'s Option F encoding to subsume
`succ_ m ⊑ Fin (succ_ n)` directly, without a wrapper constructor. -/
def Nat_ := och{
  fix N. ι self:N.
    λP:(N → Type). λz:(P zero_). λs:(λpred:N. P (succ_ pred)). P self
}


def one_   := och{ succ_ zero_ }
def two_   := och{ succ_ one_ }
def three_ := och{ succ_ two_ }
def four_  := och{ succ_ three_ }
def five_  := och{ succ_ four_ }

-- ============================================================
-- Operations
-- ============================================================

-- isZero: non-dependent case analysis.
def isZero_ := och{
  λn:Nat_. n (λ_:Nat_. Std.Bool) Std.true_ (λpred:Nat_. Std.false_)
}

-- Predecessor (Scott-style: direct access, no recursion needed).
def pred_ := och{
  λn:Nat_. n (λ_:Nat_. Nat_) zero_ (λpred:Nat_. pred)
}

-- Addition. Scott-style Nat_ has no IH in the succ case, so we need an
-- explicit `fix`.
def add_ := och{
  fix add_:(Nat_ → Nat_ → Nat_).
    λn:Nat_. λm:Nat_.
      n (λ_:Nat_. Nat_) m (λpred:Nat_. succ_ (add_ pred m))
}

-- Doubling via addition.
def double_ := och{ λx:Nat_. add_ x x }

-- ============================================================
-- Tests
-- ============================================================

section Tests

-- ── Positive computation tests (concEval) ───────────────────

example : concEval 200 (och{ isZero_ zero_ }) = .ok Std.true_ := by native_decide
example : concEval 200 (och{ isZero_ one_ }) = .ok Std.false_ := by native_decide
example : concEval 200 (och{ isZero_ two_ }) = .ok Std.false_ := by native_decide

example : concEval 200 (och{ pred_ zero_ }) = concEval 200 zero_ := by native_decide
example : concEval 200 (och{ pred_ one_ }) = concEval 200 zero_ := by native_decide
example : concEval 200 (och{ pred_ two_ }) = concEval 200 one_ := by native_decide

-- ── Dependent elimination ───────────────────────────────────

-- depMotive: zero_ → (Type, here used as a placeholder 'metatype')
private def depMotive := och{
  λn:Nat_. n (λ_:Nat_. Type) Type (λpred:Nat_. Std.Bool)
}

example : concEval 200 (och{ depMotive zero_ }) = concEval 200 Expr.type := by native_decide
example : concEval 200 (och{ depMotive one_ }) = concEval 200 Std.Bool := by native_decide

-- Different branches return values of DIFFERENT types.
private def depElim := och{
  λn:Nat_. n depMotive Type (λpred:Nat_. Std.true_)
}

example : concEval 200 (och{ depElim zero_ }) = .ok Expr.type := by native_decide
example : concEval 200 (och{ depElim one_ }) = .ok Std.true_ := by native_decide

-- ── Positive subtype checks ─────────────────────────────────
--
-- NOTE: The Option A singleton-tightened `succ_` thread each
-- predecessor through the contra chain, so fuel scales with numeral
-- size. `two_ ⊑ Nat_` at fuel 800 works; `three_ ⊑ Nat_` takes
-- ~50k fuel. SoundnessAudit pins `two_ ⊑ Nat_` at fuel 800.

example : SubstEval.subCheckT 200 zero_ Nat_ = .ok true := by native_decide
example : SubstEval.subCheckT 200 one_ Nat_ = .ok true := by native_decide
example : SubstEval.subCheckT 800 two_ Nat_ = .ok true := by native_decide
-- three_/four_/five_ ⊑ Nat_ close fast via subCheckT's typeCheck
-- fast-path; bare subCheckVal hits the singleton-tower scaling and is
-- ~14s for three_, projected hours for five_. The typed wrapper makes
-- these tractable for both engines.
example : SubstEval.subCheckT 200 three_ Nat_ = .ok true := by native_decide
example : SubstEval.subCheckT 200 four_ Nat_ = .ok true := by native_decide
example : SubstEval.subCheckT 200 five_ Nat_ = .ok true := by native_decide
-- Same checks via the substitution-based subCheckT.
example : SubstEval.subCheckT 200 three_ Nat_ = .ok true := by native_decide
example : SubstEval.subCheckT 200 four_ Nat_ = .ok true := by native_decide
example : SubstEval.subCheckT 200 five_ Nat_ = .ok true := by native_decide

-- ── Negative subtype checks ─────────────────────────────────

example : SubstEval.subCheckT 200 Nat_ zero_ = .ok false := by native_decide
-- Note: under the permissive Bool encoding, `true_` and `zero_` are
-- structurally identical (both `λP:Type. λt:Type. λf:Type. t`), so
-- `true_ ⊑ Nat_` correctly succeeds. Use `Std.Bool` (the type) as
-- the non-Nat witness instead.
example : SubstEval.subCheckT 200 Std.Bool Nat_ = .ok false := by native_decide
example : SubstEval.subCheckT 200 zero_ one_ = .ok false := by native_decide

-- ── Computation tests for add_ / double_ ────────────────────
--
-- These tests now pass — the prior "multiple minutes" comment was
-- outdated by ~10x. The bench measurements (eval-subst-vs-env-
-- benchmark.md §6.5) confirm both `concEval` and substitution-based
-- eval close `add_ one_ two_ = three_` in ~22 ms.

example : concEval 1000 (och{ add_ zero_ two_ }) = concEval 1000 two_ := by native_decide
example : concEval 1000 (och{ add_ one_ one_ }) = concEval 1000 two_ := by native_decide
example : concEval 5000 (och{ add_ one_ two_ }) = concEval 5000 three_ := by native_decide
example : concEval 2000 (och{ double_ zero_ }) = concEval 2000 zero_ := by native_decide
example : concEval 5000 (och{ double_ one_ }) = concEval 5000 two_ := by native_decide

-- ── Negative computation tests ──────────────────────────────

example : concEval 200 (och{ isZero_ zero_ }) ≠ .ok Std.false_ := by native_decide
example : concEval 200 (och{ isZero_ one_ }) ≠ .ok Std.true_ := by native_decide
example : concEval 200 (och{ pred_ two_ }) ≠ concEval 200 zero_ := by native_decide

end Tests
end Std
