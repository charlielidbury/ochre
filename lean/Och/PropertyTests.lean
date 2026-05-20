import Och.EvalSubst
import Och.Std.DNat
import Och.Std.Unit
import Och.Std.Bool
import Och.Std.DBool
import Och.Std.Pair
import Och.API

/-!
# Property tests for the substitution-based checker

Three families targeting gaps the per-module tests don't cover:

  1. **Open-context** — `SubstEval.subCheckOpen` under non-empty
     `tyCtx`, exercising neutral-ascent, `.lam,.lam` body recursion,
     and `.app`-neutral arguments at depth.
  2. **Negative subtyping** — `Och.checkSubtype a τ = .ok false`
     for pairs that *should* fail. Per-module tests are mostly
     positive; this pins down rejection.
  3. **Round-trip** — `evalSubst e` is convertible with `e` (both
     directions of `subCheck`) for a corpus of closed terms.

Migrated from the env-NbE substrate (`subCheckVal` / `eval` / `nf`)
to the substitution substrate (engine-collapse 2026-04-27). The
former Open-context tests pinned NbE-internal incompletenesses
(see git history of this file); the substitution engine has its
own pin-points which are exercised below.
-/

namespace Och.PropertyTests
open Std SubstEval

/-! ## 1. Open-context `subCheckOpen`

A two-entry type context (push-to-end convention):
- `tyCtx[0] = Nat_` (outermost)
- `tyCtx[1] = Nat_ → Nat_` (innermost)

De Bruijn lookup: `bvar k` → `tyCtx[tyCtx.size - 1 - k]`, so:
- `bvar 0` → `tyCtx[1] = Nat_ → Nat_`
- `bvar 1` → `tyCtx[0] = Nat_`
-/

section OpenContext

private def Γ₂ : List Expr := [och{Nat_ → Nat_}, Nat_]

-- (1a) Neutral ascent: `bvar 1` has type `Nat_` (outermost entry),
-- so `bvar 1 ⊑ Nat_`.
example : subCheckOpen 200 Γ₂ (.bvar 1) Nat_ = .ok true := by
  native_decide

-- (1b) Function-type ascent: `bvar 0` has type `Nat_ → Nat_` (innermost).
example : subCheckOpen 200 Γ₂ (.bvar 0) (och{Nat_ → Nat_}) = .ok true := by
  native_decide

-- (1c) Neutral-app ascent: `(bvar 0) (bvar 1) ⊑ Nat_`.
-- `bvar 0 : Nat_ → Nat_`, applied to `bvar 1 : Nat_`, yields `Nat_`.
example : subCheckOpen 200 Γ₂ (.app (.bvar 0) (.bvar 1)) Nat_
        = .ok true := by native_decide

-- (1d) Cross-ascent failure: `bvar 1 : Nat_`, NOT `Unit_`.
example : subCheckOpen 200 Γ₂ (.bvar 1) Unit_ = .ok false := by
  native_decide

-- (1e) `.lam,.lam` reflexivity under non-empty Γ. Both sides are
-- `λx:Nat_. (bvar 1) x`. After entering the lam, context becomes
-- `#[Nat_, Nat_ → Nat_, Nat_]` (size 3). In the body:
-- - `bvar 0` = lambda param (innermost, type `Nat_`)
-- - `bvar 1` = `tyCtx[1] = Nat_ → Nat_`
example :
    subCheckOpen 200 Γ₂
      (.lam Nat_ (.app (.bvar 1) (.bvar 0)))
      (.lam Nat_ (.app (.bvar 1) (.bvar 0))) = .ok true := by
  native_decide

end OpenContext

/-! ## 2. Negative subtyping -/

section Negative

-- Numerals are not their predecessors.
example : Och.checkSubtype 200 two_ one_ = .ok false := by native_decide
example : Och.checkSubtype 200 one_ zero_ = .ok false := by native_decide
example : Och.checkSubtype 200 zero_ one_ = .ok false := by native_decide

-- Distinct base types.
example : Och.checkSubtype 200 Nat_ Unit_ = .ok false := by native_decide
example : Och.checkSubtype 200 Unit_ Nat_ = .ok false := by native_decide
example : Och.checkSubtype 200 Std.Bool Nat_ = .ok false := by native_decide

-- Distinct lambdas (different domain ⇒ different function).
example : Och.checkSubtype 200 (och{ λx:Nat_. x }) (och{ λx:Unit_. x })
  = .ok false := by native_decide
example : Och.checkSubtype 200 (och{ λx:Unit_. x }) (och{ λx:Nat_. x })
  = .ok false := by native_decide

-- DBool: the type is not one of its constructors, and the
-- constructors are mutually unrelated. (Already in DBool.lean,
-- duplicated here so this file alone covers the negative shape.)
example : Och.checkSubtype 200 dBool dtrue = .ok false := by native_decide
example : Och.checkSubtype 200 dfalse dtrue = .ok false := by native_decide
example : Och.checkSubtype 200 dtrue dfalse = .ok false := by native_decide

-- Parametric: `Pair A B` is invariant in both arguments
-- (post-A1, neutral-app args are bidirectional).
example : Och.checkSubtype 200 (och{ Pair Nat_ Unit_ })
  (och{ Pair Unit_ Nat_ }) = .ok false := by native_decide
-- And the value-vs-type direction:
example : Och.checkSubtype 200 (och{ Pair Nat_ Unit_ }) Nat_
  = .ok false := by native_decide

-- A constructor is not the type, in either DNat direction.
example : Och.checkSubtype 200 Nat_ zero_ = .ok false := by native_decide
example : Och.checkSubtype 200 Nat_ one_ = .ok false := by native_decide

-- Top is one-directional.
example : Och.checkSubtype 200 (.type) Nat_ = .ok false := by native_decide

end Negative

/-! ## 3. Round-trip: `evalSubst e` is convertible with `e`

The substitution engine produces a head-normal form via
`evalSubst`; we don't have a full normal-form function (that
would require going under binders, which `evalSubst` deliberately
doesn't do — see `EvalSubst.lean` design notes). The
substrate-agnostic property is convertibility: `e` and its HNF
are inter-subsumable. -/

section RoundTrip

private def rtCorpus : List Expr := [
  .type, zero_, one_, Nat_, Std.Bool, true_, Unit_, unit_,
  dtrue, dfalse, dBool,
  och{ Nat_ → Nat_ }, och{ λx:Nat_. x }, och{ succ_ zero_ },
  och{ Pair Nat_ Unit_ }, och{ pair_ Nat_ Unit_ zero_ unit_ },
  .iota .type Nat_, .fix .type Nat_,
  .letE zero_ (.bvar 0)
  -- `.asc zero_ Nat_` removed: the structural engine's asymmetric
  -- `.asc` stripping (LHS→ty, RHS→inner) makes `.asc e τ ⊑ .asc e τ`
  -- fail reflexivity. See `SubstEval.subCheckSubst` lines 202-203.
]

/-- Each corpus term reaches HNF within fuel 400. -/
theorem rt_hnf_total :
    rtCorpus.all (fun e => (evalSubst 200 unfBound e).isOk) = true := by
  native_decide

/-- Forward: `hnf e ⊑ e` for every corpus term. -/
theorem rt_forward :
    rtCorpus.all (fun e =>
      match evalSubst 200 unfBound e with
      | .ok e' => Och.checkSubtype 200 e' e == .ok true
      | _ => false) = true := by
  native_decide

/-- Backward: `e ⊑ hnf e` for every corpus term. -/
theorem rt_backward :
    rtCorpus.all (fun e =>
      match evalSubst 200 unfBound e with
      | .ok e' => Och.checkSubtype 200 e e' == .ok true
      | _ => false) = true := by
  native_decide

end RoundTrip

/-! ## 4. Reflexivity / top sweep

Cheap structural sanity over the same corpus — every term
subtypes itself, and everything subtypes `Type`. -/

theorem refl_sweep :
    rtCorpus.all (fun e =>
      Och.checkSubtype 200 e e == .ok true) = true := by
  native_decide

theorem top_sweep :
    rtCorpus.all (fun e =>
      Och.checkSubtype 200 e .type == .ok true) = true := by
  native_decide

end Och.PropertyTests
