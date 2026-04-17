import Och.SubCheckVal
import Och.TyCheck
import Och.Eval
import Och.Std.Pair
import Och.Std.Nat
import Och.Std.Bool
import Och.Std.Unit

/-!
# Phase 2: Soundness audit

Executable witnesses for soundness gaps in the Phase-1 checkers.
Each `theorem` here is a *true fact about the current algorithm*
(provable by `native_decide`); the surrounding prose explains why
that fact is a soundness problem.

These are deliberately phrased as positive assertions about the
checker's *current behaviour* so that fixing the underlying rule
will make this file fail to compile — at which point the entry
should be moved to a "resolved" section with the new behaviour
asserted instead.
-/

namespace SoundnessAudit
open Std

/-!
## A1: Covariant neutral-app congruence — RESOLVED

**Was**: `subCheckNeutral`'s `.app, .app` arm (and the analogous
`.stuckRec, .stuckRec` arms) compared arguments *covariantly*:
`n a ⊑ n b` whenever `a ⊑ b`. With the old `Pair l r = λk. k l r`
encoding, this gave `Pair zero_ unit_ ⊑ Pair Nat_ Unit_` via
`k zero_ unit_ ⊑ k Nat_ Unit_` — but eliminating with
`kContra = λn. λu. n → Unit_` β-reduced both sides to
`zero_ → Unit_` and `Nat_ → Unit_`, which are *not* related.
Substitution-principle violation.

**Fix** (this commit):
  - `subCheckNeutral` and `subCheckVal`'s neutral-app arms now
    require *equivalence* (`a ⊑ b ∧ b ⊑ a`), not just `a ⊑ b`.
    Same in `subCheckNF`'s `.app, .app` arm.
  - `Pair` re-encoded as `λA. λB. λX. λk:(A→B→X). X` (parametric
    body) with a separate `pair_ A B a b = λX. λk. k a b`
    constructor. `pair_ A B a b ⊑ Pair A B` now holds via
    *type-ascent* through `k` (synth `k a b : X`, then `X ⊑ X`)
    rather than congruence.

The new `Pair` is *soundly* covariant: `A ⊑ A' ∧ B ⊑ B' → Pair
A B ⊑ Pair A' B'` because A, B occur only contravariantly in
`k`'s domain (contra² = covariant) and the body `X` doesn't
mention them.
-/

/-- Bidirectional rule: a fresh neutral applied to non-equivalent
args is *not* congruent. With the old covariant rule this was
`true`; now it's `false`. -/
theorem a1_ruleFixed :
    subCheck 200
      (och{ λk:(Nat_ → Type). k zero_ })
      (och{ λk:(Nat_ → Type). k Nat_  })
      = .ok false ∧
    NbE.subCheck 200
      (och{ λk:(Nat_ → Type). k zero_ })
      (och{ λk:(Nat_ → Type). k Nat_  })
      = .ok false := by
  native_decide

/-- The new `Pair` is soundly covariant: the substitution
principle holds at `kContra` (both sides reduce to
`λk:(... → kContra). kContra`, which are contra²-related). -/
private def kContra := och{ λn:Nat_. λu:Unit_. n → Unit_ }

theorem a1_substitutionHolds :
    subCheck 200 (och{ Pair zero_ unit_ }) (och{ Pair Nat_ Unit_ })
      = .ok true ∧
    subCheck 200 (och{ (Pair zero_ unit_) kContra })
                 (och{ (Pair Nat_  Unit_) kContra })
      = .ok true := by
  native_decide

/-- And the constructor inhabits the type via ascent. -/
theorem a1_pairAscent :
    subCheck 200 (och{ pair_ Nat_ Unit_ zero_ unit_ })
                 (och{ Pair Nat_ Unit_ })
      = .ok true ∧
    NbE.subCheck 200 (och{ pair_ Nat_ Unit_ zero_ unit_ })
                     (och{ Pair Nat_ Unit_ })
      = .ok true := by
  native_decide

/-!
## A2: Type-in-type

Both checkers have `_ ⊑ Type → true` (SubCheckVal.lean:72,201;
Eval.lean's subCheckNF likewise). This is `Type : Type`, which
admits Girard's paradox.
-/

theorem a2_typeInType :
    subCheck 50 Nat_ .type = .ok true ∧
    subCheck 50 .type .type = .ok true ∧
    NbE.subCheck 50 (och{ Nat_ → Type }) .type = .ok true := by
  native_decide

/-!
This is almost certainly an *intentional* simplification — the
Pair.lean doc relies on it ("since everything is `<: Type`"), and
`fst_`/`snd_` use `Pair Type Type` as a universal pair domain.
Stratifying into `Type₀ : Type₁ : …` is the standard fix and
mostly mechanical (every `Type` annotation gets a level index)
but invasive. For Phase 2, the soundness theorem should be
stated *modulo* this: e.g. "subCheckVal is sound for terms whose
types live at a fixed universe level", or take Type-in-type as
an axiom of the model.

## A3: absEval β is type-blind

`absEval`'s `.lam` β arm (Eval.lean:160) substitutes
unconditionally, so `subCheckNF` is only meaningful on
*already-well-typed* inputs. `NbE.eval` likewise. The Phase-1
fix is `NbE.typeCheck` (TyCheck.lean), which runs the domain
check syntactically; the Phase-2 statement is therefore
"`typeCheck e τ = .ok true → e : τ`", not "`subCheck e τ = .ok
true → e : τ`".
-/

private def illTyped := och{ (λn:Nat_. n) Bool }

theorem a3_subCheckBlind :
    subCheck 200 illTyped Bool = .ok true ∧
    NbE.subCheck 200 illTyped Bool = .ok true := by
  native_decide

/-- …but `typeCheck` catches it. -/
theorem a3_typeCheckCatches :
    (NbE.typeCheck 200 illTyped Bool).isOk = false := by
  native_decide

/-!
## Summary

| # | Rule | Status | Fix |
|---|------|--------|-----|
| A1 | covariant neutral-app | **resolved** | bidirectional + re-encoded Pair |
| A2 | `_ ⊑ Type` | open (Girard) | universe levels, or accept as axiom |
| A3 | β type-blind | mitigated | use `typeCheck` as the entry point |

All other subCheckVal arms (refl, seen, lam-lam, iotaIntro,
fix-unfold, neutralAscent) follow standard sound rules. The
Phase-2 soundness theorem targets `typeCheck` with A2 either
stratified or assumed.
-/

end SoundnessAudit
