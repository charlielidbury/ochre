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
## A1: Covariant neutral-app congruence is unsound

`subCheckNeutral`'s `.app, .app` arm (and the analogous
`.stuckRec, .stuckRec` arm) compares arguments *covariantly*:
`n a ⊑ n b` whenever `a ⊑ b`. This was changed from bidirectional
in commit 4ca113b to make `Pair zero_ unit_ ⊑ Pair Nat_ Unit_`
(and hence `testArr1 ⊑ Array_ done_ Nat_`) pass.

But a neutral head `n` can use its argument at *any* variance.
The substitution principle says `a ⊑ b → C[a] ⊑ C[b]` for any
context `C`; taking `C = (· kContra)` where `kContra` is
contravariant in its first argument refutes this.
-/

private def kContra := och{ λn:Nat_. λu:Unit_. n → Unit_ }

/-- The checker accepts `Pair zero_ unit_ ⊑ Pair Nat_ Unit_`.

After β, both sides are `λk:(... → Type). k <l> <r>`, and the
body comparison `k zero_ unit_ ⊑ k Nat_ Unit_` goes through the
covariant `.app, .app` arm (k is a fresh neutral). -/
theorem a1_accepts :
    subCheck 200 (och{ Pair zero_ unit_ }) (och{ Pair Nat_ Unit_ })
      = .ok true ∧
    NbE.subCheck 200 (och{ Pair zero_ unit_ }) (och{ Pair Nat_ Unit_ })
      = .ok true := by
  native_decide

/-- Yet eliminating both sides with `kContra` is *rejected*.

`(Pair zero_ unit_) kContra` β-reduces to `zero_ → Unit_`;
`(Pair Nat_ Unit_) kContra` to `Nat_ → Unit_`. The checker
correctly says `zero_ → Unit_ ⊄ Nat_ → Unit_` (contravariant
domain needs `Nat_ ⊑ zero_`). -/
theorem a1_witness :
    subCheck 200 (och{ (Pair zero_ unit_) kContra })
                 (och{ (Pair Nat_  Unit_) kContra })
      = .ok false ∧
    NbE.subCheck 200 (och{ (Pair zero_ unit_) kContra })
                     (och{ (Pair Nat_  Unit_) kContra })
      = .ok false := by
  native_decide

/-!
`a1_accepts` and `a1_witness` together violate the substitution
principle: if `bad ⊑ Good` then for every well-typed `C`,
`C[bad] ⊑ C[Good]`. Here `C = (· kContra)` and `kContra` *is*
well-typed at the LHS's k-domain `(zero_ → unit_ → Type)` — its
declared domain `(Nat_ → Unit_ → Type)` is a subtype.

### Affected tests

The covariant rule is load-bearing for:
  - `Pair.lean:56` — `Pair one_ two_ ⊑ Pair Nat_ Nat_`
  - `Pair.lean:59` — `Pair true_ false_ ⊑ Pair Bool Bool`
  - `Array.lean:86` — `testArr1 ⊑ Array_ done_ Nat_`
  - `Array.lean:88` — `testArr2 ⊑ Array_ dtwo Nat_`

Pair.lean's doc comment (line 17) names this as the intended
mechanism: "Subtyping via app congruence gives `Pair true false
<: Pair Bool Bool`." So the unsoundness is by design, not by
accident.

### Options

1. **Restore bidirectional** (`a ⊑ b ∧ b ⊑ a` for neutral args).
   Sound, but the four tests above become false. Pair would need
   a separate value constructor, e.g. `pair_ A B a b = λk. k a b`
   with `pair_ ⊑ Πl. Πr. l → r → Pair l r` proven via type-ascent
   (the k-codomain `k l r` is reached by ascending through `k`'s
   declared type, not by congruence). `Array_` would build on
   that.

2. **Variance tracking**. Annotate each neutral head with how it
   uses its argument; allow covariance only when the head is
   provably covariant. Heavy: needs a polarity analysis pass.

3. **Quote-and-compare**. Replace the structural arm with
   `quote a == quote b` (definitional equality only). Same effect
   as (1) for the tests, simpler to state.

(1) is the standard fix and matches what `Sigma`/`dpair` already
do (Vec.lean's `mkVec` goes through type-ascent, not congruence,
which is why `vecResult ⊑ Vec Nat` doesn't hit this).
-/

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
| A1 | covariant neutral-app | unsound | bidirectional + re-encode Pair |
| A2 | `_ ⊑ Type` | unsound (Girard) | universe levels, or accept as axiom |
| A3 | β type-blind | unsound for `subCheck` | use `typeCheck` as the entry point |

All other subCheckVal arms (refl, seen, lam-lam, iotaIntro,
fix-unfold, neutralAscent) follow standard sound rules. The
Phase-2 soundness theorem should target `typeCheck` with the
A1 fix applied and A2 either stratified or assumed.
-/

end SoundnessAudit
