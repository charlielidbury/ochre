import Och.SubCheckVal
import Och.TyCheck
import Och.Eval
import Och.Std.Pair
import Och.Std.Nat
import Och.Std.Bool
import Och.Std.DBool
import Och.Std.DNat
import Och.Std.Unit

/-!
# Phase 2: Soundness audit

Executable witnesses for soundness gaps in the Phase-1 checker.
Each `theorem` here is a *true fact about the current algorithm*
(provable by `native_decide`); the surrounding prose explains why
that fact is a soundness problem.

These are deliberately phrased as positive assertions about the
checker's *current behaviour* so that fixing the underlying rule
will make this file fail to compile — at which point the entry
should be moved to a "resolved" section with the new behaviour
asserted instead.

After the legacy `subCheckNF`/`absEval` retirement, all witnesses
target `NbE.subCheck`/`NbE.typeCheck` only. The original two-checker
divergence sweep (which found A1/A5/A6/A7/A8) is replaced below by
NbE-only structural properties (reflexivity, top, the documented A6
incompleteness witness). The full audit history with both checkers
is at commit `38d1031`.
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

**Fix** (047e59f):
  - `subCheckNeutral` and `subCheckVal`'s neutral-app arms now
    require *equivalence* (`a ⊑ b ∧ b ⊑ a`), not just `a ⊑ b`.
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
    NbE.subCheck 200 (och{ Pair zero_ unit_ }) (och{ Pair Nat_ Unit_ })
      = .ok true ∧
    NbE.subCheck 200 (och{ (Pair zero_ unit_) kContra })
                     (och{ (Pair Nat_  Unit_) kContra })
      = .ok true := by
  native_decide

/-- And the constructor inhabits the type via ascent. -/
theorem a1_pairAscent :
    NbE.subCheck 200 (och{ pair_ Nat_ Unit_ zero_ unit_ })
                     (och{ Pair Nat_ Unit_ })
      = .ok true := by
  native_decide

/-!
## A2: Type-in-type

The checker has `_ ⊑ Type → true` (SubCheckVal.lean's top guard).
This is `Type : Type`, which admits Girard's paradox.
-/

theorem a2_typeInType :
    NbE.subCheck 50 Nat_ .type = .ok true ∧
    NbE.subCheck 50 .type .type = .ok true ∧
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

## A3: NbE eval β is type-blind

`NbE.eval`'s `.lam` β arm substitutes unconditionally, so
`NbE.subCheck` is only meaningful on *already-well-typed*
inputs. The Phase-1 fix is `NbE.typeCheck` (TyCheck.lean), which
runs the domain check syntactically; the Phase-2 statement is
therefore "`typeCheck e τ = .ok true → e : τ`", not
"`subCheck e τ = .ok true → e : τ`".
-/

private def illTyped := och{ (λn:Nat_. n) Bool }

theorem a3_subCheckBlind :
    NbE.subCheck 200 illTyped Bool = .ok true := by
  native_decide

/-- …but `typeCheck` catches it. -/
theorem a3_typeCheckCatches :
    (NbE.typeCheck 200 illTyped Bool).isOk = false := by
  native_decide

/-!
## A5: iotaIntro skipped the annotation check — RESOLVED

**Was**: the checker's `_, .iota ann body` arm checked only
`a ⊑ body[self:=a]`, ignoring `a ⊑ ann`. So `dtrue ⊑ ι
self:Nat_. Type` was accepted (the body `Type` is `top`)
despite `dtrue ⊄ Nat_` — the ι-type's "intersection with the
annotation" semantics was lost.

**Fix** (9a9d198): the checker now requires `a ⊑ ann ∧
a ⊑ body[self:=a]`, with `seen` extended *before* the
annotation check so the `fix B. ι self:B. …` pattern (where
`ann` is the recursive type itself) closes coinductively. The
declarative `Subtype'.iota_intro` already had both premises,
so this brings the algorithm in line.
-/

private def constrainedI := och{ ι self:Nat_. Type }

theorem a5_annotationChecked :
    NbE.subCheck 200 dtrue constrainedI = .ok false := by
  native_decide

/-- And the legitimate recursive case still closes via seen. -/
theorem a5_recursiveCaseStillWorks :
    NbE.subCheck 200 dtrue dBool = .ok true := by
  native_decide

/-- Regression for the ι-ι path: the `.iota, .iota` arm has its
own iotaIntro fallback (after the structural comparison fails)
which initially skipped the annotation premise too. -/
theorem a5_iotaIotaPath :
    NbE.subCheck 200 (.iota .type .type) (.iota Nat_ .type) = .ok false := by
  native_decide

/-!
## A6: lam-lam pushes `domA` not `domB` — DEFERRED

NbE.subCheck's lam-lam arm pushes the *source* domain
`domA` into `tyCtx`. With `domA`, a subterm in `bodyB`
needing `fresh : domB` ascends via `domA ⊑ domB` — the wrong
direction — so `(λx:Nat_. x) ⊑ (λx:zero_. zero_)` is rejected.
The (now-retired) legacy `subCheckNF` accepted it. This is an
**incompleteness**, not an unsoundness; the soundness proof
goes through with `domA`.

**Why not `domB`**: pushing `domB` (which matches
`Subtype'.lam` and is more complete) causes the seen-list to
miss on recursive types whose inner-`let` closures capture
an unused fresh `self` — `Closure.mk'`'s `.take`-trim keeps
env entries between index 0 and the highest-referenced
index, so `dNat`'s `dsucc_local` keeps `[dzero, fresh@d, N]`
even though its body only references `N`. Each structural
ι-open at depth `d` then yields a structurally-distinct
`dsucc_local`, `domB` references it, the seen-check (`==`)
never fires, and `dtwo ⊑ dNat` goes exponential (>15 min at
fuel 200, vs <1 s with `domA`).

**Plan**: replace unused closure-env entries with a
canonical placeholder so `Val.beq` identifies them across
fresh-opens; then re-enable `domB`. Until then, `SubV.lam`
pushes `domA` and `SubV → Subtype'` will need `narrow`.
-/

/-- The A6 incompleteness witness: NbE rejects this query
even though `Subtype'.lam` (with `domB`) would derive it. -/
theorem a6_incompletenessWitness :
    NbE.subCheck 200 (och{ λx:Nat_. x }) (och{ λx:zero_. zero_ })
      = .ok false := by
  native_decide

/-- The `domB` blowup, witnessed: with `domA`, `dtwo ⊑ dNat`
closes well within fuel 200. (At `domB` this query did not
terminate within 15 minutes; that's not directly testable
here, but is the regression that pins `domA`.) -/
theorem a6_dtwoFastWithDomA :
    NbE.subCheck 200 dtwo dNat = .ok true := by
  native_decide

/-!
## A7: `.fix,_`/`.iota,_` lacked productivity guard — RESOLVED

**Was**: NbE.subCheck's L-side fix/iota-unfold arms opened the
closure with `a` (the LHS itself) and recursed on `a' ⊑ b`
under `seen' = (a,b) :: seen`. When the body is bare `self`
(= `.bvar 0`), opening returns `a` unchanged, so the
recursion is `a ⊑ b` with `(a,b) ∈ seen'` — coinductively
accepted. Hence `(fix A. self) ⊑ X` and `(ι self:A. self) ⊑
X` were `.ok true` for *every* X.

**Fix**: add `if a' == a then .ok false` after the open,
matching the existing stuckRec-L arm. Equirecursively
`fix self. self ≡ ⊤`, so `⊤ ⊑ X` is false for X ≠ ⊤
(and X = ⊤ = `.type` is caught by the `b == .type` guard).

The R-side `_, .fix` was already correct (the coinductive
accept of `X ⊑ ⊤` is *right*).
-/

private def fixSelf : Expr := .fix .type (.bvar 0)
private def iotaSelf : Expr := .iota .type (.bvar 0)
private def ascZN : Expr := .asc zero_ Nat_

/-- A8: ascription is computationally transparent. `(zero_ :
Nat_) ≡ zero_`, so `(zero_:Nat_) ⊑ zero_` and `Nat_ ⊄
(zero_:Nat_)`. Previously the checker evaluated `.asc t τ` to
`τ`, accepting `Nat_ ⊑ (zero_:Nat_)` (= `Nat_ ⊑ Nat_`). -/
theorem a8_ascTransparent :
    NbE.subCheck 200 ascZN zero_ = .ok true ∧
    NbE.subCheck 200 Nat_ ascZN = .ok false := by
  native_decide

theorem a7_lhs_rejected :
    NbE.subCheck 200 fixSelf Nat_ = .ok false ∧
    NbE.subCheck 200 iotaSelf Nat_ = .ok false := by
  native_decide

theorem a7_rhs_accepted :
    NbE.subCheck 200 Nat_ fixSelf = .ok true := by
  native_decide

/-!
## A4: Inductive `Subtype'` is incomplete for equirecursion

Not an *algorithm* unsoundness — the algorithm is correct here
— but a gap in the *declarative* relation that makes
`subCheckVal_sound` unprovable as stated.

`dtrue ⊑ dBool` is accepted by the checker (it's the very
first DBool test). But every attempted `Subtype'` derivation
loops: after `unfold_fix_R` + `iota_intro` + `unfold_iota_L`,
the goal becomes the lam-lam comparison

  `λP:(dtrue→Type). … ⊑ λP:(dBool→Type). …`

whose contravariant domain premise needs `dtrue ⊑ dBool`
again. The algorithm closes this coinductively via the
seen-set; the inductive `Subtype'` cannot.
-/

theorem a4_algorithmAccepts :
    NbE.subCheck 200 dtrue dBool = .ok true := by
  native_decide

/-!
### Fix

The declarative relation must be the *greatest* fixpoint of
its rules (Amadio-Cardelli, Brandt-Henglein), not the least.
Three encodings:

  (a) **Seen-indexed** (`Subtype' seen Γ a b`): mirror the
      algorithm. Add `(a, b) ∈ seen → Subtype' seen Γ a b`;
      every rule that recurses on a *non-structurally-smaller*
      goal (the four `unfold_*` and `iota_intro`) extends
      `seen`. `subCheckVal_sound` then goes by simultaneous
      induction on fuel and `seen`-monotonicity.
  (b) **Step-indexed** (`Subtype'ₙ`): `Subtype'₀` is `⊤`;
      `Subtype'ₙ₊₁` requires premises at level `n`. The gfp is
      `∀ n, Subtype'ₙ`. Maps cleanly to the algorithm's `fuel`.
  (c) **Companion / parameterised coinduction**: heavyweight,
      not needed here.

(a) is closest to the algorithm and to the existing `Simple/`
proof; (b) is closest to the eventual semantic model
(step-indexed logical relations). Either suffices for
`subCheckVal_sound`. Soundness.lean records this as the next
concrete task.

/-!
## A9: tyInfer trusted `.fix`/`.iota` annotation — RESOLVED

**Was**: `tyInfer`'s `.fix ann body` / `.iota ann body` arm
returned `eval ann` directly without checking the body. So
`tyInfer (fix x:Nat_. unit_) = .ok Nat_`, and `typeCheck`
(via `tyCheckFallback → tyInfer → subCheckVal Nat_ Nat_`)
accepted `fix x:Nat_. unit_` at `Nat_` even though
`unit_ : Unit_ ⋢ Nat_`. A genuine soundness hole, found
while structuring `tyInfer_sound_closed` (Soundness.lean) —
the `.fix`/`.iota` case had no premise to discharge.

**Fix**: a `.fix`/`.iota` arm in `tyCheck` that checks
`subCheckVal (eval e) expected` directly (bypassing the
annotation-trusting `tyInfer` path). `tyCheck`'s `.letE`
arm, which consults `tyInfer val` to get the binder type,
now also verifies `tyCheck val valTy` (which routes through
the new `.fix`/`.iota` arm) before trusting it. `tyInfer`
itself is unchanged — `.app`-chains with fix heads
(`dadd n m`, `appendArrays …`) need it to return the
annotation so the head's domain/codomain can be computed,
and adding a verification step there regressed `appendVec`
in two attempts (a recursive body-check via `tyCheck`
cascades; a self-`subCheckVal` check fails on nested-fix
annotations that are fresh neutrals).
-/

/-- Pre-fix, the four false-lines below were `.ok true`. -/
theorem a9_fixIotaBodyChecked :
    NbE.typeCheck 200 (.fix Nat_ unit_) Nat_ = .ok false ∧
    NbE.typeCheck 200 (.iota Nat_ unit_) Nat_ = .ok false ∧
    -- The `.letE`/`.app`-head paths:
    NbE.typeCheck 200 (.letE (.fix Nat_ unit_) (.bvar 0)) Nat_
      = .ok false ∧
    NbE.typeCheck 200 (.app (.fix Nat_ unit_) zero_) Nat_
      = .ok false ∧
    NbE.typeCheck 200
      (.app (.letE (.fix (och{Nat_ → Nat_}) unit_) (.bvar 0)) zero_)
      Nat_ = .ok false ∧
    -- positive controls: a *well-formed* fix still checks,
    -- and the let-bound ill-formed fix checks at its *actual*
    -- type (the value unfolds to `unit_`):
    NbE.typeCheck 200 (.fix Nat_ zero_) Nat_ = .ok true ∧
    NbE.typeCheck 200 (.letE (.fix Nat_ unit_) (.bvar 0)) Unit_
      = .ok true := by
  native_decide
-- Regression for nested-fix-annotation programs (`appendVec`)
-- lives in `Och/Std/Vec.lean:159` — two earlier A9 attempts
-- broke it, so it's the canary.

## Summary

| # | Rule | Status | Fix |
|---|------|--------|-----|
| A1 | covariant neutral-app | **resolved** | bidirectional + re-encoded Pair |
| A2 | `_ ⊑ Type` | open (Girard) | universe levels, or accept as axiom |
| A3 | β type-blind | mitigated | use `typeCheck` as the entry point |
| A4 | inductive `Subtype'` incomplete | **resolved** | seen-indexed (`.hyp` rule) |
| A5 | iotaIntro skipped annotation | **resolved** | check `a ⊑ ann` under extended seen (both arms) |
| A6 | lam-lam pushed `domA` (incomplete) | **deferred** | `domB` blows up on dNat (closure-body mismatch); `domA` is sound |
| A7 | `.fix/.iota,_` no productivity guard | **resolved** | `a' == a → false`; R-side `→ true` |
| A8 | `.asc t τ` evaluated to `τ` | **resolved** | evaluate `t`; keep ascription check |
| A9 | `tyInfer` trusted fix/ι annotation | **resolved** | check `body : ann` under `self : ann` |

## Property sweep (NbE-only)

The original two-checker divergence sweep is replaced (now that
the legacy checker is retired) with NbE-only structural
properties on the same corpus:

- **Reflexivity**: `∀ e ∈ corpus, e ⊑ e`.
- **Top**: `∀ e ∈ corpus, e ⊑ Type`.
- **A6 incompleteness pinned**: the one known witness rejects.

A separate `Och/PropertyTests.lean` (added alongside this
retirement) covers open-Γ, negative, and quote-round-trip
properties more thoroughly.
-/

private def sweepCorpus : List Expr := [
  .type, zero_, Nat_, Bool, true_, dtrue, dBool, dNat, done_,
  dzero, Unit_, unit_, .iota Nat_ .type, .iota .type Nat_,
  .iota .type (.bvar 0), .fix .type Nat_, .fix .type (.bvar 0),
  och{ Nat_ → Nat_ }, och{ zero_ → Nat_ }, och{ Nat_ → zero_ },
  och{ λx:Nat_. x }, och{ λx:zero_. zero_ },
  och{ Pair Nat_ Unit_ }, och{ pair_ Nat_ Unit_ zero_ unit_ },
  .asc zero_ Nat_, .asc Nat_ .type
]

/-- Reflexivity on the corpus. -/
theorem sweep_refl :
    sweepCorpus.all (fun e => NbE.subCheck 400 e e == .ok true) := by
  native_decide

/-- Everything is ⊑ Type (top). -/
theorem sweep_top :
    sweepCorpus.all (fun e => NbE.subCheck 400 e .type == .ok true) := by
  native_decide

/-- The documented A6 incompleteness witness is the only known
NbE-rejection of a `Subtype'`-derivable judgment on the corpus.
Pinned as `.ok false` so re-enabling `domB` (or any other
completeness improvement) makes this file fail to compile and
prompts a re-audit. -/
theorem sweep_a6_pinned :
    NbE.subCheck 400 (och{ λx:Nat_. x }) (och{ λx:zero_. zero_ })
      = .ok false := by
  native_decide

/-- Anti-symmetry probe: for a hand-picked list of strict-subtype
pairs, `a ⊑ b` holds and `b ⊑ a` does not. (Full anti-symmetry
on the corpus is not asserted — many corpus pairs are
incomparable, and equivalent pairs would need an exclusion
list.) -/
private def strictPairs : List (Expr × Expr) := [
  (zero_, Nat_), (true_, Bool), (dtrue, dBool), (done_, dNat),
  (unit_, Unit_), (Nat_, .type), (och{ Nat_ → Nat_ }, och{ zero_ → Nat_ })
]

theorem sweep_strict :
    strictPairs.all (fun (a, b) =>
      NbE.subCheck 400 a b == .ok true &&
      NbE.subCheck 400 b a == .ok false) := by
  native_decide

/-!

A1/A3/A5 concern the *algorithm*; A2 is a design choice; A4
concerns the *declarative* side. All four addressable items
are now resolved: every algorithmic arm maps to a declarative
constructor, the algorithmic seen-set has a declarative
counterpart (`.hyp`), and the entire stack (subCheckVal, eval,
quote) is non-partial. The `dtrue ⊑ dBool` annotation-premise
witness in `Soundness.lean` confirms `.hyp` closes the cycle
that previously had no finite derivation. The
`subCheckVal_sound` proof can now be attempted by fuel
induction.
-/

end SoundnessAudit
