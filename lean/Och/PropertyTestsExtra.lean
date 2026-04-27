import Och.Syntax
import Och.EvalSubst
import Och.TyCheck
import Och.API
import Och.Std
import Och.Macro

/-!
# Property tests, extended

These tests are property-based: they assert universal claims over
small finite corpora, using `native_decide` to verify by evaluation.
They complement `Och.PropertyTests` (open-Γ / negative / round-trip)
with five further families:

  1. **Fuel monotonicity** — once `subCheckE` / `evalSubst` accept at
     a low fuel, they continue to accept (with the same answer) at a
     higher fuel.
  2. **Context monotonicity** — adding "neutral" entries to the open
     context preserves accepted subtype judgements (the property
     called out as the original Ochre concern in
     `docs/what-is-och.md`).
  3. **HNF idempotence** — `evalSubst` applied to its own output
     returns that output unchanged (HNF is a fixed point).
  4. **Bot is bottom** — `Bot ⊑ x` for every `x` in the corpus, and
     positive controls that `Bot` is *not* a value at non-Bot types.
  5. **synth/subCheck consistency** — `synth` accepts ↔ `subCheck`
     accepts the same value as itself (reflexivity through the
     public surface), and the WHNF returned by `synth` is itself
     accepted by `synth`.

These are all "for-every-term-in-corpus" claims; each `native_decide`
discharges by literal evaluation. Corpora are kept small to keep
build time reasonable.

The DBool / DFin combinatorial sweeps live with their respective
modules; see `Std/DBool.lean`, `Std/DFin.lean`.
-/

namespace Och.PropertyTestsExtra
open Std SubstEval

/-! ## Shared corpus

A spread across syntactic shapes Och cares about. -/

private def coreCorpus : List Expr := [
  -- atoms
  .type, .bot, zero_, one_, two_, true_, false_, unit_,
  dtrue, dfalse,
  -- types
  Nat_, Std.Bool, Unit_, dBool,
  -- arrows / lambdas
  och{ Nat_ → Nat_ }, och{ Bool → Bool }, och{ λx:Nat_. x },
  och{ λx:Bool. x }, och{ λx:Type. x },
  -- ι / fix at small shapes
  .iota .type Nat_, .fix .type Nat_,
  -- ascription / let
  .asc zero_ Nat_, .letE zero_ (.bvar 0),
  -- compounds
  och{ Pair Nat_ Unit_ }, och{ pair_ Nat_ Unit_ zero_ unit_ },
  och{ succ_ zero_ }
]

/-! ## 1. Fuel monotonicity

For every term in the corpus, the result of `evalSubst` /
`subCheckE` at fuel 200 is the same as at fuel 400. (We pick two
fuels rather than `n` and `n+1` so a single `native_decide` covers
a meaningful gap.) -/

section FuelMono

/-- `evalSubst` answer at fuel 200 equals the answer at fuel 400
on every corpus term. (Both are `.ok` for everything in `coreCorpus`,
so this is a consistency check more than a coverage gap.) -/
theorem evalSubst_fuel_consistent :
    coreCorpus.all (fun e =>
      evalSubst 200 unfBound e == evalSubst 400 unfBound e) = true := by
  native_decide

/-- `Och.subCheckE` is fuel-monotone on accepted reflexive pairs:
once accepted at 100 it remains accepted at 200. -/
theorem subCheckE_fuel_mono_refl :
    coreCorpus.all (fun e =>
      let r1 := Och.subCheckE 100 e e
      let r2 := Och.subCheckE 200 e e
      r1 == .ok true && r2 == .ok true) = true := by
  native_decide

/-- Cross-fuel agreement on a hand-picked positive sweep. -/
private def positivePairs : List (Expr × Expr) := [
  (zero_, Nat_), (one_, Nat_), (two_, Nat_),
  (true_, Std.Bool), (false_, Std.Bool),
  (unit_, Unit_), (dtrue, dBool), (dfalse, dBool),
  (zero_, .type), (Nat_, .type),
  (och{ pair_ Nat_ Unit_ zero_ unit_ }, och{ Pair Nat_ Unit_ })
]

theorem subCheckE_fuel_consistent_pos :
    positivePairs.all (fun p =>
      Och.subCheckE 100 p.1 p.2 == .ok true &&
      Och.subCheckE 200 p.1 p.2 == .ok true) = true := by
  native_decide

/-- Negative cross-fuel agreement: rejection at low fuel persists at
high fuel. (Vacuously: subCheckE never returns `.outOfFuel` for these
inputs, so the same `.ok false` answer is reproduced.) -/
private def negativePairs : List (Expr × Expr) := [
  (Nat_, zero_), (Nat_, Unit_), (Std.Bool, Nat_),
  (one_, zero_), (two_, one_), (dBool, dtrue),
  (.type, Nat_)
]

theorem subCheckE_fuel_consistent_neg :
    negativePairs.all (fun p =>
      Och.subCheckE 100 p.1 p.2 == .ok false &&
      Och.subCheckE 200 p.1 p.2 == .ok false) = true := by
  native_decide

end FuelMono

/-! ## 2. Context monotonicity

Adding fresh entries to `tyCtx` preserves accepted subtype judgements.
This is the analogue, on the open-context surface, of the
soundness-flavoured property called out in `docs/what-is-och.md`:

  > a sound, monotone notion of typing via abstract interpretation

The closed-context surface (`Och.subCheckE`) trivially has nothing to
widen, so we exercise `subCheckOpen` directly. -/

section CtxMono

private def Γbase : Array Expr := #[]
private def Γext1 : Array Expr := #[Nat_]
private def Γext2 : Array Expr := #[Nat_, Std.Bool]

/-- For closed terms, the answer is independent of the context's
extra entries (the engine never consults `tyCtx` on level-vars it
doesn't see). -/
private def closedPairs : List (Expr × Expr) := [
  (zero_, Nat_), (true_, Std.Bool), (unit_, Unit_),
  (dtrue, dBool), (dfalse, dBool), (Nat_, .type),
  (och{ pair_ Nat_ Unit_ zero_ unit_ }, och{ Pair Nat_ Unit_ })
]

/-- Closed-term answers are context-independent. -/
theorem subCheckOpen_ctx_independence :
    closedPairs.all (fun p =>
      let r0 := subCheckOpen 200 Γbase p.1 p.2
      let r1 := subCheckOpen 200 Γext1 p.1 p.2
      let r2 := subCheckOpen 200 Γext2 p.1 p.2
      r0 == .ok true && r1 == .ok true && r2 == .ok true) = true := by
  native_decide

/-- Adding a fresh `Nat_` entry to `tyCtx` doesn't break `level 0 ⊑
Nat_` (it's the very entry being added). The widening to a 2-entry
context preserves it. -/
theorem subCheckOpen_neutral_ascent_mono :
    let q : Expr := freshLevelVar 0
    subCheckOpen 200 Γext1 q Nat_ = .ok true ∧
    subCheckOpen 200 Γext2 q Nat_ = .ok true := by
  native_decide

end CtxMono

/-! ## 3. HNF idempotence

`evalSubst` is idempotent on its own outputs: feeding the result back
in produces the same expression. This is the head-normal-form fixed
point property. -/

section Idempotence

theorem evalSubst_hnf_idempotent :
    coreCorpus.all (fun e =>
      match evalSubst 200 unfBound e with
      | .ok h =>
          match evalSubst 200 unfBound h with
          | .ok h' => h' == h
          | _ => false
      | _ => false) = true := by
  native_decide

/-- HNF and source are convertible (forward direction was already
pinned in `PropertyTests.rt_forward`; this re-pins it across the
extended corpus and within a single quantifier). -/
theorem evalSubst_hnf_convertible :
    coreCorpus.all (fun e =>
      match evalSubst 200 unfBound e with
      | .ok h =>
          Och.subCheckE 200 e h == .ok true &&
          Och.subCheckE 200 h e == .ok true
      | _ => false) = true := by
  native_decide

end Idempotence

/-! ## 4. Bot is bottom

`Bot ⊑ x` for every `x` in the corpus. The engine implements this via
the `.bot, _` arm in `subCheckSubstMatch`. Pinned positively over the
corpus to catch any future regression that gates Bot inappropriately.
-/

section BotIsBottom

theorem bot_subtypes_everything :
    coreCorpus.all (fun e =>
      Och.subCheckE 200 .bot e == .ok true) = true := by
  native_decide

/-- Conversely: only `Type` can have things subtyping it
unconditionally. `Bot` itself does not absorb non-Bot subtypes — most
populated atoms reject `_ ⊑ Bot`. -/
theorem bot_does_not_absorb :
    Och.subCheckE 200 zero_ .bot = .ok false ∧
    Och.subCheckE 200 unit_ .bot = .ok false ∧
    Och.subCheckE 200 Nat_ .bot = .ok false ∧
    Och.subCheckE 200 .type .bot = .ok false := by
  native_decide

/-- Edge: `.type ⊑ .bot` is false (the universe doesn't fit in Bot).
A boundary check between the two universal answers. -/
theorem type_not_subtype_of_bot :
    Och.subCheckE 200 .type .bot = .ok false := by
  native_decide

end BotIsBottom

/-! ## 5. synth / subCheck consistency

If `Och.synth e` succeeds and yields `v`, then re-checking `e ⊑ e`
through the public API succeeds, and `e ⊑ v.whnf` (the term against
its own WHNF type-witness) is `.ok true`. This is reflexivity, but
phrased through the public surface that downstream code uses. -/

section SynthConsistency

private def synthCorpus : List Expr := [
  zero_, one_, two_, true_, false_, unit_, dtrue, dfalse,
  Nat_, Std.Bool, Unit_, dBool,
  och{ λx:Nat_. x }, och{ λx:Bool. x }, och{ succ_ zero_ },
  och{ pair_ Nat_ Unit_ zero_ unit_ }
]

/-- Every term in `synthCorpus` synth-validates. -/
theorem synthCorpus_all_validate :
    synthCorpus.all (fun e => (Och.synth e 200).isOk) = true := by
  native_decide

/-- `synth e` accepts ⇒ `subCheckE e e` accepts. -/
theorem synth_implies_refl :
    synthCorpus.all (fun e =>
      (Och.synth e 200).isOk → Och.subCheckE 200 e e == .ok true) = true := by
  native_decide

/-- The synth-returned WHNF is itself synth-validatable: re-running
`synth` on `v.whnf` succeeds. (Idempotence at the public surface.) -/
theorem synth_whnf_idempotent :
    synthCorpus.all (fun e =>
      match Och.synth e 200 with
      | .ok v => (Och.synth v.whnf 200).isOk
      | _ => false) = true := by
  native_decide

/-- The public `subCheck` is reflexive on every WTValue produced by
`synth`. -/
theorem subCheck_refl_on_synth :
    synthCorpus.all (fun e =>
      match Och.synth e 200 with
      | .ok v => Och.subCheck v v 200 == .ok true
      | _ => false) = true := by
  native_decide

end SynthConsistency

/-! ## 6. concEval / subCheckE alignment

For a corpus of closed concrete computations, `concEval e₁ = concEval
e₂` (an *operational* equivalence) implies the structural subtype
check accepts both directions. Conversely, concrete inequality should
not get smuggled past the structural check on values that admit one.

This is a fragment of the soundness target stated in
`docs/what-is-och.md`: "if `concEval(e) = v` and abstract eval gives
type `t`, then `v ∈ t`". We can't state full soundness without the
declarative side, but we *can* pin the forward implication on a
finite corpus. -/

section ConcEvalAlignment

/-- Pairs that compute to the same value. Computational equality
should imply (small-fuel) bidirectional convertibility. -/
private def opEqPairs : List (Expr × Expr) := [
  -- arithmetic identities
  (och{ pred_ zero_ }, zero_),
  (och{ pred_ one_ },  zero_),
  (och{ pred_ two_ },  one_),
  (och{ isZero_ zero_ }, true_),
  (och{ add_ zero_ one_ }, one_),
  (och{ add_ one_ zero_ }, one_),
  (och{ add_ one_ one_ }, two_),
  -- bool identities
  (och{ not' true_ }, false_),
  (och{ not' false_ }, true_),
  (och{ and' true_ true_ }, true_),
  (och{ and' false_ true_ }, false_),
  (och{ or true_ false_ }, true_),
  -- pair eliminators
  (och{ fst_ (pair_ Nat_ Unit_ zero_ unit_) }, zero_),
  (och{ snd_ (pair_ Nat_ Unit_ zero_ unit_) }, unit_)
]

/-- Operational equivalence pinned: each pair has equal `concEval`
outputs. -/
theorem opEqPairs_compute_equal :
    opEqPairs.all (fun p =>
      concEval 200 p.1 == concEval 200 p.2) = true := by
  native_decide

/-- And the same pairs admit bidirectional structural convertibility.
This is the abstract-interpretation analogue: the structural check
sees both as semantically equal. -/
theorem opEqPairs_structurally_convertible :
    opEqPairs.all (fun p =>
      Och.subCheckE 200 p.1 p.2 == .ok true &&
      Och.subCheckE 200 p.2 p.1 == .ok true) = true := by
  native_decide

end ConcEvalAlignment

/-! ## 7. Substitution invariance (β agreement)

For closed lambdas, the structural engine sees `(λx. b) v` and
`b[v/x]` as convertible. This is the β rule the engine implements;
the property pin asserts agreement on a corpus. -/

section BetaAgreement

/-- Pairs `(redex, contractum)` with closed terms. -/
private def betaPairs : List (Expr × Expr) := [
  -- (λx:Nat_. x) zero_  ≡  zero_
  (och{ (λx:Nat_. x) zero_ }, zero_),
  -- (λx:Type. Nat_) Bool  ≡  Nat_
  (och{ (λx:Type. Nat_) Bool }, Nat_),
  -- (λx:Type. x) Nat_  ≡  Nat_
  (och{ (λx:Type. x) Nat_ }, Nat_),
  -- (λx:Bool. x) true_  ≡  true_
  (och{ (λx:Bool. x) true_ }, true_),
  -- nested: (λx:Type. λy:Type. x) Nat_ Bool  ≡  Nat_
  (och{ (λx:Type. λy:Type. x) Nat_ Bool }, Nat_),
  -- nested: (λx:Type. λy:Type. y) Nat_ Bool  ≡  Bool
  (och{ (λx:Type. λy:Type. y) Nat_ Bool }, Std.Bool)
]

theorem beta_pairs_convertible :
    betaPairs.all (fun p =>
      Och.subCheckE 200 p.1 p.2 == .ok true &&
      Och.subCheckE 200 p.2 p.1 == .ok true) = true := by
  native_decide

/-- And concretely: `concEval` agrees on each pair. -/
theorem beta_pairs_compute_equal :
    betaPairs.all (fun p =>
      concEval 200 p.1 == concEval 200 p.2) = true := by
  native_decide

end BetaAgreement

/-! ## 8. Antisymmetry on the `strictPairs` corpus

Sweep that strict subtypes really are strict (one direction holds,
the other doesn't). Mirrors `SoundnessAudit.sweep_strict` but with a
different curated list. -/

section Antisymmetry

private def strictNew : List (Expr × Expr) := [
  -- numerals are strict in their type
  (zero_, Nat_), (one_, Nat_), (two_, Nat_),
  -- bool constructors are strict in Bool
  (true_, Std.Bool), (false_, Std.Bool),
  -- dependent bool constructors are strict in dBool
  (dtrue, dBool), (dfalse, dBool),
  -- product introduction is strict in the product type
  (och{ pair_ Nat_ Unit_ zero_ unit_ }, och{ Pair Nat_ Unit_ })
]

theorem strictNew_one_directional :
    strictNew.all (fun p =>
      Och.subCheckE 200 p.1 p.2 == .ok true &&
      Och.subCheckE 200 p.2 p.1 == .ok false) = true := by
  native_decide

end Antisymmetry

end Och.PropertyTestsExtra
