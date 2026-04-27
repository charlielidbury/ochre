# Property-test findings (overnight pass, 2026-04-27)

This is the surface-up writeup of surprises discovered while
adding property-based tests to `Och/PropertyTestsExtra.lean`.
These are not bugs — but they're behaviours that aren't entirely
obvious from the public API and that future agents/users could
reasonably expect to be different. Worth documenting.

## Finding 1: `(true_ : Nat_)` synth-validates

**Expected**: `Och.synth (.asc true_ Nat_) = .error` (true is a
Bool, not a Nat).

**Actual**: `Och.synth (.asc true_ Nat_) = .ok ⟨true_⟩`. The
ascription check `true_ ⊑ Nat_` returns `.ok true`.

**Why**: Under the permissive constructor encoding,

```
true_  = λP:Type. λt:Type. λf:Type. t
zero_  = λP. λz. λs. z          -- (Std/DNat.lean)
```

These are structurally identical Exprs. The structural subtype
check `true_ ⊑ Nat_` opens via `Nat_`'s self-type ι unfold and
the body comparison closes by reflexivity at the bvar.

**Documented at**: `Std/DNat.lean:163-167`:

> Note: under the permissive Bool encoding, `true_` and `zero_` are
> structurally identical, so `true_ ⊑ Nat_` correctly succeeds.

So this is a known fact, not a bug. The implication for the
soundness story: under type-in-type with permissive constructors,
*there is no syntactic information distinguishing `true_` from
`zero_`*. Subtyping correctly identifies them as one and the same
value living in multiple types.

This is fine for Och's "terms-are-types" thesis — `true_ = zero_`
isn't a soundness problem; both inhabit `{ x | x = true_ }` =
`{ x | x = zero_ }`. But it's a *precision* problem: the typing
relation cannot statically distinguish the two intended populations
of `Bool` and `Nat_`. The dependent encodings (`dBool` / the
`Nat_` self-type) recover the distinction by demanding more from
the constructor (each takes an explicit motive over its own type),
but the loose `Bool`/`true_`/`false_` encoding does not.

## Finding 2: `zero_ true_` synth-validates

**Expected**: applying a non-function (a "zero" of type Nat)
should fail.

**Actual**: `Och.synth (och{ zero_ true_ }) = .ok ⟨...⟩`.

**Why**: `zero_` is a 3-arg λ, so its head IS a Π
(domain `Type`, codomain → another lambda). Applying it to
`true_` (which `subCheckOpen` accepts at `Type` via the top
rule) β-reduces to a 2-arg λ. Perfectly well-typed at the
structural level.

This is a direct consequence of A2 (type-in-type) plus the
Church-style encoding of constants: every term is a function
that just hasn't been fully applied yet. There is no "value"
vs "function" distinction at the syntactic level — applying
zero to anything is just partial application of a Church
numeral.

The non-Π rejection in `synth.app` only fires for `.type`,
`.bot`, and stuck neutrals whose ascended type is non-Π —
genuinely non-applicable heads.

## Finding 3: `subCheck` on synthed `appendArrays` / `appendVec`

**Verified**: after strengthening the `.isOk` smoke pins,
`Och.synth Std.appendArrays` produces a `WTValue` `v` such that
`Och.subCheck v v 100 = .ok true`. Reflexivity at the public
surface is preserved through synth.

**Caveat**: this is *not* the same as `appendArrays ⊑ <its
declared dependent type>`, which is the documented A6-family
incompleteness pinned (commented out) at `Std/Array.lean:171-174`.
Reflexivity-on-synth-output is the strongest claim the public
surface can make about `appendArrays`/`appendVec` today.

## Coverage gaps that remain

These were considered but not addressed in this pass:

1. **Open-context monotonicity beyond a single ascent test**.
   `Och.PropertyTestsExtra` Section 2 pins one neutral-ascent
   case across two `tyCtx` widenings; a richer corpus
   (multiple tyCtx shapes, multiple neutral patterns) would
   exercise the engine more thoroughly. Not done because
   `subCheckOpen` has subtle dispatch quirks (see
   `AppendVecPath` Stages D-E) and a sloppy property test
   would surface "incompletenesses" that are really test-
   construction errors.

2. **Transitivity through synth/`subCheck` (public surface)**.
   The transitivity sweeps in `Tests.lean` use `Och.subCheckE`
   directly; a `WTValue`-based version would test that the
   public API doesn't break transitivity. Probably equivalent
   in content (`subCheckE = synth+synth+subCheck`), so left
   out as redundant.

3. **`.outOfFuel` propagation as a test category**. We never
   pin "result is .outOfFuel" — fuel is set generously enough
   that all positive tests pass. A "fuel boundary" suite that
   pins exactly when fuel runs out for each operation would
   surface fuel-cost regressions, but is closer to a perf
   benchmark than a semantic guard.

4. **Generative term corpora**. The corpora used here are
   hand-curated ~10-20 element lists. A genuine generative
   approach (Lean's `Plausible` or similar) would have
   higher coverage but is heavier infrastructure than the
   "small finite native_decide sweep" pattern Och favours.
   Pattern is intentional; preserved.

## Tests added in this pass

19 new `theorem`-level pinned properties, plus several discrete
`example` pins. Categories:

  1. Fuel monotonicity (3 sweeps)
  2. Context monotonicity for closed terms (1 + 1 ascent)
  3. HNF idempotence (2 sweeps)
  4. Bot-is-bottom (1 sweep + 4 negatives)
  5. synth/subCheck consistency (4 sweeps)
  6. concEval/subCheckE alignment (2 sweeps × 14 pairs)
  7. β agreement (2 sweeps)
  8. Preservation fragment (3 sweeps × 17 pairs)
  9. Antisymmetry on strict pairs (1 sweep)
  10. Pairwise-distinct numerals/bools (5 sweeps)
  11. Ascription transparency (3 sweeps)
  12. let-binding transparency (2 sweeps)
  13. synth-rejection negatives (8 examples)
  14. Fuel stability (1 sweep × 3 fuels)

All pass `native_decide`. Build is green.
