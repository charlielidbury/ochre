# A6: closure-env filtering unblocks both perf and encoding simplification

**Status:** investigated 2026-04-24, hypothesis disproved by profiling. Not pursued. See post-mortem at end.

## The intuition (read this first)

Closures in Och carry their entire capture environment. The subtype checker's seen-set keys, ptr-equality checks, and structural equality all include the closure value — so they include the env. The problem: a closure's env often holds bindings the body doesn't actually use, picked up incidentally as we crossed enclosing binders during unfolding.

Result: the **same sub-expression**, reached via two different unfold paths, produces two **distinct** closure values that differ only in irrelevant env baggage. Seen-set treats them as different → re-derives the same sub-problem → exponential blowup.

Filtering = restrict each closure's env to the actual free-var footprint of its body. Two semantically-equal closures then have **identical representations** regardless of how they were reached.

This buys two things at once:

1. **Stable cycle detection.** Recursive sub-problems hit the seen-set instead of looking fresh.
2. **Stable narrowing.** When body-checks push a fresh neutral typed at a closure's domain, that type is canonical — downstream sub-checks against the neutral don't fork into divergent paths.

Both reduce to: a canonical representation of *what this thing actually depends on*. Once that exists, equality checks fire where they should, and pushing `domB` (the A6 fix) becomes tractable instead of explosive.

## The A6 incompleteness

In `SubCheckVal.lean:337`, the Π-Π body check pushes the **LHS** domain (`domA`) to the type context, not the RHS:

```lean
| .lam domA clA, .lam domB clB => do
    let contra ← subCheckVal fuel tyCtx seen domB domA
    if !contra then return false
    ...
    subCheckVal fuel (tyCtx.push domA) seen bodyA bodyB
                              -- ^^^^ should be domB for completeness
```

Pushing `domA` is **sound but incomplete**. Pushing `domB` (the narrower domain, per Pierce-style Π-Π subsumption) would be more complete but currently causes exponential blowup on recursive types whose inner-let closures capture an unused fresh `self` (e.g. `Nat_`'s `succ_local`).

The blowup root cause: when the body-check creates a fresh variable at type `domB`, that fresh variable's *closure environment* still holds bindings the seen-set doesn't recognize as equivalent across recursion. Seen-list misses → re-derive → blowup.

## Why this matters for perf

`three_ ⊑ Nat_` costs ~50k fuel. The deep-dive memoization agent (2026-04-24) found sub-problems are genuinely distinct under the current algorithm — but a chunk of that distinctness is the exact A6 issue: each level of singleton-Nat traversal recreates closures with non-canonical envs, breaking seen-set hits that the spec-level relation would have closed coinductively.

So fixing A6 attacks the perf problem from a different angle than memoization: it doesn't cache redundant work, it eliminates the spurious distinctness in the first place.

## Why this matters for the encoding

Current `zero_` and `succ_` carry precise annotations (`λP:(self → Type)`, `λz:(P self)`). These are not for body-typing — the bodies are transparent (`z`, `s m`). They exist to make the body-co-check close: under iotaIntro, the LHS variable's declared type matches RHS's expected return.

A simpler encoding `λP:Type. λz:Type. λs:Type. z` would be cleaner but breaks `zero_ ⊑ Nat_` because under current A6-incomplete algorithm, z is pushed with type Type (LHS), not `P zero_` (RHS), and the co-check `z ⊑ P zero_` has no closing leaf.

If A6 were fixed (push `domB`), the simpler encoding would just work: z's declared type in context would be `P zero_`, co-check closes via reflex/ascent.

## Closure-env filtering — the proposed fix

The blowup happens because closure environments leak captured fresh vars across recursive boundaries. The fix:

1. When opening a closure with a fresh neutral inside body-check, **filter** the captured env entries that are bound by enclosing binders the seen-set has already crossed.
2. Canonicalize the resulting closure so structurally-identical closures produced by different unfold paths share representation.
3. With env-filtered canonical closures, seen-set hits become reliable across recursion, and pushing `domB` no longer blows up.

This is a non-trivial refactor of `Closure.openFresh` and the seen-set keying logic. Spec impact: declarative Subtype' is unchanged; algorithmic completeness improves.

## Payoff if landed

| Win | Mechanism |
|-----|-----------|
| `three_ ⊑ Nat_` from ~50k → much smaller | Spurious sub-problem distinctness goes away |
| `five_ ⊑ Nat_` becomes tractable | Same |
| `two_ ⊑ Fin three_` becomes tractable | Same |
| zero_/succ_ encoding shrinks to `λP:Type. λz:Type. λs:Type. z` | Body co-check closes under domB push |
| Annotations on numeral binders become genuinely Top | Pierce-narrower context discharges them |
| All Std data structures keep working | Subtyping lattice preserved |

## Risks / unknowns

- Closure-env filtering might interact badly with `fix`-unfold sharing.
- Canonicalization scheme needs to respect α-equivalence without false unification (different binders with same body shape but different captured envs are NOT equivalent).
- The simpler encoding for zero_/succ_ assumes `(λpred:m. P (succ_ pred)) ⊑ Type` and similar Top-ascription paths still close — needs verification.

## Pointers

- `lean/Och/SubCheckVal.lean:337` — the A6 site.
- `lean/Och/SubCheckVal.lean:328-336` — the existing comment explaining the trade-off.
- `docs/ideas/subcheck-perf.md` — the 2026-04-24 memoization post-mortem (the negative result that motivates this).
- `lean/Och/Std/DNat.lean` — the encoding that would simplify.
- DECISION-LOG entries tagged A6.

## Post-mortem (2026-04-24, agent-aca6f2bc)

### Plan executed

Per the task brief, profile-first to confirm the dead-env-slot
hypothesis before refactoring. Wrote an instrumented walker
(`bvarUsed` + dead-slot counter) over the closures produced by
`eval` and recursively followed by `Closure.openFresh` up to
fuel 200, depth-walking through `λ`/`ι`/`fix` binders.

### Numbers

Across `zero_/one_/two_/three_ ⊑ Nat_` after evaluation
(no opens):

| judgment       | closures | totalSlots | dead | dead % |
|----------------|----------|------------|------|--------|
| zero_ ⊑ Nat_   |        2 |          0 |    0 |   0%   |
| one_ ⊑ Nat_    |      197 |         64 |    0 |   0%   |
| two_ ⊑ Nat_    |     6632 |       2176 |    0 |   0%   |
| three_ ⊑ Nat_  |   218987 |      71872 |    0 |   0%   |

Including opens (depth-walk through binders, fuel 100):

| judgment       | closures | totalSlots | dead | dead % |
|----------------|----------|------------|------|--------|
| zero_ ⊑ Nat_   |       15 |         26 |    8 |  30%   |
| one_ ⊑ Nat_    |       24 |         32 |   10 |  31%   |
| two_ ⊑ Nat_    |      804 |        288 |   10 |   3%   |
| three_ ⊑ Nat_  |    26544 |       8736 |   10 |   0%   |

Dead-slot count is **a fixed small constant (~10)** regardless
of numeral size. The proportion goes to 0% as work grows.

### Distinct-env-per-body check

For `three_ ⊑ Nat_` after deep opens (200 depth, fuel 1000),
across 41,376 closure traversals: only **1 body** out of 16
distinct bodies had multiple distinct envs (3 distinct envs
total). The "non-canonical envs across unfold paths" pathology
the design doc predicts is barely measurable.

### Why the hypothesis is wrong

The existing `Closure.mk' body env := ⟨body, env.take
(bvarBound body - 1)⟩` (NbE.lean:84) already trims env to the
prefix the body can structurally reach. For Och's actual
closures, the live-set IS the prefix — no interior dead slots
worth filtering. The `bvarBound`-based prefix-trim was added
specifically to fix this kind of issue and **is doing its
job**.

The `three_ ⊑ Nat_` cost (~50k fuel) is therefore not from
spurious closure-env distinctness. It's the genuine algorithmic
work of the singleton-tightened `succ_` (Option A): each
predecessor is threaded through the contra chain on the
`s`-domain `λpred:m`. This is the same conclusion the previous
memoization deep-dive reached (`docs/ideas/subcheck-perf.md`).

### Decision

Do not refactor `Closure.mk'` for filtering. The prefix-trim is
already doing the work the doc proposed; further filtering
would buy <1% in canonicalisation across measured workloads
while costing significant proof-rework (47 references to
`Closure.mk'` in `SoundnessProof.lean`, including the
`shiftLvl`/`levelsBelow`/`envFullyQuotable`/`mk'_body_closed`
lemma chain).

### What might actually move the needle

(Recording for the next deep-dive — these were considered
during investigation but not executed.)

1. **Iterative subCheckVal with a worklist + structural-hash
   memo** (also flagged in `docs/ideas/subcheck-perf.md`).
   Treats fuel as a global budget rather than per-call,
   amortises across paths.

2. **Typed NbE** (`docs/ideas/typed-nbe.md`). Most ambitious;
   prunes whole branches that the current untyped checker
   re-explores.

3. **Re-encode succ_'s s-branch** to avoid the
   singleton-predecessor contra chain. Trade off the Option-F
   Fin subsumption for performance — keep `(succ_ m) ⊑ Fin
   (succ_ n)` working but via wrapper constructors instead of
   subsumption.

4. **Accept the perf wall.** The ~50k fuel cost for
   `three_ ⊑ Nat_` is the realistic ceiling for Option A.
   `five_ ⊑ Nat_` and `two_ ⊑ Fin three_` won't close at
   accessible fuel. Document this as Option-A's tradeoff and
   keep moving on metatheory.

The A6-completeness goal (push `domB` instead of `domA`)
remains genuinely incomplete in the algorithm. But unlocking
it requires more than env-filtering — the `domB`-push
exponential blowup is *not* primarily an env-canonicality
issue. It's the extra unfold work that pushing the narrower
type provokes per recursive layer.
