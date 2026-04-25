# A6: closure-env filtering unblocks both perf and encoding simplification

**Status:** research thread. Not started.

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
