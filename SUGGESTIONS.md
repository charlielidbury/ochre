# Suggestions

## Phase 1 (current)

Pick a `TODO[mega-loop]` marker from the test suite:

```
grep -rn "TODO\[mega-loop\]" lean/
```

See `AGENT_PROMPT.md` for how to approach it.

This file intentionally does not prioritise. Agents are expected to choose
their own target based on what's most central, most revealing, or most
likely to unblock others — not what's easiest. If you find a priority
ordering worth recording, add it here.

## Phase 2 (not active yet — do not start)

The soundness proof is Phase 2 work. Do not touch this until Phase 1 is
done and the checker's definitions have stabilised.

When Phase 2 starts, the first task will be choosing the **proof
architecture** — not proving anything. The previous attempt was a
step-indexed logical relation (`VCompat`, now removed from `Soundness.lean`)
which grew a disjunct per term shape and leaked the algorithmic checker
into the semantic definition. Months of effort didn't close it. Don't
assume it was the right shape.

Some approaches worth considering. None is obviously correct; this list
is non-exhaustive and non-committal:

- **Step-indexed logical relations (done carefully).** The previous `VCompat`
  tried this and suffered disjunct-explosion. A cleaner formulation might
  avoid the case-per-shape split — e.g. a single contractive definition
  parameterised semantically rather than syntactically. See `research-logical-relations` for what was tried and where it got stuck.

- **Denotational model.** Interpret types as mathematical objects (domains,
  presheaves, cpo-enriched categories, whatever fits) and interpret terms
  compositionally. More infrastructure, but potentially more principled —
  definitions don't churn when the language grows.

- **Coinductive subtyping + bisimulation.** The recursive-type walls we kept
  hitting are fundamentally coinductive. A coinductive `⊑` with a
  bisimulation-based soundness proof matches the semantics more directly.
  Lean's coinductive support is weaker than Coq's but usable.

- **Subject reduction on a separated typing judgment.** Classical. Would
  require introducing a typing judgment `Γ ⊢ e : τ` alongside the unified
  `⊑`, then proving `e : T ∧ e ⇝* v ⟹ v : T`. We've committed to the
  one-relation design so this would be a departure — but it's the best-
  understood technique in the literature.

- **Erasure to a known-safe target.** Erase types, argue the erased terms
  live in (say) untyped λ-calculus with strong normalisation given certain
  conditions, and lift. Ascription's dual interpretation makes the erasure
  non-trivial.

- **Something new that fits Och specifically.** Och is unusual (terms and
  types unified, abstract evaluation as typechecking, single subtyping
  relation doing multiple jobs). It's plausible that none of the off-the-
  shelf techniques are the right fit and something fresh is needed.

The real recommendation: **whatever you pick, be honest about what it
does and doesn't claim**. A soundness theorem that's vacuously true, or
that's expressed in terms of the checker instead of the declarative
system, is worse than no theorem. The point is to know whether Och's
dual-interpretation-of-ascription actually works — not to produce a Lean
term named `soundness`.

Pre-work before Phase 2 starts: audit which tests fail and why, so we
know what the soundness theorem actually needs to protect. Audit which
properties of the declarative `⊑` we rely on (transitivity in particular).
Audit whether the abstract/concrete evaluators agree on closed terms.
These are facts about the system, not proof strategies, and they're
useful regardless of which architecture wins.
