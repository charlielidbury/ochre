# Suggestions

## Phase 2 — soundness proof (current)

The dependency order, bottom-up. Work near the bottom
unblocks the most.

1. **Restate `R`'s Kripke clause as ∀-`unf`-quantified, add
   `m ≤ fuel` to `eval_realises`.** Recommendation from the
   `.app`-head fork: the inner `vapp` recursion in the
   `.fix`/`.iota` head sub-cases is currently *out of IH
   range* because the IH is at one specific `unf`. Making
   the Kripke clause `∀ unf' ≤ unf` (instead of fixed `unf`)
   and threading `m ≤ fuel` through `eval_realises` brings
   it in. This is a *statement* change to `R` and probably
   a one-shot edit + re-thread of the existing cases; do it
   *before* trying to close the four named obligations.

2. **`eval_realises` `.fix`/`.iota`-head obligations**:
   `vapp_open_eq` (vapp of an unfolded fix is vapp of
   body[self↦fix]); `R_resp_iota_unfold`/`R_resp_fix_unfold`
   (one-step-unfold respects `R`). After (1), these may
   become direct from the new IH shape.

3. **`Subtype'.ctx_extend`** (the one open case of
   `narrow_at`): pushing a binder past a seen-set entry. The
   seen-set Exprs are *closed* (they come from `quote` at
   depth 0), so the shift is the identity — but the
   `QuotesSeen` invariant doesn't currently say that. Either
   add `∀ p ∈ S, closedAt 0 p.1 ∧ closedAt 0 p.2` to
   `QuotesSeen`, or restate `narrow_at` over closed-seen
   only.

4. **`quote_open_subst`** (closure-opening commutes with
   substitution): derives from `eval_unf_equiv` (already
   derived from `eval_realises`). Once (1)+(2) close
   `eval_realises`, this should follow.

5. **`SubV_to_Subtype'` closure-opening cases** (10 of
   them): each is `quote_open_subst` + the case's specific
   `Subtype'` constructor. The `lam` case additionally needs
   `narrow_head` (← (3)).

6. **`typeCheck_sound`**: induction on `e`, with each
   `tyCheck` arm calling `subCheckVal` and applying
   `subCheckVal_sound` (already wired).

7. **`concEval_preservation`**: adequacy of `R` —
   `eval_realises` at the term level + `R_quote_equiv`.

The legacy `subCheckNF` (Eval.lean) fuel-mono scaffold
sorries are *off the critical path* — they only matter for
the legacy-checker divergence sweep, not for NbE soundness.

## Phase 1 (done — 0 markers)

Pick a `TODO[mega-loop]` marker from the test suite:

```
grep -rn "TODO\[mega-loop\]" lean/
```

See `AGENT_PROMPT.md` for how to approach it.

This file intentionally does not prioritise. Agents are expected to choose
their own target based on what's most central, most revealing, or most
likely to unblock others — not what's easiest. If you find a priority
ordering worth recording, add it here.

## Possible simplifications (gut-out territory)

The μ→ι+fix split retained annotations on both binders: `ι x:A. b` and
`fix x:A. b`. It's plausible that one or both annotations are unnecessary
cruft.

- **ι's annotation.** Currently the `iotaIntro` rule has two premises:
  `a ⊑ ι x:A. b` iff `a ⊑ A` ∧ `a ⊑ b[x := a]`. The `a ⊑ A` premise is a
  widening bound — it says "the value being self-typed also fits the
  annotation". Cedille's ι has no such annotation; the self-typing rule
  is just `a ⊑ ι x. b` iff `a ⊑ b[x := a]`. If this simpler form works,
  the annotation is dead weight.

- **fix's annotation.** Used by `fixAnn`: `fix x:A. b ⊑ c` via `A ⊑ c`.
  Equi-recursive unfold (`unfoldFixL`, `unfoldFixR`) does not touch the
  annotation. If we drop `fixAnn` (which exists only for convenience —
  you can always express the widening via explicit ascription), the
  annotation has no role.

**If you find that removing either annotation simplifies the encoding or
closes a `TODO[mega-loop]` marker, do it.** This is exactly the kind of
gut-out the prompt asks for: if dead weight is load-bearing only because
we added it, cut it. Updating every ι/fix site to match is mechanical.
Smaller core wins.

Counter-point to be aware of: the annotations do offer *local documentation*
— `fix self:(dNat → dNat). body` tells the reader what recursive function
this is without having to derive it from the body. If annotations are
removed, make sure nothing critical relied on them for type-inference
heuristics in the checker.

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
