# Suggestions

## Phase 2 — soundness proof (current)

`Soundness.lean` is sorry-free. `Subtyping.lean` now contains
`Subtype'.shift_above` (2026-04-21) — the helper lemma for the
`Equiv.shift` nil-Γ case. 12/23 cases proven including the
`.hyp` case that was previously characterized as the
"impossibility wall". The remaining 11 cases (binder and
productive-unfold) need `Seen.wellClosed` / `Ctx.wellFormed`
propagation; all cases documented.

**The `Equiv.shift` obstacle reassessed (2026-04-21):** The
prior claim that route (i) was a "~60-line structural induction"
was wrong; see DECISION-LOG 2026-04-21 for the full analysis.
The actual path is:

1. Seen.wellClosed (new, in Subtyping.lean) — invariant on
   seen-sets; preserved by every productive unfold rule.
2. Ctx.wellFormed (new, in Subtyping.lean) — standard de Bruijn
   well-formedness of the context; NOT preserved by `.lam` /
   `.iota_cong` / etc. without an extra closedness side
   condition on the binder.
3. Subtype'.shift_above — 12/23 cases proven. Remaining 11 need
   #2's propagation, which requires adding closedness premises
   to the binder constructors of `Subtype'` — an invasive
   change.

Alternative: restrict `Equiv` to non-empty Γ. All current
users of `Equiv.shift` access the result at a non-empty
context (one binder deeper). The catch: `concEval_refines`
needs the result at Γ=[], requiring a bespoke non-Equiv.shift
derivation at the top level.

All three root obligations solved at the definition level (DECISION-LOG
2026-04-19); remaining sorries in `SoundnessProof.lean` are
**downstream applications** — no further definition
changes needed.

### Tier 1 — direct closures (engineering, ~30 min each)

- `R_mono.decreasing_by`: lift `v` to a top-level
  positional arg so `decreasing_by` sees `sizeOf v` for the
  `(n, sizeOf v)` lex measure shared with `R`. Mutual with
  `RList_mono`.
- `eval_realises .lam/.iota/.fix` base-conjuncts (3): the
  new `R`-clause is `∃ ρe' he, RList (n+1) d cl.env ρe' ∧
  closedAt ∧ Equiv e (.ctor …)`. At each base case
  `cl.env = ρ` and `henv : REnv n d ρ ρe` is in scope;
  build the witness directly.
- `Equiv.shift` nil-Γ: `Subtype'.ctx_extend` no longer
  needs `Seen.Closed`; the cons-Γ proof routes through it,
  the nil-Γ residual is the `n=0` shift identity.

### Tier 2 — bridge threading (engineering, ~1 hr each)

- `quote_open_subst`: 4-step route documented at its
  docstring (SoundnessProof ~2310). All four pieces
  (`eval_realises`, `R_quote_equiv`, `substEnv_subst_comp`,
  `R_resp_Equiv`) are proven post-`293dc13`.
- `SubV_to_Subtype'` closure cases: add `(hRa : ∃ ea, R 1
  Γ.size a ea)` / `(hRb)` to bridge motives; extract `RList
  … cl.env ρe'` from the new `R`-clause; apply
  `quoteClosure_equiv_openω_fresh` (proven). Callers
  (`subCheckVal_sound_open`) supply `(hRa)/(hRb)` from
  `eval_realises`.
- `openNf_holds` removal: swap 6 `eval_quotes` callers to
  the proven `eval_quotes'`, threading `(hnfq)` from each
  caller's available `eval` evidence.

### Tier 3 — assembly + algorithm gap

- `whnfPi_sound_open`: structural induction on `whnfPi`'s
  unfold loop; each `.fix`/`.iota` step uses
  `Equiv.fix_unfold`/`Equiv.iota_unfold` (proven) +
  `quote_open_subst` (tier 2).
- `tyCheck_sound_open .lam` final assembly: gated on
  `whnfPi_sound_open`.
- `tyInfer_sound_open .letE` algorithm gap: the inferred
  body type may reference the let-binder. Either change
  `tyInfer .letE` (TyCheck.lean) to substitute before
  returning, or restate the soundness lemma to quote at
  depth `Γ.size+1` then `letE_R` it down. Per fork
  `a40bd0da`.
- `tyInfer_sound_open .app`: needs an `app_elim`-style step
  (`f ⊑ Π[A]B → a ⊑ A → f a ⊑ B[a]`) — derive via
  `.app_cong` + `.beta_R` + `.trans`, or add as a derived
  rule in Subtyping.lean.

### Done

- Root #1 (depth-tagged Seen): `ctx_extend_at` closed,
  Subtyping.lean sorry-free (`8d86c69`).
- Root #2 (R env-exposure): `vapp_realises` proven
  (`293dc13`). `R_resp_Equiv` non-recursive.
- Root #3 (`OpenCtx.hwf`): `tyInfer .bvar` closed,
  `letBinderType_sound_open` closed (`94483f1`).

- Root #3-old `eval_quotable` — closed via `(nf fuelω
  e).isSome` side-condition (`eval-quotable-fork`); the
  unconditional form is genuinely false (closure body
  re-eval). `quote_total_on_eval`/`eval_quotable_open`
  axiom-clean.
- `R` Kripke ∀-`unf'`-quantified (`r-kripke-restate-fork`).
- `.iota_cong`/`.fix_cong`/`.letE_cong`/`.unfold_iota_R`
  constructors; `Equiv.subst_resp`/`R_resp_Equiv`/
  `concEval_equiv`/`Equiv.iota_unfold` closed.
- Open-Γ skeleton + `OpenCtx` ρe-threading; `push_fresh`/
  `push_let`/`QuotesCtx.push`/`subCheckVal_sound_open`/
  `tyCheckFallback_sound_open` closed.
- Legacy `subCheckNF` retired; `Val.beq` ptrEq fast-path
  (clean build 580 s → 71 s).

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
