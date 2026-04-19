# Suggestions

## Phase 2 — soundness proof (current)

`Soundness.lean` is sorry-free; all four target theorems
wired. **15 sorries** in `SoundnessProof.lean` (14) and
`Subtyping.lean` (1) reduce to **three root obligations**:

### Root 1 — depth-tagged seen-set (research)

`ctx_extend_at`'s 6 binder cases and `Equiv.shift` share
the same wall: `.iota_intro`/`.unfold_*` extend `S` with
the current `(a, b)` pair at depth `|Γ|`, and the body IH
needs `S` shifted at a different cutoff. DECISION-LOG
2026-04-18 lists three routes; route (a) (depth-tag each
entry: `Seen := List (Nat × Expr × Expr)`) is most
principled. This ripples through every `Subtype'`-using
proof in SoundnessProof, so do it on a stable base.

Closes: `ctx_extend_at` (Subtyping), `Equiv.shift`
(SoundnessProof) → `subst_resp`/`R_resp_Equiv` axiom-clean.

### Root 2 — `R` clauses must expose `REnv` (research → engineering)

`vapp_realises` (consolidating `.app`'s `.fix`/`.iota` head
sub-cases) is unprovable under the current Kripke `R`:
both the mutual route and Ahmed-`R(min)` lose exactly one
step-index at the closure boundary (SoundnessProof
1495-1530). Resolution: change `R`'s `.lam`/`.iota`/`.fix`
clauses to `∃ ρe', REnv n d cl.env ρe' ∧ Equiv …`,
well-founded on `(n, sizeOf v)` lex. `.app` then applies
the fuel-IH to `cl.body` directly via `REnv_cons`. In
flight on `R-restructure` fork.

Closes: `vapp_realises` → 3 `eval_realises` leaves →
`quote_open_subst` → `SubV/SubN/SynthN_to_Subtype'`
closure cases → `subCheckVal_sound` axiom-clean (modulo
root 1 for `.lam`'s `narrow`).

### Root 3 — open-Γ residuals (engineering)

`tyCheck_sound_open .lam` is structurally complete
post-QuotesCtx-depth-`k` fix; gated only on
`whnfPi_sound_open` (which is gated on root #2 via
`quote_open_subst`). `letBinderType_sound_open` is
provable now (mutual tag-3 IH + `hctx.eq`).
`tyInfer_sound_open`'s non-`.fix/iota` arms are direct
structural recursions; the `.fix/iota` arm is
A9-unprovable as stated — restate as
"`tyInfer e = ok τ → tyCheck e τ = ok true → e ⊑ τ`" or
add `(hwf : e wellFormedFix)`. `openNf_holds` is false as
stated — drop it, thread `(hnfq)` through
`OpenCtx.eval_quotes`'s callers. In flight on
`open-gamma-residuals` fork.

Closes: `typeCheck_sound` axiom-clean (modulo roots 1+2).

### Done

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
