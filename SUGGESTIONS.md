# Suggestions

## dllbc/ — NORTH STAR: verified in-place quicksort, as natural as possible (2026-07-24, user-set)

The target program, and the iteration policy for reaching it:

**The program.** Quicksort in the shape a Rust programmer would write it —
swap-based in-place partition, recursion on sub-slices, no allocation, no
take-and-rebuild of whole sublists — with the signature carrying full
verification: sorted, and a permutation of the entry snapshot.

**The slice equivalent.** DLLBC has no heap by design (no-heap is what makes
types-never-stale work), so "mutable slice" is represented as what a slice
IS — a fat pointer: **a mutable borrow plus a comptime length bound**,
`(v : &mut List T, n : Nat)`, with segment-scoped specs (`SortedUpto n`,
count-on-`take n`, and `↝`-obligations pinning the untouched remainder to
the entry snapshot). Suffix sub-slices are tail reborrows; prefix recursion
rides the bound, not a prefix borrow. Element access/swap is nested
reborrow cursors (the zero_all pattern, two live cursors at different
depths — disjoint by the suspension tree). True random-access arrays are a
compilation-story question, out of calculus scope; the calculus-level claim
is O(1)-extra-space swap-based mutation through borrows.

**Why in-place is also the easier verification.** With count-based Perm
(`Perm s l := Π n. Id (count n s) (count n l)` — no indexed Perm family
needed), a swap is one count-preservation lemma and partition is a
composition of swaps: transitivity does the rest. The functional version
has to reason about filter/append counts instead.

**The iteration policy (user-set): naturalness first.** Each milestone
writes the DESIRED surface program first, then makes the checker accept
it. When the program comes out contorted, the finding is a missing
rule/sugar in the calculus (field-path reborrows, cursor idioms,
implicits...) — fix the calculus, don't contort the program. Gaps go in
the milestone ambiguity lists like everything else.

**The milestone train** (M10 fording in flight; then, in order): listRec +
pure let + the Sorted/Le/count pure library; dependent call-site
instantiation (§5.3's stated rule, unimplemented — every lemma application
needs it); the two-cursor swap milestone (make-or-break for naturalness —
if swap is contorted, iterate the rules there); leb-reflection + order
lemmas; Lomuto partition segment-scoped + spec; quicksort assembly.
Partial correctness first (signature-only recursion — no termination
story); totality later via fuel or §8 measures. Known caveat: type-in-type
means "verified modulo Girard" until the universe hierarchy returns.

## pss/ (branch pss-2) — Problem D2: what to try next, what not to

`pss/docs/05-conservation-law-and-escape-routes.md` (2026-06-10) maps the
full attack space for the one remaining `sorry` (`sound_app_le`, Problem D2):

- **Do not re-budget the model.** The doc's §2 "conservation law" ledger
  shows every uniform re-grading (lags, degrees, recursive/coinductive pair
  relations, type-side budgets, syntactic tier domains, ~14 variants) fails
  by exactly one index level, with the pin that kills each one named.
- **Try first (hardest-first):** Escape A — *graded Howe's method*. The
  single pivot: write the λ-case of the graded key lemma on paper, tracking
  every consumption of the base relation (doc §3). 1–2 focused days decides
  the program; if it survives, `sound_app_le` closes as a drop-in theorem.
- **Try second:** Escape B — the γ-truncation/Top-completion reduction of
  open-D2 to the proven ∅-case (doc §4); run the cheap definability
  falsification before committing.

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

**The complete closedness-propagation chain is now built** (as
infrastructure; the proof-level integration remains):

1. `Seen.wellClosed` / `Ctx.wellFormed` (Subtyping.lean, new) —
   wellformedness invariants.
2. `Subtype'.shift_above` (Subtyping.lean, 12/23 cases proven) —
   including the `.hyp` case (the supposed "impossibility wall"),
   proven via `Seen.wellClosed`.
3. `Subtype'.shift_above_closed` / `shift_nil_closed`
   (Subtyping.lean, fully proven) — trivial shift on closed
   endpoints.
4. `Equiv.shift_of_closed` (SoundnessProof.lean, fully proven) —
   bypasses the nil-Γ sorry when both endpoints are closed.
5. `Equiv.subst_resp_closed` (SoundnessProof.lean, fully proven) —
   closedness-carrying subst_resp that avoids `Equiv.shift`
   entirely (uses `shift_of_closedAt` to reduce shifted
   substituend to itself).
6. `concEval_closedAt` (Eval.lean, fully proven) — concEval
   preserves closedness at 0.

**Final step (not yet done):** rewrite `concEval_equiv`
(Soundness.lean) to carry `hcl : e.closedAt 0` and use
`subst_resp_closed` + `concEval_closedAt` at each recursive
call. Attempted but hit Lean elaboration issues in the
iota/fix unfold cases — reverted; future work.

Alternative: restrict `Equiv` to non-empty Γ. All current
users of `Equiv.shift` access the result at a non-empty
context (one binder deeper). The catch: `concEval_refines`
needs the result at Γ=[], requiring a bespoke non-Equiv.shift
derivation at the top level.

All three root obligations solved at the definition level (DECISION-LOG
2026-04-19); remaining sorries in `SoundnessProof.lean` are
**downstream applications** — no further definition
changes needed.

### Tier 0 — R-clause refactor for quoteClosure_realises (in progress)

Add `envLevelsBelow d cl.env` + `envFullyQuotable d cl.env` to R's
.lam/.iota/.fix clauses so `quoteClosure_realises` can supply them to
`RList_depth_lift` + `eval_realises` at depth d+1.

**Done (2026-04-22):**
- Commit ea5409b: Val.levelsBelow + Val.fullyQuotable defs moved
  before R.
- Commit 012437e: Val.fullyQuotable_mono +
  Closure.envFullyQuotable_mono + quote_depth_shift_n moved before
  R_depth_lift.
- Commit 1067bdd: Two conjuncts added to R's closure clauses; 18
  destructuring + 5 construction sites updated.
- Commit 860da51: eval_realises signature gains envLevelsBelow +
  envFullyQuotable hypotheses; internal sites closed via
  envLevelsBelow_take / envFullyQuotable_take; external callers
  (OpenCtx.eq, push_let, Soundness.lean) supply via
  `_of_getElem?` constructors.

**Remaining (sorry count: 4 — 1 net increase from prior 3):**
1. vapp_realises has new internal sorries (pulled into sorryAx via
   mutual eval_realises): 4 spots in .lam/.iota/.fix cases needing
   `Val.levelsBelow d va`, `Val.fullyQuotable d va`, and quote
   witness when extending eval env. Same issue for `vf` in iota/fix
   unfold branches. Fix: add these as hypotheses to vapp_realises
   signature, update all callers.
2. eval_realises .letE internal sorry: need Val.fullyQuotable +
   quote-witness on the evaluated `val`. Same core blocker as
   `eval_vapp_preserves_fullyQuotable`.
3. quoteClosure_realises proof: now has right hypotheses but body
   needs eval_realises + R_quote_equiv at d+1. Cannot be expressed
   with current forward-ref layout (quoteClosure_realises defined
   BEFORE eval_realises). Options:
   - Big mutual block: quoteClosure_realises + R_quote_equiv +
     eval_realises + vapp_realises, with lexicographic (step, Val)
     termination.
   - Move quoteClosure_realises after eval_realises; then find
     another non-circular path for R_quote_equiv's closure cases.
4. tyInfer_sound_open internal sorries + A9 known-issue (unchanged).

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
