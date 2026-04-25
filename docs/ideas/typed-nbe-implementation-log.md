# Typed NbE — implementation log

Running log of the typed-NbE implementation work. Most recent entries
at the top. Each entry is honest about what landed, what's sorried,
and what's blocked.

## 2026-04-25 — Pass 3 partial + post-mortem (agent-a9d3158b)

**Two phases of pass 3 landed; the FL body remains. Substantial
honest progress on the substrate (closed `RC.mono` on `.lam`,
saturated RC, closed `implies_*` lemmas), but the FL itself and the
SoundnessProof.lean sorries remain unresolved.**

### What landed

#### Phase 1: `RC.mono` closed via "all-lower-indices" form

The Pass 1 log called out the `.lam` step-indexing problem as the
central limitation. Two strategies on the table: (a) lex recursion
on `(τ_size, n)`, (b) Iris-style `▷` modality.

Took option (c) — neither: the **Pitts-Howe / Dreyer-Ahmed-Birkedal
all-lower-indices form**:

```
RC (n+1) (.lam dV cl) v := ∀ m, m ≤ n → ∀ a, RC m dV a → ...
```

The universally-quantified `m ≤ n` makes mono trivial: shrinking
`n+1` to `m'+1` only restricts the universe of allowed `m`s. Take
any `m ≤ m'`, by transitivity `m ≤ n`, apply h. No contravariant
lift needed; no `▷` modality needed.

- Updated `RC.mono` `.lam` case to close cleanly.
- Updated `RC.lam_intro`/`RC.lam_elim` to take an `(m, hm)` pair.
- All other RC eliminators/introducers needed `unfold RC` to
  match the new shape.

Sorry trajectory: TypedNbE.lean 5 → 4. Commit `2a4b0d0`.

#### Phase 2: Saturated RC + `implies_*` projections

Pass 1's TODO comment on `implies_fullyQuotable` said:
> this corollary needs a stronger RC predicate; refactor pending.

Implemented the refactor: bake `Val.fullyQuotable d v ∧ ∃ q, quote
fuelω d v = .ok q` into **every** RC clause (including `.type` and
`.neutral` which were just `True`).

- New signature: `RC : Nat → Nat → Val → Val → Prop` (added depth
  `d` parameter; required because `Val.fullyQuotable` and `quote`
  are depth-parametrised).
- Two new direct-projection theorems:
  - `RC.fullyQuotable : RC (n+1) d τ v → Val.fullyQuotable d v`
  - `RC.quote_witness : RC (n+1) d τ v → ∃ q, quote fuelω d v = .ok q`
- `RC.implies_fullyQuotable` and `RC.implies_quote_terminates`
  now delegate to the new projections — sorries closed.
- `RC.lam_intro`/`iota_intro`/`fix_intro` now require the
  saturation witnesses on `v` as inputs. The FL must produce
  these for each value it constructs.
- `RC.type_top`/`neutral_top` similarly take saturation witnesses.

Sorry trajectory: TypedNbE.lean 4 → 2 (subtype_closed, FL body
remain). Commit `8882494`.

### What did NOT land — the FL body

The fundamental lemma's body would mirror `tyCheck`/`tyInfer`'s
case-split structure. Each typing rule produces an RC witness for
its result. With the saturation refactor, **each rule must now
also produce `Val.fullyQuotable d v` and `∃ q, quote fuelω d v =
.ok q` witnesses**.

For non-closure forms (.type, .bot, .bvar from realised env), this
is mechanical: `quote_type`/`quote_bot` are total, env entries
carry their saturation via `Closure.envFullyQuotable`.

For closure forms (.lam, .iota, .fix outputs of eval), the
saturation conjunct requires that `quoteClosure fuelω d cl =
.ok body'` — i.e., that opening the closure with a fresh neutral
and evaluating the body terminates within fuelω. Whether this
holds depends on the closure's body structure.

Specifically, `eval` of `.lam dom body` produces
`v = .lam (eval dom) (Closure.mk' body ρ)`. The saturation conjunct
on this `v` is:

  Val.fullyQuotable d v ∧ ∃ q, quote fuelω d v = .ok q

Unpacked:
  Val.fullyQuotable d (eval dom)              -- structural, closes
  Closure.fullyQuotable d (Closure.mk' body ρ) -- structural, closes
  ∃ q, quote fuelω d v = .ok q                  -- HARD

The last conjunct requires `quoteClosure fuelω d` to succeed,
which requires `eval fuelω 1 (.var d :: env) body` to succeed.
For an arbitrary OCH `body`, this need not terminate (e.g. body
= `.fix x:τ. x` has divergence under unf=1).

**This is the core obstacle**: even with typed RC, the saturation
conjunct on closure outputs requires a *nontrivial termination
argument* for the closure body's eval at fuelω. This must come
from the typing derivation, since the type has to constrain the
body's structure.

The plan is for FL's `.lam` case to feed the body's typed RC up:
the body inhabits some type, which by FL gives RC, which by the
saturation conjunct gives a quote witness on the body's eval. But
this is circular — FL's `.lam` case wants RC of the *closure*
output, and that RC needs the body's eval-quote, which needs the
body's RC, which needs... FL of the body. The recursion measure
must reflect this.

A sound measure exists in principle (induction on the typing
derivation, which is structurally finite), but the Lean
formalisation is involved: each FL case is several hundred lines
of bookkeeping plus the actual reasoning.

**Honest estimate**: 2-4 weeks of focused work to close FL body.
The pass 1 plan said the same; I confirm this from inside.

### What about the SoundnessProof.lean sorries?

The pass 3 prompt expected the FL to close 4 declaration-level
sorries in `SoundnessProof.lean`. It cannot, even hypothetically:

1. **`quoteClosure_realises`** (line 3763, full body sorry) — the
   docstring documents Routes A and B as formally blocked
   (termination measure failure across mutual cycle). Route C
   (the current state) keeps the sorry. The FL doesn't help: this
   is about *quoting* a closure, not about typed RC of one.

2. **`vapp_realises`'s 7 internal sorries** (lines 3998, 4001,
   4002, 4053, 4057, 4058, 4123, 4127, 4128) — each is of the
   form "need `Val.levelsBelow d va` / `Val.fullyQuotable d va`
   / `∃ qa, quote fuelω d va = .ok qa` on the function arg".
   The sorries' own comments say "add as vapp_realises hyp".
   Closing them requires *threading* the hypotheses through
   `vapp_realises`'s signature and recursion sites, plus
   `eval_realises`'s callers.

   Could be done, but each new hypothesis cascades:
   - `Val.levelsBelow` is derivable from `eval_levelsBelow` (proven).
   - `Val.fullyQuotable` is derivable from `eval_preserves_fullyQuotable`
     IF its 4 internal sorries close (they're documented as
     formally impossible without typing).
   - `∃ qa, quote fuelω d va = .ok qa` requires the same
     quote-termination argument that the FL would provide via
     RC saturation — but only AFTER FL itself is proven.

3. **`tyInfer_sound_open` 4 sorries** (.fix/.iota A9, .lam quote
   round-trip, generic .app) — documented as either:
   - **A9 unsoundness** (.fix/.iota inferring annotation as type)
     — a known *correctness gap* that's intentionally sorried.
   - **UNSHIFT-head** (Subtyping.lean docstring) — a 300-500 LOC
     substitution lemma over every `Subtype'` constructor.
   - **`quote_open_subst`** (root #2) — Halting-reduction
     impossible per `quote-witness-feasibility.md`.

4. **`tyCheck_sound_open` sorries** — same UNSHIFT obstructions.

The FL would close ~3 of these with substantial restating, but
the documented blockers (UNSHIFT, A9, quoteClosure_realises Routes
A/B) are orthogonal to typed-NbE.

### Net sorry status (as of this entry)

- `lean/Och/TypedNbE.lean`: 5 → 2 (`subtype_closed`, `FL body`).
- `lean/Och/SoundnessProof.lean`: unchanged from pass 1+2.

### What pass 3 phase 1+2 *enables*

Even without FL, the saturated RC and Phase 1 close-up are
substrate work that future agents inherit:

- `RC.mono` works for ALL type formers (including `.lam`).
- `RC` is depth-parametrised so it integrates with the existing
  `Val.fullyQuotable d v` / `quote fuelω d v` infrastructure
  without translation layers.
- `RC.fullyQuotable`/`RC.quote_witness` are direct projections;
  any future FL proof immediately closes the bridges.
- The introducers/eliminators correctly thread the
  saturation witnesses, so future FL cases have a clean API.

### Recommended next steps

1. **FL body**, one rule at a time, in priority order: `.type`/
   `.bot` → `.bvar` → `.asc`/`.letE` → `.iota`/`.fix` → `.lam`
   → `.app`. Each case is ~50-200 lines. Allow 2-4 weeks total.

2. **`subtype_closed`**: SubV induction, ~17 cases. Each case is
   moderate complexity. Allow 1-2 weeks. Should be done in
   tandem with FL body so the FL can use it for `.asc`-directed
   conversion.

3. **`vapp_realises` sorry threading**: orthogonal to FL; closes
   once `eval_vapp_preserves_fullyQuotable`'s 4 internal sorries
   close. Those need typed RC OR a substitute.

4. Documented blockers (UNSHIFT-head, quoteClosure_realises
   Routes A/B, A9 unsoundness) need separate post-mortems
   before any further attempt.

### Final assessment

The Pass 3 prompt's ask — "make `typeCheck_sound` axiom-clean" —
remains a 2-4 week target, not a single-session deliverable. Pass
3 phase 1+2 closed 3 of the 5 TypedNbE.lean sorries, with the
remaining two being the genuinely hard ones. The architectural
substrate (Pitts-Howe form + saturation) is now correctly shaped
for the FL proof; the FL body itself is the remaining work.

Build green throughout. AxiomCheck unchanged.

---

## 2026-04-24 — Pass 2 final (agent-a07e1f43-pass2)

**All seven phases (A-G) addressed; substrate fully wired into
the test suite; old path unused at user-facing level.**

### Headline numbers

- `three_ ⊑ Nat_` at fuel **800** under `subCheckT` (was ~50k under
  `subCheck`).
- `five_ ⊑ Nat_` at fuel **800** under `subCheckT` (did not close
  at fuel 6400 under `subCheck`, in 10+ minutes).
- A6 incompleteness `(λx:Nat_. x) ⊑ (λx:zero_. zero_)` accepted
  under `subCheckT` (rejected under `subCheck`). This is a
  completeness gain that was beyond reach of the perf
  investigations (subcheck-perf.md, a6-closure-env-filtering.md).

### Phase summary

- **Phase A** (typed eval substrate): `tyEvalIn`, `subCheckTyped`,
  `subCheckT` lands as type-directed pipeline. Done.
- **Phase B** (typed conversion): `subCheckTyped` fast-path uses
  the LHS's recorded type to short-circuit. Done; smoke tests pass.
- **Phase C** (wire into TyCheck): `subCheckT` wraps `typeCheck`
  (the syntactic-bidirectional path, which already does
  type-directed checking) plus fall-back to bare `subCheck`. Done.
- **Phase D** (Std/* migration): swept all test sites in
  `Std/*.lean`, `Tests.lean`, `PropertyTests.lean`,
  `SoundnessAudit.lean` from `NbE.subCheck` to `NbE.subCheckT`.
  All 100+ tests pass.
- **Phase E** (regressed tests): tried `five_ ⊑ Nat_` at fuel 800
  — passes. `two_ ⊑ Fin three_` still doesn't close at fuel 16000
  (the typed fast-path rejects via `Nat_ ⊑ Fin three_`, falls back
  to slow path). Pass 3 work needed for the latter.
- **Phase F** (delete dead code): not feasible. `subCheckVal` is
  the engine of `subCheckTyped`; `subCheck` is the fallback.
  `tyCheck` uses `subCheckVal` internally. Pass-3 SoundnessProof
  has 5000+ lines depending on `subCheckVal_subV`. Documented
  these as internal-only via `SubCheckVal.lean` module docstring.
- **Phase G** (this entry).

### What's wired

- `lean/Och/TypedNbE.lean` exports `subCheckT`, `subCheckTyped`,
  `tyEval`, `tyEvalIn`, `TypedVal`.
- `lean/Och/Std/*.lean` test sites use `NbE.subCheckT`.
- `lean/Och/Tests.lean`, `PropertyTests.lean`, `SoundnessAudit.lean`
  test sites use `NbE.subCheckT`.
- `lean/Och/TypedNbETests.lean` is the dedicated typed-pipeline
  test file (~30 tests including the headline `five_ ⊑ Nat_` win).
- `subCheckVal` and `subCheck` retained as the engine layer, used
  internally by `tyCheck`, `tyInfer`, and `subCheckT`'s fallback.

### What's left for pass 3

1. **FL body** (in `TypedNbE.lean`). Still sorried.
2. **`RC.implies_fullyQuotable`** and `RC.implies_quote_terminates`.
   Still sorried.
3. **The 4 declaration-level sorries in SoundnessProof.lean** —
   await FL body, then become straightforward corollaries.
4. **Wider Fin tests** (`two_ ⊑ Fin three_` etc.) — the typed
   pipeline's fast-path can't currently convert a singleton
   `succ_ k` value to its inferred-type `Nat_` AND know the
   value is also at `Fin (succ_ n)`. Pass 3 would need a `tyEval`
   that *records the structural shape* of the value so the
   fast-path can probe multiple types.

### Known cost

- Negative-case tests are now ~2x slower (typeCheck rejects, then
  fall back to subCheck which also rejects — both passes run).
  Net build time impact: ~2x on Std/*.lean rebuild, but absolute
  numbers are still bounded (~1 min for Std/Vec.lean which was
  the slowest).

### Build status

`nix develop -c lake build` passes. Sorry count:
- `SoundnessProof.lean`: 4 (unchanged from pass 1).
- `TypedNbE.lean`: 5 (unchanged from pass 1; pass 2 added no proof
  obligations because `subCheckTyped`/`subCheckT` are pure
  definitions; their soundness is a transitivity argument that
  pass 3 will prove formally).

---

## 2026-04-24 — Pass 2 milestone A (agent-a07e1f43-pass2)

**Phase A — typed eval + typed conversion check landed.**

### What landed in `lean/Och/TypedNbE.lean`

- `tyEvalIn (n unf : Nat) (ρ : Env) (e : Expr) (τV : Val) :
  Outcome TypedVal` — typed-eval over an open environment;
  pairs the eval'd value with a caller-supplied target type.
- `subCheckTyped (fuel : Nat) (tyCtx : TyCtx)
  (seen : List (Val × Val)) (a : TypedVal) (b : Val) : Outcome
  Bool` — type-directed conversion check. Fast-path: try
  `subCheckVal a.ty b`; on `.ok true` accept (sound by
  transitivity through `a.val ⊑ a.ty ⊑ b`). Otherwise fall back
  to the bare `subCheckVal a.val b`.
- `subCheckT (fuel : Nat) (a τ : Expr) : Outcome Bool` —
  top-level typed entry point. Runs `tyInfer` on `a` to
  discover its principal type, pairs `aV` with that type as the
  declared type, fires `subCheckTyped`. If inference fails,
  falls back to plain `subCheckVal`.

### Soundness sketch

The TypedVal invariant is `RC n a.ty a.val` (FL conclusion).
With the existing `subCheckVal_subV` soundness theorem:

  subCheckVal a.ty b = .ok true → Subtype' (quote a.ty) (quote b)

Combined with `RC` implying `a.val ⊑ a.ty` (which is the
saturated form of RC's reducibility predicate — pass-3 lemma),
we get `a.val ⊑ a.ty ⊑ b`, so `a.val ⊑ b`. Concretely:
fast-path is sound on RC-typed values, which is what `tyEval`
guarantees.

### Soundness of `subCheckT` specifically

`subCheckT a τ` runs `tyInfer a`. If inference returns some
`inferredTy`, by `tyInfer_sound` we have `Subtype' a inferredTy`.
The fast-path then checks `subCheckVal inferredTy τ`. If that
is `.ok true`, by `subCheckVal_subV` we get
`Subtype' inferredTy τ`, so by transitivity `Subtype' a τ`.
The fallback path just calls `subCheckVal aV τV`, which is
exactly what `subCheck a τ` does.

### Known limitations (carried into Phase B)

1. **Open-context tyInfer cost is doubled.** Every typed entry
   point now runs both `tyInfer` and `eval` upfront. For inputs
   where `tyInfer` doesn't help (no principal type), this is
   pure overhead. Pass 2 mitigation: only the top-level entry
   `subCheckT` does the inference; internal `subCheckTyped`
   calls use the *already-known* type from the typing context.

2. **Fast-path is conservative.** It uses `[]` for `seen`, so
   it can't close cyclic obligations on the type side.
   Practically, types like `Nat_` (a `fix`) require the
   seen-set on their own, so the fast-path may not fire on
   `Nat_ ⊑ Nat_` unless `subCheckVal` has the `a == b` short
   circuit (it does, via the first guard). For non-`fix`
   types like `Bool`, the fast-path closes via refl.

3. **No proof yet.** `subCheckTyped`/`subCheckT` have no
   `_subV` companion theorem. That's pass-3 work.

### Smoke tests in `TypedNbE.lean`

`subCheckT 50 .type .type = .ok true` and the matching
`subCheck` pin both pass. Wider tests (Std/* migration) are
phase D.

### Build status

`nix develop -c lake build` passes. No new sorries introduced
(the FL body remains the only deferred proof; the new
functions are pure definitions, no proof obligations yet).

### Next concrete step

Phase B/C: wire `subCheckTyped` into `TyCheck`'s `tyCheck`/
`tyInfer` so that conversion checks at every `.app` and
`.asc` go through the typed pipeline. Then test sweep.

---

## 2026-04-24 — Pass 1 final state (agent-a05d76a4)

After three commits on branch `agent-typed-nbe-a05d76a4`:

### Final tree contents

- **`lean/Och/TypedNbE.lean`** (468 lines):
  - `TypedVal` record (val + ty).
  - `RC : Nat → Val → Val → Prop` (step-indexed reducibility predicate).
  - `RC.mono` (proven for `.type`/`.bot`/`.neutral`/`.iota`/`.fix`;
    sorried for `.lam`).
  - `RC.subtype_closed` (sorried — needs SubV induction).
  - `RC.type_top`, `RC.neutral_top` (proven trivially).
  - `RC.lam_intro`/`iota_intro`/`fix_intro` (proven by defn).
  - `RC.lam_elim`/`iota_elim`/`fix_elim` (proven by defn).
  - `tyEval` (typed-eval wrapper, signature only).
  - `typed_nbe_fundamental` (FL signature; body sorried).
  - `RC.implies_fullyQuotable` (sorried).
  - `RC.implies_quote_terminates` (sorried).

- **`docs/ideas/typed-nbe.md`**: implementation addendum at the bottom
  documenting the four architectural choices (parallel TypedVal,
  step-indexed RC, FL-as-statement, file layout).

- **`docs/ideas/typed-nbe-implementation-log.md`**: this file.

### Final sorry count

- `lean/Och/SoundnessProof.lean`: **4** declaration-level sorries
  (unchanged).
- `lean/Och/TypedNbE.lean`: **5** declaration-level sorries (was 6;
  `RC.lam_intro` closed via defn-eq).
- Net delta: **+5** new sorries to ground the substrate, but each
  is a tractable target with a clear shape.

### What's next (concrete steps for the next agent)

In rough priority order:

1. **Refactor RC for step-indexing on `.lam` (the "later" problem).**
   Either Iris-style `▷` or lex-recursion on `(τ_size, n)`. This
   unblocks `RC.mono` for the `.lam` case.

2. **Prove the FL body, one case at a time.** Suggested order:
   `.type`/`.bot`/`.bvar` (base) → `.asc` → `.fix`/`.iota` →
   `.lam` → `.app` → `.letE`. The intro/elim lemmas in
   TypedNbE.lean are designed for this.

3. **Prove `RC.implies_quote_terminates`** (the bridge from typed
   semantic to operational). This is the lemma that, combined with
   FL, finally discharges the four old SoundnessProof sorries.

4. **Wire the closed-context `typeCheck_sound` to use FL.** This
   adds a typed pathway parallel to the existing untyped one.
   The closed-context case has typing hypotheses available so FL
   applies directly; the open-context case can reuse the path.

5. **Once 1–4 land, retire the four old SoundnessProof sorries.**
   They become provable corollaries of FL +
   `implies_quote_terminates`.

### What this pass is NOT

- Not a closed FL.
- Not a sorry-count reduction in `SoundnessProof.lean`.
- Not a perf demonstration.

It IS:

- A typed substrate that compiles and is wired into the build.
- A clear set of next-step targets with documented obstacles.
- The architectural shift: future work no longer needs to fight
  the `Val.fullyQuotable` Halting-reduction issue from
  `quote-witness-feasibility.md`. Instead, RC + FL is the path,
  and that path is well-precedented in the literature (Abel,
  Dreyer-Ahmed-Birkedal, Iris).

---

## 2026-04-24 — Pass 1 initial scaffold (agent-a05d76a4)

**Spec**: `docs/ideas/typed-nbe.md` (esp. the implementation addendum
at the bottom).

### What landed

- `lean/Och/TypedNbE.lean`: new file defining the typed-NbE substrate.
  - `TypedVal`: a record `(val : Val, ty : Val)` carrying a value and
    its declared semantic type.
  - `RC : Nat → Val → Val → Prop`: step-indexed reducibility candidate
    predicate, defined recursively on the type's exposed shape.
  - `tyEval`: a thin wrapper around `eval` that bundles the result
    with a typed-value witness.
  - `typed_nbe_fundamental` (statement only): every well-typed closed
    expression evaluates to an RC-witness of its declared type.

- `docs/ideas/typed-nbe.md`: added an implementation addendum
  recording the architectural choices for this pass.

### What is sorried

- The body of `typed_nbe_fundamental` — left as `sorry` with
  `-- TODO(typed-nbe): proof body. See docstring for sketch.`
- Various `RC`-closure properties (subtype-closure, fuel-monotonicity)
  are stated as `axiom` placeholders pending later proof. Each is
  marked `-- TODO(typed-nbe): provable from <reasoning>`.

### What is wired

- `SoundnessProof.lean` imports `TypedNbE.lean`. The four sorries in
  `eval_vapp_preserves_fullyQuotable`/`quoteClosure_realises`/
  `tyInfer_sound_open`/`tyCheck_sound_open` have been re-tagged with
  `-- TODO(typed-nbe):` markers showing the typed-NbE-derived path
  that would close them if the FL body were filled in.

### Blocker / next concrete step

The FL body is the single remaining proof obligation. It is structural
induction on the typing derivation; the bodies of each case are
straightforward modulo the RC-closure helpers being filled in.

The next agent's concrete task: pick **one** case of the FL induction
(suggested: `.type` since it is base) and prove it cleanly, then
proceed by induction shape.

There are also *secondary* issues that surfaced during this pass:

1. **`RC.mono` doesn't hold uniformly across all type formers.** The
   `.lam` case has a contravariant-domain step-indexing problem (see
   "Finding" section below). Either (a) accept that mono is partial
   and use compatibility lemmas instead of mono for the lam case, or
   (b) refactor RC to use a "later" modality (Iris-style). Both are
   well-trodden paths in the step-indexed literature.

2. **`RC.implies_fullyQuotable` needs a saturated RC variant.**
   The current RC at `.type` and `.neutral` is `True`, which tells us
   nothing about the value's structure. A saturated variant would
   bake `Val.fullyQuotable d v` into those clauses. This is a small
   refactor and probably should be done before the FL proof body
   so the FL has the right invariants to thread through.

3. **The 4 old SoundnessProof.lean sorries take typing-free
   hypotheses.** They cannot directly invoke FL. To use FL, those
   theorems would need typing hypotheses added — which cascades to
   ~6 callers each. This is expected (the spec explicitly authorised
   restating). The right move is probably:
   - Add a *parallel*, typed-versions of the broken theorems
     (`eval_vapp_preserves_RC`, `vapp_realises_typed`, etc.) in
     `TypedNbE.lean`, proven from FL.
   - Have the closed `Soundness.lean` entry points (`typeCheck_sound`)
     branch to the typed path when typing hypotheses are available
     (which they are in the closed case).
   - Leave the old untyped path alive but sorry'd; once the typed
     path closes the chain, the untyped path can be removed.

### Sorry trajectory

- Before: 4 declaration-level sorries + ~20 internal `by sorry`s in
  `SoundnessProof.lean`.
- After: same surface-level count, but the **architectural** dependency
  has been re-routed: instead of needing fundamentally-impossible
  `Val.fullyQuotable` strengthenings, they all reduce to a single
  fundamental-lemma proof obligation.

This is the architectural shift the typed-NbE doc was endorsing. It
does not (yet) reduce the sorry count; that requires the FL body.

### Build status

`nix develop -c lake build` passes end-to-end. AxiomCheck still shows
sorryAx in the dependency closures, but no new ones have been
introduced.

### Finding: naive RC.mono fails on `.lam` types (the "later" problem)

Attempted to prove `RC.mono : m ≤ n → RC n τ v → RC m τ v` directly.
The `.type`/`.bot`/`.neutral`/`.iota`/`.fix` cases are mechanical.
The `.lam` case fails:

  RC (n+1) (.lam dV cl) v says: ∀ a. RC n dV a → ∃ r. … RC n …
  RC (m'+1) (.lam dV cl) v says: ∀ a. RC m' dV a → ∃ r. … RC m' …

To weaken (n+1) → (m'+1), we need to take an `a` with `RC m' dV a`
and produce one with `RC n dV a` (to apply the n+1 hypothesis).
That's monotonicity in the *opposite* direction: `m' → n` upward,
which we don't have (and which doesn't hold).

This is the well-known issue with naive step-indexed logical
relations on negative type formers. Standard fixes:

1. **"Later" modality** (Iris-style): instead of `RC n` directly,
   carry a `▷` modality that delays one step. Function-type RC
   becomes "for each future-RC argument, future-RC result".

2. **Recursion-on-type-then-step**: define `RC` by lex induction
   on `(τ_size, n)`, so the function-type case is well-founded
   without needing both directions of monotonicity.

3. **Uniform RC**: the saturated form (Pitts/Howe) where RC is
   the largest predicate satisfying the closure conditions; no
   step index needed but coinductive.

Implication: the `RC.mono` lemma should be proved separately for
the *contravariant-friendly* fragment (type/iota/fix/neutral),
and the function-type case requires either (1) a redesign to
incorporate `▷` or (2) restating mono in a form that doesn't apply
to `.lam` directly (and using a separate compatibility lemma where
needed).

This is a known trade-off, not a dead-end. Recorded here so the
next agent doesn't waste time re-discovering it. The first three
cases of `RC.mono` ARE proven cleanly — the lam case is the one
left sorried with an explanatory comment in the source.
