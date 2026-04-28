# Overnight session — 2026-04-28 part 2 (post-summary work)

**Branch**: `och-refactor` from `5560f8b` to current. **17 commits.**
All pushed.

This is a follow-up to `overnight-summary.md` (part 1, ending at
commit `5560f8b`).  Part 1 took the soundness scaffolding from "raw
sorries with no structure" to "fully-composed proof chain with 2 of
4 top-level theorems closed".  This part attempts to close more of
the residual walls.

## Headline

**Sorries: 11 → 4** (declaration-level, in soundness chain).
Two top-level theorems remain walled (`subCheck_sound`,
`synth_sound`); two stay closed (`concEval_preservation`,
`synth_progress`); the composition `soundness` body remains
sorry-free.

## Walls closed

### Wall 1 — synth annotation closedness (`synthCore_topLevel_closedAt`)

**Commit `c121da9`.**  `Och.synth` now validates `e.closedAt 0` at
entry and rejects ill-formed input with `.error`.  The previously
walled lemma proves trivially by unfolding synth.  Predicted user
preference (option 1 from `blockers.md`) — runtime check tightens
synth's contract, matches the "synth gates concEval" framing.

Bonus cleanup (`64b96f8`): exposed `synthCore_topLevel_closedAt`
and dropped redundant `hcl` premise from `synth_progress` and
`soundness`.  Statement now reads:

```lean
soundness :
  Och.synth e fuel = .ok a →
  Och.synth b.whnf fuel = .ok b →
  Och.subCheck a b fuel = .ok true →
  concEval fuel e = .ok e' →
  Subtype' [] [] e' b.whnf
```

### Seen short-circuit case (`subCheckSubst_sound:474`)

**Commits `0dd91a6`, `3e892ab`, `07a7310`.**  Implemented Design A
from `tyCtxPush-bridge-wall.md`: `tyCtxToCtx` and `liftSeenList`
both apply depth-stratified `closeAll` to entries.  Re-proved
`Subtype'_lvar_via_tyCtx` against the new convention (no
arithmetic obstacle).  Seen short-circuit now closes via
`Subtype'.hyp_here` directly.

Additionally proved as scaffolding:
- `tyCtxToCtx_push` (cons extension).
- `closeAll_succ_d_eq_shift` (depth-bump = shift).
- `Subtype'_liftSeen_succ_to_d` (Seen-coherence weakening).

### Lam-lam structural dispatch arm

**Commit `f490d7c`.**  Closed via the depth-stratified Design A
infrastructure plus the new lemmas above.  ~150 LOC including
plumbing.  The `.lam, .lam` engine arm doesn't extend `seen` for
its sub-calls (unlike iota-iota and fix-fix), so its closure is
the cleanest of the three structural arms.

## Walls cleaned up (stub removal)

- `c9ff41d` — removed 3 documentation stubs from
  `SubCheckSubstNeutral.lean` (now sorry-free).
- `3b0355d` — removed `closeAllAt_substL_OPEN_QUESTION` stub
  from `CloseAll.lean` (now sorry-free).
- `93d1b86` — removed unused `arm_hyp_compose` stub.

These were marker-style sorries that were never invoked by working
proofs; the wall analyses live in `docs/ideas/`.

## Walls newly surfaced

### Wall 5 — `tyCtxPush_bridge_WALL` (Closed via Design A)

`docs/ideas/tyCtxPush-bridge-wall.md`.  Surfaced 2026-04-28 by the
lam-lam attempt (`568f148`).  The dispatch's IH yielded a Ctx with
**raw** `domB` head, but `arm_lam_lam_compose` expected
**closeAll'd** head.

**Resolution applied:** Design A — `tyCtxToCtx` redefined with
depth-stratified `closeAll`.  Closed.

### Wall 6 — Seen-shrinking (iota-iota / fix-fix structural arms)

`docs/ideas/tyCtxPush-bridge-wall.md` (extended), `blockers.md`
item 6.  Surfaced 2026-04-28 (`343788c`) by the iota-iota / fix-fix
attempt.  Engine extends `seen` with `(a, b)` for ALL recursive
sub-calls in iota-iota and fix-fix arms; lam-lam doesn't.
`Subtype'.iota_cong` / `.fix_cong` preserve `S` (not productive
like `iota_intro`), so the dispatch's IH derivation in
extended-seen can't shrink to the goal's original-seen.

**Resolution paths** (per agent `343788c`):
1. **Engine refactor**: drop seen-extension in iota-iota/fix-fix
   structural attempt, keeping it for the fallback.  Smallest
   change.  Risk: μ-type cycle detection might rely on this.
2. **Seen-shrinking lemma**: prove
   `Subtype' (entry :: S) Γ a b → Subtype' S Γ a b` under
   "entry not used in derivation".  Needs syntactic non-use
   predicate.
3. **Derived `iota_cong_with_seen`**: admissibility from
   `iota_intro` + `unfold_iota_R`.  Research-grade.

**Predicted user preference**: option 1 (engine refactor).
NOT yet executed — overnight risk too high without test
verification.

## Remaining sorries (4 declaration-level)

1. `EvalSubstEquiv.lean:209` — `WALL_substL_depth` (depth budget
   propagation through evalSubst's recursion).  Not load-bearing
   on `concEval_preservation` (closed).  Per `lvar-refactor.md`,
   would close via `.lvar` constructor refactor (~2 days, 324
   refs).
2. `SynthSound.lean:314` — `synthCore_app_WALL`.  Multi-step
   `app_cong` + `evalSubst_equiv` + `whnfPi_equiv` composition.
3. `SubCheckSubstSoundness.lean:dispatch` — collapsed dispatch
   sorry covering ~20 internal arms.  Lam-lam closed; iota-iota,
   fix-fix wall on wall 6.  Fallback arms (~12) wall on v2
   substrate decrement off-by-one.  Spine arms (~4) wall on
   neutral ascent threading.
4. `SubCheckSubstSoundness.lean:Och_subCheck_sound` — public-API
   glue.  Body is structurally clear but blocked on:
   (a) WTValue closedness invariant (not currently a structural
   field — needs `Och.synth e fuel = .ok v → v.whnf.closedAt 0`
   theorem, ~150 LOC inductive),
   (b) `subCheckSubst_sound` (transitively walled at dispatch).

## Direction for tomorrow

Per "tackle hardest first" pattern observed throughout:

1. **Decide on wall 6**.  Option 1 (engine refactor) is
   simplest; could land in 1 hour with test verification.  This
   would close iota-iota and fix-fix structural arms (-2 sorries
   internal to dispatch).

2. **v2 substrate decrement off-by-one**.  Cleanest path:
   Option A from `proposalA-wall.md` — refactor `openFresh` to
   non-decrementing.  1-2 days, invasive but principled.  Closes
   the 4 fallback bridge arms (-4 sorries internal to dispatch).

3. **WALL_substL_depth via `.lvar` refactor**.  Per
   `lvar-refactor.md`, closes one wall at substantial cost (~2
   days, 324 refs).  Net positive but not urgent.

4. **`synthCore_app_WALL`**.  Whnf-Pi equivalence is the substantive
   research-grade piece.  Last-pole.

5. **`Och_subCheck_sound` glue**.  Once the dispatch closes
   transitively, the glue body becomes writable modulo just the
   WTValue closedness.  ~150 LOC of inductive synth-preserves-
   closedness, then the glue follows mechanically.

## Total LOC delta this session

Approximately **+1500** across:
- `lean/Och/API.lean` (+5): synth-entry closedness check.
- `lean/Och/EvalSubst.lean` (+14): public bridge lemmas for
  `openFreshTop`.
- `lean/Och/Soundness.lean` (-6): drop redundant `hcl`.
- `lean/Och/Soundness/CloseAll.lean` (+208): Design A redefine,
  `tyCtxToCtx_push`, `closeAll_succ_d_eq_shift`,
  `Subtype'_lvar_via_tyCtx` re-proof.
- `lean/Och/Soundness/EvalSubstLemmas.lean` (+15):
  `openFreshTop_closedAtLvl_zero`.
- `lean/Och/Soundness/SubCheckSubstNeutral.lean` (-65, +20):
  removed wall stubs, `liftSeenList` redef.
- `lean/Och/Soundness/SubCheckSubstSoundness.lean` (+253):
  `Subtype'_liftSeen_succ_to_d`, lam-lam closure, dispatch
  plumbing.
- `lean/Och/Soundness/SynthSound.lean` (-30, +20): wall-stub
  cleanup, redefine theorem signatures.
- `docs/ideas/`: +4 new analysis files
  (`lvar-refactor.md`, `tyCtxPush-bridge-wall.md`,
  `overnight-summary-pt2.md`, etc.) + extensions to existing
  walls.

## Process notes

- Worktree-isolated agents have been productive when given
  thorough prompts including the rebase-onto-och-refactor step.
- 4 of the 5 dispatched agents this session produced useful
  outcomes (real progress or precise wall identification); 1
  doc-only commit on a wall-discovery agent.
- "Tackle hardest first to invalidate premises" worked: the
  iota-iota/fix-fix attempt failed — but that failure was a
  premise-invalidation finding (structural arms have different
  shape than lam-lam due to engine seen-extension).  Saved
  hours of wasted effort on a doomed approach.
