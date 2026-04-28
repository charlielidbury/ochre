# Open blockers — overnight effort 2026-04-28

Living list of items that need user input. Each is documented in
detail in its own doc; this is the index.

## 1. synth doesn't validate annotation closedness

**Surfaced**: 2026-04-28 03:50, by the `Close remaining synth_sound walls`
agent (commit `83e7366`).

**Wall**: `synthCore_topLevel_closedAt_WALL` in
`lean/Och/Soundness/SynthSound.lean` was found to be **provably false
as stated**. Counterexample: `λ:.bvar 5. .type` synth-passes (closedness
isn't checked on the lambda's domain annotation; `subCheckOpen .bvar 5
.type` accepts because `b' == .type` shortcuts to `.ok true`) but is not
`closedAt 0`.

**Connects to**: `docs/ideas/type-imprecision.md` — same root cause
(structural subtype's `S-Top` accepts anything ⊑ Type, including
ill-formed expressions in type-position).

**Resolution paths** (need user verdict):
1. **Runtime check**: synth verifies closedness of all annotations
   before accepting. Tightens synth's contract; matches the user's
   "synth gates concEval" framing.
2. **Hoisted precondition**: callers must ensure closedness; synth
   stays as-is. Less invasive but pushes the obligation upstream.
3. **`closedAtLvl` re-statement**: weaken the soundness theorem to
   require `closedAtLvl 0` instead of `closedAt 0`. Substrate-correct
   but loses the practical "synth gates concEval" claim.

**My read of user's preference**: option 1. The user has consistently
preferred tighter specs over loose ones, and explicitly framed synth
as "gating concEval against ill-typed problems". A synth that accepts
open annotations doesn't gate.

**Impact**: until resolved, `synth_sound` carries this as a sub-wall.
Chains through `Och_subCheck_sound` and the final `soundness`
composition.

## 2. closeAllAt_substL for arbitrary substituees

**Surfaced**: 2026-04-28 02:24, Proposal A v2 wall.

**Wall**: see `docs/ideas/proposalA-wall-v2.md`. The closeAll-substL
commutation walls for arbitrary substituees due to substrate-semantics
off-by-one (substL decrements; closeAll preserves).

**Affects**: 4 fallback arms (iota_intro, unfold-Fix-R/L, unfold-Iota-L)
in `Soundness/SubCheckSubstFallback.lean`.

**Resolution paths** (per `proposalA-wall-v2.md`):
1. **Engine-side fix**: refactor `openFresh`/`substL` to non-decrementing
   (standard locally-nameless `open`). 1-2 days, invasive.
2. **closeAllSubst variant**: 2-3 days, additive but trickier.
3. **β-reduction bisimulation sidestep**: tried 2026-04-28 02:50
   (`v2-sidestep-wall.md`) — only works at depth 0.

**My read**: option 1 long-term, but the v2 issue is engineering rather
than research, so could be deferred without blocking the metatheory
direction.

## 3. closeAll-evalSubst commutation at non-zero depth

**Surfaced**: 2026-04-28 03:30, evalSubst_equiv agent.

**Wall**: `evalSubst_bridge_WALL_a/b` in `Soundness/SubCheckSubstSoundness.lean`.
`evalSubst_equiv` works at depth 0; lifting through `closeAll` at
non-zero depth (which is where subCheck operates) requires a separate
commutation lemma not yet proven.

**Connects to**: same family as wall 2 (closeAll commutation lemmas).
Plausibly resolvable by the same engine-side fix.

## 4. seen-coherence and 12-arm dispatch in `subCheckSubst_sound`

**Surfaced**: 2026-04-28 03:00, mutual block agent.

**Wall**: 1 sorry for `seen_coherence_WALL` (closeAll-coherence of
the engine's seen-list with the declarative seen-set). Plus 1 collapsed
sorry covering 12 shape arms — each arm needs `tyCtxToCtx_push` and
closedness invariants to fully close.

**Resolution**: write the 12 arms (~300-400 LOC mechanical).
Conditional on walls 2+3 because the fallback arms route through
those.

## Summary

| Wall | File | Severity | Resolution |
|---|---|---|---|
| 1: synth annot closedness | SynthSound | HIGH (false-as-stated) | option 1 (validate in synth) |
| 2: closeAllAt_substL | SubCheckSubstFallback | MEDIUM | engine-side fix or wait |
| 3: closeAll-evalSubst | SubCheckSubstSoundness | MEDIUM | same family as 2 |
| 4: seen + 12 arms | SubCheckSubstSoundness | LOW (mechanical) | grind it out |

The three top-level theorems' status:
- `synth_sound`: walled at 1.
- `subCheck_sound`: walled at 2+3+4.
- `concEval_preservation`: ✅ closed.
- `synth_progress`: ✅ closed.
- `soundness` (composition): body sorry-free; only upstream walls.
