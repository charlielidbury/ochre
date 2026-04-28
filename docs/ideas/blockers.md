# Open blockers — overnight effort 2026-04-28

Living list of items that need user input. Each is documented in
detail in its own doc; this is the index.

## 1. synth doesn't validate annotation closedness — RESOLVED

**Surfaced**: 2026-04-28 03:50, by the `Close remaining synth_sound walls`
agent (commit `83e7366`).

**Resolved**: 2026-04-28 (overnight), via option 1 (runtime check in
synth).  `Och.synth` now validates `e.closedAt 0` at entry and
rejects with `.error` otherwise.  The previously-walled lemma
`synthCore_topLevel_closedAt` proves trivially by unfolding synth
and ruling out the rejection branch.

The autonomous decision matched the predicted user preference
(tighter specs / "synth gates concEval" framing).  Reversible if
disagreed with: revert `Och.synth` and revert
`synthCore_topLevel_closedAt`'s body to a `sorry`.

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
- `synth_sound`: walled at `synthCore_app_WALL` only (was 2 walls; closedness wall closed via synth-entry check in commit c121da9).
- `subCheck_sound`: walled at 2+3+4.
- `concEval_preservation`: ✅ closed.
- `synth_progress`: ✅ closed.
- `soundness` (composition): body sorry-free; only upstream walls.

End-to-end `soundness` statement simplified in commit 64b96f8 — the
redundant `hcl : e.closedAt 0` premise dropped from both
`synth_progress` and `soundness`, derived internally from synth.
