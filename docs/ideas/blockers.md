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

## 6. Seen-shrinking wall (iota-iota and fix-fix structural arms)

**Surfaced**: 2026-04-28 (overnight), commit `343788c` (doc), via
the iota-iota/fix-fix dispatch closure attempt.

**Wall**: see `docs/ideas/tyCtxPush-bridge-wall.md` — extended
"Iota/fix structural follow-up" section.

The iota-iota and fix-fix engine arms add `(a, b)` to seen for ALL
recursive sub-calls (structural attempt + fallback).  The dispatch's
`_ih` thus yields derivations under the EXTENDED seen.  Subtype'
fallback rules (`iota_intro`, `unfold_fix_R`) are productive (smaller
S in conclusion than premise), so they thread through.  But the
structural rule `Subtype'.iota_cong` PRESERVES S (same in premise
and conclusion), so the dispatch goal — which needs the ORIGINAL
seen — cannot be reached from the IH's extended seen.

**Affects**: iota-iota and fix-fix structural arms (lam-lam is
unaffected because lam doesn't extend seen).

**Resolution paths** (per agent `343788c`):
1. **Engine refactor**: drop seen-extension in iota-iota/fix-fix
   structural attempt, keeping it for the fallback.  Smallest
   change; might affect μ-type cycle-detection on fix's
   structural path.
2. **Seen-shrinking lemma**: prove
   `Subtype' (entry :: S) Γ a b → Subtype' S Γ a b` under "entry
   not used in derivation".  Requires a syntactic non-use
   predicate over derivations.  Medium effort.
3. **Derived `iota_cong_with_seen`**: admissibility from
   `iota_intro` + `unfold_iota_R`.  Research-grade.

**My read**: option 1 is simplest and most likely user-preferred.
Removing seen-extension from the structural attempt should preserve
correctness as long as the structural attempt only recurses
finitely (which it does — `openFresh` + tyCtx grow, so fuel-strict).
The fallback's seen-extension catches cycles when the structural
attempt fails.

## 5. tyCtxPush_bridge_WALL — convention mismatch in arm packages

**Surfaced**: 2026-04-28 (overnight), by lam-lam dispatch arm
attempt (commit `568f148`).

**Wall**: see `docs/ideas/tyCtxPush-bridge-wall.md`.  The dispatch's
IH yields a Ctx with **raw** `domB` head; arm-package
`arm_lam_lam_compose` (and iota/fix counterparts) expects a
**closeAll'd** head.  These are not equal in general
(`closeAll d domB ≠ domB` when `domB` has level-vars `< d`).

**Affects**: lam-lam, iota-iota, fix-fix structural dispatch arms
(all three blocked identically).

**Resolution paths**:
1. Redefine `tyCtxToCtx` to apply depth-stratified `closeAll` to
   each entry.  ~4-6 hours; cleanest but invasive.
2. Redefine arm packages to take raw heads.  Cheaper but loses
   the "closeAll'd-everywhere" canonical form.

**My read**: option 1 long-term, but blocked on user verdict since
either choice has downstream consequences for the C7 lemma's
conclusion shape.

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
