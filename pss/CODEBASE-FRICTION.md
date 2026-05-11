# Codebase friction notes — things making this hard

A running log of things that make work harder than it needs to be. To be acted on in a future cleanup pass.

## 1. Misleading `#print axioms` output for residual-conditional theorems

The `_proved` endpoints take residuals as **parameters**, not as Lean `axiom` declarations. So `#print axioms` shows only kernel axioms, even when the theorem is still conditional on multiple open obligations.

Multiple agents (and at least one cron-check) read `[Classical.choice]` as "closed" when in fact the theorem still has 4 residual parameters.

**Fix:** add a `Pss.Sanity` audit that prints the *parameter types* (residuals) alongside the axioms list. Or refactor so residuals are Lean `axiom` declarations until discharged.

## 2. Two parallel bundle developments

`Lemma_2_BundleProof.lean` (same-context bundle, walled at AppBet) and `Lemma_2_DiamondGeneral.lean` (general-context bundle, current) coexist. The former still ships infrastructure (`bridgeSubToEquHead`, `MEqRedDepth`) that the latter imports. Confusing.

**Fix:** extract shared infrastructure to `Pss/Paper/Lemma_2_Infrastructure.lean` and delete or stub the obsolete bundle file.

## 3. `bridgeSubToEquHead` duplicated

There's `sub_to_equ_head_replace` in `Pss/Mpss/DeBruijnReductions.lean` (tactic-mode) AND `bridgeSubToEquHead` in `Pss/Paper/Lemma_2_BundleProof.lean` (structural with depth-equality witness). The second was added because the first's tactic-mode definition resisted depth-preservation proofs.

**Fix:** make the original `sub_to_equ_head_replace` structural so depth preservation works directly. Then drop the duplicate.

## 4. STOP-*.md files accumulating

`STOP-PAPER-BUG-LEMMA-32.md`, `STOP-PAPER-GAP-LEMMA-2-PROVAR.md`, `STOP-VERDICT-C-WALL-ANALYSIS.md`, etc. Some are now superseded (Lemma 32 STOP was wrong; Verdict C STOP is a partial diagnosis). They accumulate as dispatch artifacts.

**Fix:** retire superseded STOP files. Keep only the current active diagnosis (`LEMMA-2-DIAGNOSIS.md`).

## 5. `MoreoverDiamondGeneral`'s universal-x ∀ baked into predicate

The `∀ (x : Nat)` is INSIDE the existential, baking universal-x quantification into every consumer's obligation. This forces ProVar/VarPro to deliver universal-NP on the lifted derivation, which is the actual wall.

**Fix:** parametric-x predicate (Option 3 in the diagnosis). Major refactor.

## 6. Misleading wrapper name: `_unconditional_UniformEqDiamonds`

The wrapper `Lemma_2_DeBruijn_DiamondMEqRedStar_proved_unconditional_UniformEqDiamonds` is "unconditional on UniformEqDiamonds" (i.e., discharges that residual) but conditional on 4 NEW residuals. Reading the name, a user might think it's unconditional overall.

**Fix:** rename to `_with_UniformEqDiamonds_discharged_via_bundle_payloads`. Verbose but accurate.

## 7. `MoreoverDiamondGeneral_ProVarVarPro_Payload` etc. are conditionally-true Props that can't be discharged at the bundle level

These payloads document the gap rather than provide a proof. They're paper-faithful only in the sense that the paper has the same gap. They're useful as "outsource the problem" but a real closure requires either dropping them or proving them via a different proof technique.

**Fix:** depends on chosen Option (3, 4, or 5 in diagnosis).

## 8. Cron success criterion was wrong

The cron at :47 checked `#print axioms` for `[propext, Classical.choice, Quot.sound]` — which always appears (residuals are parameters, not axioms). So the cron would have looped indefinitely, never detecting the actual closure (or non-closure).

**Fix:** cron should check parameter types instead, or just delete/replace this kind of automated check until a real signal exists.

## 9. PAPER-PROOFS.md hasn't been updated since Lemma 2 closure work began

The index says Lemma 2 status as of an earlier dispatch. Now we've shipped substantial Lemma 2 infrastructure (cells, bundle, wrapper) but the index doesn't reflect it. New agents reading the index get a stale picture.

**Fix:** refresh PAPER-PROOFS.md at the end of each session-end-state to reflect current closure status.
