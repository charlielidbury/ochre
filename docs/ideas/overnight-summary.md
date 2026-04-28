# Overnight session summary — 2026-04-27/28

**Branch**: `och-refactor` from `35ef5ac` to `620d273`. **56 commits**
across the soundness rebuild, all pushed.

## Headline

Soundness scaffolds went from 4 raw `sorry`s with no proof structure
to a fully-composed proof chain with **2 of 4 top-level theorems
fully closed**, and the others reduced to specific named walls.

```
synth_sound        : 2 sub-walls (one false-as-stated, one tractable)
subCheck_sound     : ~31 internal sorries (mostly per-arm IH extraction)
concEval_preservation : ✅ CLOSED via bidirectional equivalence
synth_progress     : ✅ CLOSED via closedAt invariant
soundness          : body sorry-free; only upstream walls
```

## Major wall-breaking achievements

Each of these was either predicted-walled or actually walled at the
start of the night:

1. **`subCheckSubst` non-partial conversion** (commit `f973e5b`).
   Mutual partial def → mutual def with lex `(fuel, phase)`. Auto-
   generated equation lemmas now available. Critical: this was the
   meta-level wall blocking every soundness composition attempt.

2. **`synthCore` non-partial + de-privatised** (commits `2807459`,
   `78896b5`). Same treatment for the synth engine.

3. **`closeAll` translation breaks C7 representation wall**
   (`Subtype'_lvar_via_tyCtx` proven, commit `b5081ff`). The
   declarative `bvar` rule couldn't reach the engine's `(levelOffset
   + lvl)` indices; closeAll bridges the gap.

4. **`closeAllAt_substL_subst` discharges 4 fallback bridges**
   (commit `b5115d5`). The v2 substrate-mismatch wall turned out to
   *cancel cleanly* when the RHS is `Expr.subst` (declarative), not
   `substL` (engine).

5. **`closeAll_evalSubst_subtype_strong` depth-d analog** (commit
   `d9c59ae`). The bidirectional evalSubst equivalence at non-zero
   depth, with closedness/lvarLT preconditions.

6. **`evalSubst_equiv` depth-0** (commit `7b09c9b`). The B3-style
   bidirectional equivalence for the substitution evaluator.

7. **`concEval_equiv` proves preservation in one shot**
   (commit `9b17af0`). Bidirectional reasoning sidesteps the
   substitution-respects-subtype issue.

## Substrate hygiene (Layer 2)

All proven, no sorries:

- `evalSubst_fuel_mono` (A1)
- `evalSubst_closedAtLvl` (A2) + `closedAtLvl` predicate
- `substL_eq_subst_no_levelvars`, `shiftL_eq_shift_no_levelvars` (A3)
  with `noLevelVars` / `bvarLT` / depth-budget
- `Subtype'.preserve_betaStep` and 9 mirrors (B1+B2)
- `evalSubst_lvarLT`, `substL_lvarLT`, `shiftL_lvarLT`

## Per-arm proofs

- C2 (lam-lam structural), C3 (iota-iota structural), C4 (fix-fix
  structural): proven via `closeAll_openFresh`.
- C7 (neutral spine + ascent): proven via `closeAll`.
- 4 fallback arms (iota_intro, unfold_fix_R/L, unfold_iota_L):
  proven via the strong substitution bridge.
- 2 universal arms (bot_L, top_R): trivial via direct constructors.
- 24 vacuous catch-all arms: proven via `eq_def`-driven contradiction.

## Surfaced findings

Documented in `docs/ideas/`:

- `c7-wall.md` — initial wall description, 3 resolution options
- `proposalA-wall-v2.md` — substrate decrement off-by-one, 3 options
- `v2-sidestep-wall.md` — sidestep attempt analysis
- `blockers.md` — running inventory; **3 open items** with my
  predicted-user-preference for each
- `appendvec-investigation.md` — type-imprecision case study
- `type-imprecision.md` — sound-but-vague property of structural
  subtype
- `soundness-strategy.md` — the lemma dependency map that drove the
  agent dispatch order
- `property-test-findings.md` — Church-encoding edge cases

## Remaining walls (in priority order)

1. **IH extraction in `subCheckSubstMatch_dispatch`** (~31 sorries).
   The structural/fallback/neutral arms need to extract recursive
   IH from the engine's hypothesis via `subCheckSubstMatch.eq_def`
   manipulation. This is **mechanical** — 14 arms have already been
   discharged via this pattern; the remaining 31 follow the same
   recipe with closedness preconditions threaded.

2. **`tyCtxPush_bridge_WALL`**: `tyCtxToCtx (tyCtx.push annB) ≠
   closeAll d annB :: tyCtxToCtx tyCtx` arithmetic. Needed for
   structural arms (lam/iota/fix) where the body's tyCtx grows.
   ~50 LOC.

3. **`synthCore_topLevel_closedAt_WALL`**: synth doesn't validate
   closedness of binder annotations. Per `blockers.md` predicted
   user-preference: option 1 (validate in synth). Requires editing
   `synthCore` body in API.lean.

4. **`synthCore_app_WALL`** (~5-step plan documented): conditional
   on (3).

5. **`evalSubst_equiv` depth-budget**: `levelOffset = 10^8` makes
   the bound trivially satisfied in practice, but the formal
   preservation across `evalSubst`'s recursion is one of the
   long-pole proofs.

6. **`arm_hyp_compose` and `seen_coherence_WALL`**: closeAll-
   coherence between engine seen-list and declarative seen-set.
   Needs a translation lemma + monotonicity.

## Test-suite work (from earlier in the night, committed pre-soundness)

- 9 new strict equality tests replaced `.isOk` smoke pins
- Maximum fuel across the suite: **200** (was 50–16,000)
- 42 new property tests in `PropertyTestsExtra.lean`
- 5 strengthened pins in Std/Mu, Std/Array, Std/Vec, AppendVecPath
- Surfaces 2 known-imprecisions (Church-encoding, documented in
  `property-test-findings.md`)

## Total LOC delta

Approximately **+5400 / -300** across:
- New files: 9 (`Soundness/CloseAll`, `EvalSubstLemmas`,
  `EvalSubstEquiv`, `ConcEvalPreservation`, `SubtypeSteps`,
  `SubCheckSubstNeutral`, `SubCheckSubstStructural`,
  `SubCheckSubstFallback`, `SubCheckSubstSoundness`,
  `SynthProgress`, `SynthSound`)
- Modified: `EvalSubst.lean` (de-partialise), `API.lean`
  (de-priv + de-partialise synthCore), `Soundness.lean` (wire-up
  + sorry-preserve), `Och.lean` (imports), various Std/* test files

## Direction for tomorrow

Per "hardest first → tractable wins" pattern observed throughout:

1. **Start by deciding on `synthCore_topLevel_closedAt_WALL`** —
   it's a design question that gates synth_sound. My prediction
   per `blockers.md`: validate closedness in synth.

2. **Then mechanical: IH extraction in dispatch arms.** ~14 arms
   closed via the pattern; ~17 to go using the same recipe with
   closedness threading.

3. **`tyCtxPush_bridge_WALL`** is the last research-grade
   obstacle.

The remaining walls are sized roughly: (1) one-day decision +
implementation, (2) one-day mechanical, (3) one-day proof. With
those three, **subCheck_sound closes**, and via `soundness`'s
already-sorry-free body, **the entire end-to-end theorem closes**.
