# Sorry-Closure Plan (preservation-only soundness)

**Goal.** Close the four remaining declaration-level `sorry`s in
`lean/Och/SoundnessProof.lean` so the existing preservation-only
soundness chain (`typeCheck_sound`, `concEval_preservation`,
`soundness`) becomes axiom-clean (only `[propext, Classical.choice,
Quot.sound]`). No `concEval` return-type refactor. No strengthening
to `progress_mod_fuel` — that is Phase 2 per
`docs/ideas/soundness-strengthen.md`.

Four declaration-sorries, 16 internal sub-sorries, as of commit
`2b45724`:

| # | Decl | Lines | Sub-sorries |
|---|------|------|-------------|
| 1 | `eval_vapp_preserves_fullyQuotable` | 2463–2608 | 4 |
| 2 | `quoteClosure_realises` | 3673–3682 | 1 (body) |
| 3 | `vapp_realises` | 3858–4070 | 7 (lam + iota/fix unfold) |
| 4 | `tyInfer_sound_open` | 5174–5326 | 7+ (mix of real + A9) |

Existing infrastructure is strong — the hardest structural work
(`Equiv_c d`, R-clause refactor, `Closure.fullyQuotable`,
`envFullyQuotable`, `quote_depth_shift_n`, `R_depth_lift`) is done.
What remains is **assembly** + closing three real obligations plus
one known-unprovable case (A9).

## Scope boundaries (all tasks)

- DO NOT refactor `concEval`'s return type. Phase 2.
- DO NOT touch declarative `Subtype'` rules.
- DO NOT attempt to fix A9 algorithmically. DECISION-LOG 2026-04-22:
  algorithm is correct, proof statement is wrong. Leave `.fix`/`.iota`
  Category C sorries with a comment tag.
- DO NOT introduce new axioms. Every proof must land axiom-clean
  (verify with `#print axioms`).
- DO NOT weaken `soundness`'s statement.

## Per-sorry tasks

### Task 1 — `eval_vapp_preserves_fullyQuotable` (tier 2)

**What.** Mutual statement: eval and vapp preserve
`Val.fullyQuotable d`. 4 sub-sorries at lines 2536, 2541, 2597, 2608.

**Root cause.** `Val.fullyQuotable d v` should imply `∃ q, quote
fuelω d v = some q` but proving that standalone is circular for
closure cases.

**Approach.** Strengthen the conclusion on BOTH eval and vapp sides
to carry `(∃ qv, quote fuelω d v = some qv)` alongside
`Val.fullyQuotable d v`. Add `Closure.envLevelsBelow` /
`Val.levelsBelow` as new hypotheses where needed (both already
provable — see `eval_vapp_levelsBelow` at line 2313).

The closure-case quote witness requires `quoteClosure` to succeed,
which requires eval on the body at fuelω. If this turns circular,
fall back to a helper lemma `fullyQuotable_has_quote`.

**Complexity.** Tier 2 (bridge threading), 2–4h.

**Acceptance.**
1. No `sorry` in `eval_vapp_preserves_fullyQuotable`.
2. `lake build` green.
3. `#print axioms Och.NbE.eval_vapp_preserves_fullyQuotable`
   axiom-clean.
4. Downstream consumers still typecheck.

---

### Task 2 — `vapp_realises` internal sorries (tier 1)

**What.** 7 sorries in `vapp_realises` (3917, 3920, 3921, 3972,
3976, 3977, 4042, 4046, 4047) + 1 in `eval_realises .letE` (4193).

**Approach.** Add 6 new hypotheses to `vapp_realises`:
- `hvfLvl : Val.levelsBelow d vf`
- `hvaLvl : Val.levelsBelow d va`
- `hvfFq : Val.fullyQuotable d vf`
- `hvaFq : Val.fullyQuotable d va`
- `hqvf : ∃ qf, quote fuelω d vf = some qf`
- `hqva : ∃ qa, quote fuelω d va = some qa`

Each sorry closes directly from matching new hypothesis. Caller sites
(`eval_realises .app` and recursive `vapp_realises` calls) supply
them via Task 1's strengthened lemma.

**Prerequisite.** Task 1 landed.

**Complexity.** Tier 1, ~2h.

**Acceptance.**
1. No `sorry` in `vapp_realises` or `eval_realises .letE`.
2. `lake build` green.
3. `#print axioms` on both axiom-clean.

---

### Task 3 — `quoteClosure_realises` (tier 3 structural)

**What.** Forward-reference blocker: `quoteClosure_realises`
declared BEFORE `eval_realises` / `R_quote_equiv` in the file.
Docstring lays out the 4-step proof sketch.

**Approach (Route A — preferred).** Inline `quoteClosure_realises`'s
proof into each of the 3 call sites in `R_quote_equiv`'s
`.lam`/`.iota`/`.fix` cases. Delete the standalone theorem. Add
`(fuel, sizeOf v)` lex measure to `R_quote_equiv`'s `termination_by`.

**Route B (fallback).** If Route A's termination measure fails,
prove `quoteClosure_realises` as a post-mutual theorem using
`eval_realises` + `R_quote_equiv` non-recursively.

**Prerequisite.** Tasks 1, 2 landed.

**Complexity.** Tier 3, 4–8h. Most termination-checker risk.

**Acceptance.**
1. No `sorry` in quoteClosure/R_quote_equiv.
2. Mutual termination accepted.
3. `lake build` green, axioms clean.

---

### Task 4 — `tyInfer_sound_open` internal sorries (tier 2 + A9)

**Categories.**

**A (trivial post-Task 1).** Lines 5243, 5303, 5305, 5306 — all
supply `hnfq` witness derivable from strengthened
`eval_preserves_fullyQuotable`.

**B (real work).** Lines 5269 (.lam), 5279 (.app β fast-path), 5285
(.app let-float), 5291 (.app generic), 5325 (.letE). Need
`whnfPi_quotes` helper, `app_elim`-style derivation, and a
`.letE` shift inverse.

**C (LEAVE SORRIED).** Lines 5256, 5257 — A9. Tag with comment:
```
sorry -- A9 known hole; see DECISION-LOG 2026-04-22.
```

**Critical invariant to verify.** After Task 4, `#print axioms
Och.Soundness.typeCheck_sound` MUST be axiom-clean. DECISION-LOG
says `tyCheck`'s dedicated `.fix`/`.iota` arm intercepts, so the
A9 sorries in tyInfer should NOT transit into typeCheck_sound. If
they do, A9 is wider than documented — raise a flag, don't patch.

**Prerequisite.** Tasks 1, 2, 3 landed.

**Complexity.** Category A: ~1h. Category B: 4–8h. Category C: 0.

**Acceptance.**
1. Category A closed.
2. Category B closed (or specific sub-sorries flagged with reason).
3. Exactly 2 `sorry`s remain (Category C, A9).
4. `#print axioms Och.Soundness.typeCheck_sound` axiom-clean.

## Execution order

```
Task 1 (strengthen eval_vapp) → [prereq for all]
  ↓
Task 2 (vapp_realises) [run sequentially, same mutual block]
  ↓
Task 3 (quoteClosure_realises) [termination risk]
  ↓
Task 4 [split: 4A Category A, 4B Category B]
```

Tasks 2 and 3 are textually non-overlapping but share mutual
termination plumbing. Sequential is safer.

## Risk register

- **Task 1** closure-case quote witness circularity: 60% clean,
  30% needs helper lemma, 10% deeper.
- **Task 3** termination measure: 50/50 Route A vs Route B.
- **Task 4B** `.letE` shift inverse: 40% chance needs lemma
  restatement.
- **If typeCheck_sound** shows sorryAx after all four tasks, A9
  leaks into the top-level; separate investigation needed.

## Verification after each task

```bash
# Sorry-count delta
git diff lean/Och/SoundnessProof.lean | grep -c "^-.*sorry"
git diff lean/Och/SoundnessProof.lean | grep -c "^+.*sorry"

# Axiom check (run inside a Lean file)
#print axioms Och.Soundness.typeCheck_sound
#print axioms Och.Soundness.soundness

# Build
nix develop --command bash -c "cd lean && lake build"
```

## Expected outcome

If all four tasks close cleanly, `soundness`, `typeCheck_sound`,
`concEval_preservation` will be axiom-clean (only `[propext,
Classical.choice, Quot.sound]`). The 2 remaining A9 sorries in
`tyInfer_sound_open` are documented and NOT on the path to
`typeCheck_sound`.

Phase 2 (`progress_mod_fuel`) starts from this clean baseline —
see `docs/ideas/soundness-strengthen.md`.
