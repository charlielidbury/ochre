# Slice prover: working note (keep current; a successor continues from this alone)

Worktree `/home/charlielidbury/repos/ochre-slice`, branch `spine-slice` (push there; never push `main`;
`spine` only when main says so). Build: `cd ochr/core/lean && taskset -c 0-14 lake build OchrMeaning`
(must be green before every push). Sweep: `lake exe sweep` and `lake exe sweep --probes` (source
`Sweep.lean`). Commit messages end with `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`.
Report to `main` (SendMessage) at each boundary, then end the turn; main always replies.

## What is proved (standard axioms only)

- `dropOne_exists` (the drop where the place exists), `dropAt_data`, `copyRead_aligned`,
  `runs_valTypeDecl_keep` (`Slice/DecideKeep.lean`), `logEffect_rel_shapes` (`Slice/Shapes.lean`),
  `Slice/UpdAt.lean`.
- The grain asks a `*` step's borrow type (`StepOk .deref := ∃ d, r = .ref d`, with the checker's
  D101, taken at 567c1d11): `grain_deref_not_proof`, `not_below_proof`, `joinDropOne_noop` proved.
- `Regress/StepKindsTable.lean`: step kind × parent kind, checker and reference, kernel-checked; the
  table shows agreement at the restated grain cell by cell with the clause each cell needs.
- `Regress/JoinPrefixBorrow.lean`: 13 programs where a match's result borrows a prefix of a place the
  join drops, all rejected ([Entry], [Join] D65 + K1(g), D53 in tail position), asserted.
- Reopened lemmas, and what they wait on: `dropOne_exists` concludes the extended context itself
  since item 3, so it rests on `ctx_botWrite`, the [Access]/[End] hypothesis steps and the machine
  facts (main asks to be told whenever a closed lemma reopens).

## The fixed decision table (main's decision 2026-11-20, DONE at 1f328465)

The context's decisions `K.D` are fixed for a run (the item's final state's,
`Consistency.const_split` builds them so). A step assumes `(hD : DecTab K.D st')` (aligned
after it) and concludes `CtxOk { K with Δ := Δ' }` there; no `D'`, no `AgreeOld` anywhere.
- `DecAligned extends DecTab` + `blockCaps` (per state: it reads values).
- `Steps/MachineMono.lean` (machine-only, main staffs it as its own lane, do not prove unless asked):
  `TablesGrow`, `GrowsM` + closure lemmas (proved), (b) `DecTab.back` (sorry), (a) `grows_<fn>`
  (sorry, one per machine function an assembly's rest runs; add new ones there and to the
  `grows_step` macro), `DecTab.of_rest`.
- At an IH application for a sub-run ending at `st₁`, with `hrest : Runs rest st₁ b a st'`:
  `hD.of_rest (by grows_go) hrest` (add `; all_goals exact grows_<localDef> …` for local defs such
  as `mpFinal`). Match by reducible unfolding only, or `whnf` times out on big rests.
- Where a leaf hides the rest of a run (`closeCall_split`, `idType_split`, `const_split`), the leaf
  supplies `TablesGrow …` or `DecTab …` as a conjunct.

## Open leaves of the drop step (after item 3, 19d86568)

`joinDrop_step` and `dropOne_step_asm` rest on, beyond `MachineMono`'s machine facts:
- `ctx_botWrite` (DropOneAsm): `CtxOk` after the drop's write of `⊥`. Everything but the block's
  captures at the new entry set is routine; that part is D90's obligation 1 at the state after, a
  checker-only fact once the table is fixed (MachineMono's list). Item 4 measured it: 338 block
  entries in the suite, static = checker at all 335 successful ones (3 are [Join] rejections).
  Probe: scratchpad `probe/EntryProbe.lean`, `probe/entryprobe.patch` (instruments `blockEntry`).
- `etaFresh_sim` (MovedPlace): a fresh η record means its unknown, the context extended.
- `recordedNeutral_ok` (MovedPlace): a generalisation record's value means the program (path condition).
- `Rel.kept` (EqJAsm, the lead's).
[Access]/[End] are now IH fields in the extended form; `access_ctx`/`dropAtJoin_ctx` are gone.
The lead owns `Steps/Statements.lean` from 19d86568: statement changes go through the lead.

## Typed temporaries (the new lead's coming change)

`botWrite_good` treats every position alike (the written one vs the rest, `mean_setAtE_other`);
the one temporary-specific spot is `posTyM_setAtE`'s `temp` case, `rfl` today because a temporary
has no type: with typed temporaries it needs "a write leaves a temporary's stored type as it was".
`dropOne_exists` writes only at a binding (`.bind f i`). The arm's result in flight is untouched by
the write. `dropAtJoin` rejects a drop whose value holds a loan of a borrow a temporary holds (D65),
so the drop's own access ends no such borrow; a borrow the result holds that is lent at a PREFIX of
the place (ended by `movedPlace`'s fill branch, `accessPath` of the parent) is not covered by that
check: to look at when temporaries get types.

## Idioms and traps

- `Runs f st fuel a st'` := `∃ L left log, runMachineL f st fuel L = (.ok a st', left, log)`;
  invert with `Runs.bind_inv`, `runs_get_inv`, `runs_pure_inv`, `runs_content_inv`, ….
- `lake env lean` lets unbound names through (autoImplicit); always `lake build` the module.
- Kernel-checked counterexamples: `Regress/GenNeutralContent`'s `isOk`/`outVal`/`outSt`/`runs_out`
  with `decide +kernel`; `Place` equality via `Place.beq`; no `DecidableEq DeclInfo` (use a `match`).
- `#sorry_leaves` (scratchpad `Measure.lean`, `ci.value? (allowOpaque := true)`) lists the sorried
  declarations a theorem rests on.
- The sweep's walk never steps under a `⋆` (blind spot). Report clauses (`report := true`) never
  fail the sweep. New facts about checker states are swept before they are assumed.
- zsh: quote globs (`--include='*.lean'`); a backtick inside a double-quoted shell string breaks
  the whole command (write Python to a file instead).
- (Hη≠) `ShapeFacts.etaNoSelf`: no η record names its own unknown (its recorded parameters may
  name older ones; the fields are always newer).
