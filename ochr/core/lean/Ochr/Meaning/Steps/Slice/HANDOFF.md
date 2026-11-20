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
- On the side branch `spine-slice-grainref` (94c478f9, approved, NOT yet on `spine-slice`): the
  grain asks a `*` step's borrow type (`StepOk .deref := ∃ d, r = .ref d`); with it
  `grain_deref_not_proof`, `not_below_proof`, `joinDropOne_noop` are proved. Take it only after
  main says D101 (the checker's `jdGrain` check) is on `main`: merge `origin/main`, then rebase the
  side branch's commit onto `spine-slice`.
- `Regress/StepKindsTable.lean`: step kind × parent kind, checker and reference, kernel-checked.

## The fixed decision table (main's decision 2026-11-20, in progress)

The context's decisions `K.D` are fixed for a run (the item's final state's,
`Consistency.const_split` already builds them so). A step assumes `(hD : DecTab K.D st')` (aligned
after it) and concludes `CtxOk { K with Δ := Δ' }` there; no `D'`, no `AgreeOld`.
- `Statements.lean`: DONE (46 statements got `hD` before `(bh : Nat)`; `ExtOk`, `SimConcl`,
  `SimConclT` lost `D'`; `AgreeOld` deleted; `DecAligned extends DecTab` + `blockCaps`).
- `DecExtend.lean`: deleted (`meanV_congrD`, `runT_congrD`, `decAligned_grow` gone).
- `Steps/MachineMono.lean`: `TablesGrow`, `GrowsM` + closure lemmas (proved), (b) `DecTab.back`
  (sorry), (a) `MachineGrows` (sorry, one field per machine function an assembly runs; fill as
  sites need them), `DecTab.of_rest` (an assembly's tool). Main staffs (a), (b) as their own lane.
- Repair status: `DropOneAsm` DONE; `MovedPlace`, `Match`, `SplitAsm`, `EqJAsm`, `CallAsm`, `IdAsm`,
  `Consistency` and the rest TODO. Generic textual pass: `scratchpad/genfix.py <file>`.
- At every IH application whose statement has `hD`: supply `DecTab K.D st₁` for the sub-step's
  post-state as `hD.of_rest (rest grows) hrest`, where `hrest` is the run of the rest of the
  computation (from `Runs.bind_inv`) and its growth comes from `MachineGrows` fields + closure.

## Open leaves of the drop step (what each rests on)

- `access_ctx`, `dropAtJoin_ctx`: become the hypothesis's/compositions once [Access]/[End] conclude
  the extended form (item 3 of main's queue).
- `etaFresh_sim` (fresh η record means its unknown), `placeTypeQ_sim` (item 3: state `placeType?`
  as a private computation like `evalType_step_stmt`, `KeptAfter`/`ExtOk`/`Rel.kept`; FIRST sweep
  whether its private copies can leave an η record naming an unknown of an empty type),
  `recorded_sim` (item 3: a hypothesis field `substEnv_neutral_step` in the form of
  `substEnv_abs_step`).
- `meanV_ext`: the assignment-and-Δ congruence only (`AssignCongr` shape).
- Block captures after a write (item 4): measure on recorded states that the static instance at
  the new entry set is what the checker computes; do not prove.

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
