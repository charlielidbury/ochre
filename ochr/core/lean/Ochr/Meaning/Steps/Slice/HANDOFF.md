# Slice lane: handoff note (for a successor who has seen none of this)

## First thing to do

`spine` is now **f9f685df** (the data layer's final state: function application, a constructor's
membership, and the substitution lemma for unknowns proved). Merge `origin/spine` into `spine-slice`
first, then `origin/main` if it has moved; build `OchrMeaning`; re-run `#sorry_leaves` on
`joinDrop_step` to see the open pieces as they stand.

## Where and how

- Worktree `/home/charlielidbury/repos/ochre-slice`, branch `spine-slice`. Push there after every
  commit. Never push `main`. Fast-forward `spine` only when main (the orchestrator, `main`) says so.
- Build: `cd ochr/core/lean && taskset -c 0-14 lake build OchrMeaning` (green before every push;
  `lake env lean` alone lets unbound names through: autoImplicit is on per file).
- Commits end with `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`. A statement change is
  its own commit, its message says it is one, and it needs main's authorisation. **The lead
  (`spine-lead`) owns `Steps/Statements.lean`**: statement changes go through main to the lead.
- Report to `main` (SendMessage) at each boundary, then end the turn; main always replies. Say
  plainly when a lemma that was closed (standard axioms) reopens, and what it now waits on.
- New facts about checker states are swept before they are assumed (below). A false statement is
  recorded as a kernel-checked counterexample under `Meaning/Regress/`. A checker fault (an accepted
  program on which the theorem is false in spirit) stops everything: send the smallest program.
- Design log `ochr/docs/31-meaning-spine.md`, work units `docs/32`, problem themes `docs/35` (in the
  primary checkout `/home/charlielidbury/repos/ochre`).

## What the lane is: the drop at the join (D84)

After a match arm, the checker drops every place some arm moves (`Machine.joinDrop`: `movedPlace`
re-roots a place that does not exist, `dropAtJoin` ends a borrow, skips a copy, or accesses and
writes `⊥`). The reference does `Run.joinDrop`: per place, the lent prefix accessed whole
(`accessLentPrefix`), then `dropAt` (a borrow at a root ends; a copy is skipped; otherwise access
and write `moved`, nothing where `Sem.updAt` fails). The step statements: `movedPlace_step_stmt`,
`dropOne_step_stmt`, `joinDrop_step_stmt` (Statements.lean); assemblies in `Steps/MovedPlace.lean`
(`mpTail_sim`, `movedPlace_step`, `dropOne_step_asm`), `Steps/DropOneAsm.lean` (`dropOne_exists`),
`Steps/Match.lean` (`joinDrop_step`, by induction on the list).

## State of the drop step (18662217 and after)

`joinDrop_step` and `dropOne_step_asm` are assembled with no `sorry` in their bodies. They rest on
exactly these open pieces (`#sorry_leaves`; the script is `slice2/Leaves.lean` in the session
scratchpad, or rebuild it from the idiom below):

1. **`etaFresh_sim`** (MovedPlace): unchanged, the largest. Findings from planning it: the route
   through the induction hypothesis's `split_coverage` needs that statement in a "for every run"
   form with the constructor bounded (`∃ c < d.ctors.length, ∀ b r st', Runs (ctorRefinement …
   c) st b r st' → ∃ ρ', …`): as stated it gives SOME run at its own budget and SOME `c`, so the
   one-constructor case cannot be pinned to `c = 0` nor to the checker's own run without a fuel
   determinism fact. Not yet proposed to main. Its `CtxOk` after also asks the block's captures
   at the new state (as `ctx_botWrite` did) and (Hη≠) for the new record (needs: σ's type does not
   name σ). Needs `meanV_ext` (DropOneAsm, open, `AssignCongr.lean`'s shape).
2. **`recordedNeutral_ok`** (MovedPlace): ASSEMBLED (`Slice/Recorded.lean`, standard axioms:
   `expandRefsF_mean`, `expandRefsF_anyAtom`, `pathCond_everywhere`, `recordedNeutral_ok_of_facts`).
   Rests on two open leaves in MovedPlace:
   - `recordFacts_of_good` (`RecordFacts`: refinement records loan-free and top-hint-free,
     generalisation records' programs top-hint-free). Not derivable from `Good`/`CtxOk`: the path
     conditions are at the constant future and the unknown's type only. Swept (Sweep.lean clauses
     (WF11r), (Hr), (Hn)): no violation on 72,076 suite / 739 probe states. Proposed to main as
     clauses (WF11 for the first, `ShapeFacts` for the other two).
   - `neutralKey`: `recordedNeutral`'s lookup is by `==` (`Value.beq`), which ignores a constructor
     value's recorded parameters and binder names, so the record found may differ from the program
     asked. Probe (instrumented `recordedNeutral`, `canonNeutral`, `substV`'s sealed match, whole
     suite and probes): 19,937 + 4 + 16,578 matches, every one equal up to binder names (params
     compared). The same gap is in the lead's `canonNeutral_step` and `substEnv_neutral_step`.
     Proposed: the checker compares sealed programs exactly at these three sites.
3. **`ctx_botWrite`** (DropOneAsm): ASSEMBLED, no `sorry` in its body; statement gained `hp`, `hroot`
   (the call site had them). `Slice/BotShapes.lean` (standard axioms): `ShapeFacts.of_botWrite`
   via `follow_updAt_bot_any`, `updAt_bot_head`, `ckVarPos_setAtE`, `topReadings_setAtE`. The
   block's captures are split into the open leaf `blockCaps_botWrite`, to be deleted when the lead
   moves that clause out of `CtxOk`.
4. **`Rel.kept`** (EqJAsm, the lead's). Not this lane's.
5. **Machine-only facts** (`Steps/MachineMono.lean`, `machine1`'s lane): `DecTab.back` and
   `grows_absType`, `grows_accessInside`, `grows_accessPath`, `grows_content`, `grows_content?`,
   `grows_dropAtJoin`, `grows_etaInPlace`, `grows_generalizeNeutral`, `grows_logEffect`,
   `grows_lookupInd`, `grows_movedPlace`, `grows_placeTypeQ`, `grows_ppPlace`,
   `grows_recordedNeutral`, `grows_refine`, `grows_setPlace`, `grows_substEnv`.
6. Induction-hypothesis fields the step uses (hypotheses, not leaves): `access_step`,
   `endBorrow_step`, `movedPlace_step`, `refine_step`, `generalizeNeutral_step`,
   `substEnv_neutral_step`, `placeTypeQ_step`.

Proved on the standard axioms: `grain_deref_not_proof`, `not_below_proof`, `joinDropOne_noop`,
`copyRead_aligned`, `dropAt_data`, `botWrite_rel`, `botWrite_good`, the `Slice/` files.
`dropOne_exists` is open since it concludes the extended context itself: it waits on
`blockCaps_botWrite`, the [Access]/[End] hypothesis steps, and the machine facts.

Scratch: a session scratchpad subdirectory `slice2/` holds `Leaves.lean` (the `#sorry_leaves` and
`#print axioms` script), `sweep-records.patch`, `key-probe.patch` (the instrumented lookups).

## Decisions in force (why the statements look as they do)

- **The reference's `dropAt` tests no meaning** (only the copy decision and whether `Sem.updAt` can
  write); the join's grain asks a `*` step's borrow type (`StepOk .deref`), with the checker's D101
  (`jdGrain` rejects a move through `*` of a non-borrow). `Regress/GrainDerefProof` and
  `Regress/StepKindsTable` record why (an unchecked dead arm put `*` on a `⋆`).
- **The decision table is fixed for a run** (main, 2026-11-20): the item's final state's decisions;
  every extended-form step takes `(hD : DecTab K.D st')` (aligned after it), no `D'`, no `AgreeOld`.
  An assembly gets `hD` for a sub-run ending at `st₁` from the growth of the REST of the run:
  `hD.of_rest (by grows_go) hrest` (MachineMono). Fresh names are never reused within an item.
- **[Access] and [End] conclude the extended form** (`size ∧ ∃ ρ' Δ', ExtOk ∧ Rel`).
- `ShapeFacts` clauses the lane added: (C⋆) `proofCopy` at the grain, (Hη≠) `etaNoSelf`.

## Idioms and traps

- **`Runs f st fuel a st'`** := `∃ L left log, runMachineL f st fuel L = (.ok a st', left, log)`.
  Invert with `Runs.bind_inv`, `Runs.bind_assoc_inv`, `runs_get_inv`, `runs_pure_inv`,
  `runs_content_inv`, `runs_logEffect_inv`, `runs_setPlace_inv`, `runs_dropAtJoin_inv`, ….
- **The closure tactic** `grows_go` (MachineMono): `repeat (any_goals grows_step)`; `grows_step`
  tries the closure lemmas and every `grows_<fn>`, ALL under `with_reducible` (without it `whnf` of a
  large remainder, e.g. `movedPlace`'s tail `mpTail'`, times out at any heartbeat budget). A local
  def in the remainder (`mpFinal`, `dropLoop`, `eqChecks`, `jArm`, `bodyTail`, `callTailM`,
  `closeLoopM`) gets its own `grows_<def>` by `unfold <def>; grows_go`, used as
  `(by grows_go; all_goals exact grows_mpFinal _ _)`. A machine function not yet covered: add a
  `grows_<fn>` (`sorry`) in MachineMono and a line in `grows_step`. Where a leaf hides the remainder
  (`closeCall_split`, `idType_split`, `const_split`) the leaf supplies `TablesGrow`/`DecTab`.
- **Anonymous-constructor arities** shift whenever a statement loses or gains a conjunct: `ExtOk` is
  `⟨agree, ctx, good⟩` (`e.1`, `e.2.1`, `e.2.2`); `Ext` is `⟨size, agree, ctx, rel, good⟩`.
- **Contexts** `{ K with Δ := Δ' }` nest; Lean accepts `{ { K with Δ := Δ₁ } with Δ := Δ₂ }` where
  `{ K with Δ := Δ₂ }` is expected (defeq). `runCtx_with_self K : { K with Δ := K.Δ } = K`.
- An SState equation proved under the old context and rewritten into a relation under the new one
  (`lentPrefix_absorbed_eq`, `fillPrefix_eq`) avoids re-proving it per context.
- `#sorry_leaves` (lists the `sorry`'d declarations a theorem rests on): a scratch file with
  `import Ochr.Meaning`, `open Lean Elab Command`, and an `elab "#sorry_leaves " id:ident` that walks
  `ci.type.getUsedConstants` and `ci.value? (allowOpaque := true)` from the root, collecting names
  whose type or value mentions `sorryAx`; run with `lake env lean <file>`.
- **Checking axioms**: a scratch file `import Ochr.Meaning` then `#print axioms Ochr.Meaning.Steps.<name>`,
  run with `taskset -c 0-14 lake env lean <file>` from `ochr/core/lean` after `lake build OchrMeaning`
  (a stale olean otherwise). "Proved" means exactly `[propext, Classical.choice, Quot.sound]`.
- **Kernel-checked counterexamples / checker facts**: `Regress/GenNeutralContent`'s `isOk`, `outVal`,
  `outSt`, `runs_out`, with `decide +kernel` on a concrete `MState`; `Place` equality through
  `Place.beq`; `DeclInfo` has no `DecidableEq` (use a `match … with | .x => true | _ => false`).
  `Regress/StepKindsTable` and `Regress/GrainDerefProof` are examples.
- **Program probes**: a scratch `.lean` with `import Ochr.Runtime`, `import Ochr.Examples.Nat`,
  `import Ochr.Test`, an `ochr Block uses Nats { … }`, then `(run "Block" Block).rows` for verdicts,
  `(run "Block" Block { derivation := true }).showTrace "Def"` for a derivation, and
  `runCall`/`closedCall` (Runtime.lean) for closed calls of accepted drivers; run it with
  `lake env lean` from `ochr/core/lean`. Asserted rows go in `Meaning/Regress/` as an `ochr` block
  of `reject def`s plus `#guard (run …).rejectedWith [(name, prefix)]` (`Regress/JoinPrefixBorrow`).
- **Checker probes** (instrument the checker): `git worktree add --detach ../ochre-slice-probe HEAD`,
  seed the cache with `cp --reflink=always -r ochr/core/lean/.lake ../ochre-slice-probe/ochr/core/lean/`,
  patch `Machine.lean` (a `dbg_trace` line shows in `lake build`'s output for elaboration-time
  checks; or push a log entry when `cfg.recordStates`, e.g. `.state default true (some (.sealed
  (.prim "MARK" [mt]))) st`, and read it from an exe like the sweep), run, save the patch to the
  scratchpad, then `git worktree remove … --force`. Nothing from a probe lands.
- **The sweep** (`Sweep.lean`, `lake exe sweep`, `lake exe sweep --probes`; ~10 minutes each): it
  records the checker's whole state at every located term of every example (`recordStates`) and
  evaluates `Clause`s: `name`, `premises` (counted), `check : MState → List Viol`, `report := true`
  for a report (lists cases, never fails). Add the clause to `clauses`. Output ends with
  "every real clause holds on every state" and the verdict count (2,293 suite, 27 probes). Its walk
  never steps under a `⋆` (a blind spot).
- zsh: quote globs (`--include='*.lean'`); a backtick inside a double-quoted command string breaks the
  whole command (write a Python script to a file instead). No `sleep` in the foreground: wait with
  `until …; do sleep 10; done` inside `timeout`, or a background job.
- Build CPU: always `taskset -c 0-14`.

## The rest of the row after the drop (what the next lanes meet)

- **A match on a known constructor** (`evalMatch_step`, `evalMatchInd_step`, Match.lean, open): the
  reference's `.matchNat`/`.matchInd` clauses (Run.lean ~770): `SM.erasedIf`, then `matchEntry`
  (static ends rule 2: a non-tail match accesses its stuck block's captures, `Decisions.blockCaps`,
  against the checker's `blockEntry`), the arm (the hypothesis's `eval_step`), the drop
  (`joinDrop_step`, assembled), and for a borrow result `lend R.label` (rule 1: marks). Also
  `joinEntry_stmt` (open): the reference's entry set `movedPlaces φ s` is the checker's `entryOf st`.
  The block-captures alignment belongs here, at the entry (see `ctx_botWrite`).
- **A split on an unknown**: `refine_step_asm` (SplitAsm, assembled: `substEnv_abs_step`, `refs_sim`,
  `renormAll_step`); `split_coverage` (open: a typed assignment selects a constructor and extends to
  its fresh fields); worlds; `etaInPlace_sim` (assembled) is the one-constructor in-place case.
- **Closing a stuck match into a block**: `closeBlock_step` (open), `etaPlace_sim` (open: an induction
  along `etaPlace`'s recursion, shaped like `movedPlace_step`); `Regress/EntryCheck`.
- **Leaving an arm**: `exitWorld_step_asm` (SplitAsm, assembled from `exitWorld_ctx`, a leaf, and
  `Rel.kept`).

## What is coming that will touch the step

- **Every temporary carries its type** (a checker change, then the lead migrates `Good` to speak of
  typed temporaries). The drop: `botWrite_good` treats every position alike (the written one, and
  the rest by `mean_setAtE_other`); only `posTyM_setAtE`'s `temp` case (`rfl` today, since a
  temporary has no type) needs the temporary's stored type unchanged by a write at a binding.
  `dropOne_exists` writes only at a binding; the arm's result in flight is untouched by the write.
- **The block-captures clause moves to a hypothesis of the [Entry] step** (main passed the slice's
  suggestion to the lead): then `CtxOk` no longer asks it of every state, and `ctx_botWrite` is
  routine. Until then, its open part is D90's obligation 1 at the state after the write.
- **The join rejects when it would end a borrow held in flight** (main's checker change from the
  slice's probe): the join's existing check (an arm moves a place while the result borrows it) is
  extended to the access of a lent prefix, so the tail case (`Regress/JoinPrefixBorrow`'s `TK`, `TU`,
  today rejected only by D53) is rejected at the join for its own reason. The proof gets a clause for
  the lead: the join's drop ends no borrow held in flight. Re-check `JoinPrefixBorrow`'s expected
  messages for `TK`, `TU` when it lands (they will change to the [Join] message).
- Also queued on main: the dead `⋆` test removed from `dropAtJoin` (D102; the reference no longer
  mirrors it, so nothing in the drop changes), and comparisons keeping only names on exit (fresh
  names never reused, which `MachineMono` relies on).
