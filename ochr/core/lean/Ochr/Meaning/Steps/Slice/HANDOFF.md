# Slice lane: handoff note (for a successor who has seen none of this)

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

## State of the drop step (0bff37e8 and after)

`joinDrop_step` and `dropOne_step_asm` are assembled with no `sorry` in their bodies. They rest on
exactly these open pieces (`#sorry_leaves`, below):

1. **`etaFresh_sim`** (MovedPlace): a fresh η refinement of an unknown `σ` of a one-constructor type
   (`ctorRefinement`, fresh field unknowns), recorded, means `ρ' σ` under an extension giving the
   fields the fields of `ρ σ`; the relation (reference untouched), `Good` (the record is the path
   condition just met) and `CtxOk` (with `hD`) after. Best route: the induction hypothesis's
   `split_coverage` (same shape: some `c`, an extension, the refinement satisfied) at the one
   constructor (`c = 0`), plus determinism of the run (`split_coverage` gives SOME run of
   `ctorRefinement`; `etaInPlace_sim` holds a particular one: successful runs at different fuels
   agree, a machine-only fact to add to MachineMono's list), then `Rel` unchanged (the run touches
   no environment value), `Good` with the new record (`TypedAssignment.eta` is the path condition;
   (WF6) bounds, `Good.eta_bound`), `CtxOk` (Δ at the fresh unknowns, `DeltaOk`; `ShapeFacts`: (Hη)
   top-hint-free and (Hη≠) no-self for the new record). Needs `meanV_ext` (assignment-and-Δ
   congruence, DropOneAsm, still `sorry`, `AssignCongr.lean`'s shape) for old values.
2. **`recordedNeutral_ok`** (MovedPlace): `recordedNeutral n = some r` (`r = expandRefs refs (.abs σ)`
   for `(n, σ) ∈ neutrals`) gives `NeutralOk K ρ st n r`: `r` means `n` at every future and hint,
   names typed unknowns, holds no loan. Route: mirror `etaRecorded_sim` (proved, MovedPlace ~447):
   `TypedAssignment.neutral` (`ρ σ = ⟦n⟧` at σ's type and the constant future) and
   `TypedAssignment.refs` (each refinement `σ' := r'` means `ρ σ'`), an induction on `expandRefsF`'s
   fuel; future independence from loan-freedom ((WF11) for records and refinements, `meanV_congr`);
   hint independence (`meanV_hintIndep` needs `topHintFree`: for `n` (WF16) and for the refinement
   values, which record their parameters ((WF10)); check a clause covers refs, else sweep one).
   I would attack this one first: it is the most self-contained and its pattern exists.
3. **`ctx_botWrite`** (DropOneAsm): `CtxOk` after the drop's write of `⊥` at one place. Routine except
   the block's captures: `inds`, `covers`, `faithful`, `noLabel`, `globals` unchanged (env only);
   `delta` by `refd_setAtE` (Refd shrinks); `dec.toDecTab` is the hypothesis `hD`; `shapes`: a new
   lemma `ShapeFacts.of_botWrite` (every place's content after the write is the old one, or `⊥`, or
   does not exist; the top readings are the bindings' `decl`s, unchanged). The `blockCaps` clause is
   D90's obligation 1 at the new state, a checker-only fact (MachineMono's list; measured: 338 block
   entries of the suite, static = checker at all 335 successful ones). Main passed to the lead the
   suggestion to ask it as the [Entry] step's hypothesis instead of a `CtxOk` clause: then
   `ctx_botWrite` is fully routine. Check whether the lead did before proving it.
4. **`Rel.kept`** (EqJAsm, the lead's): the relation survives a private computation (Ω the
   snapshot's; values name only old unknowns, where the extension agrees; labels made inside occur
   nowhere after). Not this lane's.
5. **Machine-only facts** (`Steps/MachineMono.lean`, its own lane, do not prove unless asked):
   `DecTab.back` and `grows_absType`, `grows_accessInside`, `grows_accessPath`, `grows_content`,
   `grows_content?`, `grows_dropAtJoin`, `grows_etaInPlace`, `grows_generalizeNeutral`,
   `grows_logEffect`, `grows_lookupInd`, `grows_movedPlace`, `grows_placeTypeQ`, `grows_ppPlace`,
   `grows_recordedNeutral`, `grows_refine`, `grows_setPlace`, `grows_substEnv`.
6. Induction-hypothesis fields the step uses (proved elsewhere or open in their areas): `access_step`,
   `endBorrow_step` (extended form), `movedPlace_step` (recursive), `refine_step`,
   `generalizeNeutral_step`, `substEnv_neutral_step`, `placeTypeQ_step`.

Proved on the standard axioms: `grain_deref_not_proof`, `not_below_proof`, `joinDropOne_noop`,
`copyRead_aligned`, `dropAt_data`, `botWrite_rel`, `botWrite_good`, the `Slice/` files.
`dropOne_exists` was closed at 1216caba and is open again since item 3 because it concludes the
extended context itself: it waits on `ctx_botWrite`, the [Access]/[End] hypothesis steps, and the
machine facts.

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
- `#print axioms` in a scratch file importing `Ochr.Meaning`.
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
- **Coming checker changes** (main's queue): the join's existing check (an arm moves a place while
  the result borrows it) extended to the access of a lent prefix, so the join never ends a borrow
  held in flight (today only D53 rejects the tail case: `Regress/JoinPrefixBorrow`'s `TK`, `TU`); the
  dead `⋆` test removed from `dropAtJoin` (D102); comparisons keeping only names on exit; every
  temporary carrying its type (then `Good` speaks of typed temporaries: `botWrite_good` treats every
  position alike, and only `posTyM_setAtE`'s `temp` case, `rfl` today, would need the temporary's
  stored type to be unchanged by a write at a binding).
