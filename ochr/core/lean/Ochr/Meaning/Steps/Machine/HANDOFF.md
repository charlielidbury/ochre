# Machine lane: working note (keep current; a successor continues from this alone)

Worktree `/home/charlielidbury/repos/ochre-machine4`, branch `spine-machine4` (machine4, from 2026-11-21 night;
before it machine3 in `ochre-machine3`/`spine-machine3`, machine2 in `ochre-machine2`/`spine-machine2`; push to your own branch; never `spine` or `main`). Lean project `ochr/core/lean`; build `taskset -c 0-14 lake build <Module>` (long builds in
the background), and `taskset -c 0-14 lake build OchrMeaning` before each push. Report to the lead
(`team-lead`) by SendMessage, then end the turn. Owned: `Steps/MachineMono.lean`, everything under
`Steps/Machine/`. Never edit the checker or other files (to check a consumer, copy it into a scratch
module here, build that, delete it).

STATUS LINE: see "Build state" at the end (kept current at every push).

## What is proved (standard axioms only: `propext`, `Classical.choice`, `Quot.sound`)

### (a) The tables only grow (`grows_*`)

The property is `GrowsIn tb x` (`GrowsIn.lean`): every successful run of `x` from a state whose
globals and declarations are `tb` only extends the tables (`TablesGrow`, `Defs.lean`). Relative to
`tb` because a private copy's exit (`restoreKeep saved`, `exitWorld w`) takes the globals and the
declarations from the saved state, which keeps them only if the saved state had them: true when it
was read earlier in the same run (`get`, `enterWorld` give `OnTab tb s`).
`GrowsM x ↔ ∀ tb, GrowsIn tb x` (`growsM_of_growsIn`, `growsIn_of_growsM`, `GrowsIn.runs`).

- `Comb.lean`: the monad's combinators, Env's brackets (`withLive`, `withErased`, `withRuntime`,
  `withCopying`, `privately`, `inStatement`, `restoreKeep`, worlds), `freshAbs`, `freshLoan`;
  `GrowsAt s x` for read-then-write-back code; `growsIn_get_restore` (`closeBlock`'s `set e … set cur`).
- `EnvLeaves`, `DecideLeaves`, `MachineLeaves`: every function outside the machine's mutual block
  that the block calls.
- `IH.lean`: `MachineGrows tb nf`, one field per function of the block (generated; functions taking
  no fuel, `joinLogged` and `lentInFields`, proved on their own); `joinContRet` (`RetOk`).
- `Zero.lean`, `Step*.lean`, `All.lean`: `machineGrows : ∀ nf, MachineGrows tb nf`.
- The files `IH`'s fields, `Zero`, `Step*` and `All`'s two structure instances are GENERATED from
  `Machine.lean`'s signatures by the scratchpad scripts `gen.py`/`gen2.py`/`regen.py` (described under
  "Regenerating" below); hand edits in them are `evalType_succ`, `observe_succ` (the `n + 1`
  unfolding by `rfl`: those two functions' equation lemmas time out when generated) and the
  heartbeats of `step_callFn`.
- `MachineMono.lean`'s `grows_*` follow from these; `restoreKeep_grows` is the corrected
  `grows_restoreKeep` (hypothesis `TablesGrow saved cur`); `grows_closeBlock_of` the corrected
  `grows_closeBlock` (hypothesis: every arm grows). The two false ones stay, flagged, until
  `EqJAsm` moves (`False.lean` has `not_grows_restoreKeep`; `eq_step_asm` goes through with
  `restoreKeep_grows`, checked on a scratch copy: a forward chain of `TablesGrow` along the run,
  then the same `back`s; `J_split` must give the arm's growth for `grows_closeBlock_of`).

### Decisions agree across fuels (`FuelDefs.lean`, `DecideFuel.lean`)

`FuelLe x y`: every success of `x` is one of `y` (same value and final state) from the same state and
ANY budget and log (the decision procedures never touch either). Each function of Decide's block the
decisions reach is `FuelLe` itself one fuel up (`decideFuelLe`, `jdFuelLe`, `jaFuelLe`,
`fuelLe_typeState`; macro tactics `fuel_go`, `fuel_ih`, both bodies walked in step). Hence
`FuelAgree`/`FuelMono` for each field of `Decisions` as `checkerDecisions₀` and `DecTab` read it
(`fuelAgree_flags`, `_placeDecl`, `_declOf`, `_copy`, `_piSort`, `_joinMoves`, `_rePointed`,
`_typeState`, `_typeDecl`). `DecisionsFF.decide_fuel_agree` (a `sorry` on `spine`) is proved in its
own form as `decide_fuel_agree'` (`DecideFuelFF.lean`); `DecisionsFF` imports only `Statements`, so it
can import `DecideFuel` and take that proof term verbatim. NOT the block captures (`ckBlockCaps` runs the machine: a fuel induction over the
whole block, the same shape as (a) but relational; see the queue).

### machine2: `DecTab.back` and the column's inversions (2026-11-21 evening)

- `DecBack.lean`: `decTab_back` (= `MachineMono.DecTab.back`, = `ColumnC.DecBack`). One-way simulation
  `Fwd R x` = `Keep x` and every success from `s₁` is one from each `R`-related `s₂` (same value,
  budget, log). Keep is bundled so binds need `R` only at start states. Relations: `TabLe` (tables;
  `declCopy` at raw states), `LiveLe` (+ mode, + top readings when `liveScope`), `EnvTab` (+ same
  frames: the `scopeState` pairs), `LiveEq` (a state against `scopeState` at its own readings:
  `decTab_declOf_at`, `decTab_placeDecl_at`, the machine's own reading is the table's).
- `Inv.lean`: run inversions (`runs_get_bind`/`runs_modify_bind` as `Iff.rfl` for `rw`, `Runs.tick_bind`,
  `Runs.log_bind`, `Runs.onFail_inv`, `Runs.located_inv` (equal up to `locs`), `Runs.noteValue_inv`,
  Keep lemmas, `preFlags_inv`, the `peel` macro for SMALL hypotheses).
- `EvalInv.lean`: `evalAt_inv`, `evalInvR`. `StepInv.lean`: `quiet_conv` (D103), `expectTy_inv`,
  `succInvR`, `letInvR`, inversions of `refineDecl`, `getFlags`, `pushBind`, `pushTemp`, `popTemp`.
- TECHNIQUE (what worked): `unfold Ochr.evalCore at h` is fast (no zeta); peel `tick`/`get`/`wanted`;
  then either `change Runs (case's do block) _ _ _ _ at h` (cheap for small cases, `succInvR`) or
  `simp only [Term.placeOperand?] at h` (reduces the 40-arm match to the case, `letInvR`; a verbatim
  `change` for `let` took 4 min and failed). Equation lemmas: `f.eq_1` is the `n+1` case where it
  exists (`eval`, `dropTopBind`, `conv`, `endLoansOfTopBind`); `evalAt.eq_1`/`evalCore`'s time out.
  Big hypotheses: never `simp`/`split` (zeta duplicates join points, `split`'s simp hits its step
  limit): targeted `rw [runs_get_bind]`, `rw [if_pos]` with the condition as a side goal,
  `Runs.bind_inv`, and `clear` what `obtain := Runs.bind_inv h` leaves behind. Witnesses: an `rfl`
  or a hypothesis about `st₀.field` in an anonymous constructor assigns the state metavariable by
  first-order approximation before the run does: give states explicitly, or `?_` and fill after,
  `by exact ⟨rfl, …⟩` to delay. A record literal spanning lines must keep its fields at one indent.
- Proposed forms (reported to the lead; each docstring says why): `EvalInvR` (pre-pass pinned by the
  reading, not `D.flags`), `SuccInvR` (typed clause on `T₀` as returned, no `some`), `LetInvR` (`u`'s
  reading at the ENTRY, `T₀ : Option`, `ModeEq` for the mode, no Inv clause, no `0 < size`).
  `AssignNumInv` is FALSE without `b.ty = some .tNat` (a field step under a non-number is a match).
- `ReadInv.lean`: `varNumInv` (= the lead's `VarNumInv`, exact). `BorrowInv.lean`: `borrowNumInv` (= the
  lead's `BorrowNumInv`, exact, spine-lead8). The read machinery at a variable holding a number:
  `NumAt`, `runs_placeType_var`, `runs_repackAt_num`, `runs_accessPath_num`, `runs_accessInside_num`,
  `runs_content_var`, `runs_readPlace_num`, `runs_borrowPlace_num`, `runs_copyRead_inv`,
  `runs_isCapture_inv`, `runs_unsizedCheck_num`, `runs_openWrite_var`, `runs_freshLoan_inv`.
  Two traps: a case split on `bd.val`'s shape (`rcases hx _ hn.num with e | ⟨w, e⟩; rw [e] at h`)
  reduces readPlace's `match v`; `obtain ⟨rfl, rfl⟩` on a state equation may eliminate the NAMED state
  (`st`) in favour of the local one, so state a sub-lemma over an arbitrary state (`varNum_read`)
  rather than naming states after substitutions.
- Ruled by the orchestrator (2026-11-21, OPEN.md on spine-lead8): `InvCore` DROPPED; the invariant is
  carried by state-level lemmas `Inv D Γ st.norm → Inv D Γ st'.norm`, one per kernel shape an
  inversion fact concludes (first column: a number binding set to ⊥, a binding pushed at Nat holding
  a number, the top binding popped, a number temporary pushed, `setAtE (.succ v₀)`; the borrow
  column's five are listed in OPEN.md). The lead states them in `FormMachine.lean`; this lane proves
  them. `Inv` under `Kern` is free (`Kern a b` is `a.norm = b.norm`).
- Reviewed (reported 2026-11-21): `AssignDerefInv` FALSE by reading (y's old content a borrow:
  assignPlace's [Drop] ends it; fix `(∀ m z, w ≠ .borrow m z)` in the Kern clause's antecedent);
  `SeqInv` needs `ModeEq st₁ stW` for `Mode stW` and loses its Inv clause; lead8's LetInv conjunct
  `topReadings st₁ = topReadings st` is provable only for u without a write (Z, S, variables, let:
  an induction through `eval`; a write at a non-Nat variable runs the [Proj] match); `VarEndInv` true
  (its work: `endTopLoan`/`endBorrow` inverted at the two-binding state).
- `InvShape.lean`: `inv_of_kern` (free), `runs_conv_of_beq` / `runs_expectTy_of_beq` (a comparison of
  `==`-equal values is the identity: the column's `S(u)` with `u : Nat`). Its docstring warns: the
  state-level lemmas over a push/pop of a binding meet `ShapeFacts.fits`, which reads `D.placeDecl`
  at the TOP READINGS, so they need the table aligned at the new state; a number set where a place
  reads `.ind n _` violates `fits`. The general "every run keeps `absTy.size = nextAbs`" (WF6 across a
  private exit) is a whole-machine induction like `machineGrows`, to schedule when a step needs it.
- `lead9` (origin/spine-lead9 332b0a1e) adopted `SuccInvR`/`LetInvR` word for word, deleted `InvCore` and
  `ColTerm`, and bundled ten state-level Props as `InvSteps` (top of `OPEN.md`); `column_C_ff` now
  assumes exactly `VarNumInv` + `InvSteps`. Its finding: `Inv` across a `Quiet` stretch is not
  state-level (`Quiet` leaves `nextAbs` and the new unknowns' types free; WF6's `absTy.size = nextAbs`
  and WF8/WF11 on `absTy` read them). It added `KeepsInv st st₁` beside each `Quiet` (in `VarNumInv`,
  `BorrowNumInv`, `AssignNumInv`, `AssignDerefInv`, `VarEndInv`) and `InvExpectTy` for `S`. This
  RESTATES `VarNumInv` and `BorrowNumInv` (proved here in the earlier form).
- JUDGEMENT (machine2) between `KeepsInv` (lead9's) and extending `Quiet` with two fields (`nextAbs` in
  step with `absTy`'s size; the new unknowns' types clean): both are true of the code, and for a
  comparison of values that are not `==` BOTH rest on the same whole-machine invariant (every run keeps
  `absTy.size = nextAbs` and makes only clean types: an induction of `machineGrows`' size), so neither
  avoids it in general. For the columns NOW, `KeepsInv` is cheaper: every `Quiet` witness in
  `varNumInv` and `borrowNumInv` is the state itself (`Quiet.refl`), so the new conjunct is
  `fun _ _ h => h`, a one-line change to each proof; `InvExpectTy` for the column's `S(u)` with
  `u : Nat` follows from `runs_expectTy_of_beq` (the check is the identity). Extending `Quiet` is the
  more uniform endpoint but forces `quiet_conv` to prove the two fields for EVERY comparison at once,
  i.e. the whole-machine induction immediately. Recommendation: keep `KeepsInv` now; move to the
  extended `Quiet` (with the induction) when a column first needs a comparison of unequal values.
- NEXT, in order (the orchestrator's, 2026-11-21 night):
  1. settle the `KeepsInv` / `Quiet` decision above with the orchestrator (recommended: `KeepsInv`);
  2. the ten `InvSteps` (review each for truth first; note `ShapeFacts.fits` reads `D.placeDecl` at
     the TOP READINGS: a push/pop needs the table aligned at the new state, and a number where a
     place reads `.ind n _` violates `fits`);
  3. re-prove `VarNumInv` and `BorrowNumInv` in lead9's restated form (add `fun _ _ h => h`);
  4. `VarEndInv` (the inversion of `endTopLoan`/`endBorrow` at the two-binding state);
  5. the unconditional corollary of `ColumnCFF.column_C_ff` (`varNumInv` + the `InvSteps`);
  6. then merge `origin/main` into the proof line (D115 at 226dcdd6: calls' heads and arguments,
     constructor fields, an assignment's right-hand side, a borrow made during invalidation, an arm's
     result at the join, the comparison's generic arguments held as typed temporaries; `evalCall`,
     `callFn`, `runBodyCore`, `closeCall`, `evalCtor`, `joinEnds`, `convFnRun` changed; D116 pending:
     `clone` of a proof place returns the proof), re-run the generator (`gen/`, "Regenerating" above)
     so `machineGrows` holds, repair `Steps/` minimally, list every `sorry` left with its reason; a
     statement the change makes false is a finding.
  Still owed from the borrow column's review: `AssignDerefInv` and `SeqInv` in their fixed forms, the
  LetInv readings conjunct for a write-free `u`.

### machine3 (2026-11-21 night): InvSteps, PlaceLocal, the first unconditional column, SeqInv

- Form point RULED: keep `KeepsInv` (lead9's). The extended `Quiet` (fields: `nextAbs` in step with
  `absTy`, the new unknowns' types clean, AND `absDecl`: old readings kept, new ones sorted, since
  `ShapeFacts.readingsSorted` reads it) with the whole-machine induction is scheduled for when a
  column first compares unequal values (`InvExpectTy` beyond `==`).
- Six of the ten `InvSteps` were false at a free table (`Inv D Γ` takes any `D`; `ShapeFacts.fits`
  reads `D.placeDecl` at the top readings). Fix adopted word for word by lead9: `Form.PlaceLocal`
  (root-locality + no inductive under `.other`/`.ref .other`), on the push/pop and write lemmas.
- Proved (standard axioms; `FormFacts` prints all): `invSteps : InvSteps` (`InvEnv.lean` generic
  value-level transfer `inv_step`; `InvPos.lean` position-level `PosRel`/`inv_of_posRel`;
  `PlaceLocal.lean` `readClauses_reroot` for a binding pushed/popped; `InvSteps.lean` the ten,
  `invLend`/`invEndRead'` via `inv_step` directly); `invExpectTyEq`; `placeLocal_ff`
  (`PlaceLocalFF.lean`: `Fwd2` two-computation simulation of `placeDecl` on a re-rooted place,
  `ResIn` result invariant); `column_C_free` (`ColumnCFree.lean`; the lead must import it from
  `Ochr/Meaning.lean`); `seqInvR` (`SeqInv.lean`, `SeqInv` with `ModeEq` under the Kern
  antecedent, reported: unconditional it is a whole-machine fact) and `runs_dropValue_inert`.
- NEXT (the borrow column, for `column_B_free` = `column_B_ff` with everything discharged):
  1. `VarEndInv`: TRUE by reading; ALL PIECES PROVED in `VarEndInv.lean`, only the assembly
     `varEndInv : VarEndInv` remains (pattern: `ReadInv.varNumInv`, lines ~353-391):
     - `runs_repackAt_lent` (repackAt at `x ↦ loan_l` is the identity);
     - `runs_accessPath_lent` (the path access ends `l`: result `{st with env := setAtE (setAtE env
       (bind 0 1) ⊥) (bind 0 0) w}`), built from `runs_endTopLoan_two`, `runs_endBorrow_two`,
       `runs_endTail_two`, `runs_mapState_two`, `runs_substV_hit/miss`, `runs_lendV_miss`,
       `setAtE_same`, `setAtE_comm`, `findBorrow_two`;
     - `runs_readPlace_after` (machine2's `runs_readPlace_num` with its access step generic: give
       `hacc` = `runs_accessPath_lent`, and `NumAt` at the ended state).
     Assembly: `DecTab.back` to `st`; unfold `evalCore`, tick, `wanted`, `placeOperand?`,
     `runs_projIn_var`; typed: `runs_placeType_var` (needs `ckVarPos st.env 1 = some (bind 0 0)`:
     NOT a hypothesis of `VarEndInv` (an extra empty frame above would make the top frame empty);
     derive it from the run's success: `varPos 1` succeeded, so `ckVarPos st.env 1 = some pos`
     (`runs_varPos_inv`), `pos ∈ allPos` (`ckVarPos_mem`, InvSteps), and `pos = bind 0 1` would
     need a third binding in frame 0, contradicting `allPos = [b00, b01]`; simplest is a lemma
     taking `∃ pos, ckVarPos st.env 1 = some pos`, the pos obtained inside placeType's inversion or
     before it), then `runs_repackAt_lent`, then `runs_readPlace_after`; untyped: `placeTypeQ` or
     none, as varNumInv. The copy decision: `decTab_placeDecl_at` at the ENDED state; its top
     readings equal `st`'s (setAtE keeps decls: `back_setAtE`), so `D.copy (D.placeDecl (topReadings
     st) (.var 1))` is the run's `c`. `Quiet st st` (`Quiet.refl`), `KeepsInv` trivially; Kern:
     the ended state with `placeLog := X` (move) is `Kern`-equal to the conclusion's.
  2. `AssignDerefInv` (fixed form, `w` not a borrow): review against `evalCore`'s `.assign`
     (lentProofAssign, the hint/`Tp0` placeType?, `eval u`, the type check, accessPath at `*y`
     (no ending: `firstLiveLoanOnPath` on `borrow l w` at `[deref]` meets a number), `assignPlace`,
     `openWrite`), then prove. Not yet reviewed.
  3. Then `column_B_free` (as `column_C_free`; `SeqInv` is now restated in FormMachine and proved,
     `FormFacts.seqInv`, 9a54a71e, the orchestrator having let this lane apply forced statement fixes
     itself while the lead lane is empty: edit FormMachine + the minimal consumer lines, keep
     OchrMeaning green, list every edit in the report).
  4. Asked by the orchestrator (from the retired lead): `DropNoopInv` concludes only `Kern`; also
     conclude `ModeEq st st'` if true of the code (dropTopBind on a loan-free, borrow-free binding:
     topIdx, gets, `endLoansOfTopBind` no-op, the pop: no mode field touched, so it should be), prove
     the stronger form, apply the statement change (FormMachine + consumers in ColumnLet/ColumnLetB),
     report it.
  5. The model lane (`model4`) is changing the reference run under the columns (SGood `uniq`, `.letIn`
     reading before `u`, typed hints); after it lands, merge `origin/spine` and check `column_C_free`
     still builds unchanged; tell the orchestrator at once if not.

### machine4 (2026-11-21 night): the borrow column closed with nothing assumed

- `varEndInv` (`VarEndInv.lean`, "The assembly"): the variable's position is derived from the run's
  success (`ckVarPos_one_two`: every branch of `.place` runs `varPos 1` first; `allPos = [b00, b01]`
  does not fix `env.size = 1`); the copy decision read at the ENDED state, whose top readings and
  tables are the entry's.
- `AssignDerefInv` was FALSE (y lent at u's end: the access ends y's borrower) and two conjuncts were
  whole-machine facts (ModeEq across an ending, KeepsInv across a comparison of unequal types);
  RESTATED in FormMachine (conditions on u's END state `st₁`, under the conclusion), consumers
  adapted (`assignDeref_core`'s `hnum` also gives u's type is Nat; `run_write`; `sim_write_read`),
  proved (`AssignDerefInv.lean`). Trap met: the hint's `if … (u matches …)` is duplicated by the
  do-elaborator's inlined join point; naming the condition (`by_cases`, `generalize`) timed out at
  whnf; `Runs.ite_bind_inv` (shared continuation) inverts it without naming it.
- `column_B_free` (`ColumnBFree.lean`, root-imported), `dropNoopInvM` (DropNoopInv + `ModeEq st st'`;
  FormMachine's `DropNoopInv` NOT restated: no consumer needs the mode; its `holdsBorrow` hypothesis
  is unused).
- NEXT: step 5 of the brief (merge `origin/main`: D115/D116; regenerate `gen/`; repair; list sorries),
  only after telling the orchestrator.

## Non-total constructs in the checker (read-only census, 2026-11-21, at the merge with spine 1e226c6a)

Reachable from `checkProgram`: `Loc.termAddr` (`opaque`/`implemented_by`, the standard's one allowed
exception); well-founded recursion, total but not kernel-reducible: `Machine.firstLiveLoanOnPath`
(Machine.lean:76), `Obs.owners` (Obs.lean:175), `Loc.Locs.relocate` (Loc.lean:113). None blocks this
lane's proofs (the tactic treats pure functions as values); they block only kernel evaluation of
concrete runs (`decide +kernel` counterexamples through an access or an end). No `while`/`repeat`
remains (`blockCaptures`' loop is fuel-bounded since D104). Not reachable from `checkProgram`: the
`ochr` command's elaborator (`Notation.lean`: nine `partial def`s, `evalBlock` `unsafe`/
`implemented_by`/`opaque`), `RuleGuard.lean` (three `partial def`s, build-time tooling), `Run.lean`'s
`exportsWith`/`libWith` (WF; they assemble a block's library before it is checked, outside `checkProgram`), `Consistency.holeIn` (WF; the statement side).

## The tactic (`Tactic.lean`) and its idioms

`grows_go` / `grows_go ih` walks a `GrowsIn` goal by the head constant of each sub-computation, never
by unfolding: `@[grows]` lemmas indexed by head (`Attr.lean`; the last registered is tried first), the
field of `ih` named after the function, a local hypothesis (binders, `have`s and `∧` opened), a match
on a constructor reduced (`reduceMatcher?`: the fuel's `n + 1`) or else `split` (then `fuelCleanup`),
`∀ a ∈ [..]/map/[]` elementwise, a projection of a constructor reduced, a refuted case of a functional
induction closed (`growsAbsurd`), `bind` of a function returning a computation through the `…Ret`
field (`growsIn_bind_ret`). It never fails; open goals are left for the caller.

Traps: `grows_go ih` takes the identifier on the same line only (`colGt`). `lean_run_code` (the MCP)
runs in ANOTHER worktree: test in a scratch module here with `lake env lean`. Value-recursive
functions: `f.mutual_induct` (or `f.induct`). `while` loops are `repeatM` (opaque: unprovable); the
checker's one `while` is gone (D104's fuel-bounded loop in `blockCaptures`).

## Regenerating after a checker change

The scripts are in `gen/`; run them from an empty scratch directory, in order: `python3 gen.py &&
python3 gen2.py && python3 regen.py`. `gen.py` (reads `Machine.lean`'s mutual block, found as the
`mutual` after line 700 and the last column-0 `end`; writes `sigs.json`), `gen2.py` (writes `fields.lean`, the IH's
fields, and `stubs.json`, each step's and base's text; `HYP` lists the hypotheses of functions taking
a computation), `regen.py` (writes the `Step*` files grouped as listed, `Zero.lean`, `All.lean`'s two
instances, re-applying the hand edits). Then paste `fields.lean` into `IH.lean`'s structure. If the
scripts are lost: each step is `intro …; unfold Ochr.f; grows_go ih`, each base `unfold Ochr.f; grows_go`.

## The queue (the lead's, 2026-11-21 afternoon): the column's facts first

TARGET: `Steps.Form.ColumnC.column_C_ff` (on `spine-lead7`, merged here at f3e86f763) assumes ten facts
about the checker alone, as `Prop`s in `Steps/FormMachine.lean` (`EvalInv`, `ZeroInv`, `SuccInv`,
`VarNumInv`, `LetInv`, `DropNoopInv`, `InvCore`) and `ColumnC.lean` (`DecBack`), plus
`DecideFuelAgree` (PROVED: `decide_fuel_agree'`) and `GrowsM` of the body's `eval` (PROVED:
`machineGrows`), plus `AssignNumInv` for the field-write column. Proofs go in
`Steps/Machine/FormFacts.lean` (downstream of `FormMachine`, which imports `MachineMono` through
`StrictSim`; the root `Ochr/Meaning.lean` must import it: the lead's line).

Judged against `Machine.lean` (reported to the lead 2026-11-21):
- PROVED: `ZeroInv` (`FormFacts.zeroInv`: the run computed by `rfl` at `bh = k + 1`).
- TRUE, not yet proved: `DropNoopInv` (`dropTopBind`: `borrowBelowRoot` false on success, not a borrow,
  `endLoansOfTopBind` finds no live loan since `loans = []`, then the pop). Two attempts failed the same
  way: in `endLoansOfTopBind (j+1)`, rewritten by `Ochr.endLoansOfTopBind.eq_1` (the per-case equation
  for `fuel'.succ`; `unfold` leaves the fuel's match), peeling `get` with `Runs.bind_inv` +
  `runs_get_inv` leaves a hypothesis that still prints as `do let __do_lift ← get; match …` and
  `rw [hb]`/`split` find nothing. Diagnose first with `set_option pp.explicit true in trace_state`
  right after the first `Runs.bind_inv` (is the remainder a β-redex, or does the do-elaboration of
  `let some b := (← get).… | pure ()` put a second bind or a `have __do_jp` join point in front?).
  `dropTopBind` itself peels fine (`topIdx`, `get`, then the binding's match, which `rw [hb']` and
  `split` handle; its branches are `have __do_jp := …` join points: `simp only [] at h` or
  `intro`-style zeta before `Runs.bind_inv`).
- TRUE: `DecBack` (`∀ D st st', DecTab D st' → TablesGrow st st' → DecTab D st`). Plan: a ONE-WAY
  simulation `Fwd R x` (every success from `s₁` is one from `s₂`, same value, fuel, log; `R` after),
  closure lemmas as `FuelDefs.lean`'s, the seventeen-function induction as `DecideFuel.lean`'s. The
  relation: tables (`globals`, `inds` equal; `absDecl` a prefix, read only by `absReading`, which fails
  past the end), `liveScope` equal, and the frames' readings equal WHEN `liveScope` is true (only
  `placeDecl`'s `.var` case reads the frame, through `liveDecl`, and only then). The `copy` field runs
  `declCopy` at the two raw states (frames differ): `declCopy` reads no frame before `fieldDecl`'s
  `withLive false`, so prove it under the tables-only relation with a lemma `withLive false` lifting it.
- FALSE as written, with fixes (the lead decides whether `FormMachine` is restated):
  - `SuccInv`, `LetInv`, `AssignNumInv` conclude `st₀.tailNext = false` but nothing in those `evalCore`
    cases clears it (`evalAt` does, before): add `st.tailNext = false`.
  - `EvalInv`: where `st.tailDecl = some d` the pre-pass classifies by `d`, not by `D.flags` at the
    term's own reading: add `st.tailDecl = none ∨ st.tailDecl = some (D.declOf (topReadings st) t)`. At a
    `let`'s tail the handed reading is the tail's own (`declOf`'s `.letIn` reads `w` in scope
    `du :: sc` = the live frame after the push): a lemma to prove for the column.
  - `VarNumInv`, `AssignNumInv`: a lazily typed binding's type is computed privately and the copy's exit
    (`restoreKeep`) keeps fresh names and η/generalisation records: add `b.ty.isSome`.
  - `AssignNumInv`: the write's [Access] ends `x`'s borrowers (not quiet) where `x` is lent: assume
    nothing lends `x` at `st₁`, or conclude with the access run.
  - `InvCore` as stated is the whole checker's well-formedness preservation (the largest machine item;
    `borrow_wf` suspected false): restrict to the column's forms with sub-run hypotheses.
  - `SuccInv`, `LetInv` need "a typed `eval` returns `some` type" (a machine lemma).
- Suggested tool for the inversions: a `runs_inv` tactic, the dual of `grows_go`: on a hypothesis
  `h : Runs x st b a st'` it dispatches on `x`'s head constant: `bind` (`Runs.bind_inv`, naming the
  intermediate state and value), `get` (`runs_get_inv`, substituting), `pure` (`runs_pure_inv`),
  `modify` (`FormFacts.runs_modify_inv`), `err`/`exhausted` (contradiction), `ite`/`match` (`split at h`,
  or rewriting a known discriminant first), a `have __do_jp` join point (zeta), a function with an
  inversion lemma (a table like `@[grows]`'s: `runs_topIdx_inv`, `runs_varPos_inv`,
  `runs_content?_inv`, `runs_setPlace_inv`, …), and leaves a sub-run of an unknown computation as a
  named hypothesis. Rewrite a function at `n + 1` with its `f.eq_1` (the per-case equation; `unfold`
  leaves the fuel's match). Each inversion statement is then: run `runs_inv`, close the leftovers.
- The entry facts the corrected inversions need: `st.tailNext = false` at `evalCore`'s entry (from
  `EvalInv`, since `evalAt` clears it); the handed reading at a `let`'s tail is the tail's own
  (`declOf`'s `.letIn` case: `w` in scope `du :: sc`, which is the live frame after `pushBind` with
  `du' = refineDecl du = du`); a typed `eval` returns `some` type; a typed run's bindings have a stored
  type (`ty.isSome`, `lazyTy = none`: `deferCallTy` only when `!typed`); `Mode` is kept by every
  sub-run of these forms (none touches `headEval` after `evalAt`, `copying`, `inPlace`, `erasedDepth`).

- (8b) PROBED 2026-11-21: FALSE as stated (reported to the lead). Accepted by the checker:
  `def H4 : Nat := (let z = 0; match z { Z => 0, S n => NoSuchNameD })` and, with
  `inductive P (f : Π(x : Nat). Nat) := MkP`, `inductive Q4 := MkQ4(p : P(λ(y : Nat) : Nat => (let z =
  0; match z { Z => 0, S n => NoSuchNameE })))`: a match on a known constructor runs only its arm, so
  the other arm's constants are never looked up. Rejected ("unknown constant", `lookupGlobal`): an
  undeclared name in a λ's body anywhere else (a λ is checked when formed, an unknown scrutinee split
  into every arm). The checker change proposed (the lead's decision): [Ind-decl] and [Def] check
  syntactically that every constant a declaration's terms mention is declared; (8b) is then its
  postcondition.

The earlier queue (still owed, after the column):
   - (M-a) data writes have no live loan or mark on their path. Not a property of one function: a
     trace property of `setPlace`'s call sites. Proposed form: each split lemma of a writing rule
     (`assign_split` and the like, which expose the state before the write) gains a conjunct
     `firstLiveLoanOnPath st₁.env (valAt st₁.env pos) ss = none` at that state, proved from
     `accessPath`'s postcondition (it loops until that is `none`: easy) plus "nothing between the
     access and the write puts a live loan on the path" (per site; the risky part). Exclude the
     join's mark write by name. The data writes (at the merge with spine 1e226c6a): `openWrite`
     (`setPlace fp .bot`), `readPlace` (two moves), `borrowPlace` (`setPlace p (.loan l)`),
     `assignPlace`, `capture` (a move into a closure), `dropAtJoin`; the mark write is `joinEnds`'
     `setPlace q (lentTo [k] w)`. MEDIUM, per site.
   - (M-b) CORRECTED (holds only outside private copies: `endTopLoan`'s D106 check is skipped at
     `privateDepth > 0`): `Runs (accessPath fuel p) st b () st' → st.privateDepth = 0 →
     findBorrow st.env l = some (.temp f i) → findBorrow st'.env l = some (.temp f i)`, the same for
     `accessInside` and `accessNeutralHead` (an access pushes and pops no temporary and does not
     change `privateDepth`). Needs "`endBorrow` of one label leaves every other borrow where it is"
     (`setAt` of the holder, `substEnv` of the loan, `lendEnv` of marks; `substEnv` re-normalises
     sealed programs, which hold no borrows). MEDIUM.
   - (M-c) `endBorrow` succeeds on `l` only if the content is whole and repacked: `Runs (endBorrow
     (fuel+1) l) st b () st' → findBorrow st.env l = some p → (valAt st.env p).takeBorrow l = some (c,
     rest) → c.hasHole = false ∧ (st.typing → valAt is a borrow → tyAt p = some (.tRef A) → ∃ run of
     repackCheck fuel "a borrow of it ends" c A from st)`. EASY (inversion of one body; `hasHole` is
     "has `⊥`").
   - (8a) CORRECTED (as worded it is too weak: a decision about `.const n` reads `n`'s stored type, a
     value that can mention other globals (`gfn m`, through `valueDecl`/`closedTypeDecl`), and a term
     can hold unknowns (`Term.val`) read by their frozen readings). Form the chain needs: `st₂`
     extends `st₁` (equal `inds`; `st₁.globals` a prefix of `st₂.globals`, or `find?` equal at every
     name `st₁` has; `st₁.absDecl` a prefix of `st₂.absDecl`), and every global name `t` mentions is
     one of `st₁` (an unknown name reads `.any` at `st₁` but may resolve at `st₂`); then for every
     scope and field, `chainDecisions fuel st₁` and `chainDecisions fuel st₂` agree on `t` and on its
     subterms. The closure under the globals' stored types then comes for free (a global of `st₁`
     was checked at `st₁`, so its type's names are `st₁`'s; that is a separate machine fact about
     `checkItem`, the same shape as (8b)). Proof: the one-way simulation of `DecTab.back` with this
     relation, then `decide_fuel_agree'` to move from fixed fuels to the table. HARD.
   - (8b) `checkItem (.ind d)` ok ⇒ every global name in `d`'s parameter and field-type terms is a
     global: DOUBTFUL. It holds only if the checker looks up every such name. `checkInd` runs
     `telescope … true` over the parameters and `typePos … true` over every field type, but Decide's
     readers answer `.any` for an unknown constant (`declOf`'s `.const` case: "an unknown name is the
     machine's error, reported where it is met"), so only evaluation finds one. It evaluates the
     parameter types and the field types at generic values, and a Π-type's codomain is evaluated too
     (`piSort` runs `evalType c` at generic arguments); but evaluation need not reach every subterm
     (an arm a match on a known constructor does not take, a λ's body), so a name there may never be
     looked up. Measurement first (sweep, report clause): at every accepted `ind` item, every
     constant of its parameter and field-type terms is a global of the state; and a probe that hides
     an unknown name where evaluation does not reach it, e.g. inside a λ passed as a value parameter
     of a type former in a field type (`D(λy. NoSuchName)`, `D` with a function-typed parameter: the
     λ is captured, its body not run). If the probe is accepted, (8b) is false and the checker
     change I would propose is a syntactic check in [Ind-decl] (and [Def]): every constant a
     declaration's parameter and field-type terms mention is declared (a scan of the terms against
     `globals`, read from syntax, so it is a decision of the kind the checker's standard allows);
     then (8b) is that check's postcondition. HARD only if the measurement fails and the change is
     refused.
4. The rest of `Meaning/OPEN.md`'s machine-only section (an access losing no unknown; the resolution
   facts; the well-formedness preservation statements, `borrow_wf` suspected false).

## Build state

2026-11-21 night, `spine-machine4` (machine4; `spine` 847f05ab and `spine-machine3` 761d0ce9 merged):
`OchrMeaning` green; `varEndInv`, `assignDerefInv`, `dropNoopInvM`, `column_B_free`, `column_C_free`
standard axioms.

2026-11-21 night, `spine-machine3` (machine3; `spine-lead9` f6c88026 merged): `OchrMeaning` green;
`invSteps`, `placeLocal_ff`, `column_C_free` (built explicitly until the root imports it), `seqInvR`
proved, standard axioms.

2026-11-21 night, `spine-machine2` (machine2; `spine` 63ca5e66 and `spine-lead8` 73ce48c3 merged): `OchrMeaning`
green; `DecTab.back`, `DropNoopInv`, `EvalInvR`, `SuccInvR`, `LetInvR`, `VarNumInv`, `BorrowNumInv`, `runs_expectTy_of_beq` proved
(`FormFacts` prints their axioms).

2026-11-21 evening, `spine-machine` 6ad1cd32e (after merging `spine` c0c95fb6 and `spine-lead7`; the root
imports `Steps/Machine/FormFacts`): `OchrMeaning` green. Since the merge with `spine` 1e226c6a the whole lane builds; `machineGrows` has NO
`sorry` (`#print axioms`: the three standard), all 118 steps proved on the merged checker (main's D102
to D114, the fuel-bounded loop and D103's `restoreNames` included); `decide_fuel_agree'` proved. What the
merge broke (repaired): five new block functions and ten changed signatures (regenerated), `pushTemp`'s
type and site (`notePush`), `located`'s split (`locatedCore`, `noteStateAt`), new leaves (`underProof`,
`neutralLookup`, `ctorNeedsCtx`, `inferFrom`, `inferablePos`, `fieldIsLeaf`, `restoreNames`, `lentInFields`),
a name clash (`paramDecls`), `evalCore`'s step now needs 4M heartbeats. D115 (to come on main) changes
`evalCall`, `callFn`, `runBodyCore`, `closeCall`, `evalCtor`, `joinEnds`: re-run the generator then.
