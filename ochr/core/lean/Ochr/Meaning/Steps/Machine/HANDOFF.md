# Machine lane: working note (keep current; a successor continues from this alone)

Worktree `/home/charlielidbury/repos/ochre-machine5`, branch `spine-machine5` (machine5, 2026-11-21; before it
machine4 in `ochre-machine4`/`spine-machine4`, machine3 in `ochre-machine3`/`spine-machine3`, machine2 in `ochre-machine2`/`spine-machine2`; push to your own branch; never `spine` or `main`). Lean project `ochr/core/lean`; build `taskset -c 0-14 lake build <Module>` (long builds in
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

### machine5 (2026-11-21): the fragment's facts (`FragOpen`, 18 statements in `Steps/FragMachine.lean`)

Target: `frag_run_free` = `FragTop.frag_run_ff` with all 18 `FragOpen` fields proved, in
`Steps/Machine/FragFree.lean` (root-imported; header: the checker's run existing is not proved; a
fragment; the meaning from the model half). Reports to `team-lead` by appending to
`…/scratchpad/reports/machine<N>.md`; SendMessage only for a non-minimal false statement or the stop.

PROVED (standard axioms, root-imported):
- `DropLentFail` (machine4, `FragFacts.lean`, restated: the temporary the only holder).
- `FragInv.lean`: `invPopBot`, `invSetBotNum`, `invPopUnit`, `invBindUnit`, `invEnd`, `invLendG`. Tool:
  `inv_of_fval` (Inv across a change to an all-`FVal` environment; the position-reading clauses from
  loan/borrow uniqueness, read at the old state off WF2's count (`inv_loan1`) and WF1's shapes
  (`inv_bor1`)); `setAtE` lemmas for any position (`*_setAtE_any`, temporaries too); `FEnd.erase'`.
  `InvSteps` generalised in place for a unit binding (`BindsFrom` admits `Unit`; `noInd`,
  `inv_pushBind` take `.unit`). `PlaceLocal.unit` added (FormMachine) and `placeLocal_ff` extended.
- `FragRuns.lean`: `evalLow` (goal-directed `NoRun` walk of `evalAt 1`; walking the hypothesis timed out),
  `varBotInv`, `borrowBotInv` (⊥ versions of the read machinery: `runs_content_at`, `runs_repackAt_bot`,
  `runs_accessPath_bot`, `runs_accessInside_bot`, `noRun_readPlace_bot`, `noRun_borrowPlace_bot`).
- `FragEndRuns.lean` (the shared core, IN PROGRESS): `setAtE_valAt_self` (writing a position's own value is
  the identity), `foldl_setAtE_id`, `foldl_setAtE_one`, `runs_forIn_fold`, `runs_mapState_fold`
  (`mapState f false` = the fold of `setAtE p (φ (valAt p))` when `f` acts as a pure `φ`).

RESTATED (minimal, in the lead's files): `SeqBorInv` gains `(∀ q ∈ allPos st₁.env, valAt st₁.env q = .loan l → q
= px)` (the end's `substEnv` gives `c` to EVERY holder of `loan_l`); `FragSeqB.seqB_core` supplies it
from `hF₁.loan1`.

REVIEWED TRUE, NOT YET PROVED, in the order to do them:
1. `runs_endBorrow_fend` / `runs_endTopLoan_fend` (FragEndRuns, next): `FEnd s.env px ph l c` → a run of
   `endBorrow k l` ends at `{s with env := endE s.env px ph c}`. Copy `VarEndInv.runs_endBorrow_two`
   (its `hK` continuation, the obsFrame split) with `ph` general: `findBorrow s.env l = some ph` from
   `FragFacts.findBorrow_unique` + `FEnd.bor1` (an FVal value holds borrow `l` only as `borrow_l _`);
   `cases ph` before the obsFrame `match p`; the tail = `runs_endTail_fend`: `setAt ph ⊥`, then
   `substEnv` by `runs_mapState_fold` with `φ v = if v = loan l then c else v`, `P = FVal` (substV hit
   at `loan l`: `runs_substV_hit`; miss elsewhere: `runs_substV_miss`, an FVal value other than `loan_l`
   has no `exact (loan l)` atom), the fold computed by `foldl_setAtE_one` at `px` (FEnd.loan1); then
   `lendEnv (.ended l [])` by `runs_mapState_fold` with `φ = id`, `P v = FVal v ∧ no label l`
   (`runs_lendV_miss`), fold = identity (`foldl_setAtE_id`). Then `endE` is `setAtE (setAtE E ph ⊥) px c`
   (exactly the order of the run). `endTopLoan`: holder `ph = .bind f' j'` (the F4 check errs or passes;
   no D106 error at a binding).
2. `DropBorrowInv`: `dropTopBind` → `topIdx`, `b.val = borrow l c` → `endBorrow` (1) → pop. Quiet = refl.
3. `VarLentInv`: `varNumInv`'s skeleton (`ReadInv.lean`) with `runs_repackAt_lent` (VarEndInv), the
   access through `runs_endTopLoan_fend` (accessPath loops once: after the end `x ↦ c`, a number), then
   `runs_readPlace_after` (VarEndInv) at the ended state; the copy decision at the ended state (top
   readings unchanged: `back_setAtE_any`).
4. `BorrowLentInv`: `borrowNumInv` (BorrowInv.lean) with the access ending `m` as in 3.
5. `SeqBorInv` (restated): `seqInvR` (SeqInv.lean) + `dropValue` of `borrow_l c`: `pushTemp`, `endBorrow`
   at the temporary (FEnd at the pushed env: holder the new temp), `popTemp` (now ⊥).
6. `AssignVarInv`, `AssignDerefInvF`: `assignDerefInv` (AssignDerefInv.lean) is the template; for
   `AssignDerefInvF` re-prove inside the same inversion adding the conjunct (y ↦ ⊥ at u's end: the
   assignment's `accessInside` runs `content (*y)`, which errs through ⊥); `AssignVarInv`: `x` a number/⊥
   overwritten, or lent (the access ends `m` by (1)).
7. `FragDec` (at the fuel-free table): for every fragment term, `declOfD t` succeeds at some fuel at
   `scopeState st₀ sc` with `A.rd` when `sc` reads Γ's variables `A.rd` (induction on `FTy`, the scope
   generalised; `.var i` reads `sc[i]`, `letIn` extends the scope); then `readDecisionFF_of_runs` with
   `decide_fuel_agree'`; `preFlags` of `.other`/`.unit`/`.ref .other` at a non-call is `(false,false)`.
8. `FragRun`: the checker-only induction over `FTy` mirroring `frag_sim`'s cases (EvalInv, then each
   form's inversion fact, IH on sub-terms, the FSt/FStT transfer lemmas of `Frag*.lean`). The largest.

Traps met (machine5): `by_contra`, `convert`, `split_ifs` do not exist (no Mathlib): `Classical.byContradiction`;
a `match` written in a lemma statement elaborates to its own matcher, so `rw` with `occ_loan` /
`occ_numBorrow` fails against `MState.Occurs`'s lambda: use `(occ_loan _ _).symm.trans h` (defeq);
`subst` after `runs_getAt_inv` keeps the OLD state name (`s`), the new one (`s₂`) is gone; an
`induction` hypothesis's argument order is the reverted order: state a loop lemma separately with
explicit arguments (`runs_forIn_fold`); `(… : c.Bland)` type ascriptions do not give dot-notation on
`Value.Bland`: call `Ochr.Value.Bland.anyAtom (v := c) …`.

### machine6 (2026-11-21): 17 of 18 `FragOpen` facts proved; `FragRun` false as stated, its proof under way

PROVED (standard axioms, root-imported, branch `spine-machine6`):
- `FragEndRuns.lean`: `runs_endBorrow_fend`, `runs_endTopLoan_fend` (from `EndAt` = `FEnd` without the
  temporaries clause, which no end reads; `FEnd.endAt` converts): `endBorrow l` ends at exactly
  `{ s with env := endE s.env px ph c }`.
- `FragEnds.lean`: `dropBorrowInv` (+ `dropBorrowInvM`, which also gives `ModeEq st st'`), `varLentInv`,
  `borrowLentInv`, `seqBorInv` (`runs_dropValue_borrow`, `popTempE_endE_push`).
- `FragAssign.lean`: `assignVarInv` (`runs_assignPlace_after`: [Assign] at a root after its path access),
  `assignDerefInvF` (`noRun_assignPlace_deref_bot`).
- `FragDecs.lean`: `fragDec` (any end state, any `bc`): `declOf_frag` builds the unchecked `declOf` run as
  a `runAll` equation (forward runs: `runAll_bind`, `runAll_withLive_pure`, `runs_of_runAll`).
RESTATED: `AssignVarInv`'s `ModeEq st₁ st'` conjunct gained the antecedent "x's old content is a number,
`⊥`, or lent to a binding (`FEnd`)" (unconditional it is a whole-machine fact; consumer unchanged).

FALSE: `FragRun` (Steps/Frag.lean). `FSt` says nothing about the label counter; `&x` lends at the counter.
Counterexample: `z ↦ loan_0`, `w ↦ borrow_0 Z`, `x ↦ Z`, `nextLoan = 0`; `&x` gives `x ↦ loan_0` and
`borrow_0 Z` in flight; the run succeeds; `FStT.loan1`/`bor1` fail. Proposed to the lead (fix (A)): one
more antecedent, `∀ l, st.norm.Occurs l → l < st.nextLoan` (Inv's last conjunct; every consumer has it
from `Pre`). AWAITING THE LEAD'S RULING (A, or (B): a freshness field in `FSt`/`FStT`).

IN PROGRESS: `FragRunF` (`FragRunProof.lean`): `FragRun` with `Fresh st` at the entry and `Fresh` at the
end with the value in flight (`RunOut`). Done: `frag_lift_run` (a case at `evalCore`, `CoreCase`, gives the
step at `eval`: `evalLow`, `evalInvR`, the Kern transfers), `core_zero`. The groundwork, all proved
(`FragRunLemmas.lean`): `Fresh`; `SameSkel`; `FStT.mono` (a value change with one skeleton adding no
label); `FSt.toT`, `FStT.toFSt`, `FStT.of_erase`; `FSt.pushNum` (number or `()` in flight); `FStT.setAt`;
`FStT.ofEnd` (end at bindings); `FSt.lend` (`&x`, needs `Fresh`); `FStT.popBind`; `frag_drop` (the `let`'s
drop: `DropOut` = FStT Γ, Fresh, ModeEq, top temps, readings `.tail`, size); Fresh across each. In
`FragRunProof.lean`: `FSt.setInert`, `FSt.ofEnd`, `topReadings_setAt`, `FSt.nat_at`.

NEXT (the recipe): prove `fragRunF (hdec : FragDec D) : FragRunF D` by `induction hty`, each case
`frag_lift_run hdec hty (core_X …)`, the IH an `eval`-level `RunOut`. Cases:
1. `var` (`FSt.var_cases`): number: `varNumInv` (T? from `hTs`/`hT` and `b.ty = Nat`), `Quiet` → `FSt.of_erase`
   and `Fresh.of_erase`; copy: `Kern` then `pushNum`; move (`cases hc : D.copy …`): `FSt.setInert` with `⊥`
   (`holds_bot`) then `Kern`, `pushNum`. Lent: `varLentInv`, `FSt.ofEnd hF.endAt` (then `setInert` ⊥ on a
   move). Moved: `varBotInv` contradiction. topReadings: `topReadings_of_erase`, `topReadings_setAt`,
   `topReadings_endE`.
2. `bor`: number: `borrowNumInv`, then `FSt.lend` at `stq` (Fresh from `Quiet.nextLoan`); lent:
   `borrowLentInv`, `FSt.ofEnd` then `FSt.lend` at the ended state; moved: `borrowBotInv`.
3. `succ`: `succInv`, IH on `u` (`.inl` tail), `FStT.untemp` (FragSeq), `Quiet` → of_erase, `pushNum`.
4. `asg`: `assignVarInv`, IH on `u` (hint `hu`), `untemp`; x at `st₁` by `FSt.top`: number/⊥ → `setInert`;
   loan → `FSt.fend` then `FSt.ofEnd` then `setInert`; mode via the restated antecedent; `pushNum .unit`.
5. `asgD`: `assignDerefInvF`, IH, `untemp`; y holds ⊥ (contradiction by the new conjunct) or `borrow l w`:
   `FStT.setAt` with `borrow l v₀` (labels kept), `toFSt`.
6. `letIn`: `letInvR`/`LetInv`, IH on `u`, `du = A.rd` (FragDec), `fst_push` (FragLet) then `Kern`; Fresh of
   the pushed state from Fresh with the value in flight; IH on `w` (tailDecl `.inr` via FragDec, as
   `letF_core`); `frag_drop` at `st₂.withTempT r T?`; `popped_of_topTemps` (FragLet) gives `v = r`;
   readings: `topReadings_pushBindE`/`popBindE` (InvSteps).
7. `seq`: `A ≠ ref`: `seqInv` (its `Kern stu stW ∧ ModeEq` under no-borrow/no-loan), `untemp`, IH on `w`;
   `A = ref`: `seqBorInv`, its antecedents from `FStT` at `stu.withTempT` (`FStT.noHold`), `FStT.endTemp`
   (FragSeqB) gives `FSt` after `px ↦ c`; Fresh by `Fresh.setAt`.
Then `frag_run_free` in `FragFree.lean` = `frag_run_ff` with `FragOpen` built from the proved facts and
`fragRunF` adapted to the lead's ruling (under (A): `FragRun` restated with the counter antecedent; its
consumers pass `Inv`'s last conjunct; `Fresh` from it via `occurs_of_pos` + `occ_loan`/`occ_numBorrow`).

RULING (lead, 2026-11-21): fix (A); FSt/FStT unchanged; the restatement and the consumer edits on this branch,
one line per consumer passing Inv's last conjunct (`hp.inv`'s 14th conjunct, from the `Pre` each consumer
holds at that state). NOT DONE (machine6 at its context limit). The call sites of FragRun: FragLet.lean
693 (u at st₀: `hp.of_kern hk₀`) and 728 (w at stB: `hpB`), FragSeq.lean 100, FragSeqB.lean 233, FragAsg.lean
116 and 241, FragTop.lean 58 (`(pre_stC dm D ρ).of_kern hk`), and FragSim.lean 75 through `FragRun.nat`
(FragNatRun). SNAG at the last: FragSim's `S(u)` case calls FragNatRun inside `Column.succ_core`'s `hnum`
callback, which receives only `Pu st₀` (= FSt Γ), not `Pre`; so FragNatRun cannot be given the counter
fact there without changing `succ_core`'s `hnum` to also receive it (Column.lean: one line in the
statement, one at its use (line 330: `(hp.of_kern hk₀).inv`), and one binder in each of its two other
callers, ColumnC.lean 257 and ColumnBSim.lean 146). Reported to the lead.

Traps met (machine6): the names `FT`, `topTemps` are ambiguous inside `Machine` (write `Form.FT`,
`Form.topTemps`); a lemma named `Fresh.endE`/`FStT.endE` shadows `endE` inside its own statement (named
`ofEnd`); a lemma about `FSt`/`FStT` must be declared `_root_.Ochr.Meaning.Steps.Form.FSt.x` for dot
notation; `{ s with a := …, b := … }` split over two lines needs newline-separated fields without commas;
`subst` after `obtain ⟨…, h⟩` can re-expose a shadowed `h` (name the new hypothesis freshly); `show` of
a goal on `{ s with env := E }.env` with metavariables fails (use `change` with explicit terms).

### machine7 (2026-11-21): all 18 `FragOpen` facts proved; `frag_run_free` has no assumed fact

PROVED (standard axioms, root-imported, branch `spine-machine7`):
- `FragRun` RESTATED per the lead's ruling (fix A): one more antecedent, the label counter above every
  label that occurs (`∀ l, st.norm.Occurs l → l < st.norm.nextLoan`, Inv's last conjunct); `FragNatRun`
  likewise; `FSt`/`FStT` unchanged. Consumers pass the conjunct from the `Pre` they hold; `Column.succ_core`'s
  `hnum` takes it too (ColumnC/ColumnBSim: one ignored binder). Commit a4d0ef081 (edits by machine6).
- `FragRunProof.lean`: `fragRunF` (by induction on `FTy`, each case at `evalCore` lifted by
  `frag_lift_run`): `core_zero`, `core_var`, `core_bor`, `core_succ`, `core_asg`, `core_asgD`, `core_let`,
  `core_seq_inert` (first part `Nat`/`Unit`, `seqInv`), `core_seq_bor` (first part `&Nat`, `seqBorInv`);
  `fresh_of_counter` (Inv's conjunct gives `Fresh` at a fragment state); `fragRun : FragDec D → FragRun D`.
  Helpers there: `core_out_of`/`core_out_num` (a case's end from the state of its last write),
  `Fresh.pushBind`, `FSt.setKeep`, `FSt.holds_nat`, `FSt.ty_at`, `topReadings_lent`, `quiet_size`.
- `FragFree.lean`: `fragOpen_ff st' : FragOpen (checkerDecisionsFF st')` and `frag_run_free` = `frag_run_ff`
  with it: the fragment's run theorem with NO assumed fact.
Not touched: `FragTop.lean`'s docstrings still call `FragOpen` "the facts not yet proved" (outside this
lane's files).

READ, NOT PROVED (lead14's statements in `Steps/ParFacts.lean` on `spine-lead14`, against the checker):
- `VarNumAInv`: TRUE as stated. The read of a variable holding `Sᵏ(Z)` or `Sᵏ(σ)` takes the number's
  code path in `evalCore`/`readPlace`/`repackAt`: `hasDependent` is false on `.abs` (so [Repack]
  returns at once), `firstLiveLoanOnPath`, `loans`, `ownedLoans`, `outerLoans`, `hasHole` see no atom in
  `.abs σ`, the read's `match` takes the `_` arm. The one new step is `unsizedCheck` on a bare `.abs σ`
  at runtime (`absType σ`, `isUnsizedType`): it only reads the state, or fails. Proof = `varNumInv`'s
  (`ReadInv.lean`) with `NumAt.num` generalised, `runs_hasDependent` and `runs_unsizedCheck` for NumA,
  and the value split `zero | succ | abs`.
- `InvNumA`: all three TRUE as stated. A numeral over an unknown holds no loan, borrow, `⊥`, closure,
  sealed program or constructor value, so every clause of `Inv` reading Ω's values is as for a number;
  the one new obligation is (WF6)'s bound on the unknowns occurring in Ω (`Refd σ → σ < absTy.size`),
  which `push` gets from `NumAt` (`absTy[σ]? = some Nat`); `pop` and `setBot` only remove atoms
  (`fitsInd ⊥ = true` for (V); the `⊥` at a path-free binding holding no loan meets (WF14)).

### machine8 (2026-11-21): main merged (D118, D119); the four facts read TRUE; `ConstRunJ` proved; `CallJInv` half-built

Branch `spine-machine8` (worktree `ochre-machine5`). Merge of main 9c6ebe88 into the proof line done (7cb2cd800): no
`machineGrows` repair needed (generator reproduces every Step file; no mutual-block signature changed); D119 flipped
`Regress/TailJoin` (leaves now `n ↦ ⊥`; `[Join]` counts T1/T4/T7 = 2, T6 = 3, T5 = 6) and `Regress/JoinPrefixBorrow.TU`
(still rejected, now by [Access] at the join in world Z, as main's own copy says). D118's `undeclaredCheck` only reads.

READ (step 1, against the merged checker): `FixRunI`, `ConstRunJ`, `CallJInv`, `BodyLazyInv` all TRUE as stated (reasons
in the 7cb2cd800..HEAD commit messages and the report). Points that matter for proofs: the read inside `S(#0)` is never
"wanted" (the outer `evalAt` clears `wantTy`; `.succ` calls `eval` without `demand`), so the lazy type is never read;
a PROOF reading of `#0` makes the read a statement (env restored) but then `declCopy` is `true`, so `BodyLazyInv`'s copy
branch covers it; `.any` → no pre-pass, `leafProof` false.

PROVED (standard axioms; root-imported through `ColumnJFree.lean`, whose `ColumnJ.column_J_def4` is `column_J_def`
with `ConstRunJ` discharged: it ASSUMES 4 facts, `FixRunI`, `CallJInv`, `VarNumAInv`, `InvNumA`):
- `ConstRunJ.lean`: `constRunJ : ColumnJ.ConstRunJ` (checkDef's guards via `rfl`-decided conditions; `keep_declared`,
  `keep_fuelLeft`, `keep_undeclaredCheck`; `runs_evalType_nat` for the goal).
- `CallJLeaves.lean`: `piNat`'s decisions at every fuel (`fnClass` 0, `isPropV`, `declKind`, `paramDecls`, `paramFlags`,
  `typeDecl Nat`, the telescope) — reusable for `FixRunI`.
- `CallJEval.lean`: `evalCall_J_inv` (I(Z) down to `callFn` from `stJ2` = stJ + head and argument temporaries),
  `evalAt_inv_call`, `eval_const_I_inv`, `eval_zero_inv`, `eval_nat_inv`, `runs_evalType_nat`, `runs_callType_J`,
  `Runs.privately_inv`, `Runs.withErased_inv`, `Runs.withLive_inv`, `runs_restoreKeep_same`, `Kern.size/temps/binds`,
  `Kern.withTempT'`, `callTemps_J`. `EvalInv.evalAt_inv'` (= `evalAt_inv` + tailDecl kept).
- `NoStuck.lean`: `NSAt x s` ("x from s never ends `Fail.stuck`"), `nsAt_bind` (over successful prefixes),
  `nsAt_onFail`, `nsAt_privately`, `nsAt_withErased`, leaf `ns_*` lemmas and tactics `ns_go`/`ns_go2`/`ns_go3`,
  `decideNS` (the whole Decide block never stuck, by the decideKeep induction), `nsAt_readPlace_num`,
  `nsAt_evalAt` (evalAt stuck only where its evalCore is; hyps headEval false, tailDecl none, not a value).
- `CallJBody.lean`: `nsAt_locateErrors`, `nsAt_atLoc`, `nsAt_noteStateAt_bind`, `nsAt_log_bind`, `nsAt_set_bind`,
  `nsAt_noteValue`, `nsAt_evalCore_varNum` (untyped unwanted read of a numeral never stuck).

FINDING: `CallJInv` needs a fact about FAILING runs. `callFn` runs `runBody` under `catchStuck`; a stuck body run would
close the call off ([App-close]) and the call would return a sealed program, not `S(Z)` (all CallJInv's hypotheses
still hold on that path). So the proof needs `NSAt (runBody …) sR`; `NoStuck.lean` is the infrastructure.

NEXT for `CallJInv` (the plan, in order):
1. `nsAt_located` (∀ LocsEq-states NSAt x → NSAt (located t x fl ot) s). Automation over `located`'s join points blew
   up (dsimp zeta + repeat); do it by hand: `unfold located locatedCore; simp only [bind_assoc]; refine nsAt_get_bind`,
   then split `deep`, `nsAt_log_bind`, split `table.isEmpty`, `nsAt_noteStateAt_bind`, `nsAt_set_bind`, `nsAt_atLoc`.
   Then `nsAt_eval` = located + `nsAt_noteValue` + `nsAt_evalAt`.
2. NSAt of the untyped `eval` of `S(#0)` from the callee state: `evalCore .succ` (tick, wanted, `placeOperand?` none,
   `eval` of `#0`, pure) with `nsAt_evalCore_varNum` (NumAt transfers: it reads env only; `wantHere` false because
   `nsAt_evalAt` hands `wantTy = false` on).
3. Success side of the body: the lazy read (copy `varNumInv`'s `| false` branch with `want = false`; `ty = none`), then
   `evalInvR`/`succInv` for `S(#0)` (reading `.other`, via `DecTab` back from the end of the whole run).
4. `runBodyCore`/`runBody` from the callFn state: depth check; `paramFlags`/`paramDecls` (leaves exist); `paramTypes`
   with need `[]` returns `#[none]`; `funType` of `.gfn I`; push frame; `takeCallTemps`; `pushBind` self and `n ↦ Z`
   (ty none, lazyTy set); `fnClass` 0 (erasedFn false); `needsCtx bodyI` false (`runs_needsCtx_bodyI`); tailNext; body;
   `wholeReturned`; `pushTempAt`; `popFrame` (two drops, no loans: `runs_endLoansOfTopBind_noop`); `popTemp`. Both the
   Runs inversion and the NSAt walk.
5. `callFn` inversion (plan in `CallJEval.lean`'s history: callTemps_J; findIdx none; funType; `runs_callType_J`;
   setLater; `recCheck` writes only recStack or errors; `funType?`/`declKind`/`fnClass` leaves; lent []; fixOf;
   `catchStuck` inversion with the NSAt; setFlags), then `CallJInv` from `evalAt_inv_call` + `evalCall_J_inv`.
Then `FixRunI` (checkDef → checkFix → checkTail → locatedTail → checkTailAt's `_` case; leaves mostly exist: piNat,
evalType Nat; new: `absAt`, `modelSignature`, `borrowParamCheck`, `markCapRec`, `markLastRec`, `popFrameRaw`, a
`locatedTail` inversion), `VarNumAInv` and `InvNumA` (machine7's notes above), `BodyLazyInv` in full.

### machine9 (2026-11-22): the nine column facts read TRUE; main merged (D117, D122, D124)

READ (against the proof line's checker at f6c59f58, before this merge): `SplitPInv`, `FixRunP`, `SplitRInv`,
`FixRunR`, `CallJ2Inv`, `BlockQInv`, `FixRunQ`, `BodyWInv`, `BodyKInv` all TRUE as stated (reasons field by field in
the lane report). Points for the proofs: `catchStuck`'s handler runs from the state AT THE CALL POINT (Lean's
`StateT` `tryCatch`), so a stuck callee leaves nothing, counters included; `recCheck` only rewrites `recStack` or
rejects; `exitWorld` keeps `nextAbs`, `nextLoan`, `absDecl` and `absTy`'s new tail, which is all `KeepsAtZ` needs;
`readPlace` moves a borrow before reading the copy or in-place flags.

MERGE (branch `spine-machine10`, origin/spine b54f9c83 + origin/main e0b73bce, no conflict): the checker gained
`forceHint` inside the mutual block (D124's deferred hint), and `readsHint`, `hintLater`, `resolveLoans` outside it.
Regenerated with the scripts (their paths name the worktree `ochre-machine`: copy them to a scratch directory and
`sed` the path; `regen.py`'s groups now list `forceHint` under `StepCall`); `IH.lean` gained the `forceHint` field;
`MachineLeaves.lean` the grows leaves of `readsHint`, `resolveLoans`; `HintKeep.lean` their `Keep` lemmas. Repairs:
- the typed `let`/`;` tail's hint is now `if typed || !tail then none else hint`: `simp only [Bool.true_or, …]` at
  `StepInv`, `SeqInv`, `FragEnds`, `MasterDepth`, `MasterSeq`;
- an assignment's and a call argument's hint test now runs `readsHint` first (a nested `←` is lifted before the
  `if`, typed runs included): one `Runs.bind_inv` + `runs_keep keep_readsHint` at `AssignDerefInv`, `FragAssign` (two
  sites), `CallJEval` (`runs_needsCtx_zero` no longer used there);
- the untyped inversions `SeqInvDU`, `LetInvDUn`, `LetCallInvU` (`Steps/MasterUntyped.lean`) RESTATED: the tail runs
  at `if st.curTail then hint else none` (they said `hint`, false out of tail position since D124); consumers take
  them at `none` and `rw [ite_self]`.
- `runBodyCore`'s hint is now `readsHint fuel' true false body` (then `hintLater` unless a borrow argument), not
  `needsCtx`: the `CallJInv` plan's step 4 needs `readsHint … bodyI = false` in place of `runs_needsCtx_bodyI`.
PROVED (`HintFacts.lean`): `HintSites.UntypedLetTailNoHint`, `UntypedSeqTailNoHint`, `UntypedMatchNatArmNoHint`,
`UntypedMatchIndArmNoHint` (`runMachineL` of the two runs equal past the tail flag's read), `ClonePeekPlace`.

After the merge (same branch, commits da155db36, 1d97ac932):
- READ: `TailOtherInv` FALSE as stated (`located` restores `locs.callArgs`/`locs.here` after the continuation when the
  editor's table is non-empty; counterexample `MasterTail.TailGuards.stE`/`kLocs`); restated (`∃ st₂, Runs (k v T)
  st₁ b₂ () st₂ ∧ { st₂ with locs := st'.locs } = st'`) and PROVED (`TailOther.lean`: `Runs.locatedTail_inv`, then
  `checkTailAt`'s default case; `tStepOther_free`). `SplitNotInv`, `CallKInv`, `InvMoveBorrow`, `InvPushType`,
  `CheckIndGivesChecks` read TRUE (reasons in the commit message of da155db36).
- Tools for the next proofs: `Runs.locatedTail_inv` (any `checkTail` run reaches its `checkTailAt` from a `LocsEq`
  state and ends `LocsEq`); `tailOtherInv` turns any `checkTail` of a non-tail-shaped body into its typed `eval` at
  the goal (so `FixRunI`/`FixRunQ` reduce to inverting `checkDef`/`checkFix` down to `checkTail`).
- NOT DONE, with the obstacle: `InvPushType` needs `Value.Bland`/`Simple` (InvEnv) widened to the atoms `Nat`/`Unit`
  (`PosRel`'s fwd/bwd and `inv_step`'s per-value condition use them; every lemma destructing them gets two cases);
  `InvMoveBorrow` needs `PosRel`'s moved-borrow clause (`NumBorrow`, `w.Num`) widened to a borrow of a `NumAt`
  numeral (K's `borrow₀ σ0`), with `τ` the swap of the binding and the new temporary (injective; the binding then
  holds `⊥`, bland). `checkFix`'s inversion (for `FixRunI`, `FixRunP`, `FixRunR`, `FixRunQ`, shared): the steps are
  listed in machine8's plan above.

### machine10 (2026-11-22): main merged (D125, D126, D124 for J and for an embedded value); step 1 found six facts false; eight proofs

Branch `spine-machine11` (worktree `ochre-machine5`). Merge: origin/spine 36c6f669 + main up to 021ca7cd5, no
conflict; one new block function, `jMotiveAt` (regen.py lists it under StepEval; IH, Zero, All gained its lines).
Guards flipped, all in `Steps/HintSites.lean`: SplitData's braces form is `split IsZ(n) { … }` and H/H2/H3 are
accepted (D125); the untyped run of `split` runs its term; JHint.JL2 is accepted.

READ (step 1; reasons in the lane report, scratchpad `reports/machine10.md`):
- FALSE: `ItemFacts` (twice: an embedded value in an arbitrary item's field type, `EV := MkEV(x : L(⟨0⟩))`;
  `VaryValFree` on the surface program `TL (A : Type) (B : (let z = A; Type)) := MkTL(x : B)`, because
  `paramIsType` is syntactic while D55 reads the declared reading); `DecLocal.join` (the join regrains entry
  places: a CHECKER BUG, `f3`/`h` in `reports/machine10-JoinRegrain.lean` falsely rejected; fix: grain only the
  places the arms add); `DecStable` (unconstrained `st0`); `SuccFlightG` (untyped, a borrow under `S`, WF1);
  `LetPushG` (the binding's reading unconstrained, `ShapeFacts.fits`).
- TRUE: `inds_prefix`, `NamesFact` (resolved items), `FieldLevels`' checker part, `DecLocal`'s caps/rep/inv,
  `ReadInvD`, `PlaceInvD`, `EvalInvDT`, the checker parts of `PlaceTypeG`, `AccessG`, `SuccStrictG`, `LetDropG`,
  `DropValueG`.

PROVED (standard axioms, root-imported):
- `EvalInvT.lean`: `evalInvDT`; `PlaceInv.lean`: `placeInvD`, `stepPlace_direct5` (`stepPlace_direct` assuming 5).
- `CheckItem.lean`: `runs_checkInd_tables`, `runs_checkDef_tables`, `checkItem_tables` (what an accepted item does
  to the declarations and globals), `indsOf_take_prefix` (= `Consistency.inds_prefix` with no hypothesis; the lead
  lane can replace that `sorry` by it after importing CheckItem), Keep/grows lemmas for checkInd's checks.
- `CheckIndChecks.lean`: `runs_forIn_all`, `runs_fieldTele_vals`, `firstOrder_foB`, `readViolation_rvB`.

NOT DONE: `CheckIndGivesChecks`'s assembly (the plan is in CheckIndChecks.lean's docstring: re-peel `checkInd` as
`runs_checkInd_tables` does, keeping `declared`'s answer for `fresh`, the [Ind] loop's `late.isEmpty` for `TeleOk`
via `runs_forIn_all` twice, and through `runs_forIn_all` + `runs_fieldTele_vals` the continuation's run at each
field: peel its ifs, `firstOrder_foB`/`readViolation_rvB` at a state whose declarations are `declEnv Γ0 d'`
(TablesGrow from the stub write), and `sortNestViolation` = none; `nest` by `nestableSet` not reading `nestable`).
`ReadInvD` needs "the access keeps the mode" (copying/inPlace), which no lemma gives yet (a mode analogue of
`machineGrows` would). Then the predecessor's list: `checkDef`/`checkFix` down to the end-of-body check,
`InvPushType`, `InvMoveBorrow`.

TRAPS found here: (1) `MachineMono.lean` declares a `grows_go` MACRO (for `GrowsM`) beside `Tactic.lean`'s
elaborator; a module importing both gets the macro, which does nothing on `GrowsIn`: use `grows_goI` (declared in
CheckItem.lean). (2) `lake env lean` does not run imported `initialize`, so `@[grows]` is empty there: test with
`lake build <module>`. (3) After `unfold f at h`, `dsimp only at h` reduces instance projections and breaks the
`@[grows]` lookup; use `dsimp (config := { proj := false }) only at h`. (4) `split at h` on a large `if` exceeds
simp's step limit: `cases`/`by_cases` the condition and `rw [if_pos …]`/`rw [if_neg …]`.

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

2026-11-21, `spine-machine8` (machine8): `OchrMeaning` green after merging main 9c6ebe88; the new files
(`CallJLeaves`, `CallJEval`, `NoStuck`, `CallJBody`, `ConstRunJ`, `ColumnJFree`) build in the default build
(root imports `ColumnJFree`), standard axioms; `fund_all`, `column_C_free`, `column_B_free`, `frag_run_free` no assumed
fact; `column_I_def` 3 facts as before; `column_J_def4` 4 facts. The stray `example … sorry` in `Inv.lean` is removed.

2026-11-21, `spine-machine7` (machine7; from `spine-machine6` 117a755e6): `OchrMeaning` green; `frag_run_free`,
`fragOpen_ff`, `fragRun`, `fragRunF`: standard axioms (no fact assumed).

2026-11-21, `spine-machine5` (machine5; `spine` aa410844 merged): `OchrMeaning` green; `column_C_free`,
`column_B_free`, `frag_run_ff` and the nine fragment facts proved so far: standard axioms.

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
