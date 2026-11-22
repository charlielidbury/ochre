# Open statements of the consistency spine (working file, sixth lead)

Every named statement of `Ochr/Meaning/` whose proof is `sorry`. First made at `spine-lead` 0b0dc6b9; updated at the merge of spine 8a966499 (docs/31 D84: the chain's decisions fuel-free; `typedFutureF_exists` restated and proved; `app_mem`, `ctorOut_mem`, the substitution lemma for unknowns proved by the data layer). Kept current by the lead; scheduled from.

Columns. **Says**: plain words. **Checked**: a kernel-checked run (`Regress/…`), a sweep on recorded checker states, or none. **Size**: few lines / a page / several pages / core (an induction over the interpreter or the run, of the size of the core lemmas). **Status**:
- `FALSE (K)`: refuted by a kernel-checked counterexample (named);
- `suspect`: false as stated by reading, NOT kernel-checked; the missing hypothesis is named; mostly the use site has it;
- `uncertain`: no reason to believe it false, no reason to believe it true beyond reading;
- `likely true`: reading found the argument and nothing against it (a guess, not a proof).
**M**: `M` = about the machine alone (no model, no assignment), to be staffed as its own lane; `M*` = machine-only conclusion under a `WF`/`CtxOk` hypothesis that could be dropped.

Reading-based verdicts were produced by four read-only agents and spot-checked by the lead where marked (✓). Three root causes recur; a fix to the root removes several rows at once:
- **T (D81)**: a temporary has no stored type. Any statement asking `Good` of a state that holds a borrow in a temporary lent by a typed binding is vacuous there (`Regress/EvalMemGap.borrowArg_not_good`); no statement gives an evaluated value's membership. Marked †.
- **U (D81)**: untyped runs bind at types they never check (`Regress/EvalMemRuns` part 3); `Good` cannot be maintained through them.
- **L (docs/35, trial)**: a comparison's private copy keeps η records that can name an unknown of an empty type, after which no extension is good; to be removed by the checker change "a comparison keeps nothing but names" (D103). Marked +L.

## THE MASTER INDUCTION OF (II), CONTINUED (lead26, 2026-11-22, `spine-lead26`; docs/31 D180 to D183)
- `EvalAt` concludes `OutL` (D183, ruled): a call run with the deferral flag set and the record clear means, by any pair it records, the reference's result type (`LaterOk`). Every proved step and `master` re-proved, mechanically.
- PROVED at every tail flag: `stepSeq_unerased` (typed or untyped; 3 facts: `SeqTailDecl`, `DropValueG`, `ValsCongrA`), `stepLetIn_unerasedAll` (every `let`, typed or untyped, a call's right-hand side included; 5 facts: `LetTailDecl`, `LetPushG`, `LetLazyPushG`, `LetDropG`, `ValsCongrA`); `hintM_congrA`, `Machine.letCallInvU` (restated with the record link) PROVED. D124's facts are no longer assumed by any step.
- RESTATED: `Master.LetLazyPushG` (was FALSE: no link between the recorded type and the reference's; now takes it, from `OutL`). SUSPECT (by reading, D183, asked): `LetPushG` at a value with no type (`T₀ = none`): the binding's stored type reads `err`, the reference's the result's, `Rel.skel` compares them; the untyped `let` would need "the right-hand side returns a type" (true on every probe).
- `place` (D181, D182): `stepPlace_direct` (a direct read, unerased, typed or untyped) ASSUMES 7 facts, each STATED in `Steps/MasterPlace.lean`: `EvalInvDT`, `PlaceInvD`, `ReadInvD`, `BorrowReadWhole` (checker; the last FALSE until main's D127, RULED (A); all pinned), `PlaceTypeG`, `AccessG` (the core, attacked on six cases in `Steps/AccessAttack.lean`), `ReadOutG` (mixed). Not covered: a read with a positional projection (a one-constructor match), the erased read.

## THE MASTER INDUCTION OF (II), CONTINUED (lead25, 2026-11-22, `spine-lead25`; docs/31 D174 to D179)
- PROVED: `stepSeq_untyped` (out of tail position; assumes `UntypedSeqTailNoHint` [checker, PROVED since the merge of D124: `Machine.untypedSeqTailNoHint`], `SeqTailDecl`, `DropValueG`, `ValsCongrA`), `stepLetIn_untyped` (out of tail position, right-hand side not a call; assumes `UntypedLetTailNoHint` [checker, PROVED since the merge of D124: `Machine.untypedLetTailNoHint`], `LetTailDecl`, `LetPushG`, `LetDropG`, `ValsCongrA`); `Machine.seqInvDU`, `Machine.letInvDUn` (proved).
- PROVED at the merge of main (machine9, spine-machine10): `HintSites.UntypedLetTailNoHint`, `UntypedSeqTailNoHint`, `UntypedMatchNatArmNoHint`, `UntypedMatchIndArmNoHint` (D124), `ClonePeekPlace` (D122), all in `Steps/Machine/HintFacts.lean`. `Machine.LetCallInvU` PROVED since (lead26); `Master.LetLazyPushG` restated (lead26, D180).
- NEW, open (Consistency chain): `Assembly.inds_prefix` (checker leaf: every stage's declarations are a prefix of the whole program's); `covered_prefix` deleted.
- The tail shape `split f in u`: the reference now runs `u` (D178). The braces form `split f {…}` is gone from the core since main's D126 (it resolves to `split f in match f(ā) {…}`), so it has no clause and no step (lead27, D184).
- `EvalAt`/`CoreSimK`/`EvalSimK` assume `HintBelow` (D179, ruled); the old form is not shown false (counterexample not built).

## THE MASTER INDUCTION OF (II), CONTINUED (lead24, 2026-11-22, `spine-lead24`; docs/31 D170 to D173)
- PROVED: `stepSucc` (typed and untyped), assuming 3 NEW facts: `SuccStrictG` (mixed, typed only), `SuccMeanG` (model), `SuccFlightG` (mixed); `Machine.succInvD` (PROVED). The model change it needed (the reference runs `S`'s argument with no hint) is built (D171).
- (superseded by lead25: `UntypedTailNoHint` is now four facts, one per site)
- (superseded by lead25, D178: `split f in u` now has its clause; the braces form is gone from the core since main's D126, lead27 D184)
- The erased depth is tested on the reference's side (D170): `DepthRef.column_CapE` (nothing assumed), `column_CtorE` (`CtxFaithful` only); `NestE`, `MatchE`, `ReadE` argued, not run.
- The hint audit (D172): the model's remaining drifts fixed (`Eq`'s sides, every parameter); eleven sites where the checker's typed and untyped runs differ, and three where the reference differs from the typed check (`J` stuck: open; `rewrite`, `lentProofAssign`: proofs on copies), listed for rulings.

## THE MASTER INDUCTION OF (II) (lead22, lead23, 2026-11-22, `spine-lead23`; docs/31 D150 to D159)

`Steps/Master.master`: (II) for `eval` and `checkTail` at every fuel, `Δ`, assignment, term and erased depth, ASSUMING the 32 step statements of `AllSteps` (no `sorry`); each statement concludes `Kept` (mode, frames, top readings) beside `Out`, and says a typed run is not in tail position. The table of the 32 is docs/31 D153. Proved in general: `stepZero`, `stepTt` (nothing assumed); `stepNat`, `stepUnit` (`InvPushType`); `tStepOther` (`TailOtherInv`); `stepLetIn_typed` (typed, unerased `let`: `LetTailDecl`, `ValsCongrA`, `LetPushG`, `LetDropG`, `FundCtx`); `stepSeq_typed` (typed, unerased `;`: `SeqTailDecl`, `DropValueG`, `ValsCongrA`, `FundCtx`). Proved facts at any depth: `Machine.evalInvD`, `letInvD`, `seqInvD`.
- NEW FACTS, open: `TailOtherInv` (checker, guarded), `InvPushType` (checker), `LetTailDecl`, `SeqTailDecl` (table, guarded), `ValsCongrA` (model), `LetPushG`, `LetDropG`, `DropValueG` (each part checker, part model; checker halves guarded).
- The erased wrapper (every former's erased case), stated with its four missing facts: docs/31 D158 (the erased path's inversion, an erased value holds no label, `Pre` across the restore, a proof's type means a true proposition); `Rel` across the restore is proved (`Rel.private_copy`).
- FIXED at the merge of main's D122 (machine9, spine-machine10): `StepPrim` at `clone`/`peek` of a non-place was known false (`Steps/MasterGuards.lean`; the core checker now rejects it, the pin flipped); "the operand is a place" is `HintSites.ClonePeekPlace`, PROVED (`Machine.clonePeekPlace`).
- The model's tail-hint change is BUILT (D156); `Form.eval_sim` is DELETED (D154).

## THE FIRST DATA TYPES `B` AND `Box`; A CAPTURE PINNED (lead21, 2026-11-22, `spine-lead21`; docs/31 D147 to D149)
- Stated checker facts, unreviewed, guarded: `ColumnNot.SplitNotInv` (`Steps/DataNot.lean`), `ColumnBox.WrapInv`, `ColumnBox.UnboxInv` (`Steps/DataBox.lean`). For the machine lane.
- Data-model hypotheses (named, one per column; each is `CtxS`'s data-model fields at the column's declarations; instances given): `ColumnNot.DataModelB` (`dataModelB_triv`), `ColumnBox.DataModelBox` (`dataModelBox_leafNat`).
- Not built: `Unbox`'s and `Wrap`'s `TailSim` steps; the join after an arm (`UseO`); `Not`'s `.fix`-level column; the capture's `.fix` step (D149) and the ruling on `refTy` by name if a lambda's body must be simulated.

## `K` CLOSED AT THE COLUMN LEVEL; `K`'S STEP; THE FIRST CALLER OF `K` (lead20, 2026-11-22, `spine-lead20`; docs/31 D141, D145, D146)

- **D141 built**: `OutGood`'s final clause at the futures typed for the result (`HeldTyped` at `BodyOut.held`). `ColumnW.closure_mem_K`, **`ColumnW.column_K_ff` (NO assumed fact)**.
- **`K`'s body step** `ColumnW.body_simK` ASSUMES 2 checker facts, unproved: `BodyKInv` (lead18) and `InvMoveBorrow` (NEW, state-level, `Steps/BorrowParStepK.lean`: a binding holding a borrow of a numeral over unknowns set to `⊥` with the borrow pushed as the top temporary keeps `Inv`; its `K` instance `#guard`ed). The relation after is the general `MoveOut.rel_moveOut` (no assumed fact).
- **Facts about the checker (machine lane), stated and `#guard`ed, unproved:** `ColumnW.CallKInv` (`Steps/CallKGuards.lean`: `K(&x)` from `x ↦ S(Z)` returns `borrow₁ S(Z) : &Nat` or a borrow of a sealed call, ends at `stLY`: `x ↦ lent₁ loan₁`, counter 2).
- Open: `L`'s call step (D146's list); `body_simK` at `K`'s concrete start; `Q`; `J2` (unchanged).

## THE BORROW-PARAMETER COLUMNS `W`, `K`; D138 BUILT; D137 (B)'S TEST (lead19, 2026-11-22, `spine-lead19`; docs/31 D140 to D144)

- **D138 built**: a borrow parameter's cell is its label's loan site (`fixStep`). `rel_startW`, `rel_startK` (every clause of `Rel` at the start), no assumed fact. `FrameProp.FrameRel.lentCl` restated (a closure may lend at its cells).
- **`W` closed at the column level with NO assumed fact**: `ColumnW.column_W_ff` (the reference forms `W`'s closure, a member of `Π(r : &Nat). Nat`, at the checker's table). The body step in the form, `body_simW`/`body_outW` (applied at the start with `pre_stW`, `rel_startW`, `sgood_SBW`), ASSUMES `BodyWInv`, `InvNumA` (checker facts, unproved).
- **D141 RULED AND BUILT (lead20)**: `OutGood`'s final clause is at the futures typed for the result (`HeldTyped` at `BodyOut.held`, beside `TypedFut`); a data codomain gives the old clause; no result holds two labels (core D48). `ColumnW.closure_mem_K` (`K`'s closure a member of `Π(r : &Nat). &Nat`), no assumed fact; `not_outGood_K` refutes the old clause (`OutGoodEvery`).
- **`K`'s body step**: not written. Needs a new checker fact for `Inv` after moving a borrow into flight (proposed `InvMoveBorrow`) and the relation after the move (template: `ColumnLetB.rel_pushBind_borrow`, the inverse move).
- **D137 (B)**: not dropped; its test is `Regress/BlockReadings.A3` (stored reading `.pi .other`, the model's `.other`); `KeepTP` closes no block.
- Unchanged from lead18: `Q`'s step and column; `J2`'s `Pre`/`Rel` after the call, the `let`, `column_J2_ff`.

## THE FIRST CLOSED-OFF BLOCK (`Q`), THE FIRST BORROW PARAMETERS (`W`, `K`), `J2`'S CALL (lead18, 2026-11-21, `spine-lead18`; docs/31 D137 to D139)

- **Two model faults found, both ruled (A):** (1) D137, FIXED (ecb7288d): `CapsOk` reads a closure's captures against the first readings only (a stuck block keeps its parameters' readings in `rd`); `ColumnQMean.mean_vQ` proves the block means the reference's result. (B), the parameters' readings from `rd` in the `.fix` run, is decided and not built; its regression (main's `FrozenReadings.KeepTP`) is not pinned yet. (2) D138, NOT BUILT: `fixStep` must record a borrow parameter's cell as its label's loan site; until then `BorrowParStart.rel_start_false` stands (no `fixBodyAt` state for a borrow parameter is related to the checker's start).
- **Facts about the checker (machine lane), stated and `#guard`ed, unproved:** `ColumnQ.BlockQInv` (`Steps/BlockQ.lean`: the typed `eval` of `Q`'s match from `stQ`'s kernel returns `⌈anonQ(σ0)⌉ : Nat` and ends with `endQ`'s kernel); `ColumnQ.FixRunQ` (`checkDef defQ` inverted to the body's typed `eval`); `ColumnW.BodyWInv`, `ColumnW.BodyKInv` (`Steps/BorrowPar.lean`: each body's typed `eval` from its start kernel: value, type, end kernel). Guards: `Steps/BlockGuards.lean`, `Steps/BorrowParGuards.lean`.
- **Restated (D139, the orchestrator's ruling):** `CallJ2.CallJ2Inv`'s last conjunct is a disjunction: the body's untyped run to the value, or the sealed call `sealJ2`.
- Proved (standard axioms, no assumed fact): `ColumnQMean.runMatchQ`, `runBodyQ` (the reference's direct run of a non-tail match: [Entry], one arm, the join), `gA_run`, `gA_mem`, `runT_anonFix`, `callOf_A` (the block's code as a closure gives the same number); `CallJ2Step.runT_callJ2_J2`, `mean_sealJ2`, `ColumnQMean.mean_vQ`; `mean_callJ2` assumes `CallJ2Inv`, `BodyLazyInv`.
- Next: `Q`'s step (`Out` for the match: `Ext` gives the leftover `σ1` any number; `Rel` by one `botWrite_rel` at `n` after `rel_transfer`), the body via `SuccInv`/`EvalInv`, `column_Q_ff`/`_def`; on ruling (2), `Rel` at `W`'s/`K`'s start, the bodies' steps, membership in `Π(r : &Nat). …` (one final, the cell's content); `J2`: `Pre`/`Rel` after the call in each branch, the `let`, `column_J2_ff`.

## THE FIRST RECURSIVE FUNCTION, `R` (lead17, 2026-11-21, `spine-lead17`; docs/31 D133, D134)

`def R (n : Nat) : Nat by n := match n { Z => Z, S m => R(m) }`; the checker pinned in `Steps/RecGuards.lean` (the self-call on `σ1` closes off to the sealed program `⌈R(σ1)⌉ : Nat`; `recCheck` keeps the candidate since `σ1` is a strict subterm of `S(σ1)`).
- **Facts about the checker (machine lane), stated and `#guard`ed, unproved:** `ColumnR.SplitRInv` (`Steps/RecR.lean`: `SplitPInv` for `R`'s body; the leaves `leafZR` on `Z : Nat` and `leafSR` on `⌈R(σ1)⌉ : Nat`, with `KeepsAtZR`); `ColumnR.FixRunR` (`checkDef defR` inverted to the body's `checkTail`).
- **Restated (D133):** `CallBody.BodyLazyInv` takes `CopyDec D st (.var 0)` (the read's copy decision at the body's start) instead of `DecTab D st'` at its end; `VarNumAInv` keeps the old pattern (same narrowing recommended).
Proved (standard axioms): `ColumnRSplit.split_outR`/`split_simR` (`TailSim` for `R`'s body at stage `b + 1`, context `KR … (GR … b fn) b`, from every assignment with `ρ σ0 ≤ b`; hypothesis `GoodBelow` (the outer induction); checker: `SplitRInv`; model: none); `ColumnR.goodBelow_stg` (the knot: every reference stage good below its bound; no assumption); **`ColumnR.column_R_run` (the closure a member of `Π(n : Nat). Nat`; NO assumption)**; `column_R_ff` (+ `TailSim` at every stage with the hypothesis discharged; checker: `SplitRInv`; model: none); `column_R_def` (+ `FixRunR`). `CallJ2.copyDec_calleeJ2`, `parDecJ2`, `flags_bodyI_J2` (J2's table gives the callee's decisions; no assumption).
Next for recursion: a recursive function whose result is used after the call (`S(R(m))`, a `let` around the call), where the relation at the leaf carries the sealed call into the continuation; a recursive function with a λ capturing its own name (D123's stage 2, `Regress/SelfCapture.R7`).

## THE FIRST SPLIT, AND J2'S CALLEE (lead16, 2026-11-21, `spine-lead16`; docs/31 D131, D132)

Open statements added, none with `sorry` (all are named hypotheses):
- **Facts about the checker (machine lane), stated and `#guard`ed, unproved:** `ColumnP.SplitPInv` (`Steps/SplitP.lean`: `checkTail` of `P`'s body from `stP`'s kernel, in the plain mode, with a continuation keeping the counters in world `Z` (`KeepsAtZ`), ran the continuation at two leaves with the kernels `leafZ` (on `Z : Nat`) and `leafS` (on `σ1 : Nat`); guards in `Steps/SplitGuards.lean`); `ColumnP.FixRunP` (`Steps/ColumnP.lean`: `checkDef defP` inverted to the body's `checkTail` from `stP`'s kernel, with a continuation keeping the counters in world `Z`; guarded by the derivation); `CallJ2.CallJ2Inv` (`Steps/CallJ2.lean`: the checker's call `I(x)` at `J2` decomposed into the untyped body run from `stCJ2`'s kernel, the value at `Nat`, the end kernel `stX`; guarded).
- **The form:** `Out`/`Ext` unchanged; a wrapper for tail position, `FormTail.TailOut`/`TailSim` (some leaf where the continuation ran, with `Out` there).

Proved (standard axioms): `ColumnPSplit.split_outP`/`split_simP` (`TailSim` for `P`'s body from every related reference state; checker: `SplitPInv`; model: none); `ColumnP.column_P_ff` (checker: `SplitPInv`; model: none); `column_P_def` (+ `FixRunP`); `CallJ2.rel_calleeJ2`, `pre_stCJ2`, `lazyNum_stCJ2`, `hint_nLazy`, `hpi_of_globals` (no assumption); `CallJ2.closureRun_J2` (checker: `BodyLazyInv`, `InvNumA`; model: none; without `FundCtx`/`SGood`/`FrameStart`).

Open at `J2` (docs/31 D132, D133, D135, D136): the call's step in the form and the `let` around it. Closed: `callOf` of `J2`'s own closure and its membership at `J2`'s table (`CallJ2Fn.callOf_fJ_J2`, `fJ_mem_J2`; no assumption); `frameRelS_start`'s lent-site hypothesis (D135: held labels only, vacuous at `J2`). The table at the callee is closed (D133: `BodyLazyInv` takes only the read's copy decision, `CallBody.CopyDec`, which `CallJ2.copyDec_calleeJ2` gives at `J2`'s table by kernel evaluation; `parDecJ2`, `flags_bodyI_J2` likewise). The reference's run of `I(x)` is built (`runT_callJ2`, `caller_of_rel`).

## THE FRAME PROPERTY (model6, 2026-11-21, `spine-model6`; docs/31 D129, D130)

- **`FrameJ2` PROVED** (`Steps/FrameFrag.frameJ2_holds`, no assumption). `closureRun_of_checker_free` (D128's steps (3)+(4)): checker facts `BodyLazyInv`, `InvNumA`; model facts: none.
- **`FrameProp.run_frame` (D113's form) FALSE (K)**: `Strict/FrameLocCE.run_frame_loc_false` (a callee-frame value reading an unheld label is read at `φ l` in the closure and `φ (σ l)` in place). The `sorry` theorem is deleted. Restated: `Steps/FrameFrag.RunFrameS`, a named proposition (no `sorry`) over `FrameRelS` with a locality clause; OPEN in general; PROVED on the label-free fragment (`run_frameS_lf`: `Z`, `S`, a variable read, `x := u`, `let`, `;`; no parameter label; any tails and hints). What each remaining clause of `runT` needs is in `RunFrameS`'s docstring.
- `FrameRel.held` relaxed (D113's note): `heldMem` off the parameter labels only, `heldTy` at every label of the frame.
- `callOf_inPlace` (Steps/Call.lean, `sorry`) is NOT restated: the in-place result's type is the body's, `callOf`'s is the codomain's code at the arguments; their agreement is a typing fact about the body, not a frame fact; a restatement should compare values and type meanings, with the frame part from `RunFrameS`.
- **`GlobalsOk.fn` for the global `I` at `J`'s start PROVED** (`Steps/GlobalsLocal.fn_clause_I_tab`, no assumption): frame locality of closed code (`meanV_clo_closed`). `fJ_mem` and `callOf_fI_at` proved at `I`'s table (checker facts `VarNumAInv`, `InvNumA`). Open: one table for both (`J`'s body at a table aligned at `stJ`, `fJ_mem` at one aligned at `stI`; they differ in `absDecl`).

## THE FIRST CALL (lead15, 2026-11-21, `spine-lead15`; docs/31 D127, D128)

Open statements added, none with `sorry` (all are named hypotheses):
- **Facts about the checker (machine lane), stated and `#guard`ed, unproved:** `ColumnJ.CallJInv` (the checker's call `I(Z)` from `J`'s start returns `S(Z)` at `Nat` and keeps the kernel; its proof needs the untyped read of a LAZILY typed binding, which `VarNumAInv` does not cover); `ColumnJ.ConstRunJ` (`checkDef defJ` inverted down to the body's `eval`); `CallBody.BodyLazyInv` (the untyped run of `S(#0)` from a callee frame whose parameter is lazily typed and holds a closed numeral).
- **Fact about the model (model lane): `FrameJ2.FrameJ2`** (PROVED since, model6: `FrameFrag.frameJ2_holds`), the instance of the frame property `J2 := (let x = S(Z); I(x))` needs, with the function's own binding related by `SelfRel` (the ruling of D127); its relation is checked to hold at `J2`'s states (`frameRelS_start`, proved). This is its specification.
- `FrameProp.run_frame`'s relation `FrameRel` cannot hold at the start of any call (the function's own binding: in place the callee's meaning at its declared type, in the closure the stage below at the weakened type; D127). Ruled: `FrameRelS` (`SelfRel` at that binding), stated for bodies in which the own name does not occur; `run_frame` and `callOf_inPlace` are to be restated on it. For recursive functions `SelfRel` gains "agree below the current argument" (planned, not built).

Proved (standard axioms): `ColumnJ.callJ_sim` (the call's step in the form; assumes `CallJInv`), `ColumnJ.column_J_ff` (checker facts: `CallJInv`, `VarNumAInv`, `InvNumA`; model facts: none), `column_J_def` (+ `FixRunI`, `ConstRunJ`), `CallBody.bodyLazy_sim`/`bodyLazy_out` (the untyped body step in place; checker: `BodyLazyInv`, `InvNumA`; model: none), `FrameJ2.closureRun_of_checker` (steps (3)+(4) of `J2`'s plan compose; checker: `BodyLazyInv`, `InvNumA`; model: `FrameJ2`; plus the callee state's `Pre`/`Rel`/`SGood`/`FrameStart`/`FrameRelS` as hypotheses). Not yet assembled: `J2`'s step (docs/31 D128's plan).

## THE FIRST COLUMNS WITH A PARAMETER, CONTINUED (lead14, 2026-11-21, `spine-lead14`)

`I`'s body start state: `Pre`, `Rel`, `SGood` PROVED with no checker fact (`Steps/ColumnIStart.lean`); `ParDecI` and the reference `.fix` clause's decisions at scope `[]` PROVED from the aligned table by kernel evaluation (`parDecI`, `fixDecI`); the body's reference run from the start state PROVED (`Steps/ColumnI.body_runI`: `S(a)` at `Nat`, no live label) from `VarNumAInv`, `InvNumA` (READ against the checker by the machine lane and judged true as stated, not proved; each `#guard`ed in `Steps/ParGuards.lean`) and proved facts. `FrameDrop0` DELETED (model5, docs/31 D126 ruled: the reference's body runs in the checker's frames, `SState.under`; for `I` the two start states are equal, `ColumnIRun.start_I`). `Steps/ColumnIRun.column_I_ff` (from the checker's run of the body; the reference's `.fix` run of `I` from the empty state succeeds at `Π(n : Nat). Nat` and the closure is a member) ASSUMES 2 facts about the checker: `VarNumAInv`, `InvNumA`; `column_I_def` (from `checkDef defI`'s acceptance) assumes 3: `FixRunI` (STATED, model5: the inversion of `checkDef defI` down to the body's `eval`, FOR THE MACHINE LANE; `#guard`ed by `checkDef defI`'s derivation), `VarNumAInv`, `InvNumA`. The `.fix` clause's reading of `I` proved (`Steps/ColumnIFix.lean`). `P`: waits for main's D119 (docs/31 D125 re-ruled (B′): the checker's split joins at each leaf) in the proof line. The surface's `S(n)` is a call of `succFn` (docs/31 D124): column `I` is `succFn`'s body.

## THE FIRST COLUMNS WITH A PARAMETER (lead13, 2026-11-21, `spine-lead13`): `I`, then `P`

`def I (n : Nat) : Nat := S(n)` and `def P (n : Nat) : Nat := match n { Z => Z, S m => m }`, each to "the `.fix` closure is a member of its type". The body's start state needed a change to the relation's types (docs/31 D123, `Binding.refTy`: a binding marked as the function being checked has the context's type). Facts stated so far (`Steps/ParFacts.lean`):
- FOR THE MACHINE LANE: `VarNumAInv` (the read of a variable holding a numeral over an unknown, `Value.NumA`; `VarNumInv` with `NumA`); `InvNumA` (state-level: a numeral over unknowns of type `Nat` pushed/popped as the top temporary, a binding holding one set to `⊥`). And the fact D123's sufficiency rests on (not yet a `Prop`): in an accepted definition's body the function's own name occurs only as the head of a call, or, for a recursive function, inside a λ's captures ([Rec]'s "occurs in its own body other than as the head of a call (fix L1)"; D31's "not in scope in its own body"); asserted on examples in `Regress/SelfCapture.lean`.
- FOR THE DECISIONS' LANE: `ParDecI D R` (`Steps/ParBody.lean`): at the top frame's readings `R` of `I`'s body the parameter's read has flags `(false, false)` and reads `.other`, and so does `S(n)`.
- PROVED from these (lead13): `ParRead.varAbs_core` (the read of `n ↦ σ`), `ParSucc.succA_core` (`S(u)` over a numeral holding unknowns), `ParBody.body_simI` (`eval_sim` for `I`'s body `S(n)` at every fuel from every state whose variable 0 holds an unknown of type `Nat`), assuming `EvalInv`, `SuccInv`, `InvSteps` (proved), `EvalLow` (open, `FragOpen`), `VarNumAInv`, `InvNumA`, `ParDecI`.
- FOR THE MODEL LANE: (`FrameDrop0`, assumed for these two columns, is DELETED: docs/31 D126 ruled the mirror of the checker's frames, built as stage 1 by model5, `SState.under`.) D126 stage 2's cells are BUILT (model5: frame-0 bindings `x° ↦ loan l`, `FrameRel` restated); left, D123's stage 2: a closure value's capture of the function being checked read at the context's type (`capsTys`, `codeMeaning.clo`); its regression is `Regress/SelfCapture.R7`.

## THE FRAGMENT (lead11, lead12, 2026-11-21, `spine-lead12`): the machine lane's queue

`Steps/FragSim.frag_sim` (standard axioms): `eval_sim` for EVERY term of the fragment (`Z`, `S`, reads/writes of number variables, `&x`, `*y := u`, `let`, `;`; at `Nat`, `Unit`, `&Nat`), every fuel, `Δ` and assignment, by induction on the typing `FTy`. EVERY CASE PROVED (lead12: `FragCases` is gone): `Z`, `S`, the read (number, lent, moved; `fvar_core`), `let` at every type (`FragLet.letF_core`), `;` after a number or `()` (`FragSeq.seqI_core`) and after a borrow (`FragSeqB.seqB_core`), `&x` (`FragBorrow.borF_core`), `x := u` (`FragAsg.asgF_core`), `*y := u` (`FragAsg.asgDF_core`). It assumes exactly the fields of `FragFacts` (29), listed here. THE RUN THEOREM (`Steps/FragTop`, lead12, standard axioms): `frag_run` (every closed fragment term `t : A`, every successful typed run from the constant-body start state: the strict run succeeds with a member of its type at the checker's type; every hypothesis of `frag_sim` but `FragFacts` discharged at the start state) and `frag_run_ff` (at the fuel-free table, assuming exactly `FragOpen`, the 18 facts below; `FragOpen.facts` fills in the 11 proved ones). `B`'s and `C`'s bodies are fragment terms (`fty_bodyB`, `fty_bodyC`; `bodyB_frag_run_ff`).

PROVED by the machine lane (discharge at instantiation, 11): `EvalInv`, `ZeroInv`, `SuccInv`, `VarNumInv`, `InvSteps`, `LetInv`, `DropNoopInv`, `SeqInv`, `BorrowNumInv`, `PlaceLocal` (fuel-free table); `noInv` (the table: D112's invalidation empty, `fun _ _ => rfl` at the fuel-free table, as `column_B_ff`).

TO REVIEW AND PROVE (18; each sanity-run in `Steps/FragGuards.lean` unless said "not run"):
- `FragRun D` (`Frag.lean`): a typed run of a fragment term of type `A` from `FSt Γ`, at ANY hint, entered as `eval` is: its type is `A`, its value `A.val` (a number, `()`, a borrow of a number), `ModeEq` across it, readings and frame count kept, and `FStT Γ` of the end state with the value in flight. By induction over the fragment from the inversion facts; the last fact of the fragment to prove.
- `FragDec D` (the decisions' lane): at a fragment state a fragment term of type `A` is classified neither statement nor proof and read `A.rd`. NOT yet checked against the fuel-free table.
- `EvalLow`: `eval` below fuel 3 fails.
- Reads: `VarLentInv` (a read of a LENT number variable, `FEnd`: quiet [Repack], the end `endE`, copy/move by the aligned decision; generalises `VarEndInv`), `VarBotInv` (a read of a moved number variable fails).
- `let`'s drop: `DropBorrowInv` (a binding holding `borrow_l c`: quiet, `endE` at that binding, pop; other borrows kept), `DropLentFail` (the drop of a binding lent to the value in flight fails: `let x = Z; &x` is rejected).
- `&x`: `BorrowLentInv` (`x` LENT: quiet, the end, then the lend), `BorrowBotInv` (`x` moved: fails).
- `;` after a borrow: `SeqBorInv` (the discard: quiet with the value parked, `x` gets its content back; lead12 RESTATED its invariant clause as `KeepsInv (st₁.withTempT v₀ T₀) (st₂.withTempT v₀ T₀)`: first stated on the states without the parked value, where `x` holds a loan whose borrow is nowhere, which `Inv` need not admit, so it was unusable).
- `x := u`: `AssignVarInv` (at a root: a number or `⊥` overwritten; lent: end, then overwrite). `*y := u`: `AssignDerefInvF` (`AssignDerefInv` plus: `y` holding `⊥` at `u`'s end makes the write fail, e.g. `*y := x` with `y = &x`).
- State-level (`Inv` is not computable; not run): `InvEnd` (`Inv` across `endE`, lender a number binding read `.other`; used with the holder a binding AND, since lead12, a temporary: `;` after a borrow), `InvBindUnit`, `InvPopUnit` (the unit twins of `InvBindNum`, `InvPopBind`), `InvLendG` (lead12: `InvLend` with other loans live, at a fragment environment), `InvPopBot` (lead12: `⊥` in flight popped), `InvSetBotNum` (lead12: a moved binding at `Nat` read `.other` overwritten by a number).
`FSt` gained (lead11) `order` (a lender's binding precedes its holder's), `lent` (a lent binding is a number variable read `.other`), `frame` (a top frame exists).

For the model lane (from lead10): `Run.lean`'s `.succ` still hands `.plain nat` to its argument where the typed checker hands none (harmless for the fragment: `Frag.frag_hint`).
D120's hint conjunct on `AssignNumInv`/`AssignDerefInv` is GONE (docs/31 D121): the steps take `hhint`, which `Frag.frag_hint` discharges for every fragment term.

## FOR THE MACHINE LANE (`machine2`): the facts to review and prove, as of lead9 (2026-11-21; docs/31 D116)

All in `Steps/FormMachine.lean`; sanity runs in `Steps/ColumnC.lean` (first column) and `Steps/ColumnB.lean` (borrow column, `#guard`s, including the three refutations). `InvCore` and `ColTerm` are GONE (the lead's ruling).

- **Proved by you, now used in your forms**: `EvalInv` (= `EvalInvR`), `ZeroInv`, `SuccInv` (= `SuccInvR`, word for word), `LetInv` (= `LetInvR`, word for word), `VarNumInv`, `BorrowNumInv` (with `KeepsInv`, `spine-machine3` 60883538, merged), `DropNoopInv`, `DecTab.back`, `GrowsM`, `decide_fuel_agree'`. `FormMachine` restates your `ModeEq` (your files import the column's); `Steps/ColumnCFF` converts (`ModeEq.ofMachine`, `succInv`, `letInv`). If you move `ModeEq` out of `Machine/EvalInv.lean` and use `Form.ModeEq`, the conversion goes.
- **Inversion facts still open**: `AssignNumInv`, `AssignDerefInv` (your review's fix applied: the `Kern` clause also asks `y`'s old content not a borrow), `SeqInv` (your fix: `ModeEq st₁ stW`, no invariant clause), `VarEndInv` (judged true by you; now with `KeepsInv` beside `Quiet`). Also this round: `AssignNumInv`/`AssignDerefInv` conclude `ModeEq st₁ st'` (u's end to the write's end); lead8's `LetInv` conjunct (readings kept) is gone from the fact (the caller's run facts give it).
- **`KeepsInv a b := ∀ D Γ, Inv D Γ a.norm → Inv D Γ b.norm`, and `InvExpectTy`** (a type check keeps `Inv`): `Inv` across `Quiet` is NOT a state-level fact (`Quiet` leaves `nextAbs` and the new unknowns' types free; (WF6), (WF8), (WF11) read them), so it is the private computation's: a comparison or a [Repack] makes only unknowns with clean types, and keeps `absTy.size = nextAbs`. If you would rather strengthen `Quiet` (two fields: `nextAbs` kept in step; the new unknowns' types loan-free, not misplaced, naming only unknowns below the size) and get `Inv` across it as a state-level lemma, say so; that is the uniform form.
- **The state-level lemmas** (`InvSteps`, read no run; each "`Inv` before, the exact change, `Inv` after"; machine3 found six FALSE as first stated, all from `Inv`'s (V) read at a FREE table `D`: now `InvBindNum`, `InvBindBorrow`, `InvPopBind`, `InvSetNum`, `InvWriteDeref`, `InvEndRead` take `PlaceLocal D` (machine3's text, word for word; `placeLocal_ff` for the fuel-free table) and the written binding's reading; `InvExpectTy` is restricted to a type checked against itself): `InvPushInert`, `InvPopInert` (a number or `()` temporary pushed/popped), `InvSetBot`, `InvSetNum` (a number binding set to `⊥` / to a number), `InvBindNum`, `InvBindBorrow` (the value in flight moved into a pushed binding: a number at `Nat` read `.other`; `borrow_l w`, `w` a number, at `&Nat` read `.ref .other`), `InvPopBind` (the top binding, `⊥` or a number, popped), `InvLend` (a number binding at `Nat` lent at the counter, the borrow in flight, no loan live), `InvWriteDeref` (`y ↦ borrow_l w` to `borrow_l v₀`, numbers), `InvEndRead` (B's read: `y ↦ ⊥`, `x ↦ w` or `⊥`). The pushed bindings' readings are pinned (`.other`, `.ref .other`) because (V) asks a value at a reading `.ind n _` fit `n`.
- Checklist each was read against: the term in tail position; a reading handed down; a lazily typed binding; the place lent; a private copy (`Mode`); an untyped run; the type of the place written; an undecided reading (`.any`); when a decision is read; a sub-run's type an `Option`; `ModeEq` across a stretch, never `Mode` later; the OLD content a write overwrites (a borrow there is ended by the drop); a fact with a FREE decision table is constrained only where the table is aligned: say what it needs of `D` off those points.

## The borrow column (lead8; docs/31 D115, D116)

Proved (standard axioms): the five steps and the ASSEMBLY `ColumnB.column_B_ff` (`Steps/ColumnBFF.lean`, lead9): every run of the checker's `eval` on `B`'s body from the constant-body start state makes the strict run succeed with `0`, a member of `Nat`, at `Nat`. It assumes three unproved facts about the checker's runs, `AssignDerefInv`, `SeqInv`, `VarEndInv` (the last judged true by machine2), the state-level `InvSteps`, and `PlaceLocal` of the fuel-free table (`placeLocal_ff`, machine3). Files: `ColumnBStart` (decisions at `B`'s three scopes, kernel-evaluated), `ColumnBRuns` (states by exact environment; the checker's runs of each sub-term), `ColumnBSim` (`sim_bodyB`, `column_B`), `ColumnBFF`.
- FOUND at the assembly, for the machine lane: `DropNoopInv` concludes only `Kern`, so the mode after any `let` is unknown (`LetInv`'s `ModeEq st₃ st'` needs `Mode st₃`); `B` never needs it (nothing follows a `let` but its frame's end), a `let` followed by anything in a sequence would. Add `ModeEq st st'` (or `Mode`) to `DropNoopInv`.

## Facts about the checker the columns assume

`column_C_ff` (`Steps/ColumnCFF`) assumes `InvSteps` and `PlaceLocal` of the fuel-free table, nothing else (both with machine3).
- The decision table does not align `Decisions.invalidated` (D112) with `openWrite`: `assign_core` assumes it empty at the place written; to be added to `DecTab` (decisions).
- Owed lemmas the column takes as hypotheses: the reading a `let` hands its tail is the tail's own (`htail`; for `C` a kernel-evaluated decision fact, `ColumnStart.declOf_body_x`). (`hwhint`/`hwcong` are gone, lead10: the reference runs a typed `let`'s tail at no hint, D119, and a tail with no unknowns runs alike at every extension, `ColumnLet.wcong` from `runT_congrA`.)

## The column of (II) in the form of `Steps/Form.lean` (lead7, spine-lead7 594ad7b5)

Proved on the standard axioms, no sorry, over named facts about the checker alone (`Steps/FormMachine.lean`: `EvalInv`, `ZeroInv`, `SuccInv`, `VarNumInv`, `LetInv`, `DropNoopInv`, `AssignNumInv`, `InvCore`; and `DecTab.back`, `GrowsM`, `DecideFuelAgree` where the assembly needs them): composition `sim_seqS`; `zero_core`, `succ_core` (argument a number), `var_core` (a variable bound at `Nat` to a number, copy or move), `let_core` (typed, a number bound, the binding ending nothing), `assign_core` (a number written at `x.0`), `eval_of_core`; the assembly `Steps/ColumnC.column_C` (`def C : Nat := let x = S(Z); x`: for every run of the checker on the body from `checkDef`'s state, the strict run succeeds with `1`, a member of `Nat`), every hypothesis instantiated (`Steps/ColumnStart`), the checker's side `#guard`ed. Restrictions the general steps must lift (each a hypothesis now): a right-hand side's value a number (the general steps need the value in flight to hold no live loan, the general read needs `RepackSound`); `Decisions.invalidated` empty at the place written.

## The five most likely false (not yet kernel-checked)

1. ~~The decisions instance cannot meet `DecTab`~~ FALSE (K) (`Regress/OpenFalse.decTab_fixedFuel_false`) and FIXED (D84: `DecisionsFF.chainDecisions`, `decTab_ff` proved from the machine-only `decide_fuel_agree`). As first found: `DecTab` asks agreement with the checker at EVERY fuel; `DecisionsInst.checkerDecisions st fuel` answers each decision at ONE fuel and returns a default (`readDecision`) where that fuel runs out, so on a term deeper than the fuel it answers `.other` where a larger fuel answers the real reading. Mechanism verified ✓ (`Decide.declOf` recurses at one fuel less; `checkerDecisions₀` reads at `fuel`). Fix: a fuel-free instance (the answer at any fuel where the decision succeeds; decisions are fuel-monotone by the checker's no-catch-and-default rule), or `DecTab` restricted to fuels up to the instance's.
2. FALSE (K) for `eval_step` at ANY typed hole (`Regress/OpenFalse.eval_hole_false`: the reference has no clause for `?`); decided: the evaluation statements take "no hole in the term" (D84). As first found, at a hole of an empty data type: `evalCore`'s `?` returns a fresh unknown of the expected type (verified ✓, `Machine.lean` `.prim "hole"`), which no typed assignment can give a value. `consistency_rel` never uses its `NoHoles` hypothesis (build warning), and `Ochr/Consistency.holeFalse` is an accepted proof of `False` by a hole. Fix: `NoHoles` of the term as a hypothesis of the evaluation statements.
3. **`assignPlace_step`**: concludes `Good` after writing `v` at a typed place, with nothing saying `v` is a member of the place's type (the check is in `eval`, not `Machine.assignPlace`; root T).
4. **`runBody_front`**: concludes `Good` of the callee's frame, whose parameters are bound to the arguments unchecked (`runBodyCore`'s `pushBind h A (etaUnit pd w)`); nothing gives the arguments' membership (roots T, U).
5. **`closeCall_post`, `callFn_tail_closed`, `callFn_tail_ran`**: variables the conclusion reads (`fres`, `as`; `res`, `B`) are unconstrained by the hypotheses (the defect class of `Regress/CloseCallStmt`).

Kernel-checked FALSE so far: `owners_sound`, `proof_step` (`Regress/Suspects`, 2026-11-21: a reborrow's holder; an inlined captured proof), `bodyReturns_sound`, `repackCheck_sound` (`Regress/EvalMemGap`; restated as `EvalMem.RepackSound`, the return path `EvalMem.return_member`), `grows_restoreKeep`, `typedFutureF_exists` (restated and proved, D84), `eval_step` at a typed hole, the fixed-fuel decision table (`Regress/OpenFalse`), `grain_deref_not_proof` (`Regress/GrainDerefProof`, restated on `spine-slice-grainref`), `mkEqM_step`, `conv_sound`, `convPi_sound` (trial: `Rules/Counter*`, `Rules/EmptyDomain`).

## Machine-only statements (a separate lane)

`DecTab.back`; the 37 `grows_*` (all of `Steps/MachineMono.lean`; `grows_restoreKeep` FALSE as stated, needs "the snapshot has the current globals and declarations"); `access_absTy`; `eq_split`; `accepted_resolves`, `resolves_of_accepted`, `resolvesTo_unique`, `covered_prefix` (only `dm.covers`); `scopeOf_sstate` (reads only the readings); `consistencyBounded` (the theorem itself is machine-only in statement). Machine-only conclusions under a droppable hypothesis (`M*`): `borrow_wf`, `end_wf`, `assign_wf`, `close_wf`, `capture_wf`, `eval_wf6`. Nearly: `callee_bounded`, `piSort_aligned` (restatable without meanings). The hard ones are one induction over the interpreter's mutual block (`eval`, `endBorrow`→`substEnv`→`nfSealed`→`eval`) for the `grows_*` interpreter group and `access_absTy`.

## Part (b), membership, under the plan of record (docs/31 D86)

**Status at `spine` f8ebe797 (2026-11-21):** the strict run is built and is `Run.lean`'s `runT` (D94); (I) is `Strict.fund_all` (D95), proved clause by clause but resting on three `sorry`s in `Strict/OpsPlace.lean` and, on `spine`, on the hypothesis `MemReads` that has no instance (D98, D99), and FALSE as stated at a write to a field path (D104, kernel-checked on `spine-model-dep`; repair decided, not built). The type formers are strict (D97). The tables below are the design; their "to build" rows for the strict clauses are built (D94), the erased terms run as `⋆` at `prop True` (D94, not D83's per-primitive propositions). The statement migration is listed in `Steps/LEAD-HANDOFF.md`.

The proof's two halves meet at "the strict reference run succeeds" (D83 specifies the strict run). **(I)** is a lemma about the model alone: a successful strict run from a state of members returns a member and leaves such a state; for an erased term, success means its proposition is true. **(II)** is the simulation: the checker's typed run succeeds, so the strict run does; each check of the checker makes its strict clause succeed. Values in flight are members through typed temporaries (D81; the checker change is `checker2`'s). The evaluation statements take "no hole in the term" (D84; `Regress/OpenFalse.eval_hole_false`).

Who: **M1** = `model1` (branch `spine-model`, the strict run and the fundamental lemma); **DL** = the data layer (proved facts, or the existence agent on `spine-exists`); **TR** = the rules trial's conversion lemma (`origin/rules-trial`, `Rules/ComposeT.conv_sound_T`: comparison sound on values well typed inside, under named premises); **SP** = a prover on typed steps; **ML** = the machine-only lane; **OPEN** = no design yet.

### (I) The fundamental lemma's cases (one per clause of the strict run)

| Clause (`Run.lean`) | Its result is a member because | Fact | Who | Status |
|---|---|---|---|---|
| `.place` (read), `.prim "clone"/"peek"/"inplace"` | the state's positions are members; a part read at its path is a member of the type read there | `ReadMember.field_mem`, `follow_below_member` | DL | PROVED |
| `.borrow` | the borrowed content is a member (as above); `⟦&T⟧ = ⟦T⟧` | as above | M1 | routine |
| `.assign` / `assignAt` | strict: the written value checked at the place's type; the result `()` | strictness | M1 | to build |
| `.letIn`, `.seq`, matches | the tail's / arm's result; the binding a member by the producer's case | induction | M1 | routine |
| `.ctor` / `ctorOut` | strict: fields fit the record's field types | `CtorMem.ctorOut_mem`, `proof_mem_tyR` | DL | PROVED (given strictness) |
| `.call` / `callOf` | decoding at the parameter codes; the callee a member of its function type | `ApplyMem.app_mem'`, `app_mem_ref`, `app_mem_finals`, `callOfL_mem`, `app_mem_unit` (η at `Unit`) | DL | PROVED |
| `.const n`, `.val (.gfn …)`, `.val (.abs σ)` | the global's / unknown's meaning is a member | `CtxOk.globals` (`MemBelow` for the definition being checked), `TypedAssignment` | — | by hypothesis |
| `.ascribe` | strict at the annotation | strictness | M1 | to build |
| `.succ`, `.val (C(…))` | strict | strictness | M1 | to build |
| `.zero`, `.tt`, `.nat`, `.unit`, `.sort l` | by construction (`sort l : sort (sortSucc l)` is the universe code's decoding) | small lemmas | M1 | to prove |
| `.eq`, `.id` | a proposition is a member of `Prop` | `EvalMem.prop_mem_univ0` | — | PROVED |
| `.tind`, `.pi`, `.ref` (type formers) | the code's level is the sort the run gives it; with strict type formers, "well typed inside" | `fix_sortRule`, `sortOf_sound_stmt`; strict type formers (trial's measure) | M1 / DL | OPEN |
| `.fix` (a closure) | totality of the closure: the local knot | D73 item 5 | OPEN | not designed |
| erased terms (C1) | the erased run succeeded at its proposition: a proof call's codomain, a `Prop` constructor, `cong`, `symm`, `trans`, `rewrite`, `J` | strictness + the cases above | M1 | to build |
| `.prim "J"` (data) | the transported term at `P(a)`, its proof true so `P(a) = P(b)` | (C1) on the proof | M1 | to build |
| `.prim "hole"` | — | excluded by hypothesis | — | — |

### (II) The checks that make the strict clauses succeed (in typed runs)

| Check (`Machine.lean`) | Strict clause it serves | Lemma | Who | Status |
|---|---|---|---|---|
| `expectTy` of an ascribed term against its annotation | `.ascribe` | conversion sound on types well typed inside | TR | proved under named premises (trial) |
| `expectTy` of an assignment's value against the place's type | `assignAt` | the same | TR | as above |
| `expectTy` of each field against its type (`evalCtor`), parameters solved from fields (`unifyParams`) | `ctorOut` | conversion; unification sound | TR / SP | unification: OPEN |
| a call's argument types against the parameter types (`callType`) | `callOf`'s decoding | conversion | TR | as above |
| [Def]'s and [Const]'s conversion of the body's type to the goal, then [Return] | the result at the goal | `EvalMem.return_member` (PROVED from its pieces): conversion + `RepackSound` ([Return]/[Repack]'s honest content, a guess, restating the FALSE `bodyReturns_sound`, `repackCheck_sound`) | TR / SP | `RepackSound` open |
| the arms of a non-tail match against one type; a stuck block's arms at its declared type | the match's result type | conversion | TR | as above |
| `Eq`'s sides against its type (`eqChecks`) | `.eq` (with strict meanings) | conversion | TR | as above |
| `cong`, `symm`, `trans`, `rewrite`, `J`: the shapes of their premises | (C1)'s proposition | conversion (`trans`), `rewriteGoal_step` | TR / SP | open |
| the checker's sort of a type (`sortOf`) | the type formers' levels | `sortOf_sound_stmt`, `fix_sortRule` | SP / DL | OPEN |
| [Rec]'s decreasing argument | a recursive call below the bound (`MemBelow`) | `recDecreases` | SP | open |
| the access before a write at a field path (sites complete on related states) | `setContent`'s and `dropAt`'s definedness at EVERY typed future (every write at a field path: a read's move, an assignment, the join's drop, D112's invalidation) | "after the access of a write at `x.p`, `x` reads no live label along `p`" (then definedness does not depend on the future, and the checker's own update gives it at one); regress `Strict/FieldWriteCE` | SIM | OPEN in general; DONE for a number written at the field `0` of a variable bound at `Nat` (`Steps/ColumnWrite.assign_core`, lead7 594ad7b5: at a good reference state every typed future is one the relation compares at, `typedFut_rel`, so `x` means its number there) |
| [Repack] at a read whole / a borrow whole (`repackAt … "read whole"`, `"borrowed whole"`) | `readPlace`'s `ReadGood`; `.borrow`'s membership | the value read or borrowed is a CLOSED member of the type the read gives it | SIM | OPEN |
| the checker's tests where lent parts are unknowns (`lentProofAssign`, `lentLeafCheck`), D112's invalidation (`openWrite`) | `lentOk` (`StateOk`: every position an open member at every typed future) after a write or a borrow at a field path, and `Decisions.invalidated` | every state the checker reaches has open members at its positions; `Decisions.invalidated` aligned with `openWrite` | SIM | OPEN in general; for the column's write `StateOk` after it follows from the reference state before being good (`Steps/ColumnWrite.stateOk_setNum`); `invalidated` is not aligned by `DecTab` (the fuel-free table's is the default `[]`): `assign_core` takes it as a hypothesis |
| [End]'s whole check (main's D98: no borrow ends over moved-out content) and [Repack] | the strict end at every end site (`EndOk` via `ContentOk`, `TagOk`, `AssignOk`, `InvalidateOk`, `DiscardOk`, `LetLendersOk`, `MatchEntryOk`, `JoinDropOk`, `CapOk`, `EndsOk`; docs/31 D106) | the holder of every borrow the checker ends holds a member of the borrow's type at every whole typed future; plus `heldTy l = holderTy s l` for live `l`: PROVED from `SGood` (`Steps/ColumnWrite.heldTy_eq_holderTy`, lead7 594ad7b5; it need not be a clause of `Rel` wherever the reference state is good, which in the form of `Steps/Form.lean` every step assumes; `Steps/DropOneAsm`, `MovedPlace`, `EqJAsm` can take `SGood` and use it) | SIM | OPEN (the holder's membership); the record-type fact PROVED |
| `depFieldType`'s typing of a dependent field by its content (D112 [Open]: "declared if the content fits, else its own type") | the read type `DataModel.readTy Γ` (a tree of another declaration than the shape's, by its own declaration found by name, `ownTy`), so the open membership `StateOk` asks | every tree a related state holds in a tree-shaped dependent field is of a declaration of the program (`Γ` has it by name); a static TREE field whose declared type computes to a LEAF at the current index holding a stale tree is read at the leaf by the model and by its content by the checker (needs `Decide.fieldIsLeaf` in the model, or the fact that the case is unreachable). The red team (2026-11-21, main 6b2ed5d1) could not reach it four ways (the leaf arm through a constant alias, another type function, a `let`, a recursive type function): `fieldIsLeaf` classified the field a LEAF each time, so it was invalidated at the index move and its write checked at the leaf; what remains is the static classification in the model, or a proof that a tree-classified field is a data type at every index | SIM | OPEN |

The membership of a typed temporary at the type the checker returned then follows from (I) and (II) by the simulation (`StrAgree`: the checker's type means the reference's); the projection to the value in flight is `EvalMem.goodT_push_mem` (PROVED). Statement requests queued for the statements' next change: typed temporaries (after `checker2`'s change is on `main`); "no hole in the term" on the evaluation statements and a state clause "no code holds a hole"; the join guarantee as a clause (no temporary holds a label that is not live: after a join's drop, a `let`'s drop, a frame's pop); (WF11)'s sixth conjunct (refinement records hold no loan) and `ShapeFacts.refsHint`, `neutralHint` (the slice's request, swept on `spine-slice` 6e7ba003); `EqJAsm` to use `restoreKeep_grows` and `grows_closeBlock_of` (`spine-machine`); [Entry]'s captures out of `CtxOk` into the [Entry] step's hypothesis.

## A. The top-level chain (`Consistency.lean`, `Bounded.lean`, `Steps/Knot.lean`)

| Statement | Says | Checked | Size | Status | M |
|---|---|---|---|---|---|
| `const_split` (Consistency) | the constant branch of `checkDef` taken apart: start good, related, aligned; body run; [Return]; stored at the goal | none | several pages | suspect: omits the conversion `conv T goal` the checker runs before [Return] (D81); concludes `CtxOk`/`DecTab` at any `D` (item 1 above) | |
| `typedFutureF_exists` (Consistency) | a typed future exists where each label's constraints have a common member | first form refuted (`Regress/OpenFalse`) | — | PROVED as restated (D84) | |
| `labelsInhabited_of_rel` (Consistency) | at a related state each label's constraints are inhabited by the reference's record | none | a page | likely true where the flight types a label at its holder's type; to restate with typed temporaries | |
| `chainDecisions_blockCaps` (DecisionsFF) | the static [Entry] captures equal the checker's wherever it computes them | 335 of 338 suite block entries equal, the rest the checker's rejections (orchestrator's measure) | — | suspect as `DecAligned` states it (every fuel against one); leaves `CtxOk` with the queued change | |
| `decide_fuel_agree` (DecisionsFF) | successful runs of a decision at different fuels agree | none | core (an induction over `Decide.lean`) | likely true (the decision procedures catch nothing) | M |
| `fix_sortRule` (Consistency) | the sort rule for a function type's parts (stronger than the stored-type form of sort soundness) | none | several pages | uncertain | |
| `fix_canon` (Consistency) | the run's type values are canonical codes | none | core (an induction over the run) | uncertain | |
| `const_value` (Consistency) | the reference's run of a constant's body, matched to the checker's value and its membership, is the constant's meaning, a member | none | several pages | uncertain: membership is given at a typed future, `defMeaning` runs at `noFuture`, so the value must be loan-free at the end | |
| `fix_split` (Consistency, datamodel version) | a function's meaning is the closure of its stage fixpoint, its type fits (`PiFits`), and stage b good below b gives stage b+1 good below b+1 | `Regress/DefKnot` (`Double` through the induction, model side) | core (the body's whole check through the step statements) | uncertain; its step's proof needs the return path (D81's `return_member`, not `bodyReturns_sound`); `PiFits` needs the function-type case of sort soundness | |
| `accepted_resolves` | an accepted program resolves to items, each accepted from the Σ of the earlier ones | none | a page | likely true | M |
| `covered_prefix` | a model covering the program covers each prefix | none | a page | likely true | M (only `covers`) |
| `falseConst_ty` | a `False` constant has an entry in the program's meanings typed `prop False` | none | a page | suspect: no acceptance hypothesis (`means` records accepted items only); no coverage of `False` | |
| `exists_dataModel` | a data model covering and faithful to every prefix exists | docs/34; `DataModel/Counterexamples` | core (the construction) | uncertain: rests on an unproved checker property (its docstring) | |
| `resolves_of_accepted` | an accepted program resolves | none | a page | likely true | M |
| `resolvesTo_unique` | resolution is a function | none | few lines | likely true | M |
| `consistencyBounded` (Bounded) | no accepted, hole-free, level-bounded program has a closed definition of `False` | `#guard`s in `Ochr/Consistency.lean` | the whole proof; a few lines from `consistencyBounded_assembled` once the import is inverted | the theorem | M |
| `stepsIH_zero` (Knot) | every step statement at fuel 0 | none | a page, plus outright proofs of the fuel-free fields | suspect: `split_coverage` at fuel 0 (and 1) needs a successful `ctorRefinement`, which is out of fuel there | |

Proved assemblies resting on the above: `step_member_const` (on `const_split`, `typedFutureF_exists`, `bodyReturns_sound` FALSE), `step_member_fix` (on `fix_split`), `defn_member`, `consistency_rel`, `consistencyBounded_assembled`; `Knot.stepsIH` (on `stepsIH_zero` and every field). `consistency_rel` does not use `NoHoles` (five-most-likely item 2).

## B. Machine facts (`Steps/MachineMono.lean`, `Steps/WF.lean`, `Steps/Decisions.lean`)

| Statement | Says | Checked | Size | Status | M |
|---|---|---|---|---|---|
| `DecTab.back` | decisions aligned at a later state of a run are aligned at an earlier one | none (table growth swept, D58) | several pages (a one-way `decideSim`, plus `jdMoves`, `typeState`) | likely true | M |
| `grows_*`, simple (content, content?, ppPlace, absType, lookupInd, recordedNeutral, setPlace, logEffect, demand, getFlags, setFlags, wholeReturned, pushTempAt, topIdx, popTemp) | the function only extends the tables (globals, declarations, frozen readings, counters) | D58 (never shrinks, swept) | few lines each | likely true | M |
| `grows_restoreKeep` | restoring a snapshot only extends the tables, from any state | `Regress/OpenFalse` | few lines once restated | FALSE (K): needs the snapshot's globals and declarations to be the current ones (true at every use); `eq_step_asm` uses it | M |
| `grows_lendEnv` | lending keeps the tables | none | a page | likely true | M |
| `grows_*`, interpreter (eval, evalType, expectTy, mkEqM, observe, blockEntry, closeBlock, joinDrop, endBorrow, accessPath, accessInside, movedPlace, etaInPlace, placeTypeQ, substEnv, generalizeNeutral, renormAll, refine, dropAtJoin, popFrame) | the same | D58 (`absTy` only; `absDecl` not swept) | core: one induction over the interpreter's mutual block | likely true (nothing writes globals or declarations; only `freshAbs` pushes a reading) | M |
| `borrow_wf` | after [Borrow], (WF1)–(WF3) hold | clauses swept, not the step | several pages | suspect: the borrow is in flight, not in Ω, so (WF2) fails right after `&x` (`Regress/InFlight`); needs `st'.withTemp v` | M* |
| `end_wf` | after [End], (WF1)–(WF3) hold | clauses swept | core (re-runs) | uncertain, leaning true | M* |
| `assign_wf` | after [Assign], (WF1)–(WF3) hold | clauses swept | several pages | likely true; vacuous when the value is a borrow (T) | M* |
| `close_wf` | after [Close], (WF1)–(WF4) hold | clauses swept | a page | likely true; vacuous at borrow arguments (T) | M* |
| `capture_wf` | a closure captures no borrow or `⊥` | (WF4) swept | core | likely true | M* |
| `eval_wf6` | evaluation keeps (WF6) and the counters | swept, D58 | core | likely true | M* |
| `eval_wf78` | evaluation keeps (WF7), (WF8) | (WF8) swept; (WF7) not | core | uncertain: (WF7) needs sort soundness | |
| `scopeOf_sstate` (Decisions) | the model's scope of the checker's state is its top frame's readings | none | few lines | likely true | M |

## C. Places, borrows, the drop at the join (`Steps/Borrow.lean`, `Records`, `DropOneAsm`, `MovedPlace`, `JoinNoop`)

| Statement | Says | Checked | Size | Status | M |
|---|---|---|---|---|---|
| `endBorrow_step` | [End] of a live borrow is the reference's end of the renamed label; extended context, `Good`, `CtxOk` after | sites and holders after [End] on concrete states (`Regress/StaticLend`) | several pages | likely true; † at every end of a borrow held in a temporary (`dropValue`, `endBorrowArgs`, inside `assignPlace`) | |
| `access_step` | [Access] (path, then inside) is the reference's static access | table growth swept (D58) | several pages | likely true; † | |
| `readPlace_step` | [Read] is the reference's `readPlace` at the same copy decision; value in flight | old form refuted (`Steps/BorrowCE`) | several pages | suspect: `flightOf r.2` types the REFERENCE's label, not the checker's; after a statement that borrows, the counters differ (`Regress/CopyLabels`) and the moved borrow's label is untyped; † | |
| `borrowPlace_step` | [Borrow] is the reference's `borrowPlace`; borrow in flight | none | a page to several | suspect: `Machine.borrowPlace` has no [Repack] (it is in `eval`), so an open value borrowed whole records a non-member (`Rel.records`); the same label mismatch as `readPlace_step` | |
| `assignPlace_step` | assigning a value in flight is the reference's `assignAt`; `Good` after | none | several pages | suspect (five, item 3): no membership of the value at the place's type (T) | |
| `dropTopBind_step` | the drop of a `let`'s binding is the reference's `letEnd` | none | a page to several | likely true; † (the `let`'s result is a temporary during the drop) | |
| `popFrame_step` | the pop of a frame is the reference's `popCallFrame` | old form refuted (`htemps` added) | a page | likely true; † when the call returns a borrow | |
| `borrowPlace_record_mem` (Records) | the content a borrow records is a member of the type it is held at | none | a page | suspect: as `borrowPlace_step` (no [Repack] in `Machine.borrowPlace`) | |
| `meanV_ext` (DropOneAsm) | a value naming unknowns below n means the same under an extension agreeing below n | — | few lines (`meanV_congrA`, proved) | likely true | |
| `ctx_botWrite` (DropOneAsm) | `CtxOk` survives the drop's write of `⊥` | none (block-captures part to be measured, `Slice/HANDOFF`) | a page | suspect: no hypothesis that the overwritten part holds no live borrow (the use site has it, `botWrite_hyps`) | |
| `access_absTy` (MovedPlace) | an access never shrinks the table of unknowns | swept: 358,141 accesses, 25,451 ends (D58) | core (interpreter) | likely true | M |
| `etaFresh_sim` (MovedPlace) | a fresh η record, its fields given from the unknown's value, keeps the relation and `Good` under an extension | none | several pages | uncertain, leaning true; † | |
| `recordedNeutral_ok` (MovedPlace) | a recorded generalisation's value means the program at every future and hint | none | a page | suspect: `Good` gives the record at the unknown's own type's hint only; no clause makes a record's program hint-free | |
| `etaPlace_sim` (MovedPlace) | `etaPlace` leaves the reference untouched; `Good` under an extension | none | core as stated (no induction hypothesis argument) | suspect as a form: lacks the `ih` that `etaInPlace_sim` has; † | |
| `grain_deref_not_proof` (JoinNoop) | no place at the join's grain dereferences below a proof | `Regress/GrainDerefProof.stmt_false` | — | FALSE (K); proved at a restated grain on `spine-slice-grainref` (94c478f9), not yet merged | |

## D. Substitution, refinement, worlds (`Steps/Subst.lean`, `SubstAbs.lean`, `Steps/SplitAsm.lean`)

| Statement | Says | Checked | Size | Status | M |
|---|---|---|---|---|---|
| `substV_loan_step` | substituting a loan's final content in a value means reading it at the future fixed there; tables grow | none (core-unchanged form false, D80) | several pages | uncertain: the value is arbitrary, and its sealed programs' re-runs need live holes and a succeeding reference run, which nothing supplies (D64's untyped `Nil`); † | |
| `substV_abs_step` | substituting a refinement `σ := r` keeps a value's meaning | none (core-unchanged form false, D76) | several pages (on `run_substAbs`) | uncertain: `RefineOk` asks neither that `r` be a constructor value nor `DecInvariantAbs` | |
| `substEnv_loan_step` | the same over Ω: shape kept, meanings at the fixed future | none | a page on `substV_loan` | uncertain; † (sealed programs in temporaries) | |
| `substEnv_neutral_step` | replacing a stuck program by a value that means it keeps the relation to the same reference state | none | core (a new value-for-value substitution induction, D77) | uncertain: no counterpart of `AbsFillOK.shape` or `DecInvariantAbs` | |
| `substEnv_abs_step` | a [Split] refinement over Ω, types and goal: same shape, same reference state, `Good` under an extension | concrete runs (`Regress/SplitSubst`, D76) | several pages | suspect by reading (the slice, 2026-11-21): `RefineOk` does not ask the refinement's own unknowns typed, false at a split whose fields nothing names yet; repaired by strengthening `RefineOk` with `CovConcl`'s `typed` clause (approved, queued, LEAD-HANDOFF M11); same for `refine_step`; † | |
| `nfSealed_step` | a re-run means the sealed program; Ω, goal, records kept | indirectly (`SplitSubst`'s `Pred2` re-run) | a page on `nestedRun_sim` | likely true; cannot be assembled from statements assuming `Good` through the untyped nested run (U) | |
| `canonNeutral_step` | a generalised program's canonical value means the same at every future and hint | old form refuted (`Regress/RefsPathCond`) | a page | suspect: as `recordedNeutral_ok` (hint independence of a record's program) | |
| `renormAll_step` | re-running every sealed program keeps the relation; `Good` under an extension | partly (`SplitSubst`) | several pages | uncertain; † | |
| `meanV_substAbs` (SubstAbs; PROVED by the data layer as `RunSubstAbs.meanV_substAbs`) | substituting `r` for `σ` keeps a value's meaning, under `AbsFillOK` | base case kernel-checked (`absFill_shape`, since cda36caf: D77's refutation is superseded) | core (generalise `RunSubst`) | likely true | |
| `run_substAbs` (SubstAbs; PROVED as `RunSubstAbs.run_substAbs`) | the same for a run | same | same induction | likely true | |
| `exitWorld_ctx` (SplitAsm) | the snapshot's `Good` and `CtxOk` carry to the restored state | an earlier form refuted (`Regress/ExitWorld_f32a7048`) | a page | suspect: `exitWorld` keeps the current `nextAbs`/`nextLoan`, which the statement does not relate to the snapshot's ((WF6)) | |

## E. Calls and the recursion argument (`Steps/Call.lean`, `CallAsm`, `FrameProp.lean`, `Steps/FixKnot.lean`)

All statements whose hypothesis is `Good (st.withTemps (fv :: ws))` are vacuous at a borrow argument (T, kernel-checked `borrowArg_not_good`): `callFn_step`, `runBody_step`, `closeCall_step` (assembled) and the leaves below marked †.

| Statement | Says | Checked | Size | Status | M |
|---|---|---|---|---|---|
| `callType_step` (Call) | the call's type means the codomain the callee's code reaches at the arguments; a private computation | none | several pages | uncertain: needs the checker's substitution of arguments into the codomain term to agree with the code's codomain | |
| `callOf_inPlace` (Call) | running the callee's body in place is applying its meaning (`callOf`) | concrete calls (`Regress/CallInPlace`, `CallInPlaceD99`, `FrameCheck`) | core | suspect: no hypothesis that the arguments are members (`callOf` decodes them, the run in place does not); a callee at sort 0 | |
| `callOf_inPlace_rel` (Call) | the same at a call related to the checker's | same | core | suspect: same; † | |
| `closeCall_means_data` (Call) | [Close]'s sealed result and fills mean `callOf`'s result and final contents | one instance (`Attack/CloseCall*`) | several pages | likely true | |
| `callee_bounded` (CallAsm) | a callee names only unknowns of the table | (WF6) swept | a page | likely true | nearly M |
| `runBody_front` (CallAsm) | `runBody` taken apart; the callee's frame good and related to `bodyFrame` | none | several pages | suspect (five, item 4): the parameters are bound to the arguments unchecked (T, U) | |
| `runBodyRef_extend` (CallAsm) | the run in place is the same under extensions of the assignment | none | a page | likely true (`runT_congrA`, proved) | |
| `runBody_back` (CallAsm) | the checker's pop after a body is `popCallFrame` | none | several pages | uncertain; † for a returned borrow | |
| `nested_start` (CallAsm) | a re-run's start is good, aligned, related to the empty state, not in tail position | none | a page | suspect: `nestedStart` keeps `tailNext`; a missing hypothesis | |
| `nested_uniform` (CallAsm) | one assignment serves every future for a loan-free re-run | none | several pages | uncertain | |
| `callFn_front` (CallAsm) | `callFn` taken apart: reservation, close-off or body run, tail | none | several pages | uncertain: "the run in place succeeds" rests on the arguments' membership (T) | |
| `callFn_tail_closed` (CallAsm) | the tail after a close-off is the call against `callOf`, typed | none | a page | suspect (five, item 5): `res`, `B` free | |
| `callFn_tail_ran` (CallAsm) | the tail after a body run, from `runBodyRef` to `callOf` | none | several pages | suspect (five, item 5): `res`, `B` free; no membership to pass from the run in place to `callOf` | |
| `closeFill_step` (CallAsm) | one fill fixes the label to its final content; related and good after | none | several pages | suspect: no membership of the fill at the lent place's type | |
| `closeCall_split` (CallAsm) | `closeCall` taken apart | none | a page | likely true | |
| `closeCall_post` (CallAsm) | after the fills, the result matches `callOf fres as` | none | several pages | suspect (five, item 5): `fres`, `as` in no hypothesis | |
| `run_frame` (FrameProp) | DELETED: false as D113 stated it (`Strict/FrameLocCE.run_frame_loc_false`); restated as the named proposition `Steps/FrameFrag.RunFrameS` (no `sorry`), proved on the label-free fragment (`run_frameS_lf`) | `Strict/FrameLocCE`, `Regress/FrameCheck` | core | FALSE (K) as stated; restated open | |
| `run_frame_obs` (FrameProp) | the same at an `Id` | none | several pages | uncertain | |
| `recDecreases` (FixKnot, datamodel version) | a strict subterm of an unknown's expanded entry means a part of its value | [Rec]'s verdicts (`Regress/DefKnot`) | a page to several | uncertain, leaning true for data-typed unknowns; as stated any unknown, and a proof unknown means `⋆`, of which nothing is a part | |

Proved on the datamodel branch (no longer open): `closure_mem_of_total` (restated), `memBelow_mem`, `memBelow_zero`, `memBelow_apply` (replaces the false `closure_apply`), `stages_below`, `knot_member`, `semRank_part`, `piFits_of_rules`.

## F. Equality and `J` (`Steps/Eq.lean`, `Steps/EqJAsm.lean`)

| Statement | Says | Checked | Size | Status | M |
|---|---|---|---|---|---|
| `mkEqM_step` (Eq) | `mkEqM`'s value means `⟦a⟧ = ⟦b⟧` at the type; private, good extension | trial `Rules/Counter.mkEqM_step_stmt_false` | core | FALSE (K): no hypothesis on the sides; +L | |
| `conv_sound` (Eq) | convertible members of one type mean the same | trial `Rules/Counter.conv_sound_stmt_false` | core | FALSE (K): needs both sides well typed inside (trial's `conv_sound_T`, proved under named premises); +L | |
| `convPi_sound` (Eq) | convertible Π-types mean the same type | trial `Rules/EmptyDomain` | several pages | FALSE (K): the leak (L) | |
| `convFn_sound` (Eq) | functions whose generic observations convert mean the same | trial `#guard conv F3 G3` | several pages | suspect: L; carries `conv_sound`'s typing gap | |
| `rewriteGoal_step` (Eq) | a rewrite by `Eq(A, a, b)` keeps the goal's truth | none | several pages | uncertain: occurrences matched by `==`, which ignores recorded parameters | |
| `type_futureFree` (Eq) | a value meaning a stored type at the constant future means it at every future | none | few lines once restated | suspect: a type holding loans (`Eq(Nat, loan₀, loan₁)`); needs loan-free | |
| `Rel.kept` (EqJAsm) | the relation survives a private computation at the extended context | same-context form proved (`Rel.private_copy`) | a page | likely true | |
| `inFlight_noLoan` | a loan-free value in flight keeps `Rel` and `GoodF` | none | a page | suspect: `borrow_ℓ 0` is loan-free by `Value.loans`, and the relation then wants a reference temporary holding it | |
| `copyEntry_ok` | entering a copy changes nothing `Good`, `CtxOk`, `Rel` read | none | a page | likely true | |
| `restore_ext` | restoring a copy gives `KeptAfter` and a good extension | none | a page | suspect: needs `Good` of the copy's end (a record of it can break (WF6)/(WF11)) | |
| `typedAssignment_of_withTemp` | `GoodF` with a temporary gives the assignment typed without it | none | few lines | likely true | |
| `eq_split` | `.eq` taken apart | `Regress/EqJ` runs | a page | likely true | M |
| `eqChecks_kept` | the side checks are private with a good extension | trial `#guard conv P2 Q2` | a page | suspect at today's checker (L); true after D103 | |
| `eq_sides_ok` | an untyped `Eq` that runs has sides that run at any hint | `Regress/UntypedNil.run_nil_none` | a page | suspect: the hint is universal; bare `Nil` fails at no hint | |
| `eq_sides` | the reference's sides mean the checker's at the type | `Regress/EqJ` | several pages | uncertain | |
| `eqType_futureFree` | any type value's meaning is future-free | none | few lines | suspect: unconstrained (`loan₀`); needs loan-free from the call site | |
| `eq_value_noLoan` | `mkEqM`'s result holds no loan | none | few lines | suspect: a stuck `Eq(Nat, loan₀, 0)`; needs loan-free sides | M |
| `J_split` | `J` taken apart: private front, then entry and arm, or the stuck block | `Regress/EqJ` (`JC`, `JS`) | several pages | suspect at today's checker (L, in the front's comparison) | |
| `J_stmts_run` | the reference's runs of `J`'s statement positions succeed | `run_nil_none` | a page | suspect: no hypothesis in the typed case | |
| `J_entry` | the checker's entry is the reference's | none | several pages | uncertain | |
| `J_arm` | the transported term and the join simulate the reference, typed `P(b)` | `Regress/EqJ` (`JC`) | several pages | suspect: `P(a)`, `P(b)` unrelated by any hypothesis (the link is `conv_sound`) | |
| `J_stuck_bridge` | the stuck block means the reference's `J` | `Regress/EqJ` (`JS`) | several pages | suspect: as `J_arm` | |

## G. `Id` and observation (`Steps/IdAsm.lean`, `Steps/Obs.lean`)

| Statement | Says | Checked | Size | Status | M |
|---|---|---|---|---|---|
| `idType_split` | `Id` taken apart; under every typed extension the conjunction means "results and owners equal" | `Regress/IdWrite`, `IdUnitWrite` | several pages | suspect: [Obs-ref]'s written unknown is referenced by nothing, so an extension may send it to `moved` (the trial's mechanism) | |
| `id_run` | the reference's `Id` is true iff the observations agree at every typed written value | `Regress/IdWrite` (`obs_same`, `obs_differ`) | a page | suspect: the type and the sides' runs are not tied by a hypothesis | |
| `fresh_realize` | written values are typed under typed extensions, and each is realised by one | `Regress/IdUnitWrite` | a page | suspect: as `idType_split` | |
| `footprint_positions` | the footprint's positions exist in the reference state | none | few lines | uncertain | |
| `cells_of_observe` | an observed side leaves whole-member cells the caller tells apart | none | several pages | uncertain: needs the written values' membership (T) | |
| `observe_step` (Obs) | an observation is private; under typed extensions the state after is good and related, and the result and owners mean the reference's observation | `Regress/IdWrite` | several pages | uncertain; L makes it vacuous at today's checker | |
| `footprint_coverage` (Obs) | positions outside the footprint mean the same after either side | `Regress/IdWrite` (`obs_z_same`) | core | uncertain: rests on `owners_sound` | |
| `owners_sound` (Obs) | every position depending on a live label is among its owners | none | a page | suspect: a reborrow's holder `r ↦ borrow₀(loan₁)` means `φ 1`, and `owners 1` lists only the lender of `0` | |

## H. Matches (`Steps/Match.lean`)

| Statement | Says | Checked | Size | Status | M |
|---|---|---|---|---|---|
| `joinEntry` | the reference's places already moved at a match are the checker's | an earlier false form (`Regress/JoinProbes`) | a page | likely true | |
| `evalMatch_step` | a match on a number simulates the run's `.matchNat` | `Regress/AdequacyProbes`, `EvalMemRuns` | several pages | uncertain; L; † (the arm's result across the join, when a borrow) | |
| `evalMatchInd_step` | the same for a declared inductive | `Regress/AdequacyProbes` | several pages | as `evalMatch_step` | |
| `evalMatchByType_step` | a match on a proof, by its type, simulates the run | `AdequacyProbes` (`UseOrInline`) | several pages | uncertain; L | |
| `split_coverage` | every assignment picks a constructor and extends to its fields, meeting the refinement | `Regress/SplitSubst` | a page | suspect: the scrutinee's unknown need not be referenced, so its value may be `moved`; also fails at fuels 0 and 1 (`ctorRefinement` out of fuel) | |
| `generalizeNeutral_step` | generalising a stuck program at a place to a fresh unknown keeps the relation; the unknown means the program | an earlier false form (`Regress/GenNeutralContent`) | several pages | uncertain: the unknown is referenced, so the program must be a whole member (T-like gap) | |
| `closeBlock_step` | the closed-off block's value simulates the match's run | `Regress/SplitSubst` check 3 (not kernel), `EqJ` (`JS`) | core | uncertain; † (the block's `&` captures pass as borrow arguments); its result's membership needs the arms' return checks (D81) | |

## I. Evaluation, types, tail (`Steps/Eval.lean`, `Steps/Types.lean`, `Steps/Tail.lean`, `Steps/EvalMem.lean`, `Statements.lean`)

| Statement | Says | Checked | Size | Status | M |
|---|---|---|---|---|---|
| `evalCore_step` (Eval) | the induction step: a term's run simulates the reference's | `UntypedNil`, `StaleTemp` (old forms), `EvalMemGap` | core | suspect: a typed hole of an empty type (five, item 2); L (`let x = Eq(Type, P2, Q2); 0`); T (no membership concluded) | |
| `eval_step` (Eval) | the same through `evalAt` | same | a page from `evalCore_step` | as `evalCore_step` | |
| `letIn_step` (Eval) | a `let` simulates the run's `.letIn` | `EvalMemGap.not_good_push` | several pages | uncertain as a statement; cannot be assembled (T, and U for untyped `let`s) | |
| `proof_step` (Eval) | a proof position is private and `⋆` is a member of its proposition | none | a page | suspect: an inlined captured proof `(⋆ : T)` is trusted at `T` (`evalCore`'s `.ascribe (.val .proof)`); true on reachable states, missing a hypothesis | |
| `etaUnit_step` (Eval) | at a `Unit` reading, `()` means what a member of `Unit` means | none | few lines | likely true | |
| `placeTypeQ_step` (Types) | `placeType?` is a private computation, good after | recorded states (`Sweep.recordNamesEmpty`, vacuous) | several pages | likely true | |
| `evalType_step` (Types) | a type's evaluation is private and means the reference's | checker side (`Regress/EqJ`) | a page | likely true | |
| `piSort_aligned` (Types) | the checker's sort of a captured Π-value is the decision's | none | a page | uncertain, leaning false: the checker reads it in the captures' frame, the decision at the current scope | nearly M |
| `capture_step` (Types) | closure formation simulates the run's `.fix` clause | none | several pages | uncertain | |
| `piShape_step` (Types) | the original and the captured Π/`fix` term give the same codes | the future part proved (`ShapeAgree`) | several pages | uncertain | |
| `evalCtor_step` (Types) | a constructor simulates the run's `.ctor`, with its type | `Regress/CodeRuns`, `DataCodes`, `EvalMemRuns` (membership of the result) | several pages | uncertain: the run cannot solve a parameter its record does not keep (D's revised parameter inference, docs/32) | |
| `evalTInd_step` (Types) | `D(ā)`: parameters on copies; the type means the run's | none | a page | likely true | |
| `fieldTypesOf_step` (Types) | the checker's field types mean the data model's | none | several pages | likely true | |
| `repackCheck_sound` (Types) | passing [Repack] makes a value a member | `Regress/EvalMemGap.repackCheck_false` | — | FALSE (K); restated as `EvalMem.RepackSound` (a guess) | |
| `bodyReturns_sound` (Types) | passing [Return] makes a value a whole member | `Regress/EvalMemGap.bodyReturns_false` | — | FALSE (K); the return path is `EvalMem.return_member` (proved from its pieces) | |
| `valType_sound` (Types) | a value's meaning lies in the type `valType?` reads off it | none | several pages | suspect: the value may be a temporary, which `Good` does not type (T); `valType?` reads `t(ps)` off a constructor without its fields | |
| `generic_good` (Tail) | for member arguments, a function's generic state is good and related to its body's frame | the frame layout on a recorded state (D80) | several pages | suspect at a borrow parameter: the checker's cell frame `x° ↦ loan` against `bodyFrame`'s empty frame 0 | |
| `checkTail_step` (Tail) | the world the assignment selects reaches a leaf that is the reference's run of the body | none | core | uncertain; cannot be assembled from `eval_step` as stated (T) | |
| `checkFix_sound` (Tail) | an accepted local `fix` is a member of its Π-type | `Regress/DefKnot` | core | suspect: `fv` (what `self` is bound to) is free; the local knot (D73 item 5) is not designed | |
| `checkInd_sound` (Tail) | an accepted declaration is covered by the context's model | none | — | suspect: `CtxOk` covers the existing declarations only, and `checkInd` admits a new one | |
| `app_mem` (EvalMem) | a member of a function type applied at members gives a member of the codomain | — | — | PROVED (`ApplyMem.app_mem`, the data layer; with `app_mem'`, `app_mem_ref`, `app_mem_finals`, `app_mem_unit`) | |
| `sortOf_sound_stmt` (Statements, not wired) | the checker's reading of a stored type's sort is the code's level | (Rd) swept (D78) | several pages | uncertain; `fix_split` needs its function-type case | |
