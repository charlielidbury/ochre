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

## The five most likely false (not yet kernel-checked)

1. ~~The decisions instance cannot meet `DecTab`~~ FALSE (K) (`Regress/OpenFalse.decTab_fixedFuel_false`) and FIXED (D84: `DecisionsFF.chainDecisions`, `decTab_ff` proved from the machine-only `decide_fuel_agree`). As first found: `DecTab` asks agreement with the checker at EVERY fuel; `DecisionsInst.checkerDecisions st fuel` answers each decision at ONE fuel and returns a default (`readDecision`) where that fuel runs out, so on a term deeper than the fuel it answers `.other` where a larger fuel answers the real reading. Mechanism verified ✓ (`Decide.declOf` recurses at one fuel less; `checkerDecisions₀` reads at `fuel`). Fix: a fuel-free instance (the answer at any fuel where the decision succeeds; decisions are fuel-monotone by the checker's no-catch-and-default rule), or `DecTab` restricted to fuels up to the instance's.
2. FALSE (K) for `eval_step` at ANY typed hole (`Regress/OpenFalse.eval_hole_false`: the reference has no clause for `?`); decided: the evaluation statements take "no hole in the term" (D84). As first found, at a hole of an empty data type: `evalCore`'s `?` returns a fresh unknown of the expected type (verified ✓, `Machine.lean` `.prim "hole"`), which no typed assignment can give a value. `consistency_rel` never uses its `NoHoles` hypothesis (build warning), and `Ochr/Consistency.holeFalse` is an accepted proof of `False` by a hole. Fix: `NoHoles` of the term as a hypothesis of the evaluation statements.
3. **`assignPlace_step`**: concludes `Good` after writing `v` at a typed place, with nothing saying `v` is a member of the place's type (the check is in `eval`, not `Machine.assignPlace`; root T).
4. **`runBody_front`**: concludes `Good` of the callee's frame, whose parameters are bound to the arguments unchecked (`runBodyCore`'s `pushBind h A (etaUnit pd w)`); nothing gives the arguments' membership (roots T, U).
5. **`closeCall_post`, `callFn_tail_closed`, `callFn_tail_ran`**: variables the conclusion reads (`fres`, `as`; `res`, `B`) are unconstrained by the hypotheses (the defect class of `Regress/CloseCallStmt`).

Kernel-checked FALSE so far: `bodyReturns_sound`, `repackCheck_sound` (`Regress/EvalMemGap`; restated as `EvalMem.RepackSound`, the return path `EvalMem.return_member`), `grows_restoreKeep`, `typedFutureF_exists` (restated and proved, D84), `eval_step` at a typed hole, the fixed-fuel decision table (`Regress/OpenFalse`), `grain_deref_not_proof` (`Regress/GrainDerefProof`, restated on `spine-slice-grainref`), `mkEqM_step`, `conv_sound`, `convPi_sound` (trial: `Rules/Counter*`, `Rules/EmptyDomain`).

## Machine-only statements (a separate lane)

`DecTab.back`; the 37 `grows_*` (all of `Steps/MachineMono.lean`; `grows_restoreKeep` FALSE as stated, needs "the snapshot has the current globals and declarations"); `access_absTy`; `eq_split`; `accepted_resolves`, `resolves_of_accepted`, `resolvesTo_unique`, `covered_prefix` (only `dm.covers`); `scopeOf_sstate` (reads only the readings); `consistencyBounded` (the theorem itself is machine-only in statement). Machine-only conclusions under a droppable hypothesis (`M*`): `borrow_wf`, `end_wf`, `assign_wf`, `close_wf`, `capture_wf`, `eval_wf6`. Nearly: `callee_bounded`, `piSort_aligned` (restatable without meanings). The hard ones are one induction over the interpreter's mutual block (`eval`, `endBorrow`→`substEnv`→`nfSealed`→`eval`) for the `grows_*` interpreter group and `access_absTy`.

## Part (b), membership, under the plan of record (docs/31 D86)

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
| `substEnv_abs_step` | a [Split] refinement over Ω, types and goal: same shape, same reference state, `Good` under an extension | concrete runs (`Regress/SplitSubst`, D76) | several pages | uncertain, leaning true; same `RefineOk` gap; † | |
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
| `run_frame` (FrameProp) | the frame property with the label renaming: in-place and closure-frame runs agree | `Regress/FrameCheck` (`Inc`, `Id1`) | core | uncertain (a 16-clause relation, two calls checked) | |
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
