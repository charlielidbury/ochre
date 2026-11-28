# Existence of the data model: handoff (working file)

Lane: prove `Assembly.exists_dataModel` (`Meaning/Consistency.lean`). Branch `spine-exists13` (from `origin/spine` 62dcac80c, main 73bcc8750 merged at 203e13f87), worktree `/home/charlielidbury/repos/ochre-exists3`. Durable record: `ochr/docs/34-data-model-existence.md` §18 (§18.19: what exists13 proved and found, the status). This file holds what only a successor needs; delete it when the lane's work is merged. Last updated 2026-11-28 by `exists13`.

## Where exists13 stopped (read this first)

`exists_dataModel` now assumes THREE facts (`DataFacts`): `VaryValFact`, `NamesConstTy` (about the checker), `DecStable` (on its decisions), plus the program's resolution (`hres`, from which `NoValFact` and `DefsNoVal` are proved).

Done (default build, standard axioms):
- Merge of main (D139, D140, the capture sort): `runs_checkInd_*` peels gain D140's loop; `staticBlockCaps`/`ckBlockCaps` sort by `blockCapOrder`; the three skeleton capture statements take `kept`.
- `FieldHeads` PROVED: `Steps.Machine.runs_checkInd_heads` (D140's loop + `firstOrderTerm`'s call clause, `runs_firstOrder_call`, now the fourth conclusion of `runs_checkInd_fields`); `Assembly.fieldHeads`.
- `DecCaps` PROVED: `Steps/Machine/CapsLocal.lean` (`staticBlockCaps_root`, `decLocal_caps_chain`); `DecLocal` is `exists_dataModel_facts`' own hypothesis, whole.
- `NamesFact` PROVED but for a constant's stored type: `Exists/Names.lean` (`nok_of_undeclared`, `foB_ctorFree`), `Steps/Machine/NamesSpec.lean` (`runs_checkDef_names`, `runs_checkInd_undeclared`), `NoVal.lean` (`noValDef_runResolve`), Assembly (`verdict_defn`, `verdict_ind`, `stage_globals_means`, `namesFact`). The residue is `NamesConstTy`.
- Findings: `FactsCE.dVS` (VaryValFact's `.any` case is decided by a run at an inductive's type parameter; messaged), `DecStableCE.lean` (DecStable false as stated for programs with holes).

Next, most valuable first:
1. `VaryValFact`: if the lead extends D128 to reject a parameter whose declared reading is `.any` (my recommendation, messaged), derive it: off the spine from `NestLoop.nestableSet_spec` with `deepVars` (a varying value parameter read there removes the nestable parameter its type reads); on the spine (the whole field type: D140; an inductive's type-parameter argument: `typePos` through `declOf`'s `.tind` clause gives the reading `.sort` or `.any`; `.sort` gives a written sort by D128). The peel `runs_checkInd_peel` keeps `h128` (D128's loop) and `hTP` (the typePos loop) unused so far.
2. `DecStable`: the lead's call on the restatement (no holes, or `Extends.dec`'s state extending the seeded `absDecl`); then the machine lane's two-way simulation of the decision procedures under table extension (equal `SucceedsAt` predicates: `readDecisionFF` then agrees with no fuel agreement).
3. `NamesConstTy`: a whole-machine names invariant over the 113 functions of the mutual block (relational, with a precondition on the term run), generated as `machineGrows` is.

Traps met by exists13: a docstring may not precede `set_option … in` (put it after); `Option` `none == some m` and `none != some m` reduce by `rfl` (use `show (none == some m) = false from rfl` in `simp only`); a structure literal in a `have` type broken across lines does not parse (use `show` with `_`); `find?` lemmas over a `Type 3` list need `{α : Type _}`; `deriving BEq` on `Step`: `show (i == i) = true` exposes the field comparison; the D140 loop's body inverts by `repeat' (first | rw [runs_get_bind] at hr | split at hr)`.

## Where exists12 stopped

`exists_dataModel` now assumes FIVE facts (`DataFacts`): `NamesFact`, `VaryValFact`, `FieldHeads` (about the checker), `DecCaps`, `DecStable` (on its decisions), plus the program's resolution (`hres`). All five read TRUE (docs/34 §18.17 gives each reading, probe and what a derivation needs).

Done (default build, standard axioms):
- `GlobalCalls.lean`: `GlobalCallLevels` PROVED (`Assembly.globalCallLevels`): stage invariant `TyInv`; `globalTyS_tPi_sort`; the leaf-code lemma `DatLeaf`/`telL_datLeaf`/`callOfL_datLeaf` (the referee's Y3). `GlobalCallsHard.lean`: the attack at the hard case (`FT`, `FI`, `FM`, each `(A : Type₁) … : Type` heading an accepted field; `FT` in the kernel, the rest natively).
- `Steps/Machine/NoVal.lean`: `NoValFact` for resolved programs (machine12's `RRet` WIP finished; `noVal_runResolve`; `Consistency.noValFact_of_resolvesTo`).
- `Steps/Machine/CheckIndSpec.lean`: `CheckIndGivesChecks` assembled (`runs_checkInd_peel`, `runs_checkInd_fields`, `runs_checkInd_checks`); `Assembly.itemFacts`. The peel keeps every sub-run of `checkInd` (`telescope`, D128's loop, `typePos`, both `undeclaredCheck`s, the field continuations): the starting point for `NamesFact`'s declaration part, `VaryValFact`, `FieldHeads`.
- `Steps/Machine/RepLocal.lean`: `DecLocal`'s `inv` (trivial) and `rep` (`jdAssigns_ok`, `typeState_rep`); with machine11's `join`, `Assembly.DecLocal3`, supplied by `Consistency.exists_dataModel`.

Next, most valuable first:
1. `NamesFact` minus a constant's stored type: from `runs_undeclaredCheck_inv` (in `CheckIndSpec.lean`; a `checkDef` peel to its `undeclaredCheck`, as `runs_checkDef_tables` peels), no `Term.val` in resolved terms (`noVal_resolveF` covers definitions too: extend `noVal_resolveDecl` to the `.defn` branch), `foB` excluding the declared type's own constructors (so `fieldNames.rc`), and a stage invariant "every global has a meaning entry" (strengthen `checkItem_tables` to say the appended global is named `d.name`; `checkDef` appends `{ name := d.name, … }` in both branches). Restate `NamesFact` as that plus `NamesConstTy` (a constant's stored goal VALUE names only the stage's names: a whole-machine invariant). A lemma `Term.undeclared … = none → no val → Term.nok N` (mutual induction) is the core.
2. The proposal in docs/34 §18.17 (two syntactic checks in `checkInd`) is for the lead; if adopted on main, `FieldHeads` is their postcondition through `runs_checkInd_peel`'s kept runs.
3. `DecCaps`: blocked on `Array.qsort` (private recursion in Lean's core, no lemmas); see docs/34 §18.17.
4. `DecStable`: the machine lane's (8a).

Traps met by exists12: hypothesis-side `split` on the checker's do-blocks exceeds simp's step limit (each `if`'s continuation is copied into both arms): use `runs_ite_inv` (in `CheckIndSpec.lean`), which finds the condition by unification; a written `match` in a `by_cases` condition elaborates to a different matcher and `rw [if_pos]` then fails. After `subst`, a reintroduced older hypothesis takes back a shadowed name (`hC`): clear the old one. `rename_i` names the LAST inaccessible hypotheses: after `cases t` inside an `if` branch the last one is the branch's condition (`rename_i u _`). The kernel's reduction of `checkDef` on a body that reads a parameter, and of `checkInd` on a declaration with a field call, gets stuck: check acceptance natively (`#guard`) and take it as a hypothesis.

## Rulings (made by the lead 2026-11-22)

1. Checker rules (A) and (B) (docs/34 §18.6): ADOPTED, subject to measurement; `checker6` implements and measures them, reading `Knot/Grammar.lean` as its specification. In `knot_exists`, "every accepted declaration's field types satisfy the grammar" is ONE named fact about the checker, counted as assumed until the checker enforces it; state its predicates as decidable functions of syntax, declarations and declared types where possible.
2. `teleFrame` types the fields not yet bound `err`: APPROVED and BUILT by `exists6` (docs/31 D160, docs/34 §18.7; the checker's frame pinned by `TeleFrameGuard.lean`).

## Done (exists5), all in the default build, standard axioms

- `KnotCE.knotOld_false`: `knot_exists` as first written is false (a value parameter carrying the knot's record; `Pt(D2, x)`).
- `Knot/Swap.lean` `runT_stateOf_swap`: frame locality between two one-frame states differing at a set of binding indices (assumes `DecLocal`, label-free globals).
- `Knot/Grammar.lean`: `paramVaries`, `fieldVaries`, `varVaries`, `Steady`, `Spine`/`SpineArgs`, `ParamTyLocal` (definitions).
- `Knot/Interp.lean`: the interpreter `semT`/`itpArgs`/`argSem`/`itpT`, the canonical frame `canFrame`, `ftyK`.
- `Knot/Guard.lean`: `knotK` (a `KnotSpec`), guardedness PROVED (`ftyK_agree`), resting on `Spine`, `hpar`, `ParamTyLocal` as hypotheses.
- `Knot/Agree.lean`: `knotK_agree` (assumes `SteadyAt`), `uShape_recK`, `fieldTy_knot`, `rebuild_eq`, `semT_run`/`itpArgs_run`.
- `General.knot_exists` RESTATED (outside the build, `sorry`): `S := knotK …` is the witness; it also assumes `GlobalsTyped` (for `Good`).

## Earlier pieces (exists2–4), still current

- `PreludeModel.lean`, `Step2.lean`: the two kernel-checked instances of the repaired statement's bundles. `PropNestCE.lean`: piece 4 is false for `Prop`-sorted declarations nested at a `Prop` parameter.
- `RunLemmas.lean`: the run of each field-type term form (`runT_var`, `runT_tind`, `runParams_spec`, `runT_eq`, `runT_call_const`, `runT_teleFrame_param`/`field`, `teleFrame_split`, `callOf_val`). `Piece3.lean`: `memTy_small_inj`, `index_fields_eq`, `projIdx_get`/`projIdx_take`.
- `FrameLocal/`: frame locality `runT_qset` (assumes `DecLocal`). `Decomposition.lean`: the nine pieces; `runT_congrDM` (piece 1) stated, unproved.
- `General.lean` (outside the build): `globals_typed`, `mono_prop`, `truth_exists` (sorry), `runT_frameLocal` (false, kept), `knot_exists` (restated, sorry).

## Done (exists6), all in the default build, standard axioms

- D160: `teleFrame` types the fields not yet bound `err`; `TeleFrameGuard.lean` pins the checker's frame.
- `Knot/Congr.lean`: `runT_congrR`, the model congruence (no assumed fact). `Avoids` restated (no embedded value; `avoidsOld_gap`).
- `Knot/Steady.lean`: `steadyAt_knotK` (assumes `DecLocal`, label-free globals).
- `Knot/Grammar.lean`: `spineB`/`spineArgsB`/`GrammarOk` (decidable), `spineB_sound`.
- `Knot/Exists.lean`: `knot_exists`, PROVED, assuming five named facts (`GrammarOk`, `hpar`, `ParamTyLocal`, `DecLocal`, label-free globals). `SteadyAt` and `knotK_agree` now ask the earlier fields to be MEMBERS of their field types (FieldsTyped at the knot's model), not to fit the shapes; `GlobalsTyped` is no longer needed for the knot.

- `CrossSortCE.lean`: the checker accepts nesting across sorts that Lean rejects. Rule (A*) ADOPTED by the lead (subject to measurement); its predicates are `Knot/Grammar.lean`'s `occSortB`/`NestSortB`/`AStarOk` (checker6's spec: keep them exact). My first claim that `hpar` is false for `E` was WRONG: `hpar_E`/`fields_E` check that E's canonical record is parametric and faithful; the knot does not need (A*); truth-first does.
- `TruthCE.lean`: `truth_exists` as written is false (kernel-checked; no hypothesis on earlier records). `PropMono.lean`: `mono_prop` proved (its content is its hypothesis).

## Done (exists7), all in the default build, standard axioms

- The counterexample files' `ochr` blocks mark what D120/D121 now reject (KnotCE `D2`, CrossSortCE `D`/`QW`/`Q`, PropNestCE `P`).
- (B2) weakened (docs/34 §18.10): `Knot/HintFree.lean` `runT_hintFree` (a term not headed by a parameterless-written constructor, an embedded value, or clone/peek/inplace runs the same at every hint); `SpineArgs.value`/`PSpineArgs.value` take `HintSteady ∨ hintFreeB`. `HintShapes.lean` asserts DF, DK2 pass; DK, DT3 (bare constructor at a hint computed from the declared type) do not. RULING REQUESTED from the lead on DK (recommended: the checker stores solved constructor parameters).
- (A) in `Spine` weakened: the `Type`-parameter half was never used (only "a varying applied declaration is data-sorted").
- `Steady.steadyAt_spec`: the steady-node agreement for ANY `KnotSpec` (canonical frame typed by the spec's own field types; `SteadyAtS` in Agree.lean); `steadyAt_knotK` is its instance.
- `truth_exists` PROVED (`Knot/TruthExists.lean`, docs/34 §18.11): truth interpreter `semP`/`ftyP` (`TruthInterp.lean`), monotonicity `ftyP_le` and the fixed point `truthP` (`TruthMono.lean`, `Truth.lfpM`: least fixed point among argument-monotone predicates), agreement `truth_agree` (`TruthAgree.lean`). Assumes `PGrammarOk`, `hmono` (earlier Prop-sorted records monotone, genuine keys), `ParamTyLocal`, `DecLocal`, label-free globals. Returns d's records monotone (for the next `hmono`). `General.truth_exists` (sorry) retired.

## Done (exists8), all in the default build, standard axioms

- Merged spine-lead24 (D172: the reference runs every parameter of `D(ā)` and of a constructor with no hint). Guard/TruthMono: a value argument's value agrees outright; the truth interpreter `argSemP` runs at no hint too.
- (B2) REMOVED (docs/34 §18.10 outcome; main's D123 WITHDRAWN by the lead): `SpineArgs.value`/`PSpineArgs.value` have no hint field; `GrammarHintOk`, `HintSteady`, the `*CoreB` copies are deleted. `HintShapes.run_cons_noHint`: the reference's run of DK's bare `Cons(0, Nil[Nat])` with no hint equals its run at `List(Nat)` (parameter solved from the fields).

## Done (exists9), default build, standard axioms (docs/34 §18.14)

- `Knot/CongrN.lean` `runT_congrN`/`meanV_congrN`: the run at any two models and two global tables agreeing at the names a term mentions (`NameOk`, `AgreeN`), embedded values included. Replaces `runT_congrR` for the assembly (gaps (a), (b) of §18.13).
- Knot restated: `pEntryV` (value parameters kept small; `knotK`, `truthSpec`); `hpty : ParamTyLocalD K.dm d` (the declaration's own parameter types, weak form) in `knot_exists`, `truth_exists` and everything under them. `hint_eq`/`hint_eqP` still take the old `ParamTyLocal` and are dead.
- `Records.lean` (piece 6, data-sorted): `canonPs` and its lemmas; `ftyK_psAt`, `recK_congr` (the knot reads a varying value parameter only small, given `VaryValFree`); `recCanon`, `recordsFaithful_canon` (`types`, `values`, `smallOnly`; `leafOk` is the hypothesis `hleaf`, OPEN), `par_canon`.
- `Params.lean` (piece 7): `frameP`, `pty` (masked frame for non-varying parameters), `pty_local`, `pty_faithful` (frame locality), `pty_type`.
- `Assembly.lean` (outside the build): `Extends`/`Inv` at one list (`rest` added, `pty` gone), `exists_of_inv`, `inv_zero`; the step's facts stated: `ItemFacts`, `DecStable` (piece 8), `NamesOk`; `inv_step`'s docstring is the recipe.
- `Scratch/VaryValSweep.lean` (untracked): `VaryValFree` and "parameter types hold no embedded value" at all 300 stored declarations: all pass.

## Done (exists10), default build, standard axioms (docs/34 §18.15)

- `LeafOk.lean`: `leafOk` of the knot's and truth spec's records from the grammar; `hleaf` gone.
- `PropParCE.lean` + `Knot.ParHyp`/`TopSortOk`: the knot asks parametricity of data-sorted declarations only; `grammar_of_checks` has a fourth conclusion (`TopSortOk`).
- `DeclStep.lean`: `fieldsFaithful_spec` (both sorts), `paramsFaithful_pty`, `field_transfer`, `param_transfer`. Finding: `FieldLevels` (the checker's field-level check) is needed.
- `Assembly.lean` (now default build): `inv_step` proved (`inv_reject`, `inv_defn`, `inv_ind_core`, `inv_ind_faithful`); `exists_dataModel_facts`. `Consistency.exists_dataModel` restated with `hF : DataFacts` and `hpre`, proved; `consistencyBounded_assembled` takes `hdata`.
- `Scratch/ChecksSweep.lean`, `GrammarSweep.lean`, `VaryValSweep.lean` committed (the sweeps behind `ItemFacts`).

## Done (exists11), default build, standard axioms (docs/34 §18.16)

- `FactsCE.lean`: the old forms' counterexamples (`itemFactsOld_false`, `varyValFact_false`, `fieldHeads_false`, `join_regrains`/`decLocal_false`, `decStableOld_flags`). `tlAccepted` is a native `#guard` (the kernel's reduction of `TL`'s `checkItem` run gets stuck; `EV`'s and `EP`'s finish in under a second). When D128/D129 reach the line, `tlAccepted` and `join_regrains` fail: delete those parts and the facts' FALSE TODAY notes.
- `Assembly.lean`: `ItemFacts` restated (params/ctors instead of the no-value and VaryValFree parts); `NoValFact`, `VaryValFact` new; `DecStable` per program (NOT the ruling's any-state form, see docs/34 §18.16); `FieldLevels` replaced by `FieldHeads` (checker) + `GlobalCallLevels` (model, unproved); `hpre` discharged by `Steps.Machine.indsOf_take_prefix`.
- `FieldLevel.lean`: `fieldLevel0_of` PROVED (a field type runs to a level-0 code from its top shape, `HeadLevels`, `CallsLevel0` of the called globals, parameter types faithful); `callsLevel0_of_not_t2`, `enc1_lvl0`.
- Probe programs (scratchpad, not committed): `FLProbe.lean` (calls into `Type₁` and parameters written at calls: all rejected, so `FieldHeads`' call part reads true).

## Next (exists11's successor), most valuable first

1. `GlobalCallLevels` (the one model fact). Three pieces: (a) a stage invariant: for `f` in `(stage dm k).globals`, `(stage dm k).baseC.global f` has type `.plain .err` or `globalTyS` of the FIRST stored entry named `f` (means are appended with the stored type of the accepting state; globals only grow, `checkItem_tables`); (b) `meanV` at `.tPi cs (.pi hs ds (.sort l)) rd` is `.ty err` or `.ty (piTyAt R l' ps ⟨false, fun _ => univ l⟩)` (unfold `meanV`'s `tPi` clause, `runT`'s `.pi` clause at `Run.lean:1374`, `runT_sort`); (c) `CallsLevel0` of that: `l' ≤ 2` by `callsLevel0_of_not_t2` (`piTyAt` 0 is `prop`, 1 is `.t0`, 2 is `.t1`); `l' = 3` needs a version of `LeafOk.callOfL_enc` that tracks the `.dat` code through `telL` (`Apply.lean:204`: the codomain code is `(lvl2 R).codeOf (out.cod acc)`), then `codeOf` of a `.t1` code is a lift, and `enc2 (lift c) = enc1 c`. The level-3 case is reachable: `def F (A : Type₁) : Type := Unit` with `inductive W (A : Type₁) := MkW(x : F(A))` is accepted (probe `L3Probe.lean`, scratchpad).
2. `NoValFact` from `Surface.lean` (`resolveDecl`, `bindersF`, `resolveF`: no clause builds `Term.val`), and `NamesFact` (machine10's reading: `undeclaredCheck` plus resolution). Both are statements over the resolved items; `consistencyBounded_assembled` passes `ResolvesTo`.
3. `CheckIndGivesChecks` (the `IndChecks` part of `ItemFacts`): machine10 proved the pieces; the assembly plan is in `Steps/Machine/CheckIndChecks.lean`. Then `ItemFacts` is a theorem (with `checkItem_tables`).
4. `DecStable` per program: whether a hole in a called global's stored type lets the decisions read `absDecl` (the later state's `absDecl` is unconstrained by `Extends`).
5. Check `Scratch/VaryValSweep.lean` and `ChecksSweep.lean` still compile against the current definitions before rerunning them.

## Which grammar predicate each theorem assumes

- `GrammarOk` / `PGrammarOk` (exists7's `GrammarCoreOk` / `PGrammarCoreOk`): a fact about the checker, enforced since main's D120/D121, to be derived from its checks (step 2).
- `Knot.knot_exists`: assumes 5: `GrammarOk`; `DecLocal`; `hpar`, `ParamTyLocal`, label-free globals. No same-sort predicate.
- `Knot.truth_exists`: assumes 5: `PGrammarOk`; `DecLocal`; `hmono`, `ParamTyLocal`, label-free globals. `PSpine` carries (A*) for `d`; no `AStarOk` at earlier declarations.
- Report theorems as "assumes N facts", sorted: about the checker and not enforced (none now); about the checker and enforced but unproved (`GrammarOk`, step 2); obligations on the decisions (`DecLocal`); for the assembly.
- `Scratch/GrammarSweep.lean` (untracked) evaluates the grammar at every declaration of every registered example block (~16 min); run it before stating step 2's implication.

## Assembly obligation found while reading `CtxFaithful` (not yet addressed)

`CtxFaithful K` quantifies `∀ Δ ρ`, but `knotK`/`truthSpec` take `ρ` (the interpreter's `valOf` runs under `ρ`). The assembly must build records that do not depend on `ρ`: either show a declared field type's run does not read `ρ` (declared types hold no hole or unknown), or fix `ρ` and prove the run's congruence in `ρ` for such terms.

## Earlier plan (exists8; superseded by the section above)

1. Step 2 DONE (exists8; docs/34 §18.12): `Knot.grammar_of_checks` (FromChecks.lean): `IndChecks Γ0 d` (Checks.lean: fresh name, stored nestable = `nestableSet`, `TeleOk`, mirrors `foB`/`rvB` and `sortNestViolation` at every field) + `FieldsNoVal d` (resolution) + `hval` (earlier value parameters not nestable; the theorem's third conclusion, for the assembly) give `GrammarOk`/`PGrammarOk` at `Γ0 ++ d :: rest`. `NestLoop.nestableSet_spec` proved. The bridge `CheckIndGivesChecks` (checker run ⇒ `IndChecks`) is a named fact for the machine lane. `Scratch/ChecksSweep.lean` (untracked; `SWEEP_FROM`/`SWEEP_TO` env vars, prints per block): `IndChecks` and the other two hold at every stored declaration of blocks 0..130 (286 declarations); the case studies 131..143 (run in the background, about 25 minutes): 14 more, all pass. 300 in all.
2. `globals_typed`: NOT NEEDED (exists8): no consumer is left (`knot_exists` and `truth_exists` stopped using `GlobalsTyped` in exists6/exists7; `RecordsFaithful.leafOk` is the records' `dataView`). Pieces 6 (`RecordsFaithful` of the knot's and truth records) and 7 (parameter types by the run, `ParamsFaithful`) are still to do; both sit inside `inv_step`.
3. The assembly (exists8): `Assembly.lean` (OUTSIDE the default build, one `sorry`). The invariant `Inv` (per stage: covers; `congr`, the stages' program meanings read the model only at their declarations; `faithful`, every declaration of every stage faithful at every context extending that stage, `Extends`; and `par`, `mono`, `pty`, `val` for the next construction). PROVED: `exists_of_inv` (the invariant at the last stage gives `exists_dataModel`'s conclusion), `inv_zero`, `inv_all`, `exists_dataModel'` from `inv_step`. OPEN: `inv_step`; its docstring lists what it rests on. The hard point found by attacking it: a declaration's faithfulness must transfer from the context its records are built in (declarations up to it) to every later prefix's context (more declarations), and the run reads the declaration list not only at names the term mentions but at the name a strong-updated tree carries (`DataModel.readTy`'s `ownTy`, through `Sem.follow` only). CORRECTION: exists8 first also named a move's write (`dropAt`'s `updAt … isSome` test); `Sem.updAt` does not read the list, so that write is not involved. Ruled (a), 2026-11-22: weakening in the declaration list under a scope invariant, in this lane. Necessity checked: `ScopeCE.run_differs`. Findings on the invariant's use site and on closures: docs/34 §18.13. RULED (the lead, 2026-11-22): the declaration list is the whole program's at every stage; no weakening in the list. What that leaves (docs/34 §18.13, points 1-5): (a) extend `Knot/Congr.lean` to a model with `d`'s PARAMETER TYPES replaced (same proof as `runT_congrR`, which relies on definitional equality between `K` and `KR K d R`: a general "any model agreeing off `d`" version was tried and reverted, `OMem` is indexed by the model); (b) a `Value.mean` congruence for a definition's stored type; (c) restate the assembly at the one list: `Assembly.ExistsDataModelOne` / `DataFaithfulOne` / `DeclsFaithful` are stated, `Inv`/`Extends`/`exists_of_inv` still speak of prefixes and must be redone at the one list (contexts: the full list, the stage's records at its declarations, the stage's globals; faithfulness only for the stage's declarations); (d) pieces 6 and 7.

## DecLocal, node by node (exists4, partly done)

`FrameLocal/DecAt.lean` (default build): `DecAt D t` is the obligation at one node; `DecLocal.decAt`; `decAt_of_hasDecNode`; `chainDecisions_inv`. NOT done: `runT_qset` still takes the global `DecLocal K.D`. Recipe: define `DecAll D : Term → Prop` mutually with lists/arms (`DecAt D t ∧` `DecAll` of each immediate subterm) and `decAll_of_hasDecNode`; replace `hD : DecLocal K.D` in `runT_qset` and its companions by `hinv` plus `hDA : DecAll K.D t`; at each IH call pass the subterm's component; at matches/`J`/`Id` use `hDA.1`. About sixty call sites, all mechanical.

## Idioms and traps

- A run lemma's hypothesis `hr : run K … = some (r, s')`: `unfold run at hr` first (`run` is an `abbrev`).
- `runT` of a term whose clause is `do match … with` unfolds to a match applied to the state: `revert hr; cases h : <discriminant>` instead of `split at hr`.
- `rw [h] at hr` where `h : (0 : Nat) = …` rewrites EVERY `0`: pass the variable index with its equation.
- To work at a concrete context, `cases K with | mk dm Γ C D Δ Λ cur => …`; `find?` by name on a concrete declaration list is `rfl`.
- Unfold a definition compiled by well-founded recursion (`semT`, `itpT`, `ftyK`) with `rw [f]` and close leftover `match = match` goals by `cases <discriminant> <;> rfl`; the catch-all equation of `semT` has side conditions (`semT_other`).
- Inside a `mutual` block, recursive calls do not take the section variables; passing `(ρ := ρ)` to them is an error. Structural recursion over the mutual `Spine`/`SpineArgs` proofs works for theorems.
- Forward run computations (KnotCE): `runT_var_fwd` (a read at a shape-free state under decisions that erase nothing), `run_D2`/`run_p` (`rw [runT]` the outer clause, then `simp only [find, runParams, SM.onCopy, …]` with the inner runs as rewrite lemmas quantified over the hint).
- Python edits of Lean files: never put Lean text containing `'''` in a Python triple-quoted string.
