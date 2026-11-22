# Existence of the data model: handoff (working file)

Lane: prove `Assembly.exists_dataModel` (`Meaning/Consistency.lean`). Branch `spine-exists9` (from `spine-lead25` b54f9c83: the one-list ruling, D174/D177), worktree `/home/charlielidbury/repos/ochre-exists3`. Durable record: `ochr/docs/34-data-model-existence.md` §18 (§18.5 frame locality, §18.6 the knot). This file holds what only a successor needs; delete it when the lane's work is merged. Last updated 2026-11-22 by `exists9`.

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

## Next (exists9's successor), in order of risk

1. `leafOk` for the knot's records (`hleaf` of `recordsFaithful_canon`): the knot's field type at members is never the raw data code of a `Prop`-sorted declaration. Attack: the knot's agreement (`knotK_agree`) makes it the run's value where the run is defined; elsewhere the interpreter's own value (`itpT`: `.data` along the spine, the run's value at steady nodes). Either prove the run never builds such a code from members (type parameters that are members of a universe have a level, the raw code has none), or ask the lead whether `RecordsFaithful.leafOk` can be restricted to keys where the run is defined.
2. DONE (exists9): the `Prop`-sorted analogue (`semP_psAt`, `itpP_psAt`, `ftyP_psAt`, `recCanonP`, `recordsFaithful_canonP`, `mono_canonP`). Not done for it: `par` (a `Prop`-sorted declaration's records are asked `RAgree` only by a later knot, through `hpar` for all of `K.Γ`; `truthSpec`'s `N` is constantly false, so `recK_agree` gives `RAgree` for its own `N` only: check what `hpar` needs at a `Prop`-sorted earlier declaration).
3. The step's glue, following `inv_step`'s docstring. Pieces: the build context `K0`; `K0`'s model with `d`'s parameter types `pty`; the transfer of `knot_exists`' conclusion to an extension (`runT_congrA`, `DecStable`, `runT_congrN` with `NamesOk`, `teleFrame` reads the model only at `d`'s field types and parameter types); `congr` for a definition (`runT_congrN` on its `fix` term or body and `meanV_congrN` on its stored type); `faithful` at old declarations by `Extends` monotonicity; `ItemFacts` for the stage structure; `Nodup` of the list's names (from `IndChecks.fresh` and `inds_prefix`). Also needed: `NamesOk`'s tests pass on field types (`Term.nok`), from a checker fact (names declared) plus "no constructor of `d` in its own field types" (from `Spine`/`PSpine`: off-spine nodes avoid `d`).
4. Restate `exists_dataModel` (`Consistency.lean`, approved): hypotheses `ItemFacts`, `NamesOk` per stage, `DecLocal`, `DecStable`, `inds_prefix`; repair `consistencyBounded_assembled`.

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
