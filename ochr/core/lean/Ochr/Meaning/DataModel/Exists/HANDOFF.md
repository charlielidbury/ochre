# Existence of the data model: handoff (working file)

Lane: prove `Assembly.exists_dataModel` (`Meaning/Consistency.lean`). Branch `spine-exists6` (from `spine-exists5`), worktree `/home/charlielidbury/repos/ochre-exists3` (it carries the proof line through f6c59f58). Durable record: `ochr/docs/34-data-model-existence.md` §18 (§18.5 frame locality, §18.6 the knot). This file holds what only a successor needs; delete it when the lane's work is merged. Last updated 2026-11-22 by `exists6`.

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

- `CrossSortCE.lean`: the checker accepts nesting across sorts that Lean rejects; `hpar` is false for `E` (argued). RULING REQUESTED from the lead on rule (A*) (docs/34 §18.9); read the answer first.
- `TruthCE.lean`: `truth_exists` as written is false (kernel-checked; no hypothesis on earlier records). `PropMono.lean`: `mono_prop` proved (its content is its hypothesis).

## Next

Restate and prove `truth_exists` once (A*) is ruled: hypotheses `hmono` (earlier records satisfy `mono_prop`'s `hcanon`), the grammar for a `Prop`-sorted `d` under (A*), earlier fields as members; the truth predicate is the least fixed point of the one-step operator (impredicative intersection); the records hold, at every key where `d` or its truth occurs, the proposition leaf; faithfulness then follows the knot's pattern (frame locality + model congruence at steady nodes). Then `globals_typed`, pieces 6, 7 and the assembly. Older plan: `mono_prop` and `truth_exists` (piece 5, `General.lean`; attack first, especially the monotonicity induction, never exercised by an instance; `PropNestCE.lean` shows why the data construction is false there), then `globals_typed`, pieces 6, 7 and the assembly. The assembly must discharge `hpar` (by the induction over declarations: `recK_agree` for a knot's own records) and `ParamTyLocal` (piece 7's parameter types are runs of the parameter type terms, local by frame locality).

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
