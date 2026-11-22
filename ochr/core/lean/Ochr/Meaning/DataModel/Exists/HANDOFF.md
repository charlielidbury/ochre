# Existence of the data model: handoff (working file)

Lane: prove `Assembly.exists_dataModel` (`Meaning/Consistency.lean`). Branch `spine-exists5`, worktree `/home/charlielidbury/repos/ochre-exists3` (it carries the proof line through f6c59f58). Durable record: `ochr/docs/34-data-model-existence.md` §18 (§18.5 frame locality, §18.6 the knot). This file holds what only a successor needs; delete it when the lane's work is merged. Last updated 2026-11-22 by `exists5`.

## Rulings requested from the lead (read the answers first)

1. Checker rules from Lean's kernel (docs/34 §18.6): **(B)** a variable mentions what its declared type mentions (no equation side, call argument or value argument in a field type reads an earlier field whose type mentions the declaration or a varying parameter; a parameter read so is not nestable); **(A)** a data-sorted declaration does not occur inside an argument at a `Prop` parameter. `Knot.Spine` states the field-type grammar with them (plus (B2): a value argument's parameter type mentions no varying earlier argument, which typing gives). If (B) is refused: `hpar` must compare value parameters by small readings and a relational lemma over the run is needed (runs under different records agree where both are defined); `LD`, `W`/`UW` in §18.6 are the cases.
2. **`teleFrame` (Faithful.lean) should type the not-yet-bound fields `err`**, as the checker's `fieldTele` binds them (`pushBind name none .bot`). Today the field being typed carries its own type read from the knot's record, which makes the canonical frame self-referential, and frame locality cannot swap a `moved` binding (not `Good`: not whole). Proposed: the field binding's type `if j < e.length then dm.fieldTy d ps c j (e.take j) else TyM.err`. `Knot.canFrame` already uses `err` there. Fallback if refused: extend `runT_qset` to `Q` positions holding `moved` on both sides (the join-drop and capture cases are where it bites: moved places are what the join drops).

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

## Next: `SteadyAt`, the one fact `knotK_agree` assumes

`Knot/Agree.knotK_agree` (default build, standard axioms) is `knot_exists`'s conclusion for the witness `knotK`, assuming `SteadyAt K ρ d R*` (`R* := recK (knotK …)`): the run of a steady node `t` of a field type `FT` (free variables among `FT`'s) in the actual frame `A := teleFrame (setRec K.dm d R*) K.D d ps c e` gives `valOf K ρ F* h t`, its value under `K` at the canonical frame `F* := canFrame K d ps c i es tyOf*`. So `knot_exists` = `knotK` + `knotK_agree` + a proof of `SteadyAt`. The plan for `SteadyAt` (`K* := {K with dm := setRec K.dm d R*}`):
1. Frames `A = stateOf 0 bsA`, `F* = stateOf 0 bsF` equal off `X` = {fields `j < i` that vary or are no index} ∪ {parameters that vary}. Done: `fieldTy_knot` (the actual type at an earlier field is `tyOf* j`), `rebuild_eq` (the rebuilt member is `e[j]`; `es[j] = e[j].small` at an index field by `Piece3.projIdx_get`). Moved fields `j ≥ i`: equal only after the `teleFrame` repair (ruling 2). Non-varying parameters: the same expression (`canFrame`'s `if j < ps.length`).
2. `Good` at `X` under `K*`: `e[j]` via `Data.fitsOneM_mem` (needs `LeafOk` at the knot's leaves: a leaf comes from a steady node's `.ty T`, and `GlobalsTyped` gives a call's result a code of level 0 or 1, so never a `Prop`-sorted data code over its own carrier; a data-sorted one over its own carrier is not a leaf, `dataView`) and `Strict.mem_whole K.dm.read_wholeFields`; `ps[j]` the same; the dummies `0 : Nat`. `pmem_of_mem`.
3. `runT_stateOf_swap` (needs `DecLocal`, label-free globals) with `X`; free variables of `t` avoid `X`: they do not vary (`Steady`), and a field `FT` mentions is an index field (`IndDecl.indexFields`, `fieldRefs`).
4. **Model congruence** for `t` avoiding `d.name` (`Knot.Avoids`): `runT K* t F* = runT K t F*`. The run reads `recOf` only at a name it finds (`.tind`, `.ctor`, matches, `meanV` of `.val`); `read`/`car`/`tyR` are the universal signature's. Template `AssignCongr.runT_congrA` (516 lines). This is piece 1/2 of `Decomposition.lean` in a narrowed form.

Then: `mono_prop`, `truth_exists` (piece 5; attack first, especially the monotonicity induction), `globals_typed`, `DecAt` threading (when a consumer needs it; recipe below), pieces 6, 7, assembly. The knot's `pEntry` is `pEntryTy` (what `Step2` used); piece 6 (records' parameter clauses) may need value parameters' entries read small instead.

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
