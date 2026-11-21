# Existence of the data model: handoff (working file)

Lane: prove `Assembly.exists_dataModel` (`Meaning/Consistency.lean`). Branch `spine-exists3`, worktree `/home/charlielidbury/repos/ochre-exists3` (exists2's `spine-exists2` is retired). Durable record: `ochr/docs/34-data-model-existence.md` §18 (read it first; §18.5 is frame locality) and docs/31 D110. This file holds what only a successor needs; delete it when the lane's work is merged. Last updated 2026-11-21 by `exists3` (its last commit), on `spine` 217dd501.

## exists3's step 1: frame locality (read this first)

`General.runT_frameLocal` was FALSE (docs/34 §18.5: three counts, the first kernel-checked in `FrameLocalCE.lean`). Its restatement is `FrameLocal/Run.lean`'s `runT_qset`, an equation: `runT … t (qset Q β' s) = (runT … t s).map (qset Q β')`. Files, in dependency order (all but `Run.lean` in the default build, no `sorry`):
- `FrameLocal/Vars.lean`: `placeOccs_add` (occurrences under binders), `mem_freeVars`, `freeVars_sub` (a subterm's free variables under `n` binders).
- `FrameLocal/Qset.lean`: the transform `qset Q β` and its algebra against every state primitive.
- `FrameLocal/Prims.lean`: `Comm Q β x s` (`x (qset Q β s) = qmap Q β (x s)`), the SM combinators (`comm_bind`, `comm_erasedIf`, `comm_guarded`, …), and every run primitive and strict test; `Pre` is what a primitive needs.
- `FrameLocal/Join.lean`: folds over decision-given places under `Twin` (both families' `Pre`, fixed by `qset Q β`, the start's layout): join drop, [Entry], `matchEntry_qset`, `capStep_qset`, `obsEnd_qset`.
- `FrameLocal/Setup.lean`: `DecLocal`, `VarsAvoid`, `Adm`; `Adm.self`, `Adm.next`, `fix_of_comm` (the invariant read off the equation at `β' := β`), `VarsAvoid.sub`/`of_envLe`.
- `FrameLocal/Run.lean` (OUTSIDE the build: one catch-all `sorry`): the mutual induction. Proved clauses: `.place`, `.const`, `.sort`, `.nat`, `.unit`, `.zero`, `.tt`, `.val`, `.succ`, `.ref`, `.seq` (the template for a clause with a continuation: `Adm.after` gives the next state's `Adm`, `RInv` and layout). Open: `.borrow`, `.assign`, `.letIn`, `.matchNat`, `.matchInd`, `.tind`, `.ctor`, `.pi`, `.fix`, `.call`, `.eq`, `.cong`, `.prim` (symm/trans/rewrite/rewriteR/J/clone/peek/inplace), `.id`, `.ascribe`, and the companions over lists (`runArm`, `runParams`, `runFields`, `runArgs`, `runBinds`) as further members of the mutual block.

Recipes for the open clauses:
- Every clause: `unfold Comm; rw [runT]; dsimp only; rw [hA.scope]` (one `rw [runT]` rewrites both sides), then the combinators.
- A place of the term: `rAvoid_of_vars hV (root mem)`; write `root_mem_*` lemmas like `root_mem_place` from `Term.placeOccs`.
- After a primitive at `s` (not a subterm run), the next state's fix comes from the same primitive's lemma at `β` (instantiate `β' := β`; `qset Q β s = s`), as in `Twin.step`.
- `.letIn`/`.pi`/`.fix` bind variables: needs `varPos (pushBind s b) (i+1) = s.varPos i` and `varPos … 0` the new binding (not yet written; `pushBind_getLast` is in `Qset.lean`), with `freeVars_sub` at `n = 1` (let) or `n = ds.length (+1)` (Π, `fix`).
- `.fix`: use `RunCongr.run_fix_def`/`fixBodyAt`/`fixG` (exists) and `qset_under` (Q moves up: `Qup`, `βup`); the body's IH is at `Qup Q`; `rinv_under`, `formInv_init`, `foldl_fixStep_inv` give the body's `RInv`. The closure's function is equal on both sides by funext over the body's IH (both directions are the one equation). Captures: `capStep_qset` needs `hcap`.
- `.id`: `observation_eq` + `obsEnd_qset`; the proposition is equal by `propext`: the two observations differ from `s`'s only at `Q`, where each side reads its own constant (the lists agree componentwise off `Q`).
- `.pi`: `runBinds` at `extendBy s bs acc` (pushes beyond `Q`); `rinv_extendBy` exists.

Open questions for the lead (asked 2026-11-21, carry on meanwhile): (1) `capOrder`'s `Array.qsort` blocks `hcap`; proposed `List.mergeSort`. (2) `DecLocal` for the chain's decisions is an obligation on the checker's static analyses (`jdMoves`, `typeState`, `staticBlockCaps`; `invalidated` is empty there).

Then the plan below continues at step 2 (`globals_typed`).

## State

- The statement is repaired ((M-a) bc86f861, (S) d4b7a5ee) and its bundles are inhabited, kernel-checked, in the default build: `PreludeModel.lean` (the library), `Step2.lean` (library + Bool, List, EvT, Rose, TF, Ev, Q). `PropNestCE.lean` (piece 4 false for `Prop`-sorted declarations nested at a `Prop` parameter) is in the default build too. `RecordsCE.lean` is a record outside the build.
- `RunLemmas.lean`: the run of each field-type term form, under every run context and every decision table: `runT_var`, `runT_sort`, `runT_nat`, `runT_zero`, `runT_tind` (+ `runParams_spec`, `runT_tind0/1/2`), `runT_eq`, `runT_call_const` (+ `runArgs_one`, `callOf_val`: a call's value depends on callee and argument values only), `erasedIf_val`, `teleFrame_split`, `runT_teleFrame_param`, `runT_teleFrame_field`.
- `Piece3.lean` (default build): `memTy_small_inj` (two members of one level-0 type with one small reading are equal, any model), `fieldTy_t0`, `fields_small_inj`, `projIdx_get`/`projIdx_take`, `index_fields_eq` (typed earlier fields with equal PROJECTED small readings agree at every index field).
- `Probes.lean`: `DMXBoundary`, asserted: the checker admits in a field type only calls of globals of codomain `Prop` or `Type₀`; an equation side calling a function, a type function of the declaration's own type parameter, one that is a function type at some instances, and a `Prop`-valued one are accepted, and each has a faithful record by the interpreter's `.ty` case (the run's result); none is a counterexample.
- `Decomposition.lean`: the nine pieces with corrected beliefs (4 data-sorted only; 5 all `Prop`-sorted truth-first with monotonicity; 6 repaired; 3 with step 2's findings). Only `runT_congrDM` (piece 1) is stated. Nothing of the general proof is proved.

## Next, in order (riskiest first)

The statements are written, with `sorry`, in `General.lean` (outside the default build; build it with
`lake build Ochr.Meaning.DataModel.Exists.General`). Each docstring says what it rests on, how it was
attacked, and, for three of them, how the first version was false or vacuous. Prove them in this order:

1. **`runT_frameLocal`** (frame locality; the core of piece 3). An induction over the run's mutual
   block in the style of `RunCongr.run_congr`, with `DiffAt` preserved by every clause. Make it
   uniform with pieces 1 and 2 (two run contexts agreeing on the declarations the term reaches) if the
   relation stays manageable; otherwise prove the frame half alone first. The whole-state scans were
   read and none reads a value at a position the term does not mention (docstring).
2. **`globals_typed`** (finding 2's obligation): from the strict `.fix` clause (`SM.strictS` of the
   closure at the function type it builds), `app_mem'`, and `Consistency.fix_split`'s first claim (the
   stored type's code is the closure's; the lead's leaf, open). Restricted to globals of codomain
   `Prop` or `Type₀`, the only ones a field type calls (`Probes.DMXBoundary`, asserted).
3. **`knot_exists`** (pieces 3 and 4, data-sorted): the interpreter is syntactic along the `.tind`
   spine (a parameter `var j` is `parTy`; `M(ā)` is `FTy.data M` at `M`'s record at the arguments, `d`'s
   own occurrences through the knot's record function, value arguments by the run, read small) and
   the run's result elsewhere, at the canonical frame (parameters, and earlier fields chosen among
   those fitting the knot's shapes with the key's projected small readings: `Piece3.index_fields_eq`
   makes the choice agree with the actual fields at every index field, `runT_frameLocal` absorbs the
   rest). Agreement by induction on the term with `RunLemmas`; guardedness by the same induction
   (`SemAgree`, `recK_agree` of earlier records: hypothesis `hpar`).
4. **`mono_prop`, `truth_exists`** (piece 5). Replace `mono_prop`'s `hcanon` by the construction's own
   predicate once 3 defines the canonical records.
5. Pieces 6, 7, and the assembly 9 (by induction on the items, the model built declaration by
   declaration with `setRec`, earlier globals' meanings read through 1 and 2); 8a/8b with the lead.

What step 2 (`Step2.lean`) did not exercise, and the general proof must: `EvT`'s meaning as
`defMeaning` computes it (a closure with the same behaviour stood in), the monotonicity induction (the
two truths were computed outright), an equation side calling a function (`S(S(m))`, accepted: its
field type is the run's result, the interpreter's `.ty` case), and frame locality (its one non-index
earlier field was a proof).

## Idioms and traps (beyond the predecessor's, in 1765a998's version of this file)

- A run lemma's hypothesis `hr : run K … = some (r, s')`: `unfold run at hr` first (`run` is an `abbrev`; `rw` does not see through it).
- `runT` of a term whose clause is `do match … with` unfolds to a match applied to the state: `split at hr` fails ("Failed to find match-expression discriminants"); `revert hr; cases h : <discriminant>` instead.
- `rw [h] at hr` where `h : (0 : Nat) = …` rewrites EVERY `0`, constructor indices included: pass the variable index with its equation (`runT_teleFrame_param … (hvj : v = ps.length - 1 - j)`).
- To work at a concrete context, `cases K with | mk dm Γ C D Δ Λ cur => dsimp only at hdm hΓ; subst hdm hΓ`.
- `find?` by name on a concrete declaration list is `rfl`.
- Python edits of Lean files: never put Lean text containing `'''` (e.g. `s'''`) in a Python triple-quoted string; write it to a scratch file with a quoted heredoc and read it.
- An existential from `List.getElem?_eq_some_iff.1` blocks `omega`: `obtain ⟨hj, -⟩ := …` first.
