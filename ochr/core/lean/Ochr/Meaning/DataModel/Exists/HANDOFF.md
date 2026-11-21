# Existence of the data model: handoff (working file)

Lane: prove `Assembly.exists_dataModel` (`Meaning/Consistency.lean`). Branch `spine-exists2`, worktree `/home/charlielidbury/repos/ochre-exists2` (the predecessor's `ochre-exists`/`spine-exists` is retired). Durable record: `ochr/docs/34-data-model-existence.md` §18 (read it first) and docs/31 D110. This file holds what only a successor needs; delete it when the lane's work is merged. Last updated 2026-11-21 by `exists2` at 0234e634 and the commit after.

## State

- The statement is repaired ((M-a) bc86f861, (S) d4b7a5ee) and its bundles are inhabited, kernel-checked, in the default build: `PreludeModel.lean` (the library), `Step2.lean` (library + Bool, List, EvT, Rose, TF, Ev, Q). `PropNestCE.lean` (piece 4 false for `Prop`-sorted declarations nested at a `Prop` parameter) is in the default build too. `RecordsCE.lean` is a record outside the build.
- `RunLemmas.lean`: the run of each field-type term form, under every run context and every decision table: `runT_var`, `runT_sort`, `runT_nat`, `runT_zero`, `runT_tind` (+ `runParams_spec`, `runT_tind0/1/2`), `runT_eq`, `runT_call_const` (+ `runArgs_one`, `callOf_val`: a call's value depends on callee and argument values only), `erasedIf_val`, `teleFrame_split`, `runT_teleFrame_param`, `runT_teleFrame_field`.
- `Decomposition.lean`: the nine pieces with corrected beliefs (4 data-sorted only; 5 all `Prop`-sorted truth-first with monotonicity; 6 repaired; 3 with step 2's findings). Only `runT_congrDM` (piece 1) is stated. Nothing of the general proof is proved.

## Next, in order (riskiest first)

1. **Frame locality, uniformly with pieces 1 and 2**: one congruence for the run's mutual block, two run contexts and two states related on what the term reaches (the declarations it names or navigates, the model's records and parameter types there, the frame's variables it mentions; elsewhere the states hold whole members of the same types). Template: `RunCongr.run_congr` (1634 lines), `AssignCongr.lean` (519). Points to check first, since they read the whole state: `movedPlaces`/`joinDrop` (moved-ness of every binding), `lentOk`/`StateOk` (every position an open member), `SM.guarded (ContentOk …)`, `typedFuture`, the decisions' `scopeOf` (readings only), `blockCaps`.
2. ~~`mem_small_inj`~~ DONE (`Piece3.lean`, default build): `memTy_small_inj` (two members of one level-0 type with one small reading are equal, any model), `fieldTy_t0`, `fields_small_inj`, `projIdx_get`/`projIdx_take`, and `index_fields_eq`: typed earlier fields whose PROJECTED small readings agree agree at every index field. So a canonical frame rebuilt from a record key differs from the actual frame only at earlier fields that are no index, which is exactly what frame locality (1) must absorb.
3. **The interpreter and its agreement** (§18.4): syntactic along the `.tind` spine, the run's result elsewhere at a canonical frame; agreement by induction on the term using `RunLemmas` and 1–2.
4. **Stored global meanings well behaved** (§18.3 point 3): from the strict `.fix` clause (`SM.strictS` of the closure at `piT`), `app_mem'`, and `fix_split`'s first claim (the stored type's code is the closure's; the lead's leaf).
5. **Piece 4** (guardedness, data-sorted) by structural induction on the spine; **piece 5** (truth-first + monotonicity of earlier declarations' membership in nestable `Prop` parameters); 6, 7, the assembly. 8a/8b are with the lead.

## Idioms and traps (beyond the predecessor's, in 1765a998's version of this file)

- A run lemma's hypothesis `hr : run K … = some (r, s')`: `unfold run at hr` first (`run` is an `abbrev`; `rw` does not see through it).
- `runT` of a term whose clause is `do match … with` unfolds to a match applied to the state: `split at hr` fails ("Failed to find match-expression discriminants"); `revert hr; cases h : <discriminant>` instead.
- `rw [h] at hr` where `h : (0 : Nat) = …` rewrites EVERY `0`, constructor indices included: pass the variable index with its equation (`runT_teleFrame_param … (hvj : v = ps.length - 1 - j)`).
- To work at a concrete context, `cases K with | mk dm Γ C D Δ Λ cur => dsimp only at hdm hΓ; subst hdm hΓ`.
- `find?` by name on a concrete declaration list is `rfl`.
- Python edits of Lean files: never put Lean text containing `'''` (e.g. `s'''`) in a Python triple-quoted string; write it to a scratch file with a quoted heredoc and read it.
- An existential from `List.getElem?_eq_some_iff.1` blocks `omega`: `obtain ⟨hj, -⟩ := …` first.
