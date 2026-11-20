# Data layer: handoff (working file)

For a successor on the data layer (`ochr/docs/34-data-model-existence.md` is the design note; this file is deleted when the lane's work is finished). Only what is not already in docs/34 or in the code's comments. Started 2026-11-20; kept current at each milestone.

## Map (read in this order)

- `Meaning/Sem.lean`: `Small`, `RStep`, `Entry`/`Code0` (one mutual block), `Rec`, `Sem.dat name r c fs`, `DataRead`, `TyM.dataRec?`, `Sem.small`.
- `Meaning/DataLib/{Stages,Carrier,Members}.lean`: the library over a `Sig`. Read `Members.mem_iff` first (membership is the least set of trees closed under the constructors), then `Carrier.mem_iff_meanC`.
- `Meaning/Data.lean`: `DataModel := {covers, sig, recOf, paramTy}`. Read `tyR`, `fieldTyR`, `ctorR`, `mem_tyR`, `tyR_prop`, `shapeTy` (non-canonical shapes give `err`), `fitsOneM_mem`, `paramKey`.
- `Meaning/Levels.lean`: the level facts sort soundness reads.
- `Meaning/Run.lean`: `.ctor` clause (record from written params, else `recOf d []` when parameterless, else hint; `ctorOut`), `unifyTyS`/`unifyArgsTyS` (mutual; reads records at `paramKey`, any depth), `.val` clause (types a value by what it is).
- `Meaning/Places.lean`: `semHeight` = `semRank`, `Sem.step` (named field step only on `.dat` of `g.ty` not named `Nat`), `contentTyS`.
- `Meaning/ClosureStage.lean`, `ClosureRef.lean`, `Steps/FixKnotStage.lean`: the weakened stage closure, the returned-borrow leaf, the knot's statements in the forms that hold (below).
- `Meaning/Closure.lean`: `closure_mem_of_total'`, `closure_apply'`, `closure_mem_prop'`, `closureFill_apply'`, and the machinery `mkTelL_telL_some` (goods/`MkFinOk`/`FinalsOk`), `applyTelL_telL_data`, `argsFit_telL`, `leafDef_telL`, `Lvl.Fits` for the three levels. `ClosureCE.lean`: why `Steps/FixKnot`'s statements are false.
- `Meaning/DataModel/`: `Program.lean` (a hand model `dmP` of the probe declarations), `Examples`, `Residual`, `Adversarial`, `ParamSolve` (the unifyTyS design point), `ReadMember` (`follow_below_member`, `ReadCoherent`), `Faithful` (`CtxFaithful`, `FieldLevelsFaithful`), `Degenerate`, `Old` (frozen pre-port layer for the old counterexamples), `Probes` (checker verdicts).

## The weakened stage closure (item 1: done, 2026-11-20)

All proved, standard axioms; nothing in this item is stated-only.
- `Meaning/ClosureStage.lean`: `decArgRank` (the rank, as `decRank`/the run's `rankOf`), `fillTy`/`fillVal` (`Unit`/`()` at a data sort, `True`/`⋆` at sort 0), `weakCod l rk b out`, `refFinals`, `stageFn l ds rk b stage` (label `some 0` above the bound). `stage_mem`, `stage_apply` (below the bound: the stage's result at the TRUE codomain), `stage_mem_prop` (sort 0), `stage_mem_ref`, `stage_apply_ref`. Generic in `rk`.
- `Meaning/ClosureRef.lean` (the returned-borrow leaf): `RetGood` (returned label `k`; at every future, finals with `k` set to two members of the content type differ unless they are equal), `mkTelL_telL_some_ref` (threads `FinInv` for injectivity; parameter step factored as `finalsOk_step`, `domMembersFrom_cons`), `closure_mem_of_total_ref'`, `closure_apply_ref'` (the forward value's type depends on the arguments: `applyTelL_telL_ref` carries the codomain's code as a Sigma equality).
- `Steps/FixKnotStage.lean` (for the lead to adopt; does not touch `FixKnot.lean`/`Statements.lean`): `OutGood'` (`OutGood` + `RetGood` at a returned borrow + one final per borrow parameter), `PiFits` (sort 0: borrow-free, codomain a proposition; data sort: codomain and domains fit the level, codomain canonical), `MemBelow'` (global = stage closure at the weakened Π); proved `memBelow'_mem`, `memBelow'_zero`, `memBelow'_apply`, `closure_mem_of_total_stmt`, `knot_member`.
- Lead's side, not done: `GlobalsOk.ty` must type `K.cur`'s global at the weakened Π; the run's `.fix` clause binds `self` to the filled closure (`closureFillAt`) at the true type, which is not the weakened closure (rebuild the stages from it, removing the fill, or relate them); `fix_split` restated to `OutGood'`/`PiFits`.
- Trap: `telL` matches `out.isRef` in a type; `rcases out with ⟨isRef, cod⟩; subst` before reducing a leaf.

## Number-like parameters in records (next item 2, "3b")

- `Entry` gains `small (s : Small)` (stays `Type 1`); update every match on `Entry` (`entryTy`, `Program.shapeOf`/`tyEntry`, `entryOf`).
- `recOf d ps` keeps each first-order value parameter at `paramKey j` as `.small ps[j].small` (canonical records; `Program.progRecOf` and `ParamSolve.solveRecOf` too).
- `unifyArgsTyS`: an entry `.small s` against `.place (.var j)` fills `j` with `ofSmall s`, a meaning rebuilt from `s` (`el → el0`, `proof → proof`, `node c fs → .dat "" natRec c …`, `other → err`) with `(ofSmall s).small = s`.
- New faithfulness clause: `recOf d ps` reads a value parameter only through `.small` (two parameter lists with equal small forms give the same record), so the rebuilt parameter gives the same record, which is all `ctorOut` and `fieldTy` use. Core lemmas: no match on `Entry`, so expected untouched.
- Then `ParamSolve.sw_fails`/`so_fails` become runs the model gets right (re-prove as successes); `sh_fails` stays.
- Residual rule for the checker afterwards: do not infer from fields (a) a function or other large parameter, (b) a parameter occurring only at argument positions declared `Type₁` or higher. Everything else (a field's own type at any level, a `Prop`/`Type₀` argument at any depth, a first-order value parameter) is inferred by both.

## Traps

- `lake build`, not `lake env lean` on single files (autoImplicit differs); `lake env lean` is fine for `#print axioms` scratch files.
- Adding cases to `run`'s `.val` match renumbers `runT.eq_N`; the `.prim` catch-all moved 38 → 42. Find the index with `#check @runT.eq_42` in a scratch file and update `RunPresInd`, `AssignCongr`, `RunSubst`, `RunCongr`.
- `rw` cannot rewrite under binders in `match … with | some d => …` (e.g. `meanParams … d …`): state `∀ d, … = …` and `simp only [h]`.
- `applyTelL` on `telL (p :: ps)` does not unfold by `simp`; `rw [show (telL …).2 = .param … from rfl] at h` then `erw [applyTelL.eq_3] at h` works.
- Anonymous constructors for `FitsM` fail when the `Fin` proof is still a metavariable: `refine mem_intro … ⟨1, by decide⟩ _ ?_` then `exact ⟨…⟩`.
- A `TyM` function with nested overlapping patterns (`.t1 _ (.lift _ (.data …))`) makes `simp` and `cases h` fail on overlap obligations; define it through per-code helpers (`Code0.dataCode?` etc.).
- `Small` has no `DecidableEq`; define records by pattern matching on keys, not `if k = …`.
- Numerals at a carrier type `((L.codeOf T).1)` need `by exact (1 : Nat)`.
- Shell: backticks in `git commit -m "…"` run as commands; use `-F -` with a quoted heredoc. `pgrep -f` self-matches; `lake exe tests` with a `dbg_trace` is very slow (21 timed runs per program); the build replays elaboration traces, which cover every example once.
- Field-type terms number parameters first (`var 0` is the last parameter), then fields (`Machine.fieldTele`).

## Stated, unproved (with a guess)

- `Consistency.exists_dataModel` (covers + `DataFaithful`): true for a generic canonical signature built from the declarations' field-type runs (records by the run along paths; §12's closure fact). Large; the main remaining obligation.
- `DataModel/Faithful.FieldLevelsFaithful` (not wired in): true by the case analysis in its docstring.
- `ReadCoherent` (not wired in): true for the canonical model on records reachable from the program's stored types; would become a fourth part of `CtxFaithful` if anything consumes it.
- `Steps/FixKnot.closure_mem_of_total`, `closure_apply`: false as stated (`ClosureCE`); the forms that hold are `Steps/FixKnotStage.lean`'s (proved).
- `Steps/FixKnot.recDecreases`: true given (I7) (no data-typed field under a `Prop` refinement); a leaf about the checker's `strictSubterms` against meanings.
