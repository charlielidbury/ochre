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
- `Meaning/Closure.lean`: `closure_mem_of_total'`, `closure_apply'`, `closure_mem_prop'`, and the machinery `mkTelL_telL_some` (goods/`MkFinOk`/`FinalsOk`), `applyTelL_telL_data`, `argsFit_telL`, `Lvl.Fits` for the three levels. `ClosureCE.lean`: why `Steps/FixKnot`'s statements are false.
- `Meaning/DataModel/`: `Program.lean` (a hand model `dmP` of the probe declarations), `Examples`, `Residual`, `Adversarial`, `ParamSolve` (the unifyTyS design point), `ReadMember` (`follow_below_member`, `ReadCoherent`), `Faithful` (`CtxFaithful`, `FieldLevelsFaithful`), `Degenerate`, `Old` (frozen pre-port layer for the old counterexamples), `Probes` (checker verdicts).

## The weakened stage closure (item 1: done, 2026-11-20)

All proved, standard axioms; nothing in this item is stated-only.
- Definitions in `Meaning/Apply1.lean` (so `Run.lean` can use them): `fillTy`/`fillVal` (`Unit`/`()` at a data sort, `True`/`⋆` at sort 0), `weakCod l rk b out`, `refFinals`, `stageFn l ds rk b stage` (label `some 0` above the bound). `Meaning/ClosureStage.lean`: `decArgRank` (the rank, as `decRank`/the run's `rankOf`), `stage_mem`, `stage_apply` (below the bound: the stage's result at the TRUE codomain), `stage_mem_prop` (sort 0), `stage_mem_ref`, `stage_apply_ref`. Generic in `rk`.
- `Meaning/ClosureRef.lean` (the returned-borrow leaf): `RetGood` (returned label `k`; at every future, finals with `k` set to two members of the content type differ unless they are equal), `mkTelL_telL_some_ref` (threads `FinInv` for injectivity; parameter step factored as `finalsOk_step`, `domMembersFrom_cons`), `closure_mem_of_total_ref'`, `closure_apply_ref'` (the forward value's type depends on the arguments: `applyTelL_telL_ref` carries the codomain's code as a Sigma equality).
- `Steps/FixKnotStage.lean` (for the lead to adopt; does not touch `FixKnot.lean`/`Statements.lean`): `OutGood'` (`OutGood` + `RetGood` at a returned borrow + one final per borrow parameter), `PiFits R l ds out P` (what membership consumes, at the argument tuples `P` admits: sort 0 borrow-free with a proposition codomain; data sort `l ≤ 3`, codomain fits the level), `PiCallable` (what a call consumes besides: canonical codomain, domains fit), `MemBelow'` (global = stage closure at the weakened Π; asks `PiFits`/`PiCallable` only below the bound, exactly what its two lemmas consume); proved `memBelow'_mem`, `memBelow'_zero` (no fit asked), `memBelow'_apply`, `closure_mem_of_total_stmt`, `stages_below` (the induction in the run's shape: stage `b` good below `b` ⇒ stage `b+1` good below `b+1`), `knot_member`.
- The run's stages are the weakened closures (lead's decision, done): `Run.lean`'s `.fix` (`bodyAt selfT selfM`; stage `k+1`'s `self` = `closureAt l φ ps (weakCod l rankOf k out) (stageFn l ps rankOf k (stage k))` at `piTyAt l ps (weakCod …)`), mirrored by `RunCongr.fixStage` (its `piT` argument became `dec`); `fixStage_congr` (`closureAt_congr`; above the bound the finals are constant, `refFinals_const`), `AssignCongr.fixStage_congrA`, `RunSubst.fixStage_bodyEq`. The fill (`mkTelFillL`, `closureFillL`, `closureFillAt`, `LeafDefL`, `applyTelL_mkTelFillL`, `leafDef_telL`, `closureFill_apply'`, the `_congr`s) is deleted. Regress hand models rebuilt: `CodeClosures` (`dblBody` calls `self : Res` by `callOf`; `stage_val` now "stage `n` doubles every `x < n`"; the pre-D60 defs kept in `Old`), `DataCodes` (`selfOne`, `selfOne_call`), `DefKnot`.
- Lead's side, not done: `GlobalsOk.ty` must type `K.cur`'s global at the weakened Π; `fix_split` restated to `OutGood'`/`PiFits`, its induction on "stage `b` good below `b`".
- Trap: `telL` matches `out.isRef` in a type; `rcases out with ⟨isRef, cod⟩; subst` before reducing a leaf.

## Number-like parameters in records (item 2, "3b": done 2026-11-20)

- `Sem.lean`: `Entry.small (s : Small)`; `ofSmall`/`ofSmallList` (mutual), `small_ofSmall`. Matches on `Entry`: `Data.entryTy` (`.small _ => err`), `Program.shapeOf` (`=> .leaf PEmpty .err`); others had wildcards.
- `Run.lean` `unifyArgsTyS`: entry `.small sv` against `.place (.var j)` fills `j` with `ofSmall sv`; other argument forms solve nothing (as `Machine.unifyParams`, which solves only at `var j`).
- `Faithful.RecordsFaithful` is a structure: `types` (old clause), `values` (a value parameter `v ∈ paramTy = .t0 A c` is kept `.small v.small` at `paramKey j`; membership is asked so a loose `.ty T` from `ParamsTyped` cannot clash with `types`), `smallOnly` (parameter lists differing only at such value parameters with equal small readings give one record). `smallOnly` for the canonical model is a GUESS (see docs/34 §17.5); its key lemma would be "a member is determined by its small reading and its type" (not proved).
- Records: `Program.singleRec`/`vecRec`/`isZRec`/`fin1Rec` keep the value parameter at `paramKey` (pattern `[(j, 0, [.other])]`); `ParamSolve` records take small readings (`valRec sn`, `opt2Rec sn`), `recOf_ofSmall`, `tag_injective`, `wrap_solves`, `ctor1_runs`, `sw_ctor`/`sw_runs`, `so_ctor`/`so_runs` (successes), `sh_fails` (kept). Adversarial's `fpRec` (FP's level-0 function parameter) does not keep `f` at `paramKey`: not needed by any run; a faithful model would.

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
