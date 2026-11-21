# The strict reference run and the fundamental lemma: handoff

Lane `spine-model` (worktree `ochre-model`), 2026-11-20 to 2026-11-21. The prototype (strictness inside the run, option (a)), the whole lemma and the port were done in one context; this file is written so a successor can continue alone. The line is the latest commit on `spine-model` that touches this file (ruling 3 is `9a3cf614`; the port `a24fc76f`). Second agent (2026-11-21, "Model 2"): the strict type formers ("well typed inside", below) and the finding that `MemReads` holds in no model (`MemReadsCE.lean`).

State: there is ONE reference run, strict: `Run.lean`'s `runT`. The fundamental lemma `fund_all` holds for every clause of it, modulo three named guesses at field paths (the dependent-values area, below). Every core lemma (`RunPresInd`, `RunCongr`, `AssignCongr`, `RunSubst`, `RunSubstAbs`, `HintIndep`, `Lemmas`, `SubstAbs`) and every concrete run (`Regress/`, `Attack/`, `DataModel/`) builds on `propext`, `Classical.choice`, `Quot.sound`. Nothing under `Steps/` was changed by this lane. Build: `cd ochr/core/lean && taskset -c 0-14 lake build OchrMeaning` (a `Run.lean` change rebuilds every module of the model).

## Files (read in this order)

- `Run.lean` (not here): the strict run. Strict points marked `STRICT` at their sites. Helpers: `SM.strictS`, `SM.erasedIf` (C1), `SM.anyArm`/`SM.ranProof` (ruling 3), `strictVal`, `labTyOk`, `paramsOk`, `refsOf`/`refTysOf`/`refLabelsOf`, `BorrowArgsTyped`, `placeTy`, `callOfL`/`callOf` (`moved` in the undecodable branch).
- `Good.lean`: `NoData`, `GoodRes`, `PMem`, `GoodVal`, `TypedF`, `ReadOk` (THE READ CLAUSE), `SGood`, `LabOk`, `StatePres`, `FundAt`, `Fund`; `EndWhole` (the checker's rule, a named fact the lemma does not use).
- `Ops.lean`: `MemReads` (the data layer's read lemma, a hypothesis); whole writes (`sgood_setAt_const`, `sgood_setAt_pmem`), ends (`endAt_sgood`), [Access] (`access_sgood`).
- `Call.lean`: a call's result is a member (`callOf_res_mem`, from `ApplyMem.app_mem'`/`app_mem_ref`).
- `OpsCall.lean`: a call keeps the invariant (`callOfS_sgood`; the `S` in lemma names is historical, they are about `callOf`), with `applyTelL_finals`, `typed_transport`, `sgood_mapVals_fix`, `sgood_park_fix`.
- `OpsPlace.lean`: `sgood_transfer`, `sgood_pushBindShaped`, `sgood_letDrop`, `readPlace_fund_all`, `borrowPlace_fund`, `assignAt_sgood`; the three FIELD-PATH GUESSES.
- `Comb.lean`: `FundCtx`, `Term.valsOk`, `fund_strictS`, `fund_erasedS`, `erasedS_proof_some`, `erasedS_clause_true`.
- `Simple.lean`, `Clauses.lean`, `Match.lean`, `Clauses2.lean`: one lemma per clause (`fund_*`); `fund_runArmS`, `fund_matchInd` (with ruling 3's branch), `fund_join`, `HeldSame`.
- `Fund.lean`: `fund_prim` and **`fund_all`** (mutual with `fund_list`, `fund_arms`).
- `MemReadsCE.lean`: `MemReads` holds in no model (below).
- `Typed.lean`: "well typed inside". `HWT K ρ φ h T v` (the trial's predicate adapted: the meaning read at an explicit hint `h`; head condition `Fit`, `moved` or a member or a type value with a level at `err`; an `Eq`'s type at `err` by its level; a constructor value at its declaration's data code `T.dataCode?`, its fields at their field types, its recorded parameters not asked; code excepted: captures typed, code not). `hwt_of_fit` (proved, standard axioms): a value whose meaning fits is `HWT`, given `ReadCoherent`, coherent parameter types, `TyIn` of the type, and `CohVal` (no constructor value of a `Prop` declaration; coherent types where an `Eq`'s sides and captures are read): the trial's exceptions (a) code, (b) `Prop` constructors, (c) data codes off the program's declarations. `hwt_of_run`: composed with `fund_all`. `eq_types_not_hwt`: `Eq(Nat, Nat, Nat)` is `HWT` at no type.
- `Runs.lean`: kernel-checked runs (`zero_unit_none`, `let_zero_unit_none`, `succ_nat_runs`, `refl_runs`, `refl_eq_runs`, `refl_neq_none`, `sort_two_runs`).

## FOR THE SIMULATION SIDE: what the lemma asks and gives (read exactly this)

**"The strict run succeeds"** is `runT K ρ φ tl hint t s = some (r, s')` (`run K ρ φ hint t = runT K ρ φ false hint t`). Failure is `none`; strictness only adds failures.

**The strict clauses, and the type each tests at** (`SM.strictS R x`: the clause fails unless its result's value is a member, `∈ₛ[K.dm.read]`, of the result's type):
- `.ascribe u A`: the value at the annotation's code `⟦A⟧.asTy`, and a label on the result must record that type (`labTyOk`).
- `.succ u`: the value at `Nat`.
- `.ctor`: the value `ctorOut` builds at the type it gives (`tyR d r`), and written parameters members of their parameter types (`paramsOk`, `dm.paramTy`).
- `.fix`: the closure at its function type (`piTyAt`); a closure whose body fails somewhere is `err` and fails.
- `.borrow p`: the content at the place's type (so the new label's record `heldMem` is a member). `&A` (`.ref`): `A` at `Type₀`.
- `.assign p u`: the value written at the place's type AT THE WRITE (`placeTy`, read on a copy after the right-hand side ran), and the value's label recording that type (`labTyOk`).
- `.call f args`: `BorrowArgsTyped`: each argument at a borrow parameter carries a LIVE label whose record `heldTy` is the parameter's content type (a borrow is invariant).
- `.val v` (`strictVal`): a constructor value at the type its record names, failing outright where its meaning is `err`; a closure or sealed program fails where its meaning is `err`; any other value is typed as before (number `Nat`, unknown `Δ σ`, global its type, loan of a function its declared type, else the hint).
- The equality rules (`cong`, `symm`, `trans`, `rewrite`, `rewriteR`): their premises run, each on a copy, and must succeed; the result is `⋆` at `prop True`.
- "Well typed inside" (the type formers; definitions in `Value.lean` and `Run.lean`): `.eq A a b` and `.id A t u` fail unless `EqOk` (the type term's meaning has a level, each side `moved` or a member of the type; a level, not a universe: the orchestrator on the trial's advice, so `Eq(Type₁, X, Y)` is admitted); `.tind n args` unless `paramsOk` (each argument a member of its parameter type at the earlier ones); `.pi` unless `PiOk` (every domain and the codomain have a LEVEL at every tuple of arguments that are members of the earlier domains). The value meanings mirror them (`Value.mean`/`meanV`): `.tEq` and `.tInd` mean `ty err` unless `EqOk`/`paramsOk`; `.clo` means `err` and `.tPi` `ty err` unless `CapsOk` (each capture a member of its recorded type). Not mirrored: `codeMeaning.paramTy` (a deferred type of a Π-closure reads its frame without `CapsOk`), `.fix` (a closure's own function type is not tested by `PiOk`), a constructor VALUE's recorded parameters (`meanV .ind`; the trial's conversion proof does not use them, `alike_ind`).
Not strict: reads, ends.

**What an erased term returns** (`SM.erasedIf`, C1; `fl = K.D.flags (scopeOf s) t`): a proof (`fl.2`) runs its clause on a copy of the state; where the clause ran to `⋆` the term is `⋆` at `prop True`, the state as it was, no label; anything else fails. A statement (`fl.1`) runs on a copy (`SM.stmtIf`). `erasedS_clause_true`: where an erased proof runs, its CLAUSE ran to `⋆` at a type `T` with `⋆ ∈ₛ T` or `T = err`; that `T` is what the simulation relates to the checker's proposition. An erased match on a proof with other than one arm (ruling 3, `SM.anyArm`): the arms run in order, each on a copy, and the match is the first arm that runs to a proof, at that arm's type, the state as it was, no label; it fails where none runs (no arms: an empty proposition).

**The lemma** (`Fund.lean`): `fund_all (hc : FundCtx K) : ∀ t, t.valsOk (fun v => Fund K ρ φ (.val v)) → Fund K ρ φ t`, `Fund K ρ φ t := ∀ tl hint, FundAt K.dm K.Γ φ (runT K ρ φ tl hint t)`, and
`FundAt dm Γ φ x := ∀ s s' r, SGood dm Γ φ s → x s = some (r, s') → GoodRes dm.read r ∧ LabOk dm s' r ∧ LoU s' r.2.label ∧ SGood dm Γ φ s'`.
- `GoodRes R r := r.1 ∈ₛ[R] r.2.m ∨ r.1 = .moved ∨ (r.2.m = TyM.err ∧ NoData r.1)`, `NoData v := (∃ T, v = .ty T) ∨ v = .proof`. THE ERROR-TYPE ESCAPE: a type value or `⋆` may come out at `err` (a type the bounded model has no universe for, `Type₁` as a value; a field of `⋆`, which a read types `err`); a value with data never does.
- `LabOk dm s' r`: a result label records the result's type and a member (`heldTy`, `heldMem`). `LoU`: the label is live in `s'` or read nowhere, and below the counter.
- Consequence for proofs: a successful erased proof's clause ran to `⋆` at a true proposition (or `err`).

**`SGood dm Γ φ s`** (`Good.lean`), stated at every TYPED future `ψ` (`TypedF`: `ψ` agrees with `φ` off the live labels and gives each live label a partly moved member, `PMem`, of its recorded `heldTy`):
- `bind`: each existing binding's value is `GoodVal`: `pmem` of its stored type, or no data at `err`.
- `holder`: a position holding label `l` reads a `PMem` of `heldTy l`.
- `held`: each live label's record `heldMem` is a member of `heldTy`.
- `holderTy`: a binding holding `l` is stored at `heldTy l`.
- `acyc`: `RInv (fun _ => True)` (the label order). `fresh`: `ReadsBelow`.
- `read` (`ReadOk`): at every typed future, every whole value a read path reaches from a binding is a member of the type the read gives it, or no data at `err`.

**`FundCtx K`** (`Comb.lean`), the context the simulation supplies:
1. `reads : MemReads K.dm K.Γ`: a whole read path of a partly moved member gives a member of the type the read gives it (from `ReadMember.follow_below_member` under `ReadCoherent`; plus: a whole value below a member is that member).
2. `globals : ∀ n, GoodRes K.dm.read (K.C.global n) ∧ (K.C.global n).2.label = none`: `GlobalsOk.mem` for earlier definitions; for the one being checked (`K.cur`), `MemBelow`'s stage closure at the weakened function type (`ClosureStage.stage_mem`); the connecting lemma is not written.
3. `sorts : ∀ d ∈ K.Γ, d.sort ≠ 2`: no data declaration at `Type₁` (the model reads every declaration as a `Type₀` code).
4. Whole fields of the reading: automatic (`DataModel.read_wholeFields`).
5. Term precondition `t.valsOk (fun v => Fund K ρ φ (.val v))`: an embedded unknown `σ` is good iff `ρ σ ∈ Δ σ` (`TypedAssignment`/`DeltaOk`); an embedded loan `ℓ` iff `φ ℓ` is a member of the type the `.val` clause gives it (the future typed at free loans); closures, sealed programs, globals by their own runs; a value typed by the hint needs the hint to be its type where it sits (a code invariant the simulation owns).

**Where `SGood` is established.** `SGood` asks about futures whose live labels end at PARTLY MOVED members, more than the checker's invariant speaks of. (i) From the checker's invariant only at the start of a definition's body and at the empty state, where no place is lent, so the futures do not matter; the borrow parameters' records (`heldTy`, `heldMem`) must be set there (the relation's records clause). (ii) Then carried by the lemma step by step: every reference state is produced by a run of the strict run; statements and copies return their start state; split, η-refinement, generalisation and [Repack] change only the checker's state. (iii) NOT covered by the lemma, needing model-side lemmas only: the in-place call (`CallRef.runCallRef`: `callFrame`, the body's run, `popCallFrame`, `SState.endInto`) and a closure body's frame (`.fix`'s `bodyAt`, which now records `heldTy` and `heldMem`). Not yet written (Next 2).

## Decisions in force (orchestrator, 2026-11-21)

1. Equality rules: premises on copies, `⋆` at `prop True`. Generalised: EVERY erased proof is `⋆` at `prop True`; the clause's own type is checked by the lemma at the clause.
2. Borrow invariance at calls: `BorrowArgsTyped`, with "the label is live".
3. Partly moved futures; `moved` in `callOfL`'s undecodable branch. The checker's "no end over moved-out content" is the named fact `EndWhole`.
4. Reads at field paths: an invariant (`ReadOk`), not strict reads (to be revisited by the dependent-values step: whole reads become strict).
5. Embedded values: the precondition `Term.valsOk`.
6. Strict `.fix`. 7. Nothing new in the model state.
Port rulings (confirmed): `strictVal` fails outright on a constructor value meaning `err` (hint independence: `HintIndep`); `SubstAbs.absFill_shape` takes `hmem` (the filler means a member of `Δ σ`).
Ruling 3 (erased match on a proof): the ruling preferred "succeeds iff some constructor's fields hold and EVERY such arm runs". Built instead: the first arm that runs (`SM.anyArm`), because the preferred form needs the scrutinee's record and the run has none: a proof's value is `⋆`, and a proposition-sorted declaration's type is `prop (Nonempty car)` (`Data.tyR`), from which no record is recoverable (at a true proposition it is `prop True`). Sound by the lemma at the arm (arms bind nothing: a field of the scrutinee reads `⋆` at `err`, so the arm starts from the same good state). Kernel records: `Regress/Adequacy_flipped.erased_match_proof_fails` (what was wrong at `a24fc76f`, and what is left) and `erased_match_proof_runs` (OrComm's shape).

## The dependent values: the three guesses and where the answer goes

The guesses (`OpsPlace.lean`, `sorry`): `setContent_field_moved_sgood` (moving out of a field), `borrowPlace_field_sgood` (lending a field), `setContent_field_sgood` (assigning a field). Each may fail as stated: a later dependent field's read type (its declaration at the CURRENT earlier fields, `Places.contentTyS`) changes while its value does not (`⊥` reads small as `.other`; a lender's field is a different member at each typed future; an index rewritten under an old leaf). `fund_join` reaches them through the join's drop (`⊥` written at field paths), so `fund_matchInd` shows `sorryAx` too.

They are answered by the dependent-values work (branch `spine-dep`, `Meaning/Dep/HANDOFF.md`; do not start it before the checker change D112 is on `main` and that lane has written the exact clauses). As this lane sees where each part goes:
- Checker D112 (route B on `spine-dep`): a dependent field is a TREE field (a data inductive at every instance) or a LEAF field; leaf fields are invalidated by `openWrite` like proofs, never strong-updated, never typed by content; [Entry] invalidates for `&` captures on every path.
- Mirrored invalidation, in `Run.lean`: after `setContent` at a field path in `assignAt` (the `.assign` clause), in `borrowPlace` (the `.borrow` clause, after the label's write), and in `matchEntry`/`entryAccess` for `&` captures: for each prefix `q.g` of the path with `g` an index field, write `⊥` into every dependent proof and LEAF field of `q` whose type mentions `g` (`setContent … .moved`, pointwise in the future). Proofs: the three guesses become provable, since the fields whose read type changed now hold `⊥` (a partly moved member of anything); the core lemmas need the new operation's congruence (it reads no future: `RunCongr`/`AssignCongr`/`RunSubst*` by the same pattern as `setContent`), `RunPresInd` its `RInv`/`EnvLe` facts.
- Open membership in `SGood`: replace `PMem`/`pmem` in `bind`, `holder` and `TypedF`, and the whole-member conclusion of `ReadOk`, by the dep lane's field-by-field open membership (`Dep/OMem.lean` on `spine-dep`). The read clause AS STATED is false for open values (the checker's open values are exactly the counterexamples); with open membership it is the definition. `Ops.lean`'s whole writes and ends, `OpsCall.typed_transport` and `OpsPlace.readPlace_fund_all` consume `PMem` and change with it.
- Strict whole reads and borrows: the `.place` clause (`readPlace` at the empty path) and `.borrow` test the content is a WHOLE member at the place's type (the checker's [Repack] at a read/borrow whole); field reads stay as they are (by `ReadOk`). Ends stay non-strict; a lent part needs the strict test at every typed future (the dep lane's finding). Proofs: `readPlace_fund_all`'s whole case gets its membership from the test instead of `ReadOk`.

## `MemReads` holds in no model (finding, 2026-11-21; reported, decision pending)

`MemReadsCE.not_memReads` (kernel-checked, standard axioms): for every data model and every `Γ` declaring nothing named `Fresh`, `MemReads dm Γ` is false. The read types a field by the declaration it finds BY NAME in `Γ` (`contentTyS`), and the model's universal signature gives data codes, with members, to declarations `Γ` does not declare (and to declarations sharing a `Γ` name). So `FundCtx K` is uninhabited and `fund_all` is vacuous as stated. The repair needs a coherence condition on types (the data layer's `ReadCoherent`/`TyIn`): either restrict `MemReads` to coherent types and carry "every stored and held type is coherent" in `SGood` (with the run's sources of types, `Δ`, `Λ`, the hint, the assignment's type values, made coherent in `FundCtx`), or exclude incoherent codes elsewhere. The same condition is what the payoff lemma (a member is hereditarily well typed) needs at constructor values.

## Next, in order

1. The repair of `MemReads` (decision pending; see above).
2. The frame lemmas of (iii): "this frame operation keeps `SGood`" for `callFrame` (from the caller's `SGood` and `BorrowArgsTyped`: a borrow parameter's type is its label's record), the body's run (the lemma), `popCallFrame` and `SState.endInto`; and `bodyAt`'s frame (records now set: `heldTy` and `heldMem`).
3. The dependent-values step, as above, after D112 lands and the clauses are written.

## Proof idioms (what worked)

- A clause case: `intro s s' r hs h; rw [runT] at h; refine fund_erasedS ?_ s s' r hs h; intro s₀ s₁ r₀ hs₀ h₀`, then `SM.bind_some` / `Option.bind_eq_some_iff` destructuring as `RunPresInd` does.
- `.val`: never unfold the clause; use `runT_val_def`/`run_val_def` (`= strictVal R v (meanV …, { valT … with label := none }) s`), `strictVal_some` (a success returns its input, state unchanged), `strictVal_state` (the decision ignores the state). `valT` is the type function (`RunCongr.lean`). For a concrete `.clo` or `.sealed` value, `simp only [strictVal]` then `if_neg (… ≠ .err)`; for a closure, `closureL_mem` plus "the telescope is built" (`CallInPlace.closureL0_ne_err`, `run_incT`).
- `.prim`: `rw [runT]` on a generic `.prim n args` yields the catch-all equation plus one side goal per earlier string pattern. Do the specific names by `by_cases e : ∃ h, n = "symm" ∧ args = [h]` etc., then close the catch-all with `rw [runT, runT]; all_goals (first | rfl | exact f1 | … )` on ONE line (see `RunSubst.run_prim_substSame`). Never name equation lemmas by number (`runT.eq_42`): the numbering moved in the port and will move again.
- A strict test in a concrete run: `simp only [SM.strictS]` to expose the `if`, then `rw [if_pos (by exact h)]`. The `by exact` matters: the condition in the goal is usually only DEFINITIONALLY the statement of `h` (`(TyS.plain T).m` vs `T`, `(Kc dm).dm.read` vs `dm.read`, `(Sem.ty T).asTy` vs `T`). Membership of a number: `⟨n, rfl⟩`; of a function: `⟨F, rfl⟩`; of `.ty T` in `univ 1`: `⟨⟨A, c, rfl⟩, rfl⟩`.
- Equal runs through a new combinator: state it with NAMED functions (`SM.ranProof`, `Option.map`), not inline `match`es, or `rw` will not find a lemma's lambda in the goal (each inline `match` elaborates to its own matcher).

## Traps

- `open Classical` in every file that states or simplifies a strict run's `if`: the run's conditions are decided by `Classical.propDecidable`; without it `simp` cannot rewrite inside a condition (it needs a `Decidable` instance for the rewritten proposition) and silently leaves it, and a statement written with the condition fails to elaborate.
- `obtain ⟨…, rfl, rfl⟩` from an existential with state equations can fail to substitute (`s' = s` direction): name them and `subst`. Anonymous constructors against a conjunction whose components are definitions (`LoU`, `LabOk`) misparse: `refine ⟨h₁, ?_, h₃, h₄⟩` then prove the component.
- `Nat` decidable `if m = n` with variable `n` does not reduce by `rfl`: `simp [def]`.
- A hand-built state (`Regress/`) records `heldTy` for every live label, and `moved` (not `err`) where a returned borrow's final content does not decode (`Attack.RunEqs.S₃`, `CallInPlace.SC1`).
- Timeouts: the `Attack/CloseCall*` runs need `maxHeartbeats 1000000` and long simp sets; do the strict steps there with targeted lemmas (`Attack.borrowArgs_S₂`, `mem_nat`, `mem_nat_of_as`) rather than adding to the big `simp`. `lake env lean` on a file has autoImplicit on and links stale oleans: always `lake build` the module.
- The `.val` clause's type for an undeclared constructor or an unknown record falls back to the hint; that is why `strictVal` fails on an `err` meaning first.
- No Mathlib: no `split_ifs`, `by_contra`, `not_not`.
