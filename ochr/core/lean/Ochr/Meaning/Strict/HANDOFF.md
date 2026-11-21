# The strict reference run and the fundamental lemma: handoff (working file)

Lane `spine-model` (worktree `ochre-model`), opened 2026-11-20. The orchestrator accepted the prototype (strictness inside the run, option (a)) and decided its seven findings (2026-11-21). PORTED (2026-11-21): the strict run IS `Run.lean`'s `runT` (one run); the copy `RunS.lean` is deleted and every file here is about `runT`. The fundamental lemma `fund_all` holds for every clause of the real run, modulo three named guesses at field paths (the dependent-values area, staffed separately). The core lemmas are back on the standard axioms and the concrete runs (`Regress/`, `Attack/`, `DataModel/`) build against the strict run; what changed in them is listed under "The port".

## Files (read in this order)

- `Run.lean` (not here): the strict run. Strict points marked `STRICT` at their sites. Helpers: `SM.strictS`, `SM.erasedIf` (C1), `strictVal`, `labTyOk`, `paramsOk`, `BorrowArgsTyped`, `callOfL`/`callOf` (`moved` in the undecodable branch).
- `Good.lean`: `NoData`, `GoodRes`, `PMem`, `GoodVal`, `TypedF`, `ReadOk` (THE READ CLAUSE), `SGood`, `LabOk`, `StatePres`, `FundAt`, `Fund`; members whole; types kept by ends/access.
- `Ops.lean`: `MemReads` (the data layer's read lemma, a hypothesis); whole writes (`sgood_setAt_const`, `sgood_setAt_pmem`), ends (`endAt_sgood`), [Access] (`access_sgood`).
- `Call.lean`: a call's result is a member (`callOf_res_mem`, from `ApplyMem.app_mem'`/`app_mem_ref`); `callOfS_res`.
- `OpsCall.lean`: `callOfS_sgood` (a call keeps the invariant), with `applyTelL_finals` (finals are members whatever the callee), `typed_transport`, `sgood_mapVals_fix`, `sgood_park_fix`, `callOfLS_rinv`, `callOfLS_readsBelow`.
- `OpsPlace.lean`: `sgood_transfer`, `sgood_pushBindShaped`, `sgood_letDrop`, `readPlace_fund` (root/`*`), `readPlace_fund_all` (any path), `borrowPlace_fund`, `assignAt_sgood`; the three FIELD-PATH GUESSES (below).
- `Comb.lean`: `FundCtx` (context hypotheses), `Term.valsOk` (decision 5's precondition), `PresLab`, `fund_strictS`, `fund_erasedS`, `erasedS_clause_true` (a proof's run means its proposition is true).
- `Simple.lean`: universe/Π/declaration membership (`goodRes_sort`, `goodRes_pi`, `goodRes_tyR`), `fund_pure`, `fund_onCopy`.
- `Clauses.lean`, `Match.lean`, `Clauses2.lean`: one lemma per clause (`fund_*`), the match/join/entry/capture state lemmas (`sgood_joinDrop`, `sgood_matchEntry`, `sgood_capStep`), the label-record and liveness transport (`HeldSame`, `fund_join`).
- `Fund.lean`: `fund_prim` (dispatch of `.prim`), and **`fund_all`**, the one induction (mutual with `fund_list`, `fund_arms`).
- `Runs.lean`: kernel-checked runs (`zero_unit_none`, `let_zero_unit_none`, `succ_nat_runs`, `refl_runs`, `refl_eq_runs`, `refl_neq_none`, `sort_two_runs`).

## The statement

`fund_all (hc : FundCtx K) : ∀ t, t.valsOk (fun v => Fund K ρ φ (.val v)) → Fund K ρ φ t`, where `Fund K ρ φ t := ∀ tl hint, FundAt K.dm K.Γ φ (runT K ρ φ tl hint t)` and `FundAt dm Γ φ x := ∀ s s' r, SGood dm Γ φ s → x s = some (r, s') → GoodRes dm.read r ∧ LabOk dm s' r ∧ LoU s' r.2.label ∧ SGood dm Γ φ s'`.

- `SGood dm Γ φ s`, at every typed future `ψ` (`TypedF`: agrees with `φ` off the live labels, each live label a partly moved MEMBER (`PMem`, no `OpenIn`) of its recorded content type): `bind` (each existing binding: `GoodVal`, a partly moved member or a value with no data at `err`), `holder` (`PMem` of the label's content type), `held` (records are members), `holderTy`, `acyc` (`RInv (fun _ => True)`: the label order), `fresh` (`ReadsBelow`), `read` (`ReadOk`).
- `GoodRes`: a whole member, `⊥`, or a value with no data (`.ty _` or `⋆`) at `err`.
- `FundCtx K`: `MemReads K.dm K.Γ` (data layer), globals `GoodRes` and label-free, no data declaration at `Type₁` (`d.sort ≠ 2`).
- Axioms: `fund_all` uses `sorryAx` only through the three field guesses; every other lemma here is on `propext`, `Classical.choice`, `Quot.sound`.

## Decisions in force (orchestrator, 2026-11-21) and how they are built

1. Equality rules: premise proofs run on a copy, `⋆` at `prop True` (`fund_premises`). Generalised (this lane, to report): EVERY erased proof is `⋆` at `prop True` (`SM.erasedIf`), since a field of `⋆` is read at `err` and would otherwise fail C1; the clause's own type is still checked by the lemma at the clause (`erasedS_clause_true`).
2. Borrow invariance at calls: `BorrowArgsTyped`, extended (this lane) with "the argument's label is live", which discharges `callOfS_sgood`'s liveness need.
3. Partly moved futures, with `moved` in `callOfL`'s undecodable branch (the orchestrator reversed its first ruling, strict ends, on this lane's measurement: one line in Run.lean and one literal in `Locality.callOfL_ref_inv`'s proof, against a dozen signatures the step statements consume; the relation's records clause never takes the changed branch). The checker's rule (no end over moved-out content) is carried as the named fact `EndWhole`, which the simulation may use and the lemma does not need.
4. Reads at field paths: an invariant (`ReadOk`), not strict reads; the read case is proved from it.
5. Embedded values: the precondition `Term.valsOk` (the lemma at each `.val`).
6. Strict `.fix`: yes (`fund_fix`).
7. Nothing new in the model state.
Also adopted: whole membership at ascription/assignment; the assignment tested at the place's type at the write; constructor parameters' membership (`paramsOk`).

## THE CONTEXT PREDICATE (what the simulation side must supply, besides `SGood` of the state)

`FundCtx K` (`Comb.lean`), plus the term precondition `Term.valsOk`:
1. `reads : MemReads K.dm K.Γ` — the data layer's read lemma: a whole read path of a partly moved member gives a member of the type the read gives it. From `ReadMember.follow_below_member` under `ReadCoherent` for every record a type can name (plus: a whole value below a member is that member, true of every value `Sem.succ` builds).
2. `globals : ∀ n, GoodRes K.dm.read (K.C.global n) ∧ (K.C.global n).2.label = none` — each global is a member of the type it carries: `GlobalsOk.mem` for an earlier definition; for the definition being checked (`K.cur`), `MemBelow` says its meaning is the stage closure at the WEAKENED function type, of which it is a member (`ClosureStage.stage_mem`) — the connecting lemma is not written.
3. `sorts : ∀ d ∈ K.Γ, d.sort ≠ 2` — no data declaration at `Type₁`.
4. The model's read has whole fields: automatic (`DataModel.read_wholeFields`), not a hypothesis.
5. Term precondition `t.valsOk (fun v => Fund K ρ φ (.val v))`, which is where the assignment's typing and the future's typing at free loans enter: an embedded unknown `σ` is good iff `ρ σ` is a member of `K.Δ σ` (`TypedAssignment` with `DeltaOk`); an embedded loan `ℓ` iff `φ ℓ` is a member of the type the `.val` clause gives it (the future typed at free loans); a closure, a sealed program, a global by their own runs. For values the `.val` clause types by the HINT (a type value, `⋆`, a loan whose declared type is not a function, a sealed program whose result is not a function) the precondition must hold at the hint the run passes, which is a typing fact about where the value sits in the code (the code invariant the simulation side owns).

## Where `SGood` is established (the direction of the futures)

`SGood` quantifies over futures whose live labels end at PARTLY MOVED members: more futures than the checker's invariant speaks of (whole members), so `SGood` implies the whole-member form but is HARDER to establish from the checker's side. Where it must be established, and how (a reading of the code, not proved):
(i) From the checker's invariant only at the start of a definition's body (the generic run of [Def]) and at the empty state (the main theorem's start; a sealed program's re-run from `emptyState`). There no place of the state is lent: the parameters are unknowns, a borrow parameter's lender is the caller's and not in the callee's state, so no position reads a live label and the futures' shape does not matter: `bind`/`holder` hold at every future iff at one. The records of the borrow parameters' labels (`heldTy`, `heldMem`) must be set at that state (`MState.sstate` leaves them at their defaults, so the related state must carry them, as the relation's records clause has them).
(ii) From then on the simulation carries `SGood` forward by this lemma, step by step: every reference state it relates is produced by a run of the strict run from the previous one. Statements and private copies return the state they started from; a split, an η-refinement, a generalisation, a [Repack] change the checker's state and leave the reference's (it does not split, refine or repack); [Close] is the reference's call clause (`callOfS_sgood`).
(iii) Steps whose reference state is produced by a reference operation that is NOT a clause of the strict run, so the lemma does not cover them, but which need only MODEL-side lemmas, not the checker's invariant: the in-place call (`CallRef.runCallRef`: `callFrame`, then the body's run, then `popCallFrame` and `SState.endInto`), and a closure body's frame (`.fix`'s `bodyAt`, which today records a borrow parameter's `heldMem` but not its `heldTy`, so that frame is not `SGood` until it does). Each needs a lemma "this frame operation keeps `SGood`", from the caller's `SGood` and the call's strict tests (`BorrowArgsTyped` gives a borrow parameter's type = its label's record). None re-derives `SGood` from the checker's invariant at a later state. Not yet written.

## Open: the three field-path guesses (`OpsPlace.lean`, the dependent-values area)

- `setContent_field_moved_sgood`: moving out of a field keeps the invariant. May fail: `⊥` reads small as `.other`, so a later dependent LEAF field's read type (its declaration at the current earlier fields, `Places.contentTyS`) changes while its value does not.
- `borrowPlace_field_sgood`: lending a field keeps the invariant. May fail: the lender's field is a different member at each typed future, so a later dependent field's read type moves with the future (`dws_Pair_dependent_fails`).
- `setContent_field_sgood`: assigning a field keeps the invariant. May fail: an index rewritten, a later dependent leaf field keeps the old value under the new type (`OWK`-style; the checker sets dependent proof fields to `⊥`, not leaf fields).
What the read clause says at the empty path: a binding's whole value is a member, so a value open in its type (`pmem`'s `OpenIn`) breaks it at the root; the checker's open values (OWK) are therefore exactly the question.

## Other findings for the orchestrator

- `.tind` at a `Type₁` declaration: the model reads every data declaration as a `Type₀` code, so `D(ā) : Type₁` is no member of `univ 2`; `FundCtx.sorts` excludes it.
- `bodyAt` (the `.fix` clause's frame) set `heldMem` but not `heldTy` for a borrow parameter's label. FIXED in the port: `bodyAt` and `RunCongr`'s `fixStep` mirror set both.
- ADEQUACY (kernel-checked, `Regress/Adequacy_flipped.erased_match_proof_fails`): under C1 an erased match on a proof with other than one arm FAILS (the tag is `⋆`, no arm can be chosen). The checker accepts `Subsingletons.OrComm`/`OrElim`/`OrLet` (two arms on `Or`, result a proof) and `Propositions.absurdP` (no arms on `False`). On `Or` the strict run therefore fails where the checker succeeds, at members; the simulation side's "an accepted program's run succeeds" is false there. The lemma is unaffected (it is about successful runs). Needs a ruling: e.g. an erased proof match picks the arm whose constructor's field propositions hold (classically), or the run trusts an erased match's result type when every arm is a proof.

## The port (2026-11-21): what changed besides `Run.lean`

Definitions the step statements consume that changed: `runT` (strict clauses; `.place`/`.borrow`/`.assign`/`.call`/`.ascribe`/`.succ`/`.ctor`/`.fix`/`.val`/the equality rules), `SM.erasedIf` (C1; `SM.erasedAt` deleted, an erased place is `⋆` at `True` like every proof), `callOfL` (`moved`, not `err`, in the undecodable branch), `bodyAt` (records `heldTy`), `strictVal` (new; a constructor value whose meaning is `err` fails outright, so that the test never reads the hint where the meaning is `err`: needed by `HintIndep`). Unchanged: `dropAt`, `joinDrop`, `matchEntry`, `runBodyRef`/`CallRef`, `contentOf`, `assignAt`, `ctorOut`. No file under `Steps/` needed a change.
Core lemmas: `RunPresInd`, `RunCongr` (+ `strictVal_state`, `premises_congr`), `AssignCongr`, `RunSubst`, `RunSubstAbs`, `Lemmas.fillOK_upd` (through `strictVal_state`), `HintIndep` (the `.val` case reads `strictVal`; erasure keeps the value), `SubstAbs.absFill_shape` (NEW HYPOTHESIS `hmem`: the filler means a member of `Δ σ`, `ρ σ ∈ Δ σ`, since a constructor filler is now tested; it had no caller).
Concrete runs, changed only where strictness adds a test to discharge or fails by design:
- flipped by design: `OpenFalse.run_ascribe_trusted` → `run_ascribe_strict` (`(0 : Unit)` fails); `Adequacy_flipped.erased_unrun`/`erased_place` → `erased_on_copy`; `ShapeAgree.erased_proof_untyped` → `erased_proof_true`; `ReturnedRead.callOf_reads_decoded` (the lender now reads `moved` where the checker's mark does: the D66 discrepancy at `moved` is gone).
- new membership hypotheses where a data model is arbitrary: `Adequacy_flipped.ctor_no_hint`, `CodeRuns.boxProof`/`run_ctor` (discharged in the `List`/`Rose` runs from `DataCodes`), `ParamSolve.ctor1_runs`/`sw_*`/`so_*` (discharged by `CtorMem.sw_runs_strict`/`so_runs_strict` from `t ∈ Tag(3)`).
- states carrying `moved` for an undecodable final content: `Attack/RunEqs` (`S₃`, `S₄`, …), `CallInPlace` (`SC1`, `yR1`, `callOf_id1`), `DepSites.SRb`; and `heldTy` at a body frame's parameter label: `CallInPlace.SB`/`SBs`.
- every other run: the strict tests discharged (`mem_nat`, `borrowArgs_S₂`, `borrowArgs_psInc`, closures built hence members, `run_incT`/`run_id1T`).

## Idioms

- A clause case: `intro s s' r hs h; rw [runT] at h; refine fund_erasedS ?_ s s' r hs h; intro s₀ s₁ r₀ hs₀ h₀` then `SM.bind_some` / `Option.bind_eq_some_iff` destructuring as `RunPresInd` does.
- `.prim` clauses: `rw [runT]` on a generic `.prim n args` yields the catch-all equation plus one side goal per earlier pattern (`runS_prim_other`); the specific ones reduce by `rfl` (`fund_premises … rfl`).
- Liveness of results: reuse `RunPresInd`/`RunPres` (`readPlace_rinv`, `borrowPlace_rinv`, `letDrop_rinv`, `joinDrop_lou`, `lou_setLent`); label records: `HeldSame`.
- Mutual induction over nested `Term`: `termination_by structural` on each of `fund_all`, `fund_list`, `fund_arms`, the list cases as terms (`(List.mem_cons.mp h).elim …`), not tactic `rcases … rfl`.

## Traps

- The `.val` clause's equation lemma splits per value constructor; strictness goes through a function of the value (`strictVal`).
- `obtain ⟨rfl, rfl⟩` and `subst` pick a direction; refer to survivors with `_` or keep the equation (`e ▸ hs`).
- After `subst`, a re-used hypothesis name can denote the ORIGINAL hypothesis; use fresh names in long destructuring chains (`fund_J`).
- `simp` unfolds `Kt …` inside a context and loses hypotheses stated with it: state memberships at the exact form the goal shows (`(Kt dm Dpf).dm.read`).
- Two files defining the same helper in one namespace build separately and clash at the root import: import one from the other.
- No Mathlib: no `split_ifs`, `by_contra`, `not_not`.

## Next

0. The dependent-values step, after the checker's D112 is on `main` and that agent has written the exact clauses: mirrored invalidation, open membership in `SGood`, strict whole reads/borrows; then the three field guesses.
1. The frame lemmas of (iii) above (in-place call frame push/pop/renaming; `bodyAt` now records `heldTy`).
2. The erased proof match with several arms (see the adequacy finding): a ruling first.
3. The strict type formers' "well typed inside" (brief item 2) is not started.
