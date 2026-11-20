# The strict reference run and the fundamental lemma: handoff (working file)

Lane `spine-model` (worktree `ochre-model`), opened 2026-11-20. The orchestrator accepted the prototype (strictness inside the run, option (a)) and decided its seven findings (2026-11-21). The fundamental lemma is now proved on the COPY `runS` for every clause, modulo three named guesses at field paths (the dependent-values area, staffed separately). `Run.lean` is unchanged: the data layer's port (record layout) lands first; then this lane merges it and ports `runS` into `Run.lean` (one run, strict; the lead's request (b) is moot).

## Files (read in this order)

- `RunS.lean`: the strict run `runS` (a copy of `Run.lean`'s mutual block, `S`-suffixed). Strict points marked `STRICT`/`C1`/`REPAIR`. Helpers: `SM.strictS`, `SM.erasedS`, `strictVal`, `labTyOk`, `paramsOk`, `BorrowArgsTyped`, `callOfLS`/`callOfS`.
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

`fund_all (hc : FundCtx K) : ∀ t, t.valsOk (fun v => Fund K ρ φ (.val v)) → Fund K ρ φ t`, where `Fund K ρ φ t := ∀ tl hint, FundAt K.dm K.Γ φ (runS K ρ φ tl hint t)` and `FundAt dm Γ φ x := ∀ s s' r, SGood dm Γ φ s → x s = some (r, s') → GoodRes dm.read r ∧ LabOk dm s' r ∧ LoU s' r.2.label ∧ SGood dm Γ φ s'`.

- `SGood dm Γ φ s`, at every typed future `ψ` (`TypedF`: agrees with `φ` off the live labels, each live label a partly moved MEMBER (`PMem`, no `OpenIn`) of its recorded content type): `bind` (each existing binding: `GoodVal`, a partly moved member or a value with no data at `err`), `holder` (`PMem` of the label's content type), `held` (records are members), `holderTy`, `acyc` (`RInv (fun _ => True)`: the label order), `fresh` (`ReadsBelow`), `read` (`ReadOk`).
- `GoodRes`: a whole member, `⊥`, or a value with no data (`.ty _` or `⋆`) at `err`.
- `FundCtx K`: `MemReads K.dm K.Γ` (data layer), globals `GoodRes` and label-free, no data declaration at `Type₁` (`d.sort ≠ 2`).
- Axioms: `fund_all` uses `sorryAx` only through the three field guesses; every other lemma here is on `propext`, `Classical.choice`, `Quot.sound`.

## Decisions in force (orchestrator, 2026-11-21) and how they are built

1. Equality rules: premise proofs run on a copy, `⋆` at `prop True` (`fund_premises`). Generalised (this lane, to report): EVERY erased proof is `⋆` at `prop True` (`SM.erasedS`), since a field of `⋆` is read at `err` and would otherwise fail C1; the clause's own type is still checked by the lemma at the clause (`erasedS_clause_true`).
2. Borrow invariance at calls: `BorrowArgsTyped`, extended (this lane) with "the argument's label is live", which discharges `callOfS_sgood`'s liveness need.
3. Strict ends vs partly moved futures: evaluated (sent 2026-11-21): this lane recommends partly moved futures + `moved` in `callOfL`'s undecodable branch (one line in Run.lean, one literal in `Locality.callOfL_ref_inv`, measured on the probe); awaiting the orchestrator.
4. Reads at field paths: an invariant (`ReadOk`), not strict reads; the read case is proved from it.
5. Embedded values: the precondition `Term.valsOk` (the lemma at each `.val`).
6. Strict `.fix`: yes (`fund_fix`).
7. Nothing new in the model state.
Also adopted: whole membership at ascription/assignment; the assignment tested at the place's type at the write; constructor parameters' membership (`paramsOk`).

## Open: the three field-path guesses (`OpsPlace.lean`, the dependent-values area)

- `setContent_field_moved_sgood`: moving out of a field keeps the invariant. May fail: `⊥` reads small as `.other`, so a later dependent LEAF field's read type (its declaration at the current earlier fields, `Places.contentTyS`) changes while its value does not.
- `borrowPlace_field_sgood`: lending a field keeps the invariant. May fail: the lender's field is a different member at each typed future, so a later dependent field's read type moves with the future (`dws_Pair_dependent_fails`).
- `setContent_field_sgood`: assigning a field keeps the invariant. May fail: an index rewritten, a later dependent leaf field keeps the old value under the new type (`OWK`-style; the checker sets dependent proof fields to `⊥`, not leaf fields).
What the read clause says at the empty path: a binding's whole value is a member, so a value open in its type (`pmem`'s `OpenIn`) breaks it at the root; the checker's open values (OWK) are therefore exactly the question.

## Other findings for the orchestrator

- `.tind` at a `Type₁` declaration: the model reads every data declaration as a `Type₀` code, so `D(ā) : Type₁` is no member of `univ 2`; `FundCtx.sorts` excludes it.
- `bodyAt` (the `.fix` clause's frame) sets `heldMem` but not `heldTy` for a borrow parameter's label: a closure body's frame is not `SGood`. Not read by the lemma (strict `.fix`), but the simulation's body runs (`runBody`, in place) will need the record typed.

## Idioms

- A clause case: `intro s s' r hs h; rw [runS] at h; refine fund_erasedS ?_ s s' r hs h; intro s₀ s₁ r₀ hs₀ h₀` then `SM.bind_some` / `Option.bind_eq_some_iff` destructuring as `RunPresInd` does.
- `.prim` clauses: `rw [runS]` on a generic `.prim n args` yields the catch-all equation plus one side goal per earlier pattern (`runS_prim_other`); the specific ones reduce by `rfl` (`fund_premises … rfl`).
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

1. When the data layer's commit is verified: merge it; port `runS` into `Run.lean` (the strict run replaces `runT`), carrying the measured repairs (RunPresInd, RunCongr, AssignCongr, RunSubst/RunSubstAbs with `FillOK` carrying the fill's membership, Regress), then move `Strict/*` onto `runT`.
2. The field guesses: owned by the dependent-values attack; this lane supplies their exact statements.
3. The strict type formers' "well typed inside" (brief item 2) is not started.
