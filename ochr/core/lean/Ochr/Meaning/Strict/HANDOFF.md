# The strict reference run and the fundamental lemma: handoff (working file)

Lane `spine-model` (worktree `ochre-model`), opened 2026-11-20. Brief: make the reference run STRICT (docs/31 D83 route (C), with (C1): proofs actually run) and prove THE FUNDAMENTAL LEMMA: from a model state whose positions hold members of their types, a successful strict run returns a member of the type it returns and leaves such a state; a successful run of a proof term means its proposition is true. Item 1 (this prototype) is in NEW files only; `Run.lean` is unchanged. Item 2 (the port) waits for the orchestrator's answer.

## Files (read in this order)

- `RunS.lean`: `runS`, a copy of `Run.lean`'s mutual block (renamed with an `S` suffix) with the strict points marked `STRICT`/`C1`/`REPAIR`. Helpers: `SM.strictS` (fail unless the result is a member of its type), `SM.erasedS` (C1), `strictVal`, `BorrowArgsTyped` (with `refsOf`, `refTysOf`, `refLabelsOf`), `callOfLS`/`callOfS` (the repaired call).
- `Good.lean`: `GoodRes`, `TypedF`, `SGood` (the invariant), `StatePres`, `FundAt`, `Fund` (the lemma at a term); members are whole (`mem_whole`); `mem_of_pmem_proof`; types kept by state operations (`tyAt_setAt`, `tyAt_access`); `sgood_setAt_const` (a holder written whole); `endAt_sgood`, `endLabel_sgood`, `access_sgood` (ends and [Access] keep the invariant).
- `Call.lean`: `callOf_res_mem` (a call's result is a member, from `ApplyMem.app_mem'`/`app_mem_ref`), `applyTelL_cod`, `callOfL_some`, `mem_of_pmem_el`, `callOfS_res`.
- `Fund.lean`: the combinators (`fund_strictS`, `fund_erasedS`, `erasedS_true`) and the cases (`fund_ascribe`, `fund_assign_deref`, `fund_ctor`, `fund_call`), with the list lemmas (`runParamsS_state`, `runFieldsS_pres`, `runArgsS_pres`) and `readPlace_root_fund`.
- `Runs.lean`: the kernel-checked runs (`zero_unit_none`, `let_zero_unit_none`, `succ_nat_runs`, `refl_runs`, `refl_eq_runs`, `refl_neq_none`).

## The design: strictness inside the run (option (a)), and why

(a) the clauses fail unless the membership holds (a classical test inside `runS`); (b) the run unchanged plus a predicate by the same recursion. Chosen: (a). Evidence:

1. A function's meaning must come from the strict run of its body. Under (b) the `.fix` clause must read the predicate, so the predicate is in the run's mutual block and decided classically inside `runT` anyway: (b) is (a) at one point plus a second recursion of the size of the run.
2. Under (a) the simulation's statements keep their form: "the reference run succeeds" (`x ρ' s = some (r, s')`) IS the strict run succeeding. Under (b) every step statement gains an "every check passed" conjunct.
3. Core lemmas: a strict test reads the clause's result and type, which the congruence/substitution inductions have already shown equal, so each strict point costs one line (`SM.strict_congr`, or a destructuring step). Under (b) every core lemma needs a twin for the predicate.
4. Concrete runs: a strict test blocks `rfl` only at strict points; the run is already classical (decoding, `endLabel`'s `find?`), and the regress runs already reduce through it by `simp` with the needed facts. The C1 test is computable (`Sem.isProof`, `TyM.level`), so proofs stay reducible.

Measured on a throwaway worktree (`ochre-model-probe`, branch `strict-probe`, NOT for merging): `Run.lean` with the D83 strict points (ascribe, assign, ctor, succ, `.val` at a constructor, `.fix`), built. See "Measured port cost" below.

## Measured port cost (probe worktree, D83's points only, C1 not included)

Built layer by layer (a module that fails blocks its dependents, so each layer was repaired to see the next):
- `Run.lean`: the clauses; `mean_sealed_at_future`'s `simp` needs the `.val` helper unfolded (1 line).
- `RunPresInd`: 7 sites (one destructuring line per strict clause; `run_val_eq` restated, `.val` trap below).
- `RunCongr`: 4 (`run_fix_def`, `runT_val_def` restated with the strict wrapper; two one-line `SM.strict_congr`).
- `AssignCongr`: 2 (`SM.strict_congr`). `Program.lean`: 1 concrete run through `S(Z)` needs its membership.
- `RunSubst`: 4, all in the `.val` case of the substitution lemma, and NOT mechanical: substituting a loan by a constructor value turns an unchecked `.val (loan l)` into a checked `.val (C(…))`, so `run_substLoan` needs `FillOK` to say the fill passes the test (its `shape` clause compares types only; strengthened to compare the whole `.val` run, success included). The simulation discharges it from the typed future at the label. `RunSubstAbs` will need the same of `AbsFillOK`.
- Stopped there: `RunSubstAbs`, `HintIndep`, `Steps/*`, `Regress/*` not yet built against the strict run. By inspection about ten regress files run through strict points: an embedded `S(…)`, an ascription, a constructor, an assignment (`CallInPlace`, `Adequacy_flipped`, `CE5_*`, `CodeRuns`, `UntypedNil`, `ConstFree_*`, `CE3`, `StepKinds*`), each repaired by a membership `have` at the point; the closures the run forms (`CallInPlace`'s `Inc`, `Id1`) need their closure's membership, i.e. the body at every argument, because `.fix` is strict.

## The invariant and the lemma

- `TypedF R Γ s ψ`: each live label `l` reads a PARTLY MOVED member of `s.heldTy l` (`pmem`). Partly moved, because a borrow may end with parts of its content moved out (D53 (h)): its lenders then read those parts moved, and the end lemma needs the old invariant at that future. Every future `WF.TypedFuture` admits (whole members) is one, so the invariant at these futures implies `Membership`'s form.
- `SGood R Γ s`: (`bind`) every binding holds a `GoodRes` value at its stored type under every typed future; (`holder`) every holder holds a partly moved member of its label's content type; (`held`) each live label's record (`heldMem`, which `typedFuture` reads) is a member of its content type; (`holderTy`) a binding holder is stored at its label's content type; (`acyc`) `SState.RInv (fun _ => True) s`, the label order of `RunPresInd` (a holder of `x` reads no live label `≤ x`), which gives `holderIndep` and is kept by ends.
- `GoodRes R Γ r`: `pmem r.1 r.2.m ∨ r.2.m = err` (at `err` nothing is owed: the reference has no type there, e.g. `Type₁` as a value, whose type `univ 3` the bounded model lacks).
- `FundAt R Γ x`: `SGood s → x s = some (r, s') → GoodRes r ∧ SGood s'`. `Fund K ρ φ t`: `FundAt` of `runS K ρ φ tl hint t` for every `tl`, `hint`.
- Proofs: `erasedS_true`: an erased proof that runs returns `⋆` at a level-0 type of which `⋆` is a member (its proposition is true).

## Status

PROVED (standard axioms, `#print axioms`): `fund_strictS`, `fund_erasedS`, `erasedS_true`, `fund_ascribe`, `fund_ctor` (refl is this case under C1), `fund_assign_deref` (`*r := u`), `access_sgood`/`endAt_sgood`, `sgood_setAt_const`, `readPlace_root_fund`, `callOf_res_mem`, and all of `Runs.lean`.

GUESS (sorry): `callOfS_sgood` (a call keeps the invariant given `BorrowArgsTyped`; argument in its docstring). `fund_call` uses it and `readPlace_root_fund` (so its head, if a place, is a variable).

NOT DONE in the prototype: every other clause (`let`, `seq`, matches and the join, `borrow`, reads at field paths, `val`, type formers, `Id`, `J`, `clone`/`peek`/`inplace`, `fix`'s state); `runS`'s preservation of `RInv` (the port of `RunPresInd.runT_rinv`, measured mechanical).

## Findings (each for the orchestrator)

1. **Proof primitives that compute their proposition from another proof's** (`cong`, `symm`, `trans`, `rewrite`, `rewriteR`) cannot be typed by the run: a proof of `Eq(A, a, b)` is typed `prop (a = b)`, a `Prop`, which forgets `a`, `b` (and `A`). C1 needs a proposition code that keeps its sides (e.g. `Code0.eq a b : Code0 (PLift (a = b))`, a data-layer change in `Sem.lean`), or the TyS to carry them. Prototype placeholder: `⋆` at the hint if the hint is true. `J` is fine: its endpoints and motive are terms (`P(b)` is a call); its `h` should run as `(h : Eq(A, a, b))` strictly, giving `a = b`. `refl` is `True`'s constructor `I`: the constructor case.
2. **A borrow is invariant** (a strict point D83 does not list): at a call, a borrow argument's label must hold the content type of the parameter it is passed at, or the callee's final content (a member of the parameter's type) is written into a lender of another type. Prototype: `BorrowArgsTyped` (the run fails otherwise); the checker's conversion of `&T` against `&A` is what discharges it.
3. **A returned borrow ending with a partly moved content**: `callOfL` fixes the lenders' labels to `err` where the final content does not decode, and `err` is no member; with typed futures giving partly moved members (needed for ends, finding above) the invariant then fails at those lenders. Repair in the prototype: `callOfLS` writes `moved` there (a lender reads its part moved: a partly moved member). Nothing changes at futures giving whole members, so the relation (stated at those) is unaffected.
4. **Reads at a field path of an open value**: `pmem` admits `OpenIn` (a tree with the type's name and record and ANY whole fields), so a field read off such a value is not shown a member of the type the read gives it (`contentTyS`: its own type for a constructor tree, the declared field type at the current earlier fields for a leaf). Either the invariant is strengthened to "every read path gives a member" (then the question is whether a write of an index field keeps it at a later dependent LEAF field; a candidate counterexample: `MkDP(b, x : if b then Nat else Unit)`, write `b`, read `x`; checker verdict to be measured), or reads become strict (fail unless the value read is a member of the type given).
5. **`.val` at values typed by the hint** (type values, `⋆`, a loan whose declared type is not a function, a sealed program whose result is not a function) carries no membership: `meanV`'s value at the hint can be anything. D83 makes only constructor values strict. Options: the lemma takes a hypothesis on embedded values (discharged by the simulation from the state the code came from), or `.val` is strict there too (with the risk that a loan's strictness makes meanings at untyped futures `err`, which `mean_sealed_at_future` and the end lemmas read).
6. **`.fix` is strict** (the run fails if the closure is `err`): the lemma's `.fix` case is then immediate, and the local knot (D73 item 5: the body total and good at every argument) moves to the simulation, where the typed run needs it anyway.
7. **What the state must carry**: nothing new for the lemma. The reference's temporaries are only borrow holders (typed by their label's `heldTy`) and a closure frame's cells (read at the future). The `heldTy`/`heldMem` records (D66, D68) are exactly the temporaries' typing on this side; D81's typed temporaries are the checker side's.

## What the simulation side must supply (current form)

To apply the lemma at a reference state `s` and a step whose reference run is `x` (a `runS` clause): `SGood K.dm.read K.Γ s` (from `Good` of the related checker state: `bind` from `Membership.pos`, `holder`/`held`/`holderTy` from the typed temporaries and the borrow records, `acyc` from `RInv`), `K.dm.read.WholeFields` (`DataModel.read_wholeFields`), and "the strict run succeeds": `runS K ρ φ tl hint t s = some (r, s')`. At each strict point the simulation shows the check passes from the checker's check: an ascription and an assignment by conversion's soundness, a constructor by `CtorMem.ctorOut_mem` (fields fit), a call's borrow arguments by the conversion of the borrowed types, a closure by the knot.

## Idioms

- A case is `Fund` of the subterms ⇒ `Fund` of the term: `intro tl hint s s' r hs h; rw [runS] at h; refine fund_erasedS (fund_strictS hR ?_) s s' r hs h`, then `SM.bind_some`/`SM.onCopy_state`/`SM.pure_some` as in `RunPresInd`.
- Do-blocks in `Option` (not `SM`), e.g. the `.assign` clause's inner block and `readPlace`: `simp only [Bind.bind, Option.bind_eq_some_iff] at h`.
- A strict `if` (classical): `open Classical in ite_none_some h`.
- Concrete runs: keep `Kt dm D` folded (`simp` unfolding the context breaks the hypotheses that mention it); give the decisions' value at the term as a `have hfl : ∀ sc, K.D.flags sc t = … := fun _ => rfl`, the membership facts as `have`s at the exact form `(TyS.plain T).m`, and finish with `rfl` where simp leaves `TyS.plain (TyS.plain T).m = TyS.plain T`.

## Traps

- The `.val` clause's equation lemma for `runT`/`runS` has side conditions per value constructor (`rw [runT] at h` on `.val v` splits into dozens of goals); state the clause through a function of the value (`strictVal`, `SM.strictWhen`) and use `cases v <;> exact ⟨_, rfl, rfl⟩`.
- `obtain ⟨rfl, rfl⟩ := Prod.mk.inj …` substitutes in the direction Lean picks: refer to the surviving names with `_`.
- Mathlib is not available: no `split_ifs`, `by_contra`, `not_not`.
- `simp` normalises `prop (a = a)` to `prop True` and `prop (0 = 1)` to `prop False`; state the expected results in that form.
