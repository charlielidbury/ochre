# Stability (Conjecture 2): statement, decomposition, and what is left

Branch `stability`, off main `4cc0beda`. The theory lane toward full consistency. Every model lane (`depfields-model`, `split-model`, `id-model`) ends on the paper's stability conjecture: refinement commutes with checking. This note states it against the checker, breaks it into one lemma per decision site, reports what happened to the two weakest sites, and reduces what is left to as few lemmas as I could.

## 1. The statement (`Ochr/Stability.lean`)

`Conjecture2 := DecisionsCommute ∧ RunsCorrespond`, proof `sorry`.

- **Refinement.** `α : List (Nat × Value)`, values for abstract values, applied as the checker applies [Split]'s refinement: `refine` substitutes into Ω's values, stored types, unknowns' types and the goal and re-normalises every sealed program it reaches; `substV`/`substT` do the same for values and terms. Abstract functions and holes are abstract values, so this covers all three kinds the paper names. `Respects α Ω` asks each value to check at a type convertible with its unknown's.
- **"The same decisions".** The big-step machine builds no derivation tree, and the two runs do not visit the same subterms (the generic run closes off what the instance runs, and checks every arm the instance takes one of). So the paper's "at every subterm both runs reach" is split into two precise halves:
  - `DecisionsCommute`: each decision function, on refined inputs, gives the refinement of its answer on the originals: the erasure pre-pass (item 1), `byTypeMatch` (1), `fnClass` and `declKind` (4), `closeBlock`'s block (2; `closeOffMatch` before D76), `placeType` for an observed place up to conversion (5), and footprint containment (6).
  - `RunsCorrespond`: the instance run (`tα` at `Ωα`) does not fail where the generic run (`t` at `Ω`) succeeded, and when it finishes it agrees up to resolution with the generic result and final state refined by `α`. This is what puts related inputs in front of the decision functions at the subterms both runs reach; it gives item 3 (arms well typed on both or neither) and item 6's "the extra equations compute to ⊤".
- **Up to resolution (`AgreeUpToρ`).** End every borrow (`endAll`), which leaves no loan to rename; then rename the unknowns either run created (at or above `Ω.nextAbs`) injectively, itself a refinement by unknowns; then compare the values and every position's content.
- **Proved:** see §9. `stability` now lives in `StabilitySig.lean` with the `byType` and `closeRow` fields proved and the rest `sorry`, each marked with what it needs. `#print axioms stability`: propext, sorryAx, Classical.choice, Quot.sound.

## 2. Per-site decomposition (the 25 census sites)

Each site needs: *if the two runs present α-related inputs, the decision agrees*. Classification:
- **(a) by construction:** decided in `Decide.lean` from syntax, declarations and declared readings, none of which a refinement changes (it changes values and stored types, never a term's syntax or a binding's `decl`);
- **(p) follows from a principle:** a short argument from a named principle or one of the elementary lemmas in §3;
- **(o) open:** needs `RunsCorrespond` (N) or typing/machine agreement (M), §4.

| # | Decision | Class | Lemma it needs |
|---|---|---|---|
| 1 | Erasure pre-pass | a | Binding readings are now syntactic (D77), so `declOf` in live scope reads only syntax and `decl`s. Embedded values (`.val v` in sealed programs) are read by their head: L-sort, L-class. |
| 2 | After-the-fact classification | a | A check, not a decision: any disagreement with 1 is a rejection, never a different result. |
| 3 | A function type's class | a | Read off the codomain term (D54). A stuck block's function reads its codomain value's sort: L-sort. |
| 4 | Proof parameters | a | Parameter type terms. |
| 5 | Is a call a statement | p | The callee value's Π-type class: L-class (D54: Π-types of different class do not convert, so a refined value's type keeps its class). |
| 6 | Statement argument in place | a | **Was (b).** Now the argument's declared type (D77, `stmtArgInPlace`). |
| 7 | A binding's class | a | **Was (b), the weakest.** Now its declared type's syntax, type functions read through their bodies (D77). |
| 8 | [Close]'s row | a / o | **Corrected (§9).** For a function, the declared codomain term: proved (`decisionsCommute_closeRow`). For a stuck block, the codomain is the match's type, a value. Refining an unknown match type to `Unit` turns the row from data to `Unit` (η at `Unit`, D59, site 9), so the block row is value-dependent by design and carried by closing off (C). Data to `&` cannot happen: `&` is never an argument (D48 (2), tests `UseBlkRef`, `UseBlkBox`). |
| 9 | η at `Unit` | p | D59: every value at `Unit` is `()`, so normalising one path's value and not the other's changes no `Eq`. Refinement only makes a type more concrete. |
| 10 | Proof irrelevance (`isPropV`) | p | L-sort (D55: sorts are syntactic, evaluation and refinement preserve them). |
| 11 | Match on a proof | a | Proved: `byTypeMatch_arms`. |
| 12 | Arm a match on a proof takes | p | L-head on the scrutinee's stored type: refinement refines its parameters, never its head (note 25). |
| 13 | Stuck-block captures and modes | p | Syntax (occurrences); copy-ness (as 16); ⊥ per arm (type-directed); borrow-ness of a binding (now a declared-type fact, as 6); a split capture's constructor (L-ctor); (X)/(S) of `split-model`. |
| 14 | Footprint and owners | o | Containment: roots are syntax, extra owners come from a hole's fill, which refinement can only lose (`id-model` (A)/(F)). That the extra equations compute to ⊤ is N. |
| 15 | [Rec] decrease | p | L-ctor: refinement only adds constructors, so a strict subterm stays one. |
| 16 | Copy or move on a read | p | Copy-ness is monotone: an abstract or neutral type is never a copy type and refinement only makes types more concrete, so the generic run moves at least what the instance moves; the difference is a ⊥ the generic run then rejects on (fail-safe). |
| 17 | `Eq` computes | o | Injective/disjoint: L-ctor. Reflexive: conversion is closed under refinement, which for [Conv-fun] (observation of the generic call) is N. Stuck stays stuck or computes later. |
| 18 | `J` computes | o | As 17. |
| 19 | Conversion checks | o | As 17: structural conversion commutes with refinement by determinism of `substV`; [Conv-fun] needs N. |
| 20 | [Split], [Split-gen], records | o | (X)/(S)/(G)/(B) of `split-model` for the worlds; the re-normalisation of generalised sealed programs is N. |
| 21 | Re-observing a stuck side by typing | o | M: a typed run and an untyped run of the same term agree when neither is stuck. |
| 22 | Is a hole a proof | p | L-sort. Holes are outside the consistency statement anyway. |
| 23 | K2/K3 model-code checks | p | Flags are syntax; a content's type head: L-head. |
| 24 | [Open], [Repack], whole-again points | p | (W)/(P) and [Return] of D76 (`depfields-model`, unmerged): every producer of a dependent neutral checks it whole through `closeBlock`/`bodyReturns`, and the generic run is the stricter path. |
| 25 | `&A` well formed | p | L-sort (D55, D66). |

**Counts:** by construction 8 (1, 2, 3, 4, 6, 7, 8, 11); from a principle 11 (5, 9, 10, 12, 13, 15, 16, 22, 23, 24, 25); open 6 (14, 17, 18, 19, 20, 21). Before D77, 6 and 7 were the two (b) sites and site 1 was not by construction either, because binding readings came from `refineDecl`'s value reading.

## 3. The elementary lemmas

All four are about `substV` and the readers of value heads; each follows by unfolding `substV` case by case, and none needs the evaluator.
- **L-ctor.** Substitution keeps a constructor value's constructor: `substV σ r (C(ā; v̄)) = C(ā'; v̄')`. (Only `.sealed` re-normalises; constructor values are rebuilt componentwise.)
- **L-head.** Substitution keeps a type value's head (`tInd n`, `tRef`, `tPi`, `tNat`, `tUnit`, `sort`). **Not** `tEq`: `mkEqM` may compute an equation to `True`, `False` or a conjunction. Its sort is kept, which is L-sort.
- **L-sort.** Substitution keeps a type value's sort (`sortOf`): heads are kept (L-head), an equation stays a proposition, and an unknown's sort is its type's, which `Respects` makes convertible with the refined value's.
- **L-class.** Substitution keeps a Π-type value's class: the codomain term is unchanged and its captured values keep their declared readings (`valueDecl` reads heads: L-head), so `fnClass` reads the same term in the same scope (D54).

## 4. The two weak sites (D77)

- **`refineDecl` (site 7).** The census's weakest argument. Probing it found a real path disagreement: at an instance where a parameter of type `RefPred(0)` holds a *sealed* function value (`PickP(n)` stuck on `n`), `refineDecl` read `other` (there is no case for sealed values, and the call's declared codomain `RefPred(0)` is not syntactically a Π-type), so the instance ran `p(&c)` where the generic call, reading the evaluated type, erased it. The pre-pass assertion caught the disagreement, so the definition was rejected with an INTERNAL error: fail-safe, but true statements (`InstPow`, `DirectPow`) were rejected. A second probe (`MixT`: a family whose arms are Π-types of different classes) showed the generic call reading `other` and the instance reading the arm's class, again caught by the assertion.
  - **Fix (D77):** read a type function's call off its body (a Π-term through `let`s and match arms; a self-call neutral), a constant type off its value, and make `refineDecl` read nothing else. Arms that disagree with a Π-type among them are a `conflict` and the binding is rejected. Every earlier verdict unchanged; the true statements are accepted; the open lemma for site 7 is gone.
  - **Edge cases found by probing the new reading, fixed before landing:** a recursive type function's self-call through its `by` binder read as a proposition (made `RecP` a conflict); a body naming its Π-type with a `let` read as data (made `RunLet` an INTERNAL rejection). Both now read correctly and are regressions.
- **`stmtArgIf` (site 6).** Leaned on A.5 condition 5 (Assumption 11, T1, unproved). No disagreement found; made syntactic anyway (`stmtArgInPlace`, declared type a borrow type), every verdict unchanged, and the lemma it needed is gone.

**Findings:** no closed proof of `False`. One path disagreement (site 7), fail-safe through the pre-pass assertion, now removed by construction; it had made true statements unprovable.

## 5. What is left: the minimal remaining lemma

Everything open reduces to two lemmas.

- **N, symbolic naturality (`RunsCorrespond`).** Evaluation commutes with refinement up to resolution. It splits by what the generic run does at an unknown it meets:
  - **(P) Parametricity in uninspected unknowns.** A run that completes without inspecting `σ` (it would have been stuck, or split, or closed off) computes, with `α(σ)` in `σ`'s place, the same steps on the substituted values. Its value-dependent decisions read only heads and declared readings, which §3's lemmas keep. This is the paper's "hole parametricity" (A.8, Assumption 10 (N3)) generalised from holes to every unknown, and it is the one genuinely global lemma: an induction over the evaluator's 116-function cycle, uniform in each case.
  - **(C) Closing off is correct.** Where the generic run closes a call off, the sealed programs it leaves, re-normalised under `α`, compute what the instance's direct run of the call computes: its result and the final contents of its borrowed places. This is property 3 of the paper's Figure 9; it was mechanised as `close_res/fin/cur/back` for the earlier rule set in the deleted `meta-lean`.
  - **(Sp) Splits commute.** Where the generic run splits `σ`, `α(σ)`'s constructor picks the arm the instance takes, and the arm's state refined by the fields' values is the instance's. Given (X)/(S) of `split-model` this is bookkeeping.
- **M, typing refines the machine.** A typed and an untyped run of the same term agree when neither is stuck (needed for site 21, and implicitly wherever typing re-runs a callee body with the machine). This is the paper's design claim that typing is the machine run with types.

So Conjecture 2 is not a separate problem from naturality: with the decisions made syntactic (8 sites by construction) or local (11 sites from short principles), **stability reduces to symbolic naturality (N, which is P plus C plus Sp) and typed/untyped agreement (M)**. Of these, (P) is the heart; (C) has been mechanised before for an older rule set; (Sp) is bookkeeping given `split-model`; (M) is a design claim with no known counterexample.

## 6. Open questions

- **(P) in Lean.** The checker is total (D74-era), so (P) is stateable and provable in principle against `Machine.lean`: a mutual induction over the fuel-indexed cycle, with a "does not inspect σ" predicate on runs. It is large but uniform, and it is the step that would turn this decomposition into a proof.
- **Closed: type parameters.** A type function returning its type parameter (`IdTy (A : Type₁) : Type₁ := A`) first still read `other`, and `RunIdTy` was an INTERNAL rejection. `typeDecl` now substitutes the call's argument readings for the body's type parameters (`tsc`), syntactically. What syntax still cannot read (a definition's own type variable, `UseTyVar`) reads `other` on both paths, and a value of it is not known to be a function at the generic call, so a call through it is rejected there.
- **Footprint ⊤.** Site 14's second half (extra equations compute to ⊤) is N for the observation's runs; `id-model` P4 is one instance where it holds.

## 7. Mechanising (P): a bounded viability probe

(P), the heart of N: a run that never inspects an unknown commutes with substituting a value for it. Probe files in `ochr/core/lean/Scratch/` (not part of `lake build`; checked with `lake env lean`).

### What was proved, against the real checker

- **`PProbe.substV_data`** (`Scratch/PProbe.lean`, sorry-free, 2 s): on first-order data, meaning no closure, Π-type, sealed program or equation type anywhere, the real fuel-indexed `substV` has no effect on any layer of `M` and returns a structural substitution `psV`, given fuel ≥ the value's depth. It is a mutual structural induction over values and lists, about 40 lines, using Lean's generated equation lemmas (`substV.eq_1`…) and `LawfulMonad M`, which the five-layer stack has. So the real functions *can* be reasoned about, and the monad is not the obstacle by itself.
- **Run lemmas for `M`** (`Scratch/PProbe2.lean`): `step` takes the five layers apart; `step_bind`, `step_get`, `step_set`, `step_modify`, `step_getFuel`, `step_modifyFuel`, `step_exhausted`, `step_throwFail` are `rfl` or two lines. With them, `simp only` moves through `do` blocks; plain `simp` times out at `whnf` on the first `eval`.

### What the direct route costs

- **`eval` on the term `0`** (`PProbe2.eval_zero`, left `sorry` as the measurement): with the run lemmas, unfolding `eval` → `located` → `noteValue` → `evalAt` works, and the proof state is about 50,000 characters. Almost all of it is bookkeeping: the erasure pre-pass (`declOf`, `preFlags`, `curDecl`, `tailDecl`, `headEval`), the flags, `typing`, `erasedDepth`, `onFail` restores, and the editor's `locs` (`noteValue` reads the state *after* the run, so even "the editor is off" is an invariant every function must preserve).
- **What a direct proof of (P) needs from the machine.** A relation between a generic and a refined state, preserved by every function of the 116-function cycle and its ~45 helpers, with:
  - `substV`/`substT` commuting with each primitive on values (done for data; closures, Π-types and equations need the rest, and sealed programs need (C) because `substV` re-normalises them through `eval`);
  - fuel: both the explicit structural argument and the `Fuel` layer, with a "enough fuel on the refined side" lemma (refined runs can take more steps, since re-normalised sealed programs run);
  - fresh names: both runs must allocate the same `nextAbs`/`nextLoan` sequence or be related by a renaming (`AgreeUpToρ`'s `FreshRenaming`), which every allocation site must respect;
  - one invariant per bookkeeping field of `MState` (about 30 fields), most of them "equal on both runs" or "unaffected by refinement".
- **Estimate.** One spec lemma per function, 30 to 300 lines each, plus the per-field invariants: on the order of 10,000 to 20,000 lines of Lean, months of focused proof work (or a very large agent campaign), and fragile under any change to the checker. I would not start it.

### Restructuring makes (P) free

- **The design.** Make looking at a value an *effect*. Values are handles into a heap of nodes; an unknown is a node with no content yet; the machine sees a node only by asking (`view h : Option (Sh α)`, `none` for an unknown) and creates one only by `alloc`; a refinement fills a node in place (`Heap.set σ s`) instead of substituting through Ω, the stored types and every sealed program. The machine is written as a reified computation (`Prog`, a free monad over `view`/`alloc`), so running it is `exec` against a heap.
- **The probe** (`Scratch/PEffect.lean`, sorry-free): `exec_agree` is one induction on `Prog`, about 25 lines, proved once. It says two heaps with the same fresh counter that differ only on a set `D` of existing handles give the same result, and final heaps differing only on `D`, for any computation that never asks about `D`. A slice machine (variables, `0`, `S`, pairs, a projection, `let`, a match on numbers) written against the effect gets **`P_eval` with no per-construct proof**: it is `exec_agree` with `D = {σ}`. Sanity examples check that passing an unknown around asks nothing, while projecting out of one asks about it and is stuck.
- **What it also removes.** Fresh names are the same on both runs, because a refinement fills a node rather than inserting a value with its own nodes, so the renaming in `AgreeUpToρ` disappears. And the "never inspects σ" hypothesis becomes a decidable fact about the run (`σ ∉ queries`), not a semantic side condition.
- **Why not Lean's parametricity.** Lean has no internal parametricity theorem: making the machine polymorphic in the type of atoms would make (P) *true* by a free theorem, but not *provable* without proving naturality function by function. Reifying the computation (`Prog`) is what makes it one internal lemma: agreement is a fact about the tree, not about the program that built it.
- **What it does not remove.** (C) and (Sp) stay: they are exactly the runs that *do* ask about σ. A generic run that asks gets `none` and closes off or splits; the instance gets a constructor and runs. Closing off becomes "a sealed node whose content is a pending computation, re-run when viewed after its inputs are filled", and (C) is the lemma that this agrees with the direct run. Equality on atoms (conversion, generalisation records) becomes an `eq h₁ h₂` query, which counts as asking about both handles, so the subtle case, two unknowns refined to the same value, is outside (P) and inside (C)/conversion, where it belongs. (M) is unaffected.
- **Cost of the restructure.** `Machine.lean` matches on `Value` constructors in hundreds of places and substitutes through `substV`/`substT`/`substEnv`/`renormAll`. Moving to handles and `view`/`alloc`/`fill` is a rewrite of the value layer, mostly mechanical in shape but large: a multi-week lane, verdict-neutral if done right, with the 1,696 verdicts as its regression suite. Performance: running is `exec`, which builds the tree lazily through continuations, comparable to the current state monad; to be measured before landing.

### Recommendation

Do not attempt (P) against the current machine. If the project wants the stability proof in Lean, restructure the value layer around a heap with `view`/`alloc`/`fill` as effects first. (P) and fresh-name renaming then cost nothing, and the proof effort concentrates on (C), (Sp) and (M), which are the parts with real content. A sensible first step is a viability lane: port the evaluator's data slice (places, borrows, assignment, constructors, `let`/`seq`, calls that do not get stuck) to the heap representation behind a flag and compare verdicts on the suite, before committing to the whole rewrite.

## 8. Viability lane: a heap-based value layer for the data slice

Branch `stability`, commit `1c862e7a`. The restructure §7 recommended, tried on the data slice, behind a switch: a second evaluator (`Ochr/Heap/Slice.lean`) and a comparison executable (`lake exe heapslice`, `HeapSlice.lean`), neither imported by the checker. So the checker's path, and `lake build`, are untouched. The switch is a separate evaluator, not a `Config` flag, because rule switches were removed from `Config` (D70).

### What was built

- **The evaluator** runs the untyped machine's data slice over the real `Term` syntax: variables, field and predecessor places, constructors, `let`, `;`, matches on constructor values, `clone`, and calls of data functions that do not get stuck. Values are handles into a heap; the evaluator sees a node only by asking (`view`, `none` for an unknown) and creates one by `alloc`; a refinement fills a node in place (`Heap.set`). It is a reified computation (`Prog`). Reads copy: moves are not modelled, since an accepted program never reads what it moved, and §8's analysis shows moves fit the discipline anyway.
- **The proof.** `exec_agree` (one induction on `Prog`) and `P_evalH`: a run of the slice evaluator that never asks about `σ` gives the same outcome whatever `σ` is refined to, and leaves the same heap apart from `σ`. Sorry-free, axioms `propext` and `Quot.sound`, and **no case of the evaluator is inspected**: `P_evalH` is `exec_agree` with `D = {σ}`.
- **The comparison** covers every suite data function whose parameters and result are first-order data and whose body, transitively, stays in the slice: 48 functions (`Words`, `Numbers`, `Moves`, `Recursion`, `Splitting`, `Trees`, `Sugar` and others). Each runs at the generic call, at ground arguments (up to 27 combinations), and with one unknown and the rest ground, through both the heap evaluator and the real `eval` (untyped, as a called body runs).

### Results

- **251 runs:** 165 give the same value, 80 are stuck on both paths (the real machine closes off), 0 errors on both, 0 outside the slice, and **6 differences, all one kind, none a finding.** `Loop2Ok`, `SpinOk` and `KnotOk` return `Unit`; at the generic call the heap evaluator is stuck on the match, while the real machine closes the call off and normalises its result at `Unit` to `()` (D59). That is closing off and η at `Unit`, outside the slice, not a difference of representation.
- **(P) on the real machine.** Where the heap run never asked about the one unknown, the real machine's run at a ground value was compared with its generic result with that value substituted (`substV`): **46 checks, 46 agree.** This is empirical support for (P) against the real checker, with the heap's `queries` deciding which runs (P) covers.
- **The decisive measurement: whole-value walks.** With `walkOnRead`, every read views every node reachable from the value read, as the real machine's `hasHole` check on a read and its loan searches do. Of 94 runs with one unknown, the unknown is never asked about in **22** runs with reads that look only where they go, and in **3** if every read walks. Walks make (P) nearly vacuous: almost every run that so much as reads a value containing `σ` would count as inspecting it.

### Which constructs keep (P) free, and which break it

Fit the discipline, keeping (P) free:
- reads, projections and matches: they `view` only where they go;
- constructors, `let`, `;`, calls, copies: `alloc`;
- moves and assignment: a `write` to a node. The same write happens on both heaps, so agreement outside `D` survives. `exec_agree` needs one more case, and a write to `σ` itself even restores agreement there;
- [Split]: entering an arm fills `σ`, leaving it unfills. This replaces `substEnv`/`renormAll` and the 19 `substV` call sites outright; `split-model`'s worlds become node fills;
- stored types: types are values in the heap, so filling `σ` refines every type that mentions it, with no substitution;
- closing off: a sealed node is a thunk whose forcing is a run, whose queries count as the run's. Whether forcing agrees with the direct run is (C), which stays real work, but it is no longer tangled with substitution.

Break it unless redesigned, in the current `Machine.lean` (3,342 lines):
1. **Whole-value walks**, the decisive one (measured above): `hasHole` (9 sites), the loan searches `liveLoansIn`, `firstLiveLoanOnPath`, `findBorrow` (17), `owners`/`footprint`, `anyAtom`-based tests such as `typeHasRef`. Each walk views every node, unknowns included. **Fix:** keep these facts as metadata maintained when a node is written or allocated: a hole flag, and a loan index `ℓ ↦ holder`. A refinement never creates a hole or a loan (data holds no borrows), so the metadata stays right without anyone viewing `σ`.
2. **Structural keys.** Generalisation records (`neutrals`, looked up by `==` on values), `convStack`, and `==` tests on values (about a dozen) compare contents, which is viewing. **Fix:** key by node identity. D34's "re-derivations of the same closed program are replaced too" needs a canonical sealed node per (head, argument handles), which is identity, not content. Hash-consing allocation must **not** be used: `alloc` would then depend on heap contents and break `exec_agree`'s "same fresh handle".
3. **Copy-ness from a value's constructor in untyped runs** (`valType?`, 46 uses). That is a content view. **Fix:** a type per handle, set at `alloc` and unchanged by refinement (a refinement keeps the unknown's type).
4. **Fresh names.** They agree automatically on runs (P) covers. Comparisons where the instance runs further than the generic call, which is (C) and (Sp), still need a renaming, but only there.

Outside (P) by design, belonging to (C), (Sp) and conversion: `Eq` and conversion comparing `σ`'s content (comparing handle identity first makes `σ = σ` query-free), and [Split] or closing off on `σ`.

### Effort and recommendation

- **Full port.** The value layer of a 3,342-line machine: 39 value pattern matches become `view`s; substitution (`substV`, `substT`, `substEnv`, `renormAll`, `refine`) is deleted in favour of fills; the walks become metadata; generalisation is by identity; unknowns get a type per handle; the typed path's stored types move into the heap. My estimate is **4 to 8 weeks of focused agent work** to reach verdict parity on the 1,696 verdicts (the suite is the oracle, as here), plus a performance measurement. The proof side afterwards: `exec_agree` with a `write` case (small); (Sp) as fill/unfill (small); (C), a sealed thunk's forcing agreeing with the direct run (the real content); and (M).
- **Recommendation: port, with changes, in this order.**
  1. Replace the whole-value walks in the **current** machine by maintained metadata: a hole flag and a loan index. This is verdict-neutral and testable today on the suite. It is the prerequisite: without it (P) covers 3 of 94 runs instead of 22, so the port would buy almost nothing.
  2. Key generalisation records and the other value-keyed tables by identity.
  3. Give unknowns a type per handle and drop copy-ness by constructor.
  4. Then port the value layer to the heap, slice by slice (this lane's data slice first, then borrows and writes, then [Split] as fills, then closing off as thunks), each step compared with the real machine on the suite, as `heapslice` does here.

  Steps 1–3 are worth doing even if the port is not, since each removes a way for a run to depend on an unknown it has no business inspecting.

## 9. Mechanising `DecisionsCommute` against the checker (branch `decide-commute`)

The half of Conjecture 2 that needs no heap port, in Lean against the real checker: `Ochr/StabilityDecide.lean` and `Ochr/StabilitySig.lean`, sorry-free except `stability` itself, standard axioms only (`propext`, `Classical.choice`, `Quot.sound`).

### The statement, made precise

- **`fnClass` and `closeRow` now quantify over Π-type values** and say that what the generic run decided, the instance decides (they were two-sided equalities over every value). As written they were false. Take an unknown `A : Type` refined to a Π-type. At the generic run `fnClass` reads `0` and `declKind` fails ("not a function type"), and at the refinement both read the Π-type's class and row. No accepted run reads either on a non-Π type: `callFn` rejects such a callee (`callType`, `declKind`) before reading a class, and `stmtCallee`'s earlier read is followed by that `callFn`. The order is pinned by comments at both sites and by the test `CallSort` (`Examples/Functions.lean`, block `CallUnknown`, with the accepted twin `CallPi`).
- **`closeRow` excludes stuck blocks**, whose codomain is an embedded value (the match's type). Probed against the real `declKind` (`probe_blockRow_*`, with a function as control): refining the unknown match type `σ0 : Type` to `Unit` turns the row from data to `Unit`. This is η at `Unit` (D59), harmless, and the re-normalisation of the closed-off block at the refined type reads the refined row, so it belongs to (C). The other flip, data to `&`, would be Figure 16's hazard. It is unreachable: `.tRef` values come only from `.ref` terms, which D48 (2) (`checkDef`: `refTopOk`, `refsOk`) allows only as the whole declared type of a parameter, result or annotated term, never an argument. So no unknown type is refined or instantiated to a borrow type. Tests `UseBlkRef` (on the surface `&Nat` in an argument is a borrow of a place) and `UseBlkBox` (D48's rejection), block `BlockRow` in `Examples/BorrowTypes.lean`, with the accepted twin `UseBlkNat`.

### Proved

| Site | What | Theorem | Assumptions |
|---|---|---|---|
| 11 | match on a proof (field `byType`, whole) | `decisionsCommute_byType` | none |
| 8 | [Close]'s row for functions (field `closeRow`, whole as restated) | `decisionsCommute_closeRow` (`closeRow_fn`) | none |
| 3 | a function type's class, codomain a sort or an embedded value | `decisionsCommute_fnClass_shape` | class-cache soundness (A2) |
| 1, 11 | constructor and field proof-ness (D42, D45, D71), large elimination, `byTypeMatch` at the refined state | `sigDecisions_commute` | none |
| 7 | a binding's class: `refineDecl` reads only its argument | `readsSig_refineDecl` | none |
| — | the erasure flags from a declared reading (`preFlags`) | `readsSig_preFlags` | none |
| — | **refinement keeps the signature** (A1) | `onState_sig`, `sigPres_onValue`, `sigPres_onTerm` | none |

`onState_sig` was the assumption every signature-reading decision rested on. A refinement re-runs sealed programs, compares values (conversion, `Eq`) and computes field types, so it reaches a large part of the machine. The proof is a fuel induction over what it reaches: the declared-type readers of `Decide.lean` (`DecSP`, 14 functions) and 22 functions of `Machine.lean` (`RefSP`: substitution, re-normalisation, `nfSealed`, conversion, `mkEqM`, field types, `refine`). Everything that runs arbitrary code (a sealed program's re-run, a private copy, a statement) restores the state it saved, signature included, so `eval` is never analysed (`EndsAt`, `sigPres_privately`). A tactic, `sp`, takes a `do` block apart (join points once each, induction hypotheses from scope, registered lemmas), and every function went through it except `nfSealed`, done by hand in five lines. The induction is sound for the checker as it is because nothing in the machine writes `inds` or `globals`; a `ReaderT` for the signature would make that true by type.

### Left `sorry` in `stability`, and why

- **`erasure`** (site 1): `declOf` in the live scope reads embedded values' declared readings (`valueDecl` on `.abs`/`.sealed`), which commute only if evaluation preserves declared types (D55), plus the live scope's binding readings and the `constDecls` cache, which a refinement must be shown to keep. The first is typing (M); the second is an invariant like `onState_sig` (not done).
- **`fnClass`**, general case (site 3): the codomain is read in the scope of the captured values' declared readings (D55 again). The shape cases are proved, under class-cache soundness (A2: `fnClass` is the only writer of `classCache`, a machine invariant).
- **`captures`** (site 13): `closeBlock` runs its arms at both states, so this needs `RunsCorrespond`.
- **`observedType`** (site 5 of the field list, census 21): `placeType` reads values, so it needs `RunsCorrespond` and typing (M).
- **`footprint`** (site 14): **corrected claim.** This used to say containment needs only refinement keeping the environment's shape. That was wrong: a footprint also reads each binding's borrow profile. See "Footprint and D55" below.
- **`RunsCorrespond`**: symbolic naturality (N) and typed/untyped agreement (M), §5.

### Findings

- Two statement fixes, above: `fnClass`/`closeRow` over Π-type values in the generic-to-instance direction, and `closeRow` without stuck blocks. Neither is a checker bug, and no verdict changed.
- Census site 8 corrected (table, §2): for blocks it was argued only for `&`, and the `Unit` flip was missed.

### Footprint and D55 (branch `decide-footprint`)

**Footprint.** The field was false as stated. Refining `σ0 : Type` to `&Nat` makes a binding `x : σ0` borrow-typed, so a plain read of `x` then counts, and the footprint grows from `[]` to `[x]`. This is checked against the real checker by `decide +kernel` (`probe_footprint_*` in `StabilityFootprint.lean`); the value `&Nat` does check at `σ0`'s type, so `Respects` did not exclude it.
- **Restatement.** `Respects` now asks every refinement value to be borrow-free (`borrowFree`: no borrow type, borrow or loan inside). This is the paper's refinements, not a weakening: they substitute constructor values, closures and ground values; a borrow parameter's generic value is `borrow_ℓ σ` with `σ` borrow-free; and no unknown type is ever given a borrow type, because `&` is never an argument (D48 (2), tests `UseBlkRef`/`UseBlkBox`).
- **Proved** (`StabilityFootprint.lean`, sorry-free):
  - substitution keeps every term's free places (`substT_occs`, `onTerm_occs`), since it rewrites embedded values and never places;
  - the footprint is monotone in the borrow profile (`footprint_mono`): for terms with the same free places, a state whose top frame has the same size and whose bindings are borrows (by type or value) only where the other's are, with owners among the other's, has a footprint contained in the other's;
  - so the field holds whenever the refined state's profile is below the original's (`decisionsCommute_footprint`, hypothesis `ProfileLE`).
- **Left: `ProfileLE` for a refinement.** It has two parts:
  - the shape part (same top frame, same binding count) is an invariant of the kind of `onState_sig`, provable the same way, though not done;
  - the borrow part needs that a sealed type never re-normalises to `&` and that data never re-normalises to a borrow or gains a loan. These are D48 (2) and "no borrows in data" (A.5 condition 5) as invariants of runs: typing (M), not syntax.

**D55 preservation** (`ValueDeclCommutes` in `Stability.lean`): an embedded value's declared reading (`valueDecl`) survives refinement. `erasure` and the general `fnClass` rest on it. It is **not provable from the checker's code alone**:
- **A sealed program is re-run by the refinement**, and its normal form's reading must be the program's reading. That is subject reduction for the declared-type reader, and it fails at unchecked globals. With `F (n : Nat) : Nat := Nat`, the program `⌈F(σ0)⌉` reads `other`, and refining `σ0 := Z` re-runs it to `Nat`, which reads `sort 1` (`probe_d55_*`, `decide +kernel`). So it is an invariant of checked programs, an induction over the evaluator, the same scale as (P) and (M).
- **An unknown refined to `r` reads `r`'s own reading** where it read `σ`'s type's. `Respects` gives only that the types convert, and conversion of Π-types compares generic calls, not syntax. So this needs conversion to respect declared readings, which reduces to the first case.

Given `ValueDeclCommutes`, closing `erasure` still needs two invariants of the `onState_sig` kind: refinement keeps the live scope's binding readings (`mapState` never writes `decl`), and keeps the `constDecls` cache coherent (its entries are functions of the signature). Closing the general `fnClass` needs the class-cache soundness (A2). Neither field is closed on this branch.

