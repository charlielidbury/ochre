# Totality census: "all checker code is total" (2026-10-28)

The rule: no `partial def`, `unsafe`, `implemented_by` or `opaque` in code the checker runs, because the consistency theorem (`Ochr/Consistency.lean`, branch `consistency-spec`) is stated about `checkProgram`, and Lean's kernel cannot see inside a partial definition. Branch `total-checker`, off main 449b90d0.

## Scope: what the checker runs

Measured, not guessed: a Lean meta script (`#reach`, kept in the session scratchpad) walks every constant reachable from `Ochr.Test.checkProgram` through types and values, following each partial definition into its `_unsafe_rec` implementation (where its real code lives). On main it reaches 1781 constants of `Ochr.*` modules, 180 of them not total.

| Module | non-total (file) | reachable from `checkProgram` | in scope? |
|---|---|---|---|
| Syntax | 5 | 5 | yes (`==` on terms and values) |
| Basic | 20 | 19 | yes (traversals; the 20th is used by Machine) |
| Pretty | 8 | 8 | yes (rejection messages are part of a verdict) |
| Obs | 4 | 4 | yes |
| Check | 5 | 6 (with `paramNestable.go`) | yes |
| Surface | 9 | 6 | yes, all 9 (the parser: the theorem is stated over surface programs) |
| Run | 2 | 0 | yes (`exportsWith`/`libWith` assemble a block's library; not reached from `checkProgram` itself) |
| Loc | 3 | 3 (`termAddr`, its unsafe implementation, `Locs.relocate`) | yes; `termAddr` is the sanctioned exception (below) |
| Machine | 166 (169 after `no-fallbacks`) | 129 (133) | yes: Phase 2 (below), done |
| Notation | 12 | 0 | no: the `ochr` command's macro elaborators (`MacroM`) and `evalBlock` (`unsafe`/`opaque`/`implemented_by`, evaluating a block constant at elaboration). They build `Program` values; the theorem quantifies over `Program` values, so how a value was elaborated is not checker code |
| RuleGuard | 3 | 0 | no: a build-time scan of the paper's rule names |
| Fuzz, Test, Examples | – | – | no: dev tooling and the harness |

After Phase 1, rebased onto `no-fallbacks` (main 0ea85bbb), the same walk reaches 2028 constants, of which 135 are not total: Machine's 133, and `termAddr` with its unsafe implementation. The rebase also made total the one partial definition `no-fallbacks` added outside Machine.lean, `Surface.isPlace` (structural).

**After Phase 2** (on main 6de9bd17, after `no-switches`): the walk reaches 2100 constants, and the only ones not total are the sanctioned exception, `Loc.termAddr` and its unsafe implementation.

## Phase 1: how each definition became total

No verdict changed: the full `lake build` (every verdict assertion, the asserted counts, the ledger) is green.

**Structural recursion** (behaviour identical). `as.map/any/all/flatMap`, `zipIdx` telescopes and match arms became explicit structurally recursive helpers in the same mutual block (`…List`, `…Arms`, `…Doms`):
- Syntax: `Place/Term/Value.beq` (+ `Term.beqArms`).
- Basic: `unitTop`, `Term.mentionsTInd`, `Term.mapFree`/`mapDoms`, `Term.mapFreePlace`, `Term.selectArms` (+ `selectArmsNth` for `as[k]?`), `Term.inlineReads`, `Term.unHead`, `Term.placeOccs`, `Term.blockOccs`, `Term.fnOccs`, `Term.formsFn`, `Value/Term.anyAtom`, `Value/Term.loans`, `Value.ownedLoans`, `Term.refsOk`/`refTopOk` (one function, `Term.refsOkAt top`, so a declared type is not a call on the same term).
- Pretty: `Term.pp`, `Value.pp`; `ppArg`/`ppHead`/`Value.ppArg`/`ppPi`/`domsPP`/`ppClosure` became non-recursive wrappers (`argWrap`/`headWrap` decide the parentheses from the shape).
- Obs: `Value.holdsBorrow`, `takeBorrow`, `setBorrowContent`.
- Check: `Term.mentionsConst`, `Term.mentionsType`, `nestViolation`, `firstOrderTerm`. Evaluation order and short-circuiting are kept, including the `(← paramNestable …)` that do-notation runs before the `if` it is written in.
- Surface: `Block.closure` (`closureAdd`/`closureAddList`), `STerm.idents`, `STerm.strip`, `STerm.show` (`atom` became a wrapper, `atomWrap`), `toPlace`, `callRoot`.

**A real termination proof:**
- `Obs.owners` (follows loans outward through borrows): measure = the borrows of Ω not yet followed, +1 while the starting label is not a borrow's; two local lemmas on `List.filter`.
- `Loc.Locs.relocate`: `termination_by sizeOf old`, lemma `Term.sizeOf_lt_of_mem_children`.
- `Run.exportsWith`/`libWith`: lexicographic `(libRank, sizeOf block, 0/1)`: the library block ranks lowest, and a used block is smaller (`Block.sizeOf_lt_of_mem_closure`, two mutual lemmas on `closureAdd`).

**Fuel** (an explicit `Nat` that every recursive step decreases; running out is exhaustion, "the checker does not know", never an answer):
- `Check.paramNestable` walks into other inductive declarations (`paramNestableF/Go/Args`); its bound is the machine fuel left (`getThe Fuel`), and running out throws `exhausted "out of fuel"`, the outcome `tick` throws, so the declaration is `undecided`.
- `Surface.resolve`/`binders` re-resolve desugared terms (`*f(ā)` bound first, a match on a non-place, a destructuring `let`); `resolveF`/`bindersF`, seeded with `checkProgram`'s `fuel`. The resolver's monad `R` has an `Exhausted` layer below its error layer, as the machine's `M` does, so no `throw`/`onFail` in `R` sees exhaustion. `runResolve` returns it, and `checkProgram` reports such a declaration as `undecided`, and every later declaration that mentions it too (`checkDefs`'s `undecidedBefore`), so that exhaustion never becomes a rejection for a missing name. `resolveProgram` (the test harnesses and the fuzzer) turns it into an error saying `undecided`, as `runM` does.

## The sanctioned exception: `Loc.termAddr`

`Loc.termAddr` is `opaque` and `implemented_by` `ptrAddrUnsafe`: the editor keys source locations by a resolved node's address (identity, since `==` ignores binder names). The user allows it as a stated exception to "all checker code is total" (`ochr/core/CLAUDE.md`; its docstring says so), because it cannot reach a verdict the consistency statement covers: it keys only the editor's location table, which is empty unless `checkProgram`'s `located` is set; `Accepted` never sets it, and a lookup in an empty `HashMap` is `none` whatever the key. Making it total would mean carrying locations in `Term` itself, a change to every place that builds one.

## Phase 2: Machine.lean

On main 6de9bd17 (after `no-switches`), Machine.lean had 166 partial definitions: 6 before its `mutual` block and 160 in it. A call graph of the block (each body searched for the other functions' names) splits it into one cycle of 116 functions and 44 outside it.

**Milestone 1 (380aae5b): everything outside the cycle.** The 44 left the block, 43 before it (in dependency order: they call nothing in the cycle) and 1 after it (`paramDecl`, unused, which calls into the cycle). Then:
- no recursion, `partial` dropped: 37 functions;
- structural recursion (list traversals as structurally recursive helpers): `isPropTerm?`, `headOnly`, `constHeadOnly`, `unifyParams`, `strictSubterms`, `placeDecl`, `hasDependent`, `loanPath`, `sealedHead`, `sealedIn`; the local `let rec`s of `openWrite` and `sealedSort?` were structural already;
- fuel from the fuel left (`fuelLeft`), running out throws `exhausted`: `expandRefs` (a refinement may mention abstract values refined in turn; it became monadic), `unsizedTerm` (follows bodies looked up in the state; its `seen` check stays an error), `ctorFields` (a loan's borrow may hold another loan).

**Milestone 2 (e4829fc1): the cycle**, 116 functions (the evaluator, conversion, typing, closing off, observation, [Def]), as recommended below and approved: an explicit fuel argument, decreasing structurally. Converted by a script, not by hand: each function takes `(fuel : Nat)` first, begins `let fuel' + 1 := fuel | exhausted "out of fuel"`, passes `fuel'` to every call into the cycle, and ends `termination_by structural fuel`; `convList`/`convTList` (equation style) by hand. The bound counts nesting depth (one unit per call into the cycle); the global step budget (`tick`) and the depth limits are unchanged. It is seeded with `fuelLeft` at every entry from outside the cycle: Check.lean, `paramDecl`, the unit tests in Examples/Units.lean and the fuzzer. Names are unchanged, so the paper's `#lean(...)` pointers still name the implementations.

No verdict changed (the full `lake build`: every verdict assertion and the 1,558 total). Machine.lean elaborates in 24 s (14 s before).

Performance, `lake exe tests` (each declaration checked 21 times, the median kept), same machine, one run each: main 6de9bd17 sums the per-declaration medians to 4208.5 ms in 1043.5 s wall; this branch (e4829fc1) to 4162.9 ms in 1030.3 s. The explicit fuel costs nothing measurable (the difference is noise). The earlier 791–832 s are not comparable: they included the ledger's counterfactual runs, which `no-switches` deleted, and predate the 21-run medians.

## Phase 1b: design probe for Machine.lean (Scratch/TotalProbe)

Two options for the evaluator's measure:
- **(A) explicit fuel argument, decreasing structurally** (Och's `Outcome.withFuel`): every function of the SCC takes `fuel : Nat` first, starts `let fuel' + 1 := fuel | <out of fuel>`, and passes `fuel'` to every call into the SCC. `termination_by structural fuel`.
- **(B) `termination_by` on a fuel kept in an inner state layer**: Lean's measure can only be a function of the arguments, so this means passing a snapshot of the state's fuel and, at each recursive call, re-reading it with a runtime check `if h : f < fuel` (the proof of decrease). Well-founded recursion, not structural.

Evidence:
- **A real slice transforms mechanically under (A).** `Scratch/TotalProbe/Slice.lean`: Machine's `substV`, `substT`, `substEnv`, `nfSealed` (with `mapM` over partially applied recursive calls, `for` loops, `withErased`, `tryCatch`) plus stubs for `eval`, `mkEqM`, `canonNeutral`, converted by a regex (add `fuel`, pass `fuel'`), elaborate as structural recursion first time (0.85 s).
- **Elaboration scales for (A), not for (B).** A synthetic block shaped like Machine's (each function ticks, maps over a list, calls two others), in `M`:

  | functions | partial | (A) structural | (B) well-founded |
  |---|---|---|---|
  | 40 | 1.0 s | 1.3 s | 8.7 s |
  | 160 | 2.9 s | 11.1 s | fails: `simp` hits `maxRecDepth` packing the block |

  Machine.lean elaborates in 14.3 s today.
- **(B) also needs a tick on every cycle.** Structural sub-calls (`substV` on a sub-value) do not tick, so the runtime check `f < fuel` would fail there; adding ticks changes fuel consumption, and fuel restored by a catch (today's `tryCatch`) breaks it until `no-fallbacks` moves the counter out of the restored state.
- **Runtime cost of (A), compiled.** The synthetic 40-function block, 300 runs of depth 10000, best of 3: partial 182 ms, structural fuel 209–214 ms (+15%). That is per-call overhead on calls doing almost nothing (a tick and a 3-element `mapM`); the checker's calls do far more work each, so the share on the examples should be much smaller. Phase 2 measures it: the tests executable (every example and case study, and the ledger's counterfactual runs) took 832 s and 791 s (two runs) on Phase 1 before the rebase onto `no-fallbacks`; Phase 2 re-measures the baseline on its own base first, since `no-switches` deletes the ledger's counterfactual runs.

**Recommendation: (A).** Order of work in Phase 2:
1. Move the 39 non-recursive functions out of the block; give the 6 self-recursive singletons structural recursion or fuel; the 7 functions before the block likewise.
2. Convert the 114-function SCC with an explicit `fuel` argument, by script, in small reviewed chunks. Seed it at the SCC's entry points (`checkFix`, `eval` from Check.lean) from the checker's budget, so it is the single budget's value, not a new magic number. It bounds call depth and never fires before the global step budget or native stack depth would.
3. Exhaustion of the explicit fuel throws `no-fallbacks`' uncatchable out-of-fuel outcome, the same one `tick` throws, so both are "I don't know".
4. Raise `maxHeartbeats` for the block if the full SCC needs it, and record Machine.lean's elaboration time before and after.
