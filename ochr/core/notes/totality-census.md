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
| Loc | 3 | 3 (`termAddr`, its unsafe implementation, `Locs.relocate`) | yes; `termAddr` is the one exception below |
| Machine | 166 | 129 | yes: Phase 2, after `no-fallbacks` lands |
| Notation | 12 | 0 | no: the `ochr` command's macro elaborators (`MacroM`) and `evalBlock` (`unsafe`/`opaque`/`implemented_by`, evaluating a block constant at elaboration). They build `Program` values; the theorem quantifies over `Program` values, so how a value was elaborated is not checker code |
| RuleGuard | 3 | 0 | no: a build-time scan of the paper's rule names |
| Fuzz, Test, Examples | – | – | no: dev tooling and the harness |

After Phase 1 (commit 5cd27efd) the same walk reaches 1991 constants, of which 131 are not total: Machine's 129, and `termAddr` with its unsafe implementation.

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

**Fuel** (an explicit `Nat` that every recursive step decreases; running out is an error, never an answer), each marked `FUEL-OUTCOME`:
- `Check.paramNestable` walks into other inductive declarations (`paramNestableF/Go/Args`); seeded with the checker's fuel from the state.
- `Surface.resolve`/`binders` re-resolve desugared terms (`*f(ā)` bound first, a match on a non-place, a destructuring `let`); `resolveF`/`bindersF`, seeded by `resolveDecl`/`resolveProgram`/`resolveLocated`'s `fuel` (default 2000000); `checkProgram` passes its own fuel.

Where to switch when `no-fallbacks` lands: every `FUEL-OUTCOME` line (`err "out of fuel"` in Check.lean, `throw "out of fuel"` in Surface.lean) becomes its out-of-fuel outcome. Surface's resolution runs in `R` (`ExceptT String`), so today an exhausted resolution is a `(surface) out of fuel` rejection; with an `undecided` verdict, `checkProgram` must report it as that.

## What cannot be made total without changing behaviour

`Loc.termAddr` is `opaque` and `implemented_by` `ptrAddrUnsafe`: the editor keys source locations by a resolved node's address (identity, since `==` ignores binder names). A total version needs locations carried in the term itself, a change to `Term` and to every place that builds one. Until then, the argument that a proof never needs its value: the location table is empty unless `checkProgram`'s `located` is set; the consistency theorem's `Accepted` leaves it unset, and a lookup in an empty `HashMap` is `none` whatever the key.

## Phase 2 inventory: Machine.lean

166 partial definitions: 7 before the mutual block (`isPropTerm?`, `headOnly`, `constHeadOnly`, `expandRefs`, `unifyParams`, `strictSubterms`, …) and 159 in one mutual block (lines 151–3519). Call-graph SCCs of the block (a regex call graph, so an over-approximation):
- one SCC of 114 functions: the evaluator, typing, conversion, closing off, observation, [Def];
- 6 self-recursive singletons (`placeDecl`, `hasDependent`, `loanPath`, `sealedHead`, `sealedIn`, …): candidates for structural recursion;
- 39 non-recursive: they can leave the mutual block as ordinary definitions.

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
- **Runtime cost of (A), compiled.** The synthetic 40-function block, 300 runs of depth 10000, best of 3: partial 182 ms, structural fuel 209–214 ms (+15%). That is per-call overhead on calls doing almost nothing (a tick and a 3-element `mapM`); the checker's calls do far more work each, so the share on the examples should be much smaller. Phase 2 measures it: the tests executable (every example and case study, and the ledger's counterfactual runs) takes 832 s on Phase 1's commit (one run), the baseline to compare against.

**Recommendation: (A).** Order of work in Phase 2:
1. Move the 39 non-recursive functions out of the block; give the 6 self-recursive singletons structural recursion or fuel; the 7 functions before the block likewise.
2. Convert the 114-function SCC with an explicit `fuel` argument, by script, in small reviewed chunks. Seed it at the SCC's entry points (`checkFix`, `eval` from Check.lean) from the checker's budget, so it is the single budget's value, not a new magic number. It bounds call depth and never fires before the global step budget or native stack depth would.
3. Exhaustion of the explicit fuel throws `no-fallbacks`' uncatchable out-of-fuel outcome, the same one `tick` throws, so both are "I don't know".
4. Raise `maxHeartbeats` for the block if the full SCC needs it, and record Machine.lean's elaboration time before and after.
