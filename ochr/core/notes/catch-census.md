# Census: where the checker catches a failure (2026-10-28, main 449b90d0)

The checker's monad is `M := StateT MState (ExceptT Fail …)`. A `tryCatch` over it does two things at once: it turns a failure into a value, and it rolls the whole state back to the point of the `try`, the fuel counter included. So every handler that substitutes a default also refunds the fuel the failed computation spent, and an out-of-fuel or depth-limit error caught by such a handler becomes a decision ("not a proposition", "not convertible", "no hint"). Acceptance was therefore not monotone in fuel.

The rule this census enforces: **errors, running out of fuel and depth limits are never turned into a decision**. The only catch that may turn an error into something else is the top-level verdict boundary (`checkDefs`/`checkProgram`: an error is a `rejected` verdict). Below it, a handler may (A) catch the one outcome a rule of the paper names (a `stuck` run, closed off), or rethrow after restoring bookkeeping (a `finally`). A question whose answer may legitimately be "undefined" (B) is asked of a total function returning `Option`/`Bool`, never by trying and catching.

Classes:
- **(A) rule control flow**: catches `.stuck` only, which a rule of the paper handles ([App-close], [App-head], [Seal-stuck], [Obs] typed re-observation, `split`'s search). Kept, narrowed to `.stuck` by `catchStuck`, which rethrows everything else and keeps the fuel spent.
- **(F) finally**: restores bookkeeping (a flag, a frame, a private copy) and rethrows unchanged. Kept, through `onFail`.
- **(B) definedness query**: "does this place exist?", "is this value's type readable?", "is this name declared?". Replaced by a total query (`content?`, `valType?`, `placeType?`, `funType?`, `sortOf?`, `find?`).
- **(C) swallow**: an error turned into a default. Deleted: the error propagates to the verdict.
- **(X) not a catch**: `Option.orElse`/`<|>` on `Option`, flagged by the scan only.

## Machine.lean (60 sites)

| Line | In | What it caught | Class | Replacement |
|---|---|---|---|---|
| 231 | `nfSealed` | depth ≥ 2000 → `err` | exhaustion | `exhausted` |
| 235 | `nfSealed` | stuck → `⌈t⌉` | A [Seal-stuck] | `catchStuck` |
| 291 | `repackAt` | `content p` undefined → `⊥` | B | `content?` |
| 310 | `openWrite` | `content fp` undefined → skip | B | `content?` |
| 370 | `isUnsizedType` | unknown inductive → not unsized | C | `lookupInd` |
| 380 | `unsizedCheck` | unknown σ → no type | C | `absType` |
| 397 | `unsizedTerm` | unknown inductive → false | C | `lookupInd` |
| 400 | `unsizedTerm` | unfolding fuel 8 exhausted → false | exhaustion as decision | unbounded walk over earlier definitions, a revisit is an internal error |
| 401 | `unsizedTerm` | unknown constant → none | C | `lookupGlobal` |
| 448 | `copyRead` | `placeType` / `valType` fail → `⊥` (not copy) | B (+C inside) | `placeType?` then `valType?`; unknown type is not a copy type (D53's documented rule) |
| 463 | `isCopyValue` | `valType` fail → `⊥` | B, **dead (no-switches)**: reached only with `copyByType` off | `valType?` (converted before the no-switches lane was announced) |
| 500 | `loanPath` | unknown inductive → no field names | C | `lookupInd` |
| 684 | `depFieldType` | `valType c` fail → declared `T` | B | `valType?` |
| 713 | `packedErr` | `valType` fail → `⊥` (message only) | B | `valType?` |
| 730 | `convVal` | any failure of `valType`/`conv` → false | B + C | `valType?`; `conv`'s errors propagate |
| 799 | `fieldTele` | pop frame, rethrow | F | `onFail` |
| 843 | `isCopyType` | `isPropV` fail → not a proposition | C | `isPropV` |
| 870 | `fieldTypeAt` | any failure → no hint | C | removed |
| 986 | `isBorrowable` | `sortOf` fail → not borrowable | B (+C) | `sortOf?` |
| 1033 | `placeDecl` | `fieldIsProof` fail → not a proof | C | `fieldIsProof` |
| 1085 | `declOf` `.const` | unknown name, or any failure of `valTypeDecl` → `any` | B + C | `globals.find?`; `valTypeDecl` errors propagate |
| 1135 | `declOf` `.tind` | unknown inductive → `Type₀` | C | `lookupInd` |
| 1139 | `declOf` `.ctor` | `ctorIsProof` fail → not a proof | C | `ctorIsProof` |
| 1188 | `valueDecl` | `sortOf` fail → `Type₀` | C | `sortOf` |
| 1189 | `valueDecl` | unknown global → `other` | C | `lookupGlobal` |
| 1194 | `valueDecl` | unknown σ → `other` | C | `absType` |
| 1208 | `valTypeDecl` | `isPropV` fail → not a proposition | C | `isPropV` |
| 1226 | `refineDecl` | unknown σ → `⊥` | C | `absType` |
| 1423 | `convPi` | error or stuck → not convertible | C | removed |
| 1498 | `convFn` | error or stuck → not convertible | C | removed |
| 1579 | `mkEqM` | `Option.orElse` | X | none |
| 1666 | `eval` | restore `typing`, rethrow | F | `onFail` |
| 1847 | `evalCore` `.assign` | `placeType` fail → no hint | B | `placeType?` |
| 1851 | `evalCore` `.assign` | `placeType` fail → read later | B | `placeType?` |
| 1899 | `evalCore` `.val` | `valType` of a loan fail → hint's type | B | `valType?` |
| 2062 | `evalCore` `clone` | `content` undefined → skip K2 check | B | `content?` |
| 2096 | `lentProofAssign` | `content` undefined → `⊥` | B | `content?` |
| 2107 | `lentProofAssign` | `valType` fail → error with a better message | B | `valType?` |
| 2181 | `evalCtor` | `ctorIsProof` fail → false | C | `ctorIsProof` |
| 2213 | `stmtCallee` | `fnClass`/`funType` fail → not a statement | C | removed |
| 2253 | `argHint` | any failure → no hint | C | removed |
| 2276 | `funType` | `valType` of a sealed function fail → error with a better message | B | `valType?` |
| 2353 | `runBody` | restore `modelDepth`, rethrow | F | `onFail` |
| 2362 | `runBodyCore` | depth ≥ 2000 → `err` | exhaustion | `exhausted` |
| 2374 | `runBodyCore` | `evalType` of a proof parameter's type fail → none | C | removed |
| 2385 | `runBodyCore` | `fnClass`/`funType` fail → not erased | C | removed |
| 2420 | `callFn` | `funType fv none` fail → the static type | B | `funType?` |
| 2446 | `callFn` | stuck → [Close] (or rethrow at a head call) | A [App-close], [App-head] | `catchStuck` |
| 2476 | `resultIsUnit` | any failure → not `Unit` | C | removed |
| 2631 | `sealedResultType?` | any failure → none | C | removed |
| 2936 | `movedPlace` | `content` undefined → walk up | B | `content?` |
| 2977 | `closeOffMatch` | `placeType`/`isCopyType` fail → not copy | B + C | `placeType?`; `isCopyType` errors propagate |
| 3029 | `closeOffMatch` | `placeType`/`isPropV` fail → not a proof | B + C | `placeType?`; `isPropV` errors propagate |
| 3046 | `closeOffMatch` | unknown inductive → no field names | C | `lookupInd` |
| 3165 | `observeTyping` | stuck → observe with typing | A [Obs] (D63) | `catchStuck` |
| 3187–88 | `idType` | owner's `valType` fail → next candidate, else `Unit` when both sides consumed it | B | `valType?` chain |
| 3206 | `sealedHead` | `Option` `<|>` | X | none |
| 3215 | `stuckScrutinee` | stuck → its neutral; **error → none** | A + C | `catchStuck`; errors propagate |

## Other checker modules

| Line | In | What it caught | Class | Replacement |
|---|---|---|---|---|
| Env 296 | `tick` | fuel 0 → `err "out of fuel"` (catchable) | exhaustion | `exhausted`, thrown below `Fail` |
| Env 332, 343, 354, 361, 428 | `withErased`, `withRuntime`, `withCopying`, `onCopy`, `withLive` | restore, rethrow | F | `onFail` |
| Located 18 | `atLoc` | locate an unlocated error, rethrow | F | `locateErrors` |
| Check 255 | `globalsAfterFrom` | a rejected item adds nothing to Σ | verdict boundary | kept |
| Check 278–79 | `checkDefs` | error → `rejected` | verdict boundary | kept, `exhausted` added |
| Check 288 | `runM` | run result to `Except String` (unit tests) | verdict boundary | kept, `exhausted` added |
| Run 50 | `parseProgram` | a declaration that does not parse | verdict boundary | kept |
| Surface 350 | `isPlace` | `toPlace` fails → not a place | B | total syntactic `isPlace` |
| Surface 380 | `resolve` | record the failure's range, rethrow | F | `onFail` |
| Notation 507, 590 | `checkBlock`, `#ochr_error_at` | `evalBlock Prelude` fails → no library | B | "is `Prelude` declared?" asked of the environment |

Totals (excluding the two `Option` false positives): A 4 (narrowed), F 10, B 24 (five of them also drop a swallowed error, B + C), C 26 (counting `stuckScrutinee`'s error branch), exhaustion 4, verdict boundaries 4.

## What was done (branch `no-fallbacks`, 911dfbcf and after)

**Exhaustion is its own outcome, uncatchable by type.** The coordinator's steer, after Och's `ok | outOfFuel | error`: `M := StateT MState (ExceptT Fail (ExceptT Exhausted (StateT Fuel (StateM log))))`. Out of fuel and both 2000-depth limits throw `Exhausted`, a layer below `Fail`, so no `tryCatch` on `Fail` can see it, whatever its handler matches. The fuel counter left `MState` for the layer below every exception: a caught failure no longer refunds the fuel it spent, and `Fail.stuck` lost its fuel field. At the verdict boundary exhaustion is the verdict `undecided`, neither accepted nor rejected and never what a test expects. A declaration that mentions an undecided one is undecided too (`checkDefs`), and an undecided declaration is exported to the blocks that use it (`exportsWith`), so that exhaustion never shows up as a rejection for a missing name.

**Every site above is gone or narrowed.** `Ochr/Catch.lean` has the only `tryCatch` calls in the checker: `catchStuck` (class A, rethrows every error), `onFail` (class F) and `locateErrors` (the editor's F). Class B became total queries: `content?`, `valType?` (with `indValType?` and `sealedType?`), `placeType?`, `funType?`, `sortOf?`, a `find?` for an undeclared name in `declOf`, an environment lookup for the `Prelude` block in the notation, and a syntactic `isPlace` in the parser. Class C was deleted. The rule for authors is prose, in `ochr/core/CLAUDE.md` (no build-time source scan: the user ruled that mechanical source checks are fragile).

**Verdict flips** (the ledger and the asserted total of 1401 are unchanged):
- `ClosingOff.ConvBlocks`, accepted → rejected. `convFn`'s generic run of a stuck block's function reads `q0.0` of an abstract pair and errs ("no such place q0.fst: its path does not exist in σ5"); fuzz-port R3's fix made that error mean "not convertible". The paper's [Conv-fun] says an observation exists unless its run errs, so the old answer matched the paper's least relation, but reading it from a caught error is what the rule forbids. It is a fail-safe incompleteness again (`reject def`, with the reason). The principled fix is for the generic run to read a field of an abstract value of a one-constructor type (η, as D68's `etaRefs` do elsewhere), not to catch.
- `Editor`'s `EditorErrors.Deep` and `ReRun`, `reject def`s with `#ochr_error_at` tests: their rejection was the call-depth limit on `Count(3000)`, a correct program. They are undecided now, which no test expects, and were removed with a comment. They were the only tests of an error located at call depth above 0: an accepted callee's body has no other way to fail.

**Fuel monotonicity, measured once.** Every registered program at fuels 30, 100, 300, 1,000 and 3,000, and every case study at 300, against the verdict each has at the default fuel: on this branch no decided verdict changes (361, 101, 319, 6 and 1 declarations undecided at those fuels). On the old checker (449b90d0) the same comparison found 309 changed verdicts: 300 were a later declaration rejected for an "unknown constant" whose definition had run out of fuel, and 9 were decisions made by a caught exhaustion ("not convertible", "not in Type₀", "not stuck", "type not known", "cannot infer a parameter"). None was accepted at low fuel and rejected at the default. This was a build test for a while (`Examples/FuelMonotone.lean`); it was removed because exhaustion is now uncatchable by type, so the test only guarded against a deliberate catch, which the prose standard (`ochr/core/CLAUDE.md`) already forbids.
