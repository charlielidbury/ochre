# Rule audit: the paper's rules against the Lean checker

Step 1 of the user's requirement: "when I look at any example in the paper, I want to switch to the Lean to play around with the calculus and be GUARANTEED that the inference rules being applied in the Lean mechanisation are the same ones I'm reading about in the paper." This note lists, rule by rule, where that guarantee holds today and where it does not. It fixes nothing; the lead decides each divergence.

**Snapshot.** Paper `ochr/core/paper/sections/*.typ` and checker `ochr/core/lean/Ochr/*.lean` on `ochr-core` at `d671309b` (Machine.lean, Env.lean, Obs.lean, Basic.lean, Check.lean, Surface.lean unchanged since `7000ed7d`). `ochr-core-lean` has two commits not yet on `ochr-core` (`937ab2f5` D59 refined, `295882e4` array abstraction); where they change a row, the row says so. Line numbers are `file:line` on this snapshot. "Paper" means the appendix unless a body section is named; body figures are simplified versions of the appendix rules and are listed in the same row.

**Method.** Every named rule (`ir(name: …)`, `infer(name: …)`), every rule defined in prose (`[Access]`, `[Close]`, `[Type-pos]`, `[Rec]`, `[Conv-*]`, the `eq` clauses, the erasure clauses, the auxiliary definitions of @app-aux, the stuck-block definition) and every surface form was read against the code that implements it, branch by branch. Divergences were confirmed by running programs (listed under *Witnesses*, run with `lake env lean` on a scratch file under `Scratch/`, since deleted). The checker's special cases, fallbacks and "if … then … else" branches in `evalCore`, `checkTail`, `closeOffMatch`, `conv`, `idType`, `valType`, `preFlags`, `capture` and `restoreKeep` were each classified.

Status values: **MATCH** (the code performs the printed rule; mechanism differences that cannot change a verdict are noted but do not count), **DIVERGES** (a verdict or a value can differ; "(paper)" when the printed rule is the one at fault and the checker does the sensible thing), **MISSING-IN-CHECKER** (a printed premise with no code), **CHECKER-ONLY** (behaviour no printed rule states). "Known, in progress" marks the divergences already reported by reviewer-6 (W1, W5) and reviewer-7 and queued for the checker lane (task #21, examples-tour on `ochr-core-lean`).

## Summary

Rows in the table of §1: 117 (111 for paper rules and definitions, some rows grouping a family such as the four [App-*] rules; 6 for surface forms and conveniences).

| Status | Rows | Distinct issues |
|---|---|---|
| MATCH | 93 | |
| DIVERGES | 22 | 17 (five rows repeat another: T17, E28 = T5; T32 = T29; S1 = T20; S4 = E12); the paper is at fault, wholly or partly, in 5 (T1, T39, T46, O3, E12) |
| CHECKER-ONLY (surface forms with no printed rule) | 2 | plus 58 checker decisions listed in §2, 26 of which can change a verdict or a normal form |
| MISSING-IN-CHECKER | 0 standalone | 6 printed premises with no code (§3), each counted in its DIVERGES row |

Every paper rule has code; no rule is unimplemented outright. The failures of the guarantee are of three kinds: a premise the code skips (§3), a decision the code makes that no rule states (§2), and a rule the paper states wrongly (the "(paper)" rows).

### Top 10 divergences by risk

1. **A closed proof of `False` is accepted, and the paper says it is fixed** (known, in progress). `typing.typ:69` says reviewer-6's A1 is "now fixed"; `meta.typ:58` has a TODO to confirm it. On this snapshot `Scratch/A1Leak.lean` still reports `Boom : False` and `FuzzBoom` accepted. The printed rules license all three steps (generalisation records keyed by program text, @app-aux item 7; the type of an untyped observed place read from its content, item 8 and [Id]; η for `Unit`), so this is a rule bug, not only a checker bug.
2. **A `Nat` match does not check that the scrutinee's stored type is `Nat`** (new). [Split] (`appendix.typ:399`, 403) requires the place's stored type to be the inductive whose constructors the arms name. `scrutType` enforces this for declared inductives, but `evalMatch` (`Machine.lean:2155`) and `checkTail`'s `matchNat` branch (2886) split any abstract value with `Z`/`S` arms. Witness `NatT`/`NatTUse` are accepted, and `NatTUse(true)` then fails with "[Match] on a non-Nat value true": an accepted data function goes wrong at a ground instance.
3. **Closing off a stuck block manufactures η for pairs** (new). `movedPlace` (`Machine.lean:2518`) refines an abstract value of a one-constructor type to that constructor while closing off a block that moved one of its fields. The paper has no η for pairs (`appendix.typ:66`) and its block captures `q` whole. Witness `EtaP` (a read of `q.2` after such a block) is accepted while `EtaCtl` (the same read without the block) is rejected: the block path and the direct path decide differently.
4. **[T-Borrow]'s "a data type" premise is not checked** (known, in progress; reviewer-6 A12/W5.1). `evalCore .borrow` (`Machine.lean:1565`) checks only that the place's type holds no `&`. `WP4 (x : Prop) := let r = &x; ()` is accepted, as are borrows of type variables, functions and proofs.
5. **`J` with non-convertible endpoints runs its body instead of being stuck** (new). [J-stuck] (`appendix.typ:189`) makes the run stuck, so an enclosing call closes off. `jValue` (`Machine.lean:1538`) runs `t` first and returns the neutral `⌈J(A, a, b, P, h, v)⌉`, keeping `t`'s effects. Witness `JT` is accepted by `refl`; by the printed rules its statement stays a stuck equation and `refl` fails.
6. **`Eq`'s sides are not confined** (new). `Eq` is a type former, hence erased, hence a confined run ([T-Erase], `appendix.typ:326`; [T-Eq] runs both sides on the one private copy, 361). `evalCore .eq` (1653) uses `onCopy`, not `confinedCopy`, so an assignment to an outer place inside a side is silently discarded. Witness `EqConf` is accepted; the printed rules reject it ([Erase-err]). `J`'s motive `P` is likewise evaluated with copying reads but not on a private copy (1697).
7. **A closure inside a stuck block captures through the block's borrow parameter** (new, the undocumented fuzz-port R2 device). The block renames a written place `x` to `*z` (`appendix.typ:273`), so a `λ` in the arm then captures the borrow `z`, which [Fix] forbids (178, "closures capture no borrows"). `capture` (`Machine.lean:1015`, `blockRef`) captures `*z`'s content instead. Witness `BlockRef` is accepted; by the printed rules its goal's re-normalisation fails.
8. **The stuck-block definition printed in @app-block is not the one that runs** (new as a paper/code comparison; each piece has a fuzz-port finding name in the code). The paper: captures are the maximal places of `occ(m)`, `mv` only for whole variables, `M` = variables some arm leaves `⊥`. The code: `M` is a log of moved *places* (ghost moves included), captures are split into constructor fields with the block's matches pre-selected (`selectArms`), moved sub-places are moved in, proofs are never taken by `&` (R8), and occurrences inside nested functions count as reads (`blockOccs`). This is the component the paper calls the heart of "the two paths agree", and the reader cannot reproduce its captures from the appendix.
9. **`Id` evaluated by the untyped machine does not split** (new). [Obs] is stated with the typing judgement, so a stuck match in a side is closed off as a block (`appendix.typ:292`). In a callee body or a sealed program's re-run the checker observes with `eval false` (`observe`, 2700), where a stuck side makes the whole `Id` stuck. Witness `Conv1`: a hypothesis typed directly (`Eq Nat ⌈block⌉ σ1`) is not convertible with the same `Id` built by a function returning `Prop` (`⌈FId(σ0, σ1)⌉`); by the printed rules both are the same `Eq Nat ⌈block⌉ σ1`.
10. **Erasure and [Type-pos] have a third answer the paper does not have** (new). `agreeDecl` (`Machine.lean:769`) answers `.any` when a match's arms disagree on being proofs; then the pre-pass defers to "the arm that runs" (R9) and [Type-pos] accepts the term as if it were a sort. Witness `MixPos` (a type annotation `match n { Z => Nat, S _ => h }` with `h : ⊤`) is accepted; the printed [Type-pos] rejects it. Relatedly, the checker has two independent readers of "declared sort `Prop`" (`declOf`/`typeDecl` for the pre-pass and [Type-pos]; `propDecl`/`declOfDom`/`declOfVal` for classes, parameter flags and ascriptions) whose clauses differ (§2, C13).

Paper-side errors a reader would trip on (each is a "(paper)" row): the definition of type positions includes `Eq`'s and `J`'s value arguments, where [Type-pos] then demands a sort, so read literally every `Eq Nat 0 0` is ill-formed (`appendix.typ:74` with 315); [T-Match-erased] with no arms gives `⋆` at any annotated type, including data (431), where the checker, per D58, closes off; [Clone] (158) returns a copy of a borrow, duplicating `borrow_ℓ`; @app-aux item 8 gives no type to a field of a proof of a two-constructor inductive (`OrField`); the footprint order "in the order they first occur" (123) is read by the checker as evaluation order, so the conjuncts of `Id` over `x := (y := a; b)` come out `y` first (`FO`); the rule name [Ind] is used twice (185 for evaluating `D(ā)`, 447 for declarations); `appendix.typ:72` cites a rule [Pair] and `meta.typ:76` a rule [Drop], neither of which exists.

## 1. Rule table

Unqualified Lean locations are `Machine.lean`. "A." is `appendix.typ`; `eval.typ`, `typing.typ`, `obs.typ` are the body sections. Witness names refer to *Witnesses* at the end of this section.

### 1.1 Typing, erasure and declarations

| # | Rule | Printed | Lean | Status | Divergence (paper vs code) / witness |
|---|---|---|---|---|---|
| T1 | [Type-pos] (sorts are syntactic) | A.315, A.74 | `declOf` 783 with `chk`, `typePos` 870, `telescope` 882; called by `checkDef` Check.lean:55, `checkInd` Check.lean:108 | DIVERGES (paper + code) | (a, paper) A.74 makes every argument of `Eq` and `J`'s `a`, `b`, `P` a type position, and A.315 requires a sort there; the code applies [Type-pos] only to `Eq`'s and `Id`'s type argument, `J`'s `A`, `D(ā)`'s parameters, binder types, codomains, `&`'s argument and annotations. (b, code) `typePos` accepts `.any` (a zero-arm match, an unknown constant, arms that disagree on being proofs) as a sort: `MixPos` accepted. |
| T2 | Declared type and declared sort `Prop` | A.319 | `declOf` 783, `typeDecl` 855, `placeDecl` 751, `agreeDecl` 769, `valueDecl` 894, `valTypeDecl` 911; second reader `propDecl` 1446, `declOfDom` 82, `declOfVal` 1432, `headDecl` 1498 | DIVERGES (code) | Matches the printed clauses where both readers agree. Extra answers: `.any` (above); a match is `Prop` for `propDecl` if *any* arm is, for `agreeDecl` only if all are; `propDecl` sees nothing through `*p` or a field, `placeDecl` does; embedded values (`.val v`) are read from the value (`⋆` is a proof, `σ` by Δ(σ), `⌈t⌉` by re-reading `t`). See §2 C10–C14. |
| T3 | Erasure, clause 1 (proofs) and clause 2 (type formers, calls returning types, type positions) | A.320–323 | `preFlags` 955 (the decision), `eval` 1323 (after-the-fact flags kept as an INTERNAL assertion), per-former private copies in `evalCore` | MATCH | Clause 1's "a match with no arms in a proof position" is decided by `isPropV` of the annotation's *value* (`evalMatchByType` 2404): §2 C38. "Proof position" is not defined in the paper. |
| T4 | Class of a Π-type (returns types / proofs / other) | A.319, typing.typ:64 | `fnClass` 1411 (from the codomain term), `classCache` | MATCH | A stuck block's function (codomain `.val B`) gets its class at the call (`closeOffMatch` 2691): §2 C17. |
| T5 | [T-Erase] | A.326 | `eval` 1397–1400 (`settleErased`, `flushPending`), `confinedCopy` 444, `onCopy` Env.lean:283 | DIVERGES (code) | Confinement is enforced for `evalType`, `D(ā)` parameters and `J`'s endpoints, not for `Eq`'s sides (`onCopy` only, 1653) and not for `J`'s motive (1697, not even a private copy). `EqConf` accepted. An erased term restores `env` only (1400), not the goal or refinements; no verdict found that depends on it. |
| T6 | [T-Read] | A.335 | `evalCore .place` 1562, `placeType` 523, `readPlace` 311 | MATCH | Type read before the access, as printed. |
| T7 | [T-Borrow] | A.336 | `evalCore .borrow` 1565 | DIVERGES (known, in progress) | Premise "type_Ω(p) = T a data type" not checked; only `T` has no `&`. `WP4`, reviewer-6 A12 (`WP7`, `BT`, `BT2`, `BT6`, `BF`, `P5`). |
| T8 | [T-Assign] | A.337 | `evalCore .assign` 1570, `assignPlace` 478 | MATCH | |
| T9 | [T-Let] | A.338 | `evalCore .letIn` 1575 | MATCH | The binding's proof flag is "the right-hand side is a proof, or its declared type is" (1582), as A.319 says. |
| T10 | [T-Let-ann] | A.339 | Surface.lean:257 (`let x : A = t` is `let x = (t : A)`), `evalCore .ascribe` 1748 | MATCH | A match under the annotation is [Split] with annotation (1752). |
| T11 | [T-Seq] | A.340 | `evalCore .seq` 1592, `dropValue` 504 | MATCH | |
| T12 | [T-Ctor] | A.345 | `evalCtor` 1804, `evalParams` 1772, `checkParams` 1784, `unifyParams` 141 | MATCH | Parameter inference (from fields, then from the required type) is elaboration, acknowledged at A.347: §2 C25. |
| T13 | [T-Sort] | A.354 | `evalCore .sort` 1614 | MATCH | |
| T14 | [T-Type] | A.355 | `evalCore .sort` 1614 | MATCH | The surface has only `Prop` and `Type` (= `Type₀`); `Type_i`, i ≥ 1, occurs only as a computed sort (reviewer-6 W5.3). |
| T15 | [T-Ind] | A.356 | `evalTInd` 1763, `evalParams`, `checkParams`, `noBorrowParam` 1795 | MATCH | |
| T16 | [T-Ref] | A.357 | `evalCore .ref` 1672, `isDataType` 708 | MATCH | Also checked in the untyped machine. |
| T17 | [T-Eq] | A.358 | `evalCore .eq` 1653 | DIVERGES (code) | Sides on a private copy but unconfined (T5). `EqConf`. |
| T18 | [T-Pi] | A.359 | `evalCore .pi` 1615, `borrowParamCheck` 1069, `sortOf` 720 | MATCH | `sortOf` decides `Prop` from the codomain's computed sort, not its class; the two agree under [Type-pos]. |
| T19 | [T-J] | A.364 | `evalCore .prim "J"` 1680, `jValue` 1538, `jErased` 1528 | DIVERGES (code) | (a) Value: see E25. (b) `P` is evaluated with copying reads but not on a private copy. (c) No check that `F(v_a)`, `F(v_b)` are types of one sort. |
| T20 | [T-Rewrite] | A.369 | `rewriteGoal` 1299, `evalCore .prim "rewrite"` 1728; tail form `checkTail` 2862 | DIVERGES (code) | (a) A rewrite whose `b` does not occur in the goal is an error ("does not mention"); the printed rule gives `G' = G`: `RwNothing` rejected. (b) The goal is taken from any `hint`, so a rewrite also works as a constructor field or under `Id`'s type, beyond A.371's list. (c) In tail position the rewritten goal becomes the path's goal and the body may split (a [Tail-rewrite] with no printed rule, §2 C24). |
| T21 | [T-Global] | A.376 | `evalCore .const` 1602 | MATCH | A global whose Π-type returns proofs evaluates to `⋆` (1604), which [Erase-proof] also gives. |
| T22 | [T-Const] | A.377 | `evalCore .const` 1602 | MATCH | |
| T23 | [T-Fix] | A.378 | `evalCore .fix` 1621, `capture` 1015, `checkFix` 2967 | MATCH | Capture divergences are E18. |
| T24 | [Call-type] | A.384, typing.typ:26 | `callType` 1932, `paramFlags` 1466 | MATCH | An argument whose type is unknown (`none`) is not checked (`expectTy` 1315): §2 C19. |
| T25 | [T-Call] | A.390, typing.typ:27 | `evalCall` 1840, `callFn` 2008, `runBody` 1963 | MATCH | |
| T26 | [T-Call-proof] | A.391 | `callFn` 2015–2019, 2044–2047, `endBorrowArgs` 1947 | MATCH | Adds: a borrow argument of an erased call must be whole (`wholeBorrowArgs` 2043): §2 C28. |
| T27 | [Rec] | A.395, typing.typ:31 | `recCheck` 2125, `headOnly` 89, `checkFix` 2972–3030, `RecCtx` Env.lean:90 | MATCH | Candidates accumulate across state restores (`restoreKeep`); with a declared `by` there is one candidate, so this changes no verdict. |
| T28 | [T-Match] | A.402 | `evalMatch` 2155, `evalMatchInd` 2467 | MATCH | On a constructor the code checks the value's inductive, not the place's stored type; both agree in every well-formed state. |
| T29 | [Split] | A.403, typing.typ:28 | `evalMatch` 2164, `evalMatchInd` 2480, `splitThenClose` 2286, `splitArmsThenClose` 2293, `ctorRefinement` 2360, `refine` 2150, `scrutType` 2370 | DIVERGES (code) | (a) The stored-type premise (A.399) is checked only for declared inductives; a `Nat` match splits an abstract value of any type: `NatT`, `NatTUse`, `NatTStmt` accepted, `NatTRun` fails at the ground instance. (b) `M` is not the printed set: C10. |
| T30 | [Split-gen] | A.404 | `generalizeNeutral` 2176, `canonNeutral` 2210 | MATCH | Both license step 1 of A1 (known, in progress). |
| T31 | [T-Split-goal] | A.409 | `checkTail` 2827, `splitTarget` 2810, `findSplit` 2783, `stuckScrutinee` 2747, `generalizeFound` 2801 | MATCH | Δ(σ) from a closed declared codomain only (A.411 says so). Code only: chains are followed at most 64 links; only top-level function heads can be named. |
| T32 | [Tail-split] | A.416 | `checkTail` 2892–2902, 2939–2947 | DIVERGES (code) | Same missing stored-type premise for `Nat` as T29. |
| T33 | [Tail-gen] | A.417 | `checkTail` 2903, 2948 | MATCH | |
| T34 | [Tail-match] | A.418 | `checkTail` 2890, 2934 | MATCH | |
| T35 | [Tail-let] | A.419 | `checkTail .letIn` 2868 | MATCH | |
| T36 | [Tail-seq] | A.420 | `checkTail .seq` 2880 | MATCH | |
| T37 | [Tail-end] | A.421 | `checkTail` 2954 | MATCH | The goal is passed as a hint (constructor parameters, `rewrite`). |
| T38 | [T-Match-prop] | A.430 | `evalMatchByType` 2422–2426, `bindDataFields` 674, `largeElim` 664 | MATCH | `Ω₁^i` is built by binding a data field to a fresh local and renaming the arm, not by writing `C_i(…)` into `p`; the arm is erased, so no verdict differs. |
| T39 | [T-Match-erased] | A.431 | `evalMatchByType` 2393–2406, 2436–2464 | DIVERGES (paper) | With no arms the printed rule gives `⋆ : B` for any annotation `B`, data included, and requires `D` in `Prop`. The code gives `⋆` only when `B` is a proposition, and otherwise closes the match off as a stuck block (D58, as [Match-none] says for the machine); it accepts any empty inductive, `Type₀` ones too (`FromVoid`, `FromVoidNT`, same verdicts as [Split] with no arms). |
| T40 | [Tail-prop] | A.432 | `checkTail` 2910–2930 | MATCH | No arms: any empty inductive, as T39. |
| T41 | Subsingleton elimination | A.427, 434 | `largeElim` 664, `fieldTermIsProp` 647, `subsingletonMsg` 699 | MATCH | |
| T42 | [Def] | A.442, typing.typ:29 | `checkFix` 2967, `checkDef` Check.lean:48 | MATCH | `f` is always bound in the body frame (`self`, 3009); D31 (2972) rejects any use without `by`, which is the printed binding rule. |
| T43 | [Ind] (declaration) | A.447 | `checkInd` Check.lean:99, `firstOrderTerm` Check.lean:87 | DIVERGES (code) | (a) "Built from `D(x̄)`" (uniform recursive occurrences, A.447/450) is not checked: `NU` (a field `NU(Nat)` inside `NU(A)`) accepted. (b) "`D ∉ Σ`" misses the built-in `Nat` and `Unit` (known, in progress; reviewer-6 A14): `RN` accepted. (c) Code only: constructor names unique program-wide; `copy` declarations (§3). |
| T44 | [Const] | A.448 | `checkDef` Check.lean:56–64 | MATCH | |
| T45 | Sorts of type values | A.315 | `sortOf` 720, `sealedSort?` 980, `isPropV` 967, `typeClass` 1515 | MATCH | |
| T46 | Types of places and values (item 8) | A.131 | `placeType` 523, `valType` 550, `sealedType` 575, `indValType` 630 | DIVERGES (paper + code) | (a, paper) `type(p.g)` is defined only when `cont(p)` is `C(…)`, or `⋆` with `C` the only constructor; a field of a proof of `Or` has no type, so `OrField` has no derivation; the code types it from the pattern's recorded constructor and accepts. (b, code) `typeof(⌈t⌉)` is not printed; the code re-types `t` from ε (`sealedType`), and types a live loan by its borrow's content. (c) Both type an untyped binding from its content (A1 step 3, known, in progress). |
| T47 | The generic call (item 10) | A.133 | `checkFix` 2986–3002, `convPi` 1130–1141, `convFnRun` 1211–1222 | MATCH | Three copies of the same construction. On `ochr-core-lean` (`937ab2f5`) an abstract value of type `Unit` is `()`. |
| T48 | Borrow types: `&A` only of data, `&` only at the top of a declared type | A.72 | `isDataType` 708, `Term.refsOk`/`Term.refTopOk` Basic.lean:398/415, `checkDef` Check.lean:52 | MATCH (for `&A`) | The type former is checked; the borrow *term* is T7. Closures under a type parameter, including `&Box(Π(y : &Nat). &Nat)`, are accepted (`BorrowBoxF`; known, in progress, reviewer-6 W5.2); A.72 forbids `&` inside another type, which `Box(Π(y : &Nat). &Nat)` has. |

### 1.2 Conversion and `Eq`

| # | Rule | Printed | Lean | Status | Divergence / witness |
|---|---|---|---|---|---|
| V1 | [Conv-refl] | A.302 | `conv` 1079, `Value.beq` Syntax.lean:141 (binder names and recorded parameters ignored) | MATCH | |
| V2 | [Conv-cong] | A.303 | `conv` 1084–1090, `convT` 1158 | DIVERGES (code, completeness only) | Two closures that are not `==` go straight to `convFn` (1094–1096): there is no congruence case for closures, so two closures with convertible captures and the same code are compared by observation. |
| V3 | [Conv-unit] | A.304 | `unitTop` Basic.lean:33, `conv` 1081 | MATCH | |
| V4 | [Conv-pi] | A.305 | `convPi` 1114 | MATCH | A comparison that errors or gets stuck answers "not convertible" (1154): §2 C52. |
| V5 | [Conv-fun] | A.306 | `convFn` 1186, `convFnRun` 1202 | MATCH | "Least": the code answers `false` when the pair is already being compared (`convStack`, 1189), where the paper compares by [Conv-refl]/[Conv-cong]; incompleteness only. |
| V6 | η for `Unit` | A.281, A.307 | `mkEqM` 1269, `convFnRun` 1255 | MATCH | On `ochr-core-lean` (`937ab2f5`) replaced by η-normal values: abstract `Unit` values are `()`, and a stuck call returns `()` when its declared codomain is `Unit` *or its type computes to `Unit`* (`resultIsUnit`). That brings back a [Close] row for `Unit`, partly read from a computed type; A.603 (note 17) will need rewriting when it merges. |
| V7 | `eq`, same constructor (injectivity) | A.280 | `mkEqM` 1270–1285 | MATCH | If the equation's type is not `D(ā)`, the field types come from the values' recorded parameters; if neither is known, no injectivity (§2 C55). |
| V8 | `eq`, reflexive | A.281 | `mkEqM` 1266 | MATCH | Checked before injectivity; same results. |
| V9 | `eq`, distinct constructors | A.282 | `mkEqM` 1286, `distinctCtors` Basic.lean:58 | MATCH | |
| V10 | `eq`, otherwise | A.283 | `mkEqM` 1287 | MATCH | |
| V11 | `and` | A.284 | `mkAnd` Basic.lean:27, `andList` Basic.lean:45 | MATCH | |

### 1.3 Observation, `Id`, closing off, sealed programs, stuck blocks

| # | Rule | Printed | Lean | Status | Divergence / witness |
|---|---|---|---|---|---|
| O1 | Place occurrences `occ(t)` | A.119 | `Term.placeOccs` Basic.lean:223, `Term.freeOccs` Basic.lean:298 | MATCH | Stuck blocks use a different function, `Term.blockOccs` (O10). |
| O2 | Owners | A.115, obs.typ:9 | `owners` Obs.lean:90 | MATCH | |
| O3 | Footprint `W(t, u)` | A.121–123, obs.typ:13 | `footprint` Obs.lean:111 | DIVERGES (paper ambiguous) | "In the order they first occur": `placeOccs` lists an assignment's right-hand side before its own place (evaluation order), so `x := (y := a; b)` contributes `y` then `x`. The conjunct order of `Id` is what a user destructures with `Intro(l, r)`: `FO` (text order) rejected, `FO2` (evaluation order) accepted. |
| O4 | [Obs] | A.289 | `observe` 2700, `endAll` 272 | DIVERGES (code) | The printed rule observes with the typing judgement, so a stuck side is closed off (A.292). In untyped runs (a callee body, a sealed program's re-run, a type-returning function's body) `observe false` makes the whole `Id` stuck: `Conv1` rejected. |
| O5 | [Obs-borrow] | A.290 | `convFnRun` 1226–1244 | MATCH | |
| O6 | [Id] | A.296, obs.typ fig-id | `idType` 2715, `footprint`, `mkEqM`, `andList` | MATCH (known issue) | `T_i` is the stored type, else the content's type (as A.131 prints), else the observed values' type (code only, R1 residual). The content fallback is A1 step 3 (known, in progress). |
| O7 | [Close] | A.227–243, eval.typ:49–64 | `closeCall` 2080, `declKind` 1919, `callFn` 2032 | MATCH | The final read `K` of each fill is an observation read (`peek`, copies); a borrow argument must be whole (A.161). INTERNAL assertion of the precondition (2085). See V6 for `ochr-core-lean`. |
| O8 | [App] | A.217 | `callFn` 2052–2054, `runBody` 1963, `popFrame` 514 | MATCH | |
| O9 | [App-close], [App-head], [App-neutral], [App-neutral-head] | A.218–221 | `callFn` 2048–2061 | MATCH | The discarded partial run is rolled back by the exception, which also rolls back fresh-name counters; nothing from it survives, so name reuse is harmless. |
| O10 | Stuck blocks `block(Ω, m, B, M)` | A.267–275, eval.typ:80, typing.typ:50 | `closeOffMatch` 2543, `splitArmsThenClose` 2293, `armMoves` 2346, `movedPlace` 2518, `Term.blockOccs` Basic.lean:248, `Term.selectArms` Basic.lean:152 | DIVERGES (code) | The printed capture rule is not the one that runs (top-10 item 8): `M` is place-granular and counts ghost moves; captures are split per constructor field and matches pre-selected; a moved capture is `mv` even when it is not a whole variable; a proof is never taken by `&`; nested-function occurrences are reads; and closing off can refine a one-constructor abstract value (`EtaP` accepted, `EtaCtl` rejected). |
| O11 | [Seal] | A.261 | `nfSealed` 235 | MATCH | Depth bound 2000 (§2 C31). |
| O12 | [Seal-stuck] | A.262 | `nfSealed` 250, `canonNeutral` 2210 | MATCH | |
| O13 | [Seal-err] | A.263 | `nfSealed` 246 | MATCH | |
| O14 | Substitution and normal form (item 6) | A.125 | `substV` 166, `substT` 183, `substEnv` 212 | MATCH | A type's sealed programs re-run with copying reads (219, 223). |
| O15 | Refinement and generalisation (item 7) | A.127 | `refine` 2150, `generalizeNeutral` 2176, `canonNeutral` 2210, `renormAll` 2220, `expandRefs` 129, `strictSubterms` 153 | MATCH | `renormAll` re-normalises Ω, stored types and the goal, not Δ; no verdict found that depends on it. |
| O16 | Global records, private copies | A.105 | `restoreKeep` Env.lean:245 | MATCH | |

### 1.4 The machine

| # | Rule | Printed | Lean | Status | Divergence / witness |
|---|---|---|---|---|---|
| E1 | [End ℓ] | A.144, eval.typ:12 | `endBorrow` 256 | MATCH | Wholeness (A.161) at 266. |
| E2 | [Access] | A.147 | `accessPath` 279, `accessInside` 287, `accessNeutralHead` 297 | MATCH | |
| E3 | Content and update (item 1) | A.109 | `content` 31, `setPlace` 38, `stepV` Obs.lean:30 | MATCH | |
| E4 | `L^R`, `L^M` (item 2) | A.111–113 | `firstLiveLoanOnPath` 47, `liveLoansIn` Obs.lean:78 | MATCH | |
| E5 | Drop (item 7) | A.129 | `dropTopBind` 493, `dropValue` 504, `popFrame` 514 | MATCH | |
| E6 | [Copy] | A.152, eval.typ:16 | `readPlace` 325–333, `copyRead` 342, `isCopyValue` 346, `isCopyType` 602 | MATCH | `⋆` is copied by value (325), which the type also gives. |
| E7 | [Read] | A.153, eval.typ:17 | `readPlace` 334–338 | MATCH | |
| E8 | [Move] | A.154, eval.typ:18 | `readPlace` 323 | MATCH | |
| E9 | [Read-err] | A.155 | `readPlace` 319–322, 330, 332 | MATCH | |
| E10 | [Borrow] | A.156, eval.typ:13 | `borrowPlace` 463 | MATCH | |
| E11 | [Borrow-err] | A.157 | `borrowPlace` 467–471 | MATCH | |
| E12 | [Clone] | A.158 | Surface.lean:229, `evalCore .prim "clone"` 1739 | DIVERGES (paper) | The printed rule copies any content, a borrow included, which would duplicate `borrow_ℓ`; the code reads with `readPlace`, which moves a borrow (and errs on `⊥`): `CB` rejected. The printed premise needs "not `⊥`, not a borrow". |
| E13 | [Assign] | A.159, eval.typ:19 | `evalCore .assign` 1570, `assignPlace` 478 | MATCH | |
| E14 | [Let] | A.166 | `evalCore .letIn` 1575 | MATCH | |
| E15 | [Seq] | A.167 | `evalCore .seq` 1592 | MATCH | |
| E16 | [Ctor] | A.172 | `evalCtor` 1804 | MATCH | |
| E17 | [Global] | A.181 | `evalCore .const` 1602 | MATCH | |
| E18 | [Fix] and capture | A.178, A.182, eval.typ:103 | `evalCore .fix` 1621, `capture` 1015 | DIVERGES (code) | (a) `blockRef` capture through a block's borrow parameter: `BlockRef` accepted, where the printed capture fails. (b) The declared type recorded with each captured value (A.178, note 27) is recorded only for proofs, by inlining `(⋆ : T)` into the code (1058–1064); a captured datum's type is re-derived from its value (`valType`, `sealedType`). (c) A runtime capture must be whole (1045); the printed capture only excludes `⊥` and borrows. |
| E19 | [Pi] | A.183 | `evalCore .pi` 1615 | MATCH | |
| E20 | [Sort] | A.184 | `evalCore .sort` 1614 | MATCH | |
| E21 | [Ind] (evaluating `D(ā)`) | A.185 | `evalTInd` 1763 | MATCH | Same name as the declaration rule A.447 (§4). |
| E22 | [Ref] | A.186 | `evalCore .ref` 1672 | MATCH | |
| E23 | [Eq] | A.187 | `evalCore .eq` 1653 | MATCH | |
| E24 | [J] | A.188 | `evalCore .prim "J"` 1682–1691, `jValue` 1538 | MATCH | |
| E25 | [J-stuck] | A.189 | `jValue` 1538–1541 | DIVERGES (code) | The printed outcome is `stuck` (the enclosing call closes off, `t` never runs); the code runs `t` and returns `⌈J(A, a, b, P, h, v)⌉`, which re-normalises to `v` when the endpoints become convertible: `JT` accepted, where the printed rules leave `Eq Nat ⌈…⌉ 5`. |
| E26 | [Erase-proof] | A.196 | `eval` 1333–1343, `preFlags` 955 | MATCH | |
| E27 | [Erase-type] | A.197 | `eval` 1399, `confinedCopy` 444, per-former copies | MATCH | Except `Eq`'s sides (T5). |
| E28 | [Erase-err] | A.198 | `checkConfined` 423, `settleErased` 435, `flushPending` 455, `evalCall` 1864 | DIVERGES (code) | As T5: not raised for `Eq`'s sides (`EqConf`). The argument exemption for erased calls covers arguments written `&p` or `p` only (1856), as printed. |
| E29 | [Args-nil], [Args] | A.207–208 | `evalCall` 1851–1860 | MATCH | |
| E30 | [Call] | A.211 | `evalCall` 1840, `callFn` 2008 | MATCH | The head is read in place (1844). |
| E31 | [Call-err] | A.212 | `callFn` 2011–2013 | MATCH | |
| E32 | [Match] | A.248 | `evalMatch` 2161, `evalMatchInd` 2474 | MATCH | |
| E33 | [Match-stuck] | A.249 | `evalMatch` 2164–2166, `evalMatchInd` 2481, 2487 | MATCH | |
| E34 | [Match-err] | A.250 | `evalMatch` 2163, 2171, `matchContent` 365 | MATCH | Also errs on a ghost at runtime (the printed rule lists "undefined or ⊥"; a ghost is neither a constructor nor a neutral, so no rule applies either way). |
| E35 | [Match-prop] | A.251 | `evalMatchByType` 2419–2426 | MATCH | A one-constructor match on a proof of a non-subsingleton returns `⋆` without running its arm; the arm must be a proof, so [Erase-proof] gives the same. |
| E36 | [Match-none] | A.252 | `evalMatchByType` 2401–2402 | MATCH | |

### 1.5 Surface forms

| # | Form | Printed | Lean | Status | Notes |
|---|---|---|---|---|---|
| S1 | `rewrite h in t`, `rewrite ← h in t` | A.46, A.369–371, overview.typ | Surface.lean:299, T20 | DIVERGES | See T20. |
| S2 | `split f in t`, `split f { C(x̄) => t, … }` | A.50, A.409–411 | Surface.lean:301–304, `checkTail` 2827–2861 | MATCH | The arm form binds a hidden variable `⋄split` and matches it (2851). |
| S3 | Destructuring `let ⟨x, y⟩ = p; u`, `let (x, y) = p; u` | impl.typ (named only) | Notation.lean:78–243 (`destructure`) | CHECKER-ONLY | No printed rule or desugaring: a one-arm match on `Intro` or `Mk`, nested patterns get fresh names `⋄k`, and a non-place right-hand side is first bound to `⋄0`. |
| S4 | `clone(p)` | A.47, A.158 | Surface.lean:229 | DIVERGES | See E12; `clone` of a non-place is a parse error. |
| S5 | Notation: `S t`, numerals, `()`, `A × B`, `(a, b)`, `⊤`, `refl`, `P ∧ Q`, `⟨h, k⟩`, `t.1`, `t.2`, pattern variables as places | A.66, A.70, calculus.typ:30 | Surface.lean:198–309 | MATCH | `t.1` of a term that is not a place is a projection (`Term.fst`, `evalCore` 1641), an error on a neutral pair in typed code: §2 C20. `S` unapplied is a `λ` (Surface.lean:194). |
| S6 | Conveniences `cong`, `trans`, `symm`, `(t : A)`, `λ`, `→` | A.612 (note 23) | Surface.lean:220–223, `evalCore` 1660, 1708–1727, 1746–1758 | CHECKER-ONLY (acknowledged) | No printed typing rules. `symm` and `trans` have cases for `True` and `False` (R7). |

### Witnesses

Run on `ochr-core` `d671309b` as `ochr RA uses Std { … }` with `#eval IO.println (run "RA" RA).show` (the file is gone; paste to re-run). Verdicts are the checker's.

```
def EqConf (x : Nat) : Id Nat (let T = Eq Nat (x := 5; 0) 0; x) x := refl                          -- accepted
def NatT (T : Type) (x : T) : Nat := (match x { Z => 0, S _ => 1 })                                -- accepted
def NatTUse (b : Bool) : Nat := NatT(Bool, b)                                                       -- accepted
def NatTRun : Nat := NatTUse(true)              -- rejected: [Match] on a non-Nat value true
def NatTStmt (T : Type) (x : T) : Id Nat (match x { Z => 0, S _ => 0 }) 0 := match x { Z => refl, S p => refl }   -- accepted
inductive NU (A : Type) := NNil | NCons(h : A, t : NU(Nat))                                        -- accepted
def RwNothing (a : Nat) (b : Nat) (h : Eq Nat a b) : ⊤ := rewrite h in refl   -- rejected: the goal ⊤ does not mention σ1
def EtaP (q : Nat × Nat) : Nat := (match q { Mk(a, b) => (let v = a; ()) }; q.2)                   -- accepted
def EtaCtl (q : Nat × Nat) : Nat := q.2        -- rejected: no such place q.2
def JF (a : Nat) (b : Nat) (h : Eq Nat a b) (x : &Nat) : Nat := J(Nat, a, b, λ(z : Nat) : Type => Nat, h, (*x := 5; 0))   -- accepted
def JT (a : Nat) (b : Nat) (h : Eq Nat a b) : Id Nat (let c = 0; JF(a, b, h, &c); c) 5 := refl    -- accepted
def MixPos (h : ⊤) : Nat := (let n = 0; let x : (match n { Z => Nat, S _ => h }) = 5; x)          -- accepted
inductive Or (P : Prop) (Q : Prop) : Prop := Inl(p : P) | Inr(q : Q)
def OrField (P : Prop) (Q : Prop) (h : Or(P, Q)) : ⊤ := match h { Inl(p) => (let k = p; refl), Inr(q) => refl }   -- accepted
def BlockRef (n : Nat) (x : Bool) : Id Bool (match n { Z => (x := true; let f = (λ(u : Unit) : Bool => x); ()), S _ => () }; x)
                                            (match n { Z => (x := true; ()), S _ => () }; x) := match n { Z => refl, S _ => refl }   -- accepted
def FO (a : Nat) (b : Nat) (x : Nat) (y : Nat) (h : Id Unit (x := (y := a; b)) (y := b; x := a)) : Eq Nat b a := match h { Intro(l, r) => l }
                                               -- rejected: the body has type Eq Nat σ0 σ1, but the goal is Eq Nat σ1 σ0
def FO2 … : Eq Nat a b := match h { Intro(l, r) => l }                                              -- accepted
def CB (x : &Nat) : Nat := (let y = clone(x); clone(*x))   -- rejected: no such place *x (clone moved x)
def FId (n : Nat) (x : Nat) : Prop := Id Nat (match n { Z => x, S _ => x }) x                     -- accepted
def Conv1 (n : Nat) (x : Nat) (h : Id Nat (match n { Z => x, S _ => x }) x) : FId(n, x) := h
          -- rejected: has type Eq Nat ⌈(fix _ … match n { … })(σ0, σ1)⌉ σ1, but the goal is ⌈FId(σ0, σ1)⌉
def WP4 (x : Prop) : Unit := (let r = &x; ())                                                       -- accepted (known)
def BorrowBoxF (x : &Box(Π(n : Nat). Nat)) : Unit := ()                                             -- accepted (known)
inductive Void : Type
def FromVoid (v : Void) : Nat := match v {}                                                         -- accepted
def FromVoidNT (v : Void) : Nat := (let k : Nat = match v {}; k)                                    -- accepted
ochr RN { inductive Nat := Zero | One }                                                             -- accepted (known)
```

`BlockRef`'s path was confirmed by reading the code, not by a switch: the block passes `x` by `&` (it is assigned), the `λ` inside reads it as `*z`, and when the tail split refines `n := Z` the goal's sealed program re-runs the arm and `capture` takes `*z`'s content through `blockRef` (1025). A control `BlockCtl`, the same statement without the `λ`, is accepted too. A1's program is `Scratch/A1Leak.lean` (all 12 declarations accepted on this snapshot).

## 2. CHECKER-ONLY decisions

Every branch below decides something that no printed rule states. The guarantee fails on each one that can change a verdict or a normal form; those are marked **verdict**. The rest are internal (bookkeeping, assertions, resource bounds, elaboration) and are marked as such. Grouped by function, in the order of the lead's list.

**Reads, captures, types of values**

- C1 `readPlace` 325: content `⋆` is returned without a move, decided on the value. Internal (a proposition is a copy type anyway).
- C2 `copyRead` 343: if the place's type cannot be computed, the read moves. Internal (fails safe).
- C3 `readPlace` 323: a borrow is moved even by an erased read (`clone(x)`). **verdict**: `CB`. The paper says erased reads are [Copy], whose premise excludes borrows, and gives no rule for this case.
- C4 `readPlace` 327–331, `evalCall` 1844, `closeOffMatch` 2669: "in place" reads (a call's head; a block's read-only capture) consume nothing but require a whole value. Stated for call heads (A.178); for block captures A.272 says "a copy".
- C5 `capture` 1019–1027, `Binding.blockRef` Env.lean:40: capture through a stuck block's borrow parameter. **verdict**: `BlockRef`.
- C6 `capture` 1055–1064: a captured proof's declared type is recorded by inlining `(⋆ : T)` into the closure's code; a captured datum's type is not recorded and is re-derived from its value. **verdict** where the value's type differs from the binding's declared type (the A1 family is of this kind).
- C7 `capture` 1045: a runtime capture must be whole.
- C8 `valType` 561–569, `sealedType` 575, `indValType` 630: types of sealed programs (by re-typing their text from ε), of live loans (by their borrow's content), and of constructor values without recorded parameters (by unification). **verdict**: these types feed `placeType` for untyped bindings, hence [Id]'s `T_i`.
- C9 `placeType` 540–547: a field place's type comes from the constructor recorded in the pattern, not from the content. **verdict**: `OrField` (the paper leaves it undefined).

**Declared types, erasure, [Type-pos]**

- C10 `agreeDecl` 769, `preFlags` 956, `eval` 1383–1394: arms that disagree on being proofs give `.any`; the pre-pass then abstains and the after-the-fact flags of the arm that ran decide erasure (R9). **verdict**.
- C11 `declOf` 796–801: an unknown constant is `.any`. Internal (the machine reports the unknown name).
- C12 `valueDecl` 894–908: an embedded value's declared type is read from the value (`⋆` → proof, `σ` → Δ(σ), `⌈t⌉` → `declOf t`, a closure → its code). **verdict** in principle: A.559 (note 3) says proof-hood is never read from a value; embedded values have no declared type in the paper.
- C13 Two readers of "declared sort `Prop`": `declOf`/`typeDecl` (pre-pass, [Type-pos]) and `propDecl`/`declOfDom`/`declOfVal`/`headDecl` (`fnClass`, `paramFlags`, ascriptions, `leafProof`). They differ on matches (all arms vs any arm), on places through `*` and fields, and on constants (`valTypeDecl` vs `ty == Prop`). The pre-pass assertion (1391) compares the pre-pass with `eval`'s after-the-fact flags, not with `fnClass`. **verdict** wherever they disagree (none found by the suite).
- C14 `refineDecl` 932: a binding whose declared type is a Π-type only after computing (`p : Pow(Nat)`) takes what the value says.
- C15 `eval` 1333: `.val` terms and call heads skip the pre-pass; their flags are the after-the-fact ones.
- C16 `eval` 1399–1400: an erased term restores `env` only; goal, refinements and Δ changes made inside it are kept. Internal so far (refinements happen only in arms, which restore everything).
- C17 `fnClass` 1420, `declKind` 1924, `propDecl` 1459: a stuck block's function has codomain `.val B`; its class is passed at the call, its [Close] row and proof-hood of its parameters are read from the type *value* `B`. A.229 says the row is chosen by "the type of a stuck block", so the row matches; the parameter flags are code only.
- C18 `declOfVal` 1432: whether a captured variable is "declared `: Prop`" is read from its value's class. **verdict** in principle (note 27 says the declared type is recorded).
- C19 `expectTy` 1315: when a typed evaluation returns no type, the check is skipped (`callType` 1942, `evalCore .assign` 1572, constructor fields 1834). Internal where `none` cannot arise in typed code; `.fst`/`.snd` of a non-`Pair` type is one place it can.

**Terms, calls, `J`, `rewrite`**

- C20 `evalCore .fst/.snd` 1641–1652: projections of terms; on a neutral pair, an error in typed code and stuck in untyped code. **verdict**.
- C21 `evalCore` 1708–1727: `symm`/`trans` accept `True` and `False` (R7). Conveniences (A.612).
- C22 `rewriteGoal` 1308: "does not mention" is an error; a proof of `True` rewrites nothing (1303). **verdict**: `RwNothing`.
- C23 `.prim "peek"`, `.prim "inplace"` (1739–1744): internal primitives for observation reads and in-place reads.
- C24 `checkTail` 2862–2867: [Tail-rewrite], unprinted. **verdict** (completeness): the rewritten goal is the path's goal, so its body may split.
- C25 `evalCtor` 1813–1832, `fieldTypeAt` 618, `argHint` 1871, the goal and annotation as hints: parameter inference. Elaboration, acknowledged (A.347).
- C26 `evalCore .ascribe` 1746–1758: the ascription `(t : A)`, acknowledged (A.612); `(⋆ : T)` is also the carrier of C6.
- C27 `callFn` 2015–2019: calling the value `⋆` is a proof call. Internal (`⋆` in head position arises only from a proof-returning function).
- C28 `callFn` 2043, `wholeBorrowArgs` 2070: a borrow argument of an *erased* call must be whole (fuzz-port P). **verdict**: A.161 requires it only for calls that close off.
- C29 `callFn` 2028: the class and row come from the function value's own Π-type, falling back to the static type if that cannot be computed.
- C30 `funType` 1893: a sealed program in head position (a stuck cast, D56) is typed by `sealedType`.
- C31 Fuel 2,000,000 (`tick`), call depth 2000 (`runBody` 1966), normalisation depth 2000 (`nfSealed` 239): errors, not divergence. Internal, but any verdict that depends on them is a timeout (reviewer-6 W12).
- C32 `runBody` 1973–1982: in the untyped machine, a proof parameter's type is evaluated and stored when the body forms a function (so a captured proof has a type).
- C33 `runBody` 1990–1993, `checkFix` 3042: the body of a function whose calls are erased runs with copying reads (D53 (b)). **verdict** in principle: the paper decides copy-vs-move per occurrence; a callee's body is not an erased occurrence.
- C34 `closeCall` 2106: each fill's final read is `peek` (copies, sees through ghosts).
- C35 `closeCall` 2085, `eval` 1391: INTERNAL assertions ([Close]'s precondition, pre-pass agreement).
- C36 `recCheck` 2130: a recursive call is recognised by value equality of the function (`ctx.fn == fv`).
- C37 `restoreKeep` Env.lean:245: [Rec] candidates, fuel and caches survive private copies; Δ keeps new values' types but drops refinements of older ones (the arrays arm leak). Matches A.105 except that the candidate list is code only (no verdict with a declared `by`).

**Matches, splits, stuck blocks**

- C38 `evalMatchByType` 2393–2406: a zero-arm match on any empty inductive; erased iff `isPropV` of the annotation's value; otherwise a stuck block; an annotation is required outside tail position. **verdict** where "proof position" is decided by a computed type.
- C39 `evalMatchByType` 2419: an untyped non-subsingleton match on a proof is `⋆` unrun.
- C40 `bindDataFields` 674: data fields of a matched proof become fresh locals.
- C41 `splitArmsThenClose` 2323, `armMoves` 2346: `M` from a log of moves and assignments, by place. **verdict** (O10).
- C42 `movedPlace` 2518–2535: refines a one-constructor abstract value during close-off. **verdict**: `EtaP`.
- C43 `closeOffMatch` 2603–2630, `Term.selectArms`: captures split into constructor fields; the block's matches on a split place take its known arm. **verdict**.
- C44 `closeOffMatch` 2585–2592: a moved capture is `mv` whatever its shape (fuzz-port Q, M2). **verdict**.
- C45 `closeOffMatch` 2596–2597: a proof capture is never `ref` (R8). **verdict**.
- C46 `closeOffMatch` 2634–2640: a borrow variable moved into a block whose arm moves out through it is an error (M2b, N2). **verdict** (rejects).
- C47 `Term.blockOccs` Basic.lean:248: occurrences inside a nested `λ` or `Π` are reads for the capture analysis (R2). **verdict**.
- C48 `closeOffMatch` 2684: a captured proof's parameter is declared `(T : Prop)` by an ascription on its domain. Internal carrier.
- C49 `observe` 2700 with `typed = false`: untyped observations do not split. **verdict**: `Conv1`.
- C50 `idType` 2725–2730: an owner with no stored type and no typeable content is typed by the observed values (R1 residual). **verdict**.
- C51 `observe` 2703: `Id`'s sides are not erased contexts, so their effects are neither confined nor reported (they are on private copies). Consistent with A.296 ("independent copies").
- C52 `convPi` 1154, `convFn` 1199: a comparison that errors or gets stuck answers "not convertible". **verdict** (completeness).
- C53 `convFn` 1189, `convPi` 1123: a pair already being compared answers "not convertible". **verdict** (completeness; V5).
- C54 `conv` 1094: closures never compared by congruence (V2).
- C55 `mkEqM` 1275–1279: injectivity's field types from the values' recorded parameters when the equation's type is not `D(ā)`.
- C56 `findSplit` 2786: 64-link bound; `sealedHead` 2738 names only top-level functions.
- C57 `Config.confineBodies` (off by default), `checkFix` 3032–3052: an extension of D41. Off, so no verdict.
- C58 `checkInd` Check.lean:102–104: constructor names unique across a program (surface resolution by name).

Of the 58, 26 are marked **verdict**.

## 3. MISSING-IN-CHECKER

Printed premises with no code (each also makes its row DIVERGE in §1):

1. [T-Borrow] "type_Ω(p) = T a data type" (A.336). Known, in progress.
2. [Split], [Tail-split]: the scrutinee's stored type is the inductive the arms name (A.399), for `Nat` matches (`evalMatch`, `checkTail`'s `matchNat` branch).
3. [Ind]: recursive occurrences of `D` at exactly its parameters (A.447, "built from `D(x̄)`"; A.450).
4. [Ind]: `D ∉ Σ` for the built-in `Nat` and `Unit`. Known, in progress.
5. [T-Erase]/[Erase-err]: confinement of `Eq`'s sides (A.326, A.361); `J`'s motive on a private copy (A.366).
6. [T-J]: `F(v_a) ⇓ P_a : s` and `F(v_b) ⇓ P_b : s`, the motive's results are types of one sort (A.364).

In the other direction, the paper is missing rules the checker has: typing of embedded values (`evalCore .val` 1606), the type of a sealed program (C8), the declared type of an embedded value (C12), [Tail-rewrite] (C24), the destructuring `let` (S3), `copy` declarations (A.99 names `Word` "declared `copy`", but the declaration grammar A.55 and [Ind] have no `copy`; `checkInd` Check.lean:121–124 checks the fields), the definition of "proof position" (A.320, A.434), and every CHECKER-ONLY item of §2 marked **verdict**.

## 4. The `#lean("…")` pointers

The appendix has 43 `#lean` groups naming 129 declarations (with repeats). The convention (A.31) is "in `Machine.lean` unless noted". Checked mechanically (each name resolved to a declaration; each `evalCore (.x, …)` case list checked against the function's match arms), then by reading whether the declaration is the right one.

**Do not resolve (8):**

| Line | Pointer | Problem |
|---|---|---|
| A.72 | `Term.refsOk` | In `Basic.lean`, not noted (the "(Basic.lean)" is attached to the next name only). |
| A.72 | `refTopOk (Basic.lean)` | The declaration is `Term.refTopOk`. |
| A.119 | `Term.placeOccs` | In `Basic.lean`, not noted. |
| A.191 | `evalCore (…, .prod, …)` | `Term.prod` was deleted by D52 (pairs are `Pair`). |
| A.285 | `mkAnd` | In `Basic.lean`, not noted. |
| A.292 | `tupleVal (Obs.lean)` | Deleted by D52 (`6ee6c481`); an observation is now a pair of a value and a list (`observe` 2700). |
| A.298 | `footprint` | In `Obs.lean`, not noted (A.123 notes it). |
| A.361 | `evalCore (…, .prod, …)` | As A.191. |
| A.450 | `checkInd` | In `Check.lean`, not noted (the note is on `checkDef` only). |

(`sealedSort?` at A.315 and `Surface.resolve (.rewrite)` at A.371 do resolve: `Machine.lean:980`, `Surface.lean:198`/299. That is 9 rows for 8 distinct failures, `.prod` counted once.)

**Resolve, but to the wrong or an incomplete place:**

- A.169 `eval (.letIn, .seq)`: [Let] and [Seq] are `evalCore .letIn` (1575) and `.seq` (1592); `eval` only computes their erasure flags.
- A.200 and A.328, the erasure rules and [T-Erase]: name `eval`, `callFn`, `fnClass`, `paramFlags`, `propDecl`, `typeClass`, `jErased`, `evalType`, `onCopy`. The decision the paper describes ("in a pass before it runs a term", typing.typ:49 and impl.typ) is `preFlags` (955) with `declOf` (783); `propDecl`, `typeClass` and `jErased` now serve only the after-the-fact assertion. Confinement is `confinedCopy`, `logEffect`, `settleErased`, `flushPending`, `checkConfined`, none named.
- A.315 [Type-pos] has no pointer to `typePos` (870) or `declOf` with `chk`.
- A.243 [Close]: `resultKind` is used only when `erasureByDecl` is off (a counterfactual); `kindOf` only for a block's `.val B`.
- A.161 [Clone] is not pointed to: `evalCore .prim "clone"` (1739).
- A.275 stuck blocks: `splitThenClose` is the `Nat` wrapper; the capture analysis is `closeOffMatch` with `armMoves`, `movedPlace`, `Term.blockOccs`, `Term.selectArms`.
- A.366 [T-J]: `evalCtor` and `unifyParams` are about `refl`, not `J`; `jValue` (1538) is not named.
- A.409 [T-Split-goal] has no pointer (`checkTail` 2827, `splitTarget`, `findSplit`).
- A.426–435 and A.254 name `evalMatchByType`; fine. A.395 [Rec] names `recCheck`, `headOnly`; the entry values and the `by` check are in `checkFix` 2985–3020.

**Rule names in prose that do not exist:** `[Pair]` (A.72, pairs are the constructor `Mk` since D52; the check is in [Ctor]), `[Drop]` (`meta.typ:76`; drop is @app-aux item 7, not a rule). **One name used for two rules:** `[Ind]` is the machine rule for `D(ā)` (A.185) and the declaration rule (A.447).

## 5. The trace

**Today.** `trace` (Env.lean:289) records a line only when `cfg.trace` is on, from 13 call sites with 5 tags: `[Call-type]` (callFn 2023), `[Split]` (generalisation 2186, 2803; tail refinements 2834, 2839, 2847, 2895, 2900, 2945), `[Stuck block]` (2687), `[Rewrite]` (1310), `[Def]` (goal 3004, each path's end 3057). Error messages carry tags too: `[Read]` ×4, `[Borrow]` ×3, `[Drop]` ×3, `[Match]` ×14, `[Call]`, `[Rec]` ×3, `[Split]`, `[D41]`, `[D41+]`, `[D44]`, `[D48]` ×2, `[D53]` ×8, `[D55]`, and two INTERNAL ones. Of the tags, `[Call-type]`, `[Split]`, `[Rewrite]`, `[Def]`, `[Read]`, `[Borrow]`, `[Match]`, `[Call]`, `[Rec]` are paper names; `[Stuck block]` and `[Drop]` are near-misses; the `[Dnn]` tags are decision-log numbers the paper never prints. So a trace today shows goals, splits and call types, not the derivation: no line for [Copy]/[Read]/[Move], [Access], [End ℓ], [Close] and its row, [Seal], [App-*], [Match-*], [Conv-*], `eq`, [Obs], [Erase-*].

**Proposal: one enumeration, one call per rule application.**

1. A new file `Ochr/Rules.lean` with `inductive Rule` whose constructors are the paper's rules, one per `ir(name:)`/`infer(name:)` and per prose-defined rule, and `Rule.name : Rule → String` giving the printed name exactly (`.EndL ↦ "End ℓ"`, `.TLetAnn ↦ "T-Let-ann"`, `.ConvPi ↦ "Conv-pi"`, `.EqInj ↦ "eq-inj"` for the `eq` clauses once they are named in the paper). Paper-side, the two [Ind]s get distinct names first.
2. A second enumeration `inductive Ext` for each CHECKER-ONLY decision of §2 marked **verdict** (`.BlockRefCapture`, `.BlockEta`, `.UntypedObs`, `.RewriteNothing`, …), with a one-line description. A step that is not a paper rule is then visibly one: the trace prints it as `(checker) BlockRefCapture: …`. Deleting an `Ext` constructor is how a divergence is closed; the list is the running debt.
3. `fire (r : Rule) (detail : Unit → String) : M Unit` and `fireExt (e : Ext) …`: when tracing, push `"{indent}[{r.name}] {detail}"` (indent = a nesting counter kept by `eval`); always increment a per-rule counter in `MState`. One call at each decision point, e.g. `readPlace` fires `.Copy`, `.Read`, `.Move` or `.ReadErr` on its branch; `callFn` fires `.App`, `.AppClose`, `.AppHead`, `.AppNeutral`, `.AppNeutralHead` or `.TCallProof`; `closeCall` fires `.Close` with the row; `nfSealed` fires `.Seal`/`.SealStuck`/`.SealErr`; `conv` fires the `Conv-*` rule that decided; `mkEqM` the `eq` clause. Error messages use `r.name` instead of literal strings, so `[D53]` becomes the paper rule whose premise failed (`Read-err`, `End ℓ`, `Close`).
4. A trace mode `run "Block" B { trace := true }` then prints the derivation of each definition in the paper's names, and `lake exe tests --coverage` prints, per rule, how many times the suite fired it, listing paper rules never fired (untested rules) and `Ext` decisions fired (where the suite depends on the checker's own rules).

The existing `trace` calls become `fire` calls with the same text, so `08CaseSplits.genTrace` and the `AddMZero` trace the paper cites (impl.typ) keep working.

## 6. The build-time guard

A check that fails the build when the paper and the checker name different rules, or when a pointer rots. Proposal, in increasing strength:

1. **Names.** `tools/rule-guard.py` (or a Lean `#eval` in `Tests.lean`, which `lake build` already runs):
   - Paper side: every `ir(name: "…")` and `infer(name: "…")` in `paper/sections/*.typ`, plus prose-defined rules marked with a new style macro, `#rule("Conv-pi")[…]`, so that the extraction does not guess from `[…]` in running text. Also every `[Name]` reference in the prose, which must be one of those names (this catches `[Pair]` and `[Drop]`), and no name defined twice (this catches `[Ind]`).
   - Checker side: `Rule.name` of every constructor, printed by `#eval`.
   - Fail if a paper rule has no constructor, a constructor has no paper rule, or a constructor is never passed to `fire` in `Ochr/*.lean` (a grep for `fire .X`, or the coverage counters of a full test run).
2. **Pointers.** Replace hand-written `#lean("fn (.case, …)")` lists by generated ones. A Lean `#eval` (run by `lake build`) writes `paper/generated/rule-map.typ`: for each `Rule`, the declarations containing a `fire .R` and their `file:line`, found by walking the environment's declaration ranges (`Lean.findDeclarationRanges?`) of every declaration whose body mentions `Ochr.Rule.R`. The appendix's `#lean(...)` becomes `#lean-rule("Close")`, which reads the generated file. The build fails if the generated file differs from the committed one, so a pointer cannot go stale, and the pointer is right by construction (it lists where the rule fires).
   - Until that exists, a cheaper check: resolve each existing `#lean` name with `Lean.Environment.contains` over the namespaces `Ochr`, `Ochr.Surface`, and check each `(.case)` against the constructors of `Ochr.Term`; the script used for §4 does the textual version of this in 60 lines.
3. **Divergences.** Each `Ext` constructor must be listed in the paper's appendix notes (A.612 already lists conveniences) or in a named "Checker extensions" table, and the guard checks the two lists agree. This keeps the user's guarantee honest: a derivation either uses only paper rules, or its trace says which extension it used, and that extension is printed in the paper.

The guard should run where the ledger runs (`lake build` of `Tests`), since that is the build that already fails on stale verdict counts.
