# Two-paths census: every decision the checker makes, and what it reads

Branch `two-paths`, off main `59b548aa`. Phase 1 of the two-paths enforcement (`ochr/docs/14`, "Supporting: enforce the two-paths principle in the code's types").

The principle (paper §6.3): no decision that changes a result is read from a normal form. A statement is evaluated at a definition's generic call, where calls and matches on abstract values close off, and directly at each instance, where they run; a decision read from a normal form can differ between the two, and many of the closed proofs of `False` found while designing Ochr came from one (Figure 16's "two paths agree" rows; others came from positivity, subsingleton elimination and the dependent-field rules). A *decision* here is any choice the checker makes that can change a result: whether a term is erased, how a stuck block takes a place, which places an observation reads, which row of [Close] applies, whether a match is on a proof, and so on.

Classes:
- **(a)** reads only syntax and declared types;
- **(b)** reads a value or a normal form: a violation, or a latent bug unless argued stable;
- **(c)** legitimately depends on values, with the argument for why it is stable under refinement.

## The decision currency: declared types

Almost every decision is made from a `DeclInfo` ("what a declared type says": a sort, a Π-type with its codomain's reading, a borrow, a proposition, other, any, conflict). Two families of functions compute it.

**From syntax** (class a): `declOf`, `typeDecl`, `typePos`, `telescope`, `placeDecl`, `agreeDecl`, `syntacticKind?`, `isPropTerm?`, `fieldTermIsProp`, `fieldIsProof`, `ctorIsProof`, `largeElim`, `byTypeMatch`. They read terms, the declarations of inductives and globals, and the `DeclInfo` stored with each binding.

**From a value's head** (class c, by declared-type preservation): `valueDecl`, `valTypeDecl`, `paramDecls`, `isPropV`, `sortOf?`/`sortOf`, `sealedSort?`, `typeClass`, `fnClass`, `kindOf`. Terms embed values (a sealed program's arguments, a closure's captures, a stuck block's codomain), so declared types must be read off values too. These read only a value's *head*: an inductive type's declared sort, a Π-closure's codomain *term* (D54), a global's declared type, an abstract value's `Δ` type, a sealed program's head call's declared codomain (`sealedSort?`). The argument that this is stable: evaluation preserves declared types (D55: a type's declared sort is its computed sort, and sorts are syntactic; D54: a Π-type records its class from its codomain term when it is formed), and refinement substitutes into `Δ` types without changing their sorts. So the head a reader sees at the generic call and the head it sees at an instance have the same declared type.

**One implementation violation (class b): `sortOf` of a Π-type value evaluates its parameter types and its codomain** (onCopy, `evalType`, `genericValue`, `pushBind`) to compute its sort. That is the only place where a declared-type reader runs the machine, and the only thing that ties the readers into the evaluator's mutual cycle. By D55 the sort it computes is the declared sort of the codomain and parameter *terms*, which `declOf` reads without running anything. Fix: compute it syntactically.

## The decision sites

| # | Decision | Where | Reads | Class |
|---|---|---|---|---|
| 1 | Erasure pre-pass: is a term erased, is it a proof (D28, D35, D55) | `evalAt` → `declOf` + `preFlags` | the term's syntax and the bindings' stored `DeclInfo` | a |
| 2 | The after-the-fact classification, kept as an internal assertion that it agrees with 1 | `evalAt`, `leafProof`, `jErased`, `ctorIsProof` | syntax, binding flags, a closure's own codomain term | a |
| 3 | A function type's class: returns types, proofs, or other (D54) | `fnClass` | the Π-closure's codomain *term*, never evaluated | a/c |
| 4 | Which parameters are proofs | `paramFlags` | the parameter type terms | a |
| 5 | Is a call a statement (its arguments run on private copies) | `stmtCallee` | the callee's Π-type (`funType?`), its class (3) | c (see below) |
| 6 | Run a statement argument in place instead of on a copy | `stmtArgIf` | whether the argument's *value* holds a borrow or loan | b → c (see below) |
| 7 | A binding's reading when its declared type is a Π-type only after computing (`p : Pow(Nat)`) | `refineDecl` | whether the *evaluated* declared type is a Π-type | b → c (see below) |
| 8 | [Close]'s row: borrow, `Unit` or data | `declKind`, `kindOf` | the declared codomain term; for a stuck block's function, its codomain value `B` (the match's type) | a; c for blocks (below) |
| 9 | η at `Unit` for a call's result (D59) | `evalCall` → `callFn`, `closeCall` (D80; was `resultIsUnit`) | the call's declared result type as written (the head's declared codomain, a global's with its type arguments as written; a stuck block's match's declared type), read by `Decide.declOf` | a (D80; was c: the computed result type, "only more stuck") |
| 10 | A value of a proposition is `⋆` (proof irrelevance) | `isPropV` at its many call sites | the sort of the (evaluated) type, by its head | c (declared-type preservation, D55) |
| 11 | A match is on a proof (decided by its type, D45) | `byTypeMatch`, `evalMatchByType` | the arms' constructor names (a declaration) | a |
| 12 | Which arm a match on a proof takes, subsingleton elimination | `scrutType`, `largeElim` | the scrutinee's *stored* type, as refined (note 25) | c (fail-safe: refinement only refines a stored type's parameters, never its head; a still-neutral type is a type error) |
| 13 | Stuck-block captures and their modes | `blockCaptures` (K1, `notes/erasure-model.md`), called by `closeBlock` (was `closeOffMatch`) | occurrence kinds (syntax), copy-ness of each place's declared type (D80), the places some arm leaves `⊥`, whether a binding holds a borrow, the constructor of a split capture's content | a for copy-ness (D80; the block's parameters are declared as their places); c for the rest (below) |
| 14 | Observation footprint and owners | `Obs.footprint`, `owners` | the sides' syntax, and the borrow/loan graph of the environment | c (Conjecture 2, item 6: the footprint at the generic call contains the instance's, and the extra equations become `⊤`) |
| 15 | [Rec]: is a recursive call's argument a strict subterm of the entry value | `recCheck` | the entry value as refined so far | c (refinement only adds constructors, so a subterm relation found at the generic call holds at every instance) |
| 16 | Copy or move on a read (D53), closure capture, the Fn rule | `readPlace`, `copyRead`, `capture` → `Decide.placeDecl`, `declCopy` | the place's declared type, by the reader of declared types (a capture's binding's, recorded with the closure or Π-type) | a (D80; was c: the place's stored type, else the value's own type, "generic stricter") |
| 17 | `Eq` computes: reflexive, injective, disjoint, else stuck | `mkEqM` | the two values | c (the paper's argument: `[Eq-refl]` uses conversion, which is closed under refinement; constructor heads survive refinement; anything else stays stuck) |
| 18 | `J` computes | `evalCore` (`J`) | whether the endpoints are convertible | c (as 17) |
| 19 | Conversion checks | `conv`, `convT`, `convPi`, `convFn` | values | c (a check, not a choice: success at the generic call implies success at every instance; true only for values without `⊥`, which an instance may fill with anything, so a value holding `⊥` is convertible with nothing, [Conv-bot], D83; before D83 the identity test identified two stuck `Eq(Nat, ⊥, ⊥)`, docs/28) |
| 20 | [Split], [Split-gen], generalisation records | `evalMatch`, `splitArmsThenClose`, `generalizeNeutral` | the scrutinee's content | c (the rules themselves; records end with their arm, D37 and §6.4) |
| 21 | ~~An `Id` side stuck in an untyped run is observed again by typing~~ | deleted (D82): a side of `Id` runs with the typing judgement from the start, in every run | — | gone (was c: whether the machine's run got stuck) |
| 22 | Is a hole a proof | `evalCore` (`hole`) | the evaluated hint type's sort | c (as 10); holes are outside the consistency statement anyway |
| 23 | K2/K3 model-code checks | `abstractMatchCheck`, `unsizedCheck`, `atRuntime`, `modelSignature` | declarations' `abstract`/`unsized` flags; a content's type head | a / c (as 10) |
| 24 | [Open], [Repack] and the whole-again points (D64, D72, D73) | `openWrite`, `repackCheck`, `lentUnknown`, `bodyReturns`, `closeBlock` | values against their telescope types | c (checks, and the generic call is the stricter path, D72/D73) |
| 25 | `&A` is well formed only for `A : Type₀` (D66) | `isBorrowable` → `sortOf?` | the sort of the evaluated `A`, by its head | c (as 10) |
| 26 | [Close]'s fill of a lent place: `()` or a sealed program (D59, D80) | `evalCall` → `closeCall` | the borrow argument's declared type as written (`&c` with `c` declared `Unit`) | a (D80; was b: the content, `u == ()`, not listed here before) |
| 27 | A binding's type, wherever a decision or typing reads a place's type (D82) | `placeType?` (`.var`), and through it `natPlace`, `projMatch`, `idType`'s owners | the binding's stored type, its declared type, in every run | a (D82; was b, not listed here before: a binding the machine bound had no stored type, and its value's own type was read instead, `valType?`, `content?`, by a route a refinement switches) |

### The class (b) sites, one by one

- **`sortOf` of a Π-type value runs the machine.** Not a decision itself, but every reader of declared types depends on it through `valueDecl`, and it is what makes them unable to live outside the evaluator. By D55 its result is the declared sort of the parameter and codomain terms. Fixed in phase 2 by reading those terms' declared sorts.
- **6, `stmtArgIf`.** Whether a statement argument runs on a private copy or in place is decided by whether its *value* holds a borrow or a loan. Stable by well-formedness, not by construction: condition 5 of A.5 (arguments are exclusive) makes every argument value loan-free or a whole borrow, and "no borrows in data" (D48, D71) makes it a borrow exactly when its type is a borrow type. So the value test agrees with a type test on every well-formed state. Kept, as class (c), with that argument; it leans on the machine's well-formedness invariant, which is Assumption 11 (T1) in the paper and not proved.
- **7, `refineDecl`.** A binding whose declared type computes to a Π-type (`p : Pow(Nat)`) takes the class of the computed Π-type. At the generic call a declared type such as `PT(σ)` can still be stuck, so the binding reads as `other` (data: not erased, arguments in place), while an instance computes `PT(Z)` to a Π-type of another class. The disagreement is one-directional: the generic call never erases what an instance runs, only the reverse, and only for a value whose function is unknown there (an abstract value or a sealed program; a closure's class is read from its own codomain term on both paths, so for closures the paths agree). The effects of an unknown function are themselves unknown (sealed), so nothing the generic call keeps can be used to prove something an instance contradicts. Also, a family computing Π-types of different classes is constrained by sorts: a Π into a proposition has sort `Prop`, any other a `Type`, so a family declared at one sort cannot switch between "returns proofs" and the others. Kept, as class (c), with that argument. It is the weakest argument in this census.

### Site 13 in detail: stuck-block captures

`closeBlock` (formerly `closeOffMatch`), through `blockCaptures` (K1), reads, per place: its occurrence kinds in the arms (syntax); whether its declared type is a copy type (D80, as 16: syntax; it read the stored type before, generic stricter); whether some arm leaves it `⊥` (an arm moves a place exactly when it reads it whole at a non-copy type, so this is type-directed, as 16); whether its binding holds a borrow (`b.val.isBorrow`, equivalent to its type being a borrow type, as 6); and, to split a capture some arm partly moves, the constructor of its content (stable: refinement never removes a constructor head). The block exists only on the generic path; the direct path runs the match. The paper's argument (D53, the fuzz-port shapes) is that the captures mirror the direct path's effects per sub-place.

### Site 8 for stuck blocks

A stuck block's function has the match's type `B` as its codomain value, and `declKind` reads its row with `kindOf B`: a proposition by its sort (as 10), a borrow only if `B` is literally `&T`, and `&` is never produced by computation (D48 (2)), so `B` is `&T` exactly when it is written so.

## The design

**A module that cannot run the machine.** Move every reader of declared types, and the decisions made from them, into `Ochr/Decide.lean`, which sits between `Located` and `Machine` in the import graph: `Machine` imports it, it does not import `Machine`. Lean's module system then enforces what the principle asks: a decision in `Decide` cannot evaluate a term, because the evaluator is not in scope. What it can read is syntax, declarations, the state's tables (`Δ`, the signature, the bindings' stored `DeclInfo`) and the heads of values passed to it; the head readers are the sanctioned class (c) of this census.

Contents: `isPropTerm?`, `syntacticKind?`, `isPropSort`, `fieldTermIsProp`, `fieldIsProof`, `ctorIsProof`, `largeElim`, `subsingletonMsg`, `byTypeMatch`, `placeDecl`, `agreeDecl`, `conflictMsg`, `preFlags`, `sealedSort?`, `absOf`, and the mutual block `sortOf?`, `sortOf` (Π case made syntactic), `isBorrowable`, `declOf`, `typeDecl`, `typePos`, `telescope`, `valueDecl`, `valTypeDecl`, `paramDecls`, `refineDecl`, `pushCaps`, `isPropV`, `genericValue`, `fnClass`, `paramFlags`, `leafProof`, `typeClass`, `jErased`, `kindOf`, `declKind`.

How each class fits:
- (a) sites live in `Decide` and are unchanged.
- The (b) site `sortOf` is rewritten to read declared sorts, which is what lets the cluster leave the evaluator's cycle.
- (b→c) sites 6 and 7 stay where they are, marked in their docstrings as sanctioned value-dependent decisions with their arguments, and listed in §6.3.
- The other (c) sites (9, 10, 12–25) are the calculus's value-dependent rules ([Split], `Eq`, conversion, [Rec], footprints, copy-ness, the dependent-field checks), each with its stability argument above.

**Viability.** The cluster depends on the evaluator only through `sortOf`'s Π case; everything else it calls is state (`Env.lean`: `absType`, `lookupInd`, `lookupGlobal`, `liveDecl`, `varPos`, the caches). So the split is viable, at the cost of one semantic change (the syntactic sort of a Π-type value), which D55 says changes no accepted program. Phase 2 checks that against the build.

**Not done: unforgeable decision tokens.** A stronger version would give each decision outcome (erasure flags, class, [Close] row, capture mode) a type with a constructor private to `Decide.lean`, so the evaluator could obtain one only from a decider. Lean's `private` is per file and the deciders and the evaluator are mutually recursive in part (`closeOffMatch` needs arm end states), so this needs the evaluator to hand facts to pure deciders rather than call into them. Left for later; the import-graph split already makes "a decision cannot run code" true by construction.

## What landed (phase 2)

- `Ochr/Decide.lean`: the declared-type readers and the decisions made from them, 531 lines moved out of `Machine.lean`, between `Located` and `Machine` in the import graph. It does not import the machine, so nothing in it can run a term.
- `sortOf` of a Π-type value reads its parameter and codomain terms' declared sorts (`declSort`). That broke the only tie to the evaluator's cycle.
- **A transient finding.** With only that change, `Universes.Impred` and `PolyTy` (`Π(x : &Type) …`) were accepted: computing the sort of a Π-type had been the only place [T-Pi] checked its parameter types, so `&Type` (D66) went unchecked. [T-Pi] now runs them in `Machine.piSort`, as typing must, and `evalCore` asserts that the run sort equals the declared one (D55). The assertion never fires on the suite.
- The value-dependent sites are marked in the code with a comment beginning "Two paths, value-dependent by design" and their site number here: 6 `stmtArgIf`, 7 `refineDecl`, 9 `resultIsUnit`, 12 `scrutType`, 13 `closeBlock` and `blockCaptures`, 14 `Obs.footprint`, 15 `recCheck`, 16 `copyRead`, 17 `mkEqM`, 21 `observeTyping` (deleted by D82).
- Verdicts: none changed. Class (b) sites 6 and 7 were kept, argued stable, rather than rewritten; neither is a known bug.

## D80: copy-or-move, η at `Unit` and the [Close] fill read from declared types (2026-11-05)

Lane `declared-copy` (`ochr/docs/21`, DECISIONS D80). Sites 9 and 16, the copy-ness part of 13, and the [Close] fill (26, not listed before: it read the lent content, `u == ()`) read only syntax and declared types now, so their one-directional arguments ("generic stricter", "only more stuck") are no longer needed. The reader is D77's, extended to data (`Unit`, an inductive with its type arguments, the alternatives of a type function's arms, a global call's codomain at its type arguments as written); closures and Π-types record their captures' readings and a stuck block its parameters' (its places'), so no reading comes from a value. The one verdict that moved is `ClosingOff.NeutralKept` (rejected → accepted, true); decision counts are in D80.

## D82: every binding has its declared type (2026-11-05)

Lane `typed-bodies` (`ochr/docs/22`, DECISIONS D82). Every binding, in every run, has a stored type, its declared type: a called body's parameters (the callee's declared parameter types at the arguments, as at the generic call), `self`, a closure's or Π-type's captures (recorded when it is formed, with their readings: `Value.clo`/`tPi`'s `rd`), a `let` (its right-hand side's type, computed as typing computes it, a call's being its declared codomain at its arguments: `declCallType`), a sealed program's cells (`let cᵢ : Tᵢ = uᵢ`, `Tᵢ` the lent place's declared type), and the checker's internal frames (`fieldTele`, `fieldTypeAt`, `sealedResultType?`; an unknown slot of the last two is `⊥`, untyped, and never read). So site 27, a binding's type, is class (a), and site 21 is gone: an `Id` side is typed from the start everywhere, since every binding it reads has a type.

**What still reads a value's own type** (`valType?`, `valType`, `convVal`, `indValType?`): values that are not bindings, kept as class (c), a later question (`ochr/docs/22`, out of scope):
- *An embedded value* (a value inside a term: a sealed program's arguments, a stuck block's or `J`'s embedded endpoints, a captured proof) typed by the typing judgement, `evalCore`'s `.val` case: an abstract value by Δ, a constructor by its inductive at its recorded or inferred parameters, a sealed program by its program's typing. The machine uses the position's type (the hint) instead. Argument: declared-type preservation (D55); refinement substitutes into Δ and keeps a constructor's head. A constructor no field of which determines a parameter has no own type: the typing is rejected ("cannot infer the type of the value"), fail-safe.
- *A sealed function's type* (`funType?` of `⌈t⌉`): its program's typing (`sealedType?`), as above.
- *Contents checked against their telescope types*, part of site 24: [Repack] (`packedErr`, `convVal`), an open field typed by its content ([Open], `depFieldType`), and the lending checks (`lentUnknown`, `lentProofAssign`). Argument as site 24: checks, and the generic call is the stricter path (D72, D73).

