# Ochr core: an executable reference checker for RULES v2.0

A Lean 4 implementation of the calculus in `ochr/core/RULES.md` (rule set v2.1): the machine of §3, observation and `Id` of §4, the typing of §5, and the inductive definitions of §8 (sorts `Prop`/`Type₀`, both in `Type₁` (D66), zero or more constructors, uniform parameters; `Pair`, `False`, `True` and `And` are library declarations, in the `Prelude` block; `Eq` is injective on constructors, D52), with the examples of §7 and every attack found so far as tests, arranged as a library and a tour of the language (`Ochr/Examples/`, below; `Ochr/Examples/README.md` gives the reading order). It exists to run the examples, and to find every place where the rules are ambiguous or wrong. Findings are in `ochr/core/notes/lean-checker.md`.

## Build and run

```
cd ochr/core/lean
lake build          # checks every example; a declaration whose verdict is not the expected one is a build error
lake exe tests      # prints every verdict table and the counterfactual ledger; exit 1 on any unexpected verdict
```

Toolchain `leanprover/lean4:v4.33.0` (see `lean-toolchain`), no dependencies. The `ochr` command checks each block when it is elaborated, so an unexpected verdict is an error in the editor and in `lake build`, at the declaration (below). The checker is compiled to native code for this: the library `Ochr` (every module but the examples) is precompiled (`precompileModules`), and the elaborator calls it; the examples are the library `OchrExamples`, whose root `Ochr/Examples.lean` imports every example file and the asserted ledger. A clean build takes about five minutes (it took about ten when the examples ran the checker in the interpreter), half of it compiling `Machine.lean` to C; an example file rebuilds in seconds; `lake exe tests` compiles the runner first and prints per-declaration check times (all 1406 declarations check in about 2.3 s, the library's and the tour's 980 in about 0.1 s) and the ledger with each row's class.

## Writing programs

```lean
import Ochr.Test
open Ochr.Test

ochr Numbers {
  def AddM (x : &Nat) (y : Nat) : Unit by x := (
    match *x {
      Z => *x := y,
      S p => AddM(&p, y),
    }
  )

  def AddMZero (x : &Nat) : Id Unit (AddM(x, 0)) () by x := (
    match *x {
      Z => refl,
      S p => AddMZero(&p),
    }
  )

  reject def WriteThenRefl (x : &Nat) : Id Nat (*x) 5 := (
    *x := 5;
    refl
  )
}

#eval IO.println ((run "Numbers" Numbers { trace := true }).showTrace "AddMZero")   -- goals, splits, call types
```

`def` expects acceptance and `reject def` expects rejection. The block is checked when it is elaborated: a rejected `def` is an error at the smallest piece of source responsible (an ill-typed argument, the access that ended a borrow, a failed `refl`), else at its name, with the checker's reason, and so is an accepted `reject def` ("expected rejection, but accepted"); the others are silent. Hovering a declaration's name shows its verdict (for a `reject def`, why it is rejected), and hovering `ochr` shows the block's count and check time. Hovering a term shows what the checker found there, on each path through the splits, labelled by the path's refinements: a term's value and type in Ω at that point (a borrow's lender), a proof's goal, a match's scrutinee before the split and in each arm, and an argument's expected type when it differs. `run` checks a block programmatically (the test runner, the ledger, traces). A block may use other blocks, `ochr Numbers uses Nats { … }` (`uses A, B`, optional). Its library is what the used blocks export, transitively and each block once: their own `def`s (not `reject def`s) that are accepted. The library's declarations are checked again, ahead of the block's own, under the same configuration. What a block exports is decided once, when the `ochr` command checks it, and recorded on the block's constant (`Block.exports`). Under the default configuration and fuel, a block that uses it reads that record instead of deciding it again (which would check the used block's own library again, and so on down the chain). Under any other configuration or fuel (the ledger, the fuzzer, the bench driver, a traced `run`) the record is ignored and everything is decided afresh, so switching a rule off re-decides the library too. `lake exe tests` checks every record against a fresh decision. A block's report, its checks and its count cover its own declarations only; the names of a block and of the blocks it uses are one namespace, and a clash is an error when the block is elaborated. Blocks are Lean constants (`Ochr.Surface.Block`), so a block in another file is used by importing that file. Match arms are separated by commas, and a trailing comma after the last arm is allowed (`match p { Z => t, S y => u, }`); `|` separates only the constructors of an `inductive` declaration. Line breaks are whitespace. The examples wrap a multi-line body in parentheses under the signature (`:= ( … )`, ordinary grouping), put one arm per line with a trailing comma, wrap an arm of several statements in `( … ),`, put one statement per line (`;` at the end of the line), indent a nested match one step further, align nothing, and keep matches inside types and argument lists on one line without a trailing comma. `inductive List (A : Type) := Nil | Cons(h : A, t : List(A))` declares an inductive type with a parameter; `inductive And (P : Prop) (Q : Prop) : Prop := Intro(l : P, r : Q)` one in `Prop`; `inductive Void : Type` one with no constructors (the sort defaults to `Type`). A type is applied like a call (`List(Nat)`). A constructor takes its type's parameters first (core `C(ā; t̄)`, D49), written `Cons[Nat](1, Nil[Nat])`, or omitted, `Cons(1, Nil)`: omitted parameters are inferred from the fields' types, and those no field determines (`Nil`'s `A`) from the type the context requires (an annotation `(Nil : List(Nat))` or `let x : T = …`, the goal of a tail, a parameter type at a call, a field type in an enclosing constructor, the type of an `Id`). Constructor values record their parameters when known (always in checked code; in an untyped run only when written). `match xs { Nil => …, Cons(h, t) => … }` binds `h`, `t` as the field places `xs.h`, `xs.t`; `match h {}` has no arms. A match whose constructors are a `Prop` inductive's is by the scrutinee's type (RULES §8). Constructor names are unique across a program. `&A` is allowed only for a data type `A` (`Nat`, `Unit`, `×`, an inductive type in `Type`; not a universe, a Π-type, a proposition or a type variable) and only as the whole declared type of a parameter, a result or an annotated term (D48). The library is the block `Prelude` (`Ochr/Prelude.lean`), written in Ochr and checked like any block, which every block uses implicitly: `Pair (A B : Type) := Mk(fst : A, snd : B)`, `False`, `True := I` and `And := Intro(l, r)`. `A × B`, `(a, b)`, `t.1` and `t.2` are notation for `Pair(A, B)`, `Mk(a, b)` and its fields (D52): a pair is taken apart by `match p { Mk(a, b) => … }`, and an abstract pair has no known fields until it is split (no η). `⊤`, `P ∧ Q`, `⟨h, k⟩` and `refl` are notation for `True`, `And(P, Q)`, `Intro(h, k)` and `I`. Its names are in every block's namespace (so no program may declare another `Mk`). `Eq` on two values built by the same constructor computes to the conjunction of the equations between their fields (injectivity, D52), and `Id` to the conjunction of the equations over its result and each observed place. `by x` names the decreasing parameter; a definition without `by` may not call itself. Calls are saturated and written `f(a, …)` with no space before the parenthesis. `S t`, `Id A t u` and `Eq A t u` are written by juxtaposition, and transport by `J(A, a, b, P, h, t)`. Other syntax: `split f in t` and `split f { C(x̄) => t, … }` (D61: in tail position, split the goal on the first result of a call of `f` that it is stuck on: the goal's sealed programs left to right, each followed down the chain of results its run is stuck on), `rewrite h in t` and `rewrite ← h in t` (D60: with `h : Eq A a b`, `t` proves the goal with `b` replaced by `a`, resp. `a` by `b`; the goal must be known: tail position, a call's argument, or `let x : T = (rewrite …);`), `let C(x, _, …) = p; u` (D60: a one-arm match, for a `C` whose type has exactly one constructor; patterns nest; `let ⟨x, y, …⟩ = p; u` and `let (x, y) = p; u` are And's `Intro` and Pair's `Mk`), `if c { a } else { b }` (`match c { true => a, false => b }` on `Bool`; `else if` chains; no `else` is `else { () }`), `match t { … }` on a term `t` that is not a place (a temporary is bound first, and matched; `Ochr/Examples/Sugar.lean` tests these three), `&p`, `*p`, `p.1`, `p := t`, `let x = t; u`, `let x : T = t; u` (for a match, `T` is the block's type), `t; u`, `match p { Z => t, S y => u }` (and `S _`), `Π(x : A) (y : B). C`, `A → B`, `λ(x : A) : B => t`, `fix f (x : A) : B by x := t`, `(t : A)`, `()`, `(t, u)`, `⟨h, k⟩`, `refl`, `⊤`, `P ∧ Q`, `False`, `A × B`, `Nat`, `Unit`, `Prop`, `Type`, numerals, and holes, `?` or `sorry` (a value of the type the context requires: the build warns, with the goal and Ω at the hole, as Lean does for `sorry`). `Nat` and `Unit` remain built into the checker (RULES v2.1 makes them library declarations too; see "Where the rules left a choice"). `cong f h`, `trans h k` and `symm h` exist as derivable conveniences outside the core. A `λ` or `Π` in the bound position of a `let`, or a `Π` as a result type, needs parentheses.

`Config` switches each turn off one rule, for counterfactual runs: `eraseOnCopy` (P2, v1.3), `multiOwner` (D18), `recGuard` (D17), `accessInside` (D19), `selfHeadOnly` (v1.1 head-only), `argNotBot` (v1.2 temporaries), `generalize` (v1.2 generalise-then-split), `blockMoves` (v1.3 captures), `proofParamsStar` (v1.4 D27), `recNested` ([Rec] inside nested functions), `erasureByDecl` (D28), `matchEndsInside` (D29), `closureConv` (D30), `unboundWithoutBy` (D31), `patternWritesVisible` (D32), `genConsistent` (finding G1), `leafRule` (findings P1, P3), `positivity` (D36), `globalRecords` (D37), `obsBorrow` (D38), `headGuardNeutral` (D39), `genPlaceType` ([Split-gen]'s type), `confine` (D41), `borrowParam` (D44), `capTypes` (captured values keep their types), `byType` (D45: matching on a proof by its type), `subsingleton` (D45), `propValues` (D42 for constructors of `Prop` inductives), `disjoint` (D47), `injective` (D52), `scrutTyped` (a match's scrutinee has its constructors' type), `refData`, `refTop`, `piUnder` (D48 (1)–(3); `refData` is D66's `&A` iff `A : Type₀`), `borrowUniverse` (D66: off, D48 (1)'s data-only test), `propUp` (D66: off, `Prop : Type₀`), `proofDataFields` (D49 (3)), `unitNorm` (on: D50's counterfactual), `confineBodies` (an extension of D41, off by default), `classInType` (D54), `sortsSyntactic` (D55; `declOf` checks every type position), `prePass` (the erasure pre-pass decides; off: the after-the-fact classification decides), `ghosts`, `fnRule` (D53 (c) and (e); D53's moves have no switch: they are the only read semantics), `unitEta` (D59), `abstractTypes` (K3), `unsizedTypes` (K2), `dropEndsBound` (D65 amended; off: pure D65), `jStuck` (D56), `zeroArmStuck` (D58), `reborrowSurvives` (D67: an assignment ends only the loans its place owns), `repack` (D64 [Repack]), `lentProofs` (D64 amended: a proof field assigned while part of its value is lent is checked with what the borrow holds unknown), `depInj` (D64: injectivity restricted for dependent constructors), `k4` (a field type may call a type function), `k4Nest` (K4's nesting condition), `p5` (v1's call skipping), `inferRecPos` (v1's inferred decreasing parameter), and `trace`.

## Layout

| File | Contents |
|---|---|
| `Ochr/Syntax.lean` | terms, places, values (§1, §2); de Bruijn indices, binder names as `Hint`s that `==` ignores |
| `Ochr/Basic.lean` | `mkAnd`/`mkTInd` (`And`'s unit laws), `distinctCtors` (D47), traversals |
| `Ochr/Pretty.lean` | printing in the paper's notation |
| `Ochr/Loc.lean` | source locations of core terms, for the editor: a side table from each node's address to its range (`Locs`); `Located.located` reports an error at the innermost located term |
| `Ochr/Located.lean` | located evaluation, for the editor: `located` (an error escaping a term's evaluation is reported at the term), the argument refinements |
| `Ochr/Env.lean` | Ω (frames of typed bindings plus temporaries), the machine state and monad |
| `Ochr/Obs.lean` | paths, `owners`, the footprint `W`, observation tuples (the pure half of §4) |
| `Ochr/Machine.lean` | one `mutual` block: the machine, [Seal], [Close], [Split], stuck blocks, observation, `Id`, [Call-type], [Rec], [Def] |
| `Ochr/Check.lean` | programs as sequences of top-level definitions and inductive declarations |
| `Ochr/Prelude.lean` | the library, the `Prelude` block in Ochr (`Pair`, `False`, `True`, `And`), and where the kernel knows these names |
| `Ochr/Surface.lean`, `Ochr/Notation.lean` | named surface terms, their resolution, blocks (`Block`, `uses`, name clashes), the `ochr` command, which checks the block when it is elaborated (`checkBlock`) |
| `Ochr/Run.lean` | running a block after its library (`libWith`, `runWith`), with the library block `Prelude` a parameter, so the `ochr` command can run it |
| `Ochr/Test.lean` | the same with `Prelude` (`libOf`, `run`), verdict tables, traces; attributing a counterfactual flip to a library declaration's home block (`blockFlips`) |
| `Ochr/Examples/Bool.lean` … `Fixtures.lean`, `Array.lean` | the library, one block per topic, each using only what it needs (`Ochr/Examples/README.md`) |
| `Ochr/Examples/Numbers.lean` … `BorrowTypes.lean` | the example programs, as a tour of the language (next section) |
| `Ochr/Examples/ArrayBench.lean`, `Quicksort.lean` | the arrays library explained, with its benchmarks (`ArrayBench`; the hash-map benchmark is the case study `HashMap`); in-place quicksort proved sorted and a permutation (`notes/arrays-library.md`) |
| `Ochr/Examples/HashMap.lean` | the case study: Aeneas's verified hash map as one in-place program, generic in the value type and built on the arrays library, with its theorems (`notes/hashmap-case-study.md`) |
| `Ochr/Examples/DependentFields.lean` | dependent fields (D64): the telescope, open and repack, restricted injectivity, K4 (`DepFields`, in the ledger); a growable vector over the arrays library (`DepVec`, a case study) |
| `Ochr/Examples/CaseStudyLedger.lean` | the counterfactual ledger for the case study, run by hand (`lake env lean`), not part of `lake build` |
| `Ochr/Examples/Sugar.lean` | the surface sugar, with no rules of its own: a destructuring `let` for any one-constructor type, `if`, and `match` on a term (`Sugar`, after the tour in the registry) |
| `Ochr/Examples/Units.lean` | unit tests of machine functions ([Seal], owners, footprint) on hand-built values |
| `Ochr/Examples.lean` | the root of the `OchrExamples` library (what `lake build` builds): the registry and the asserted ledger |
| `Ochr/Examples/Registry.lean` | every program, in reading order, for the runner and the ledger; the case studies (`caseStudies`: checked, counted and timed, but not re-run by the ledger); the total count; the ledger's switches and row classes |
| `Ochr/Examples/Ledger.lean` | the counterfactual ledger, asserted |
| `Tests.lean` | `lake exe tests` |

## The examples: a tour of the language

Read in order (`Ochr/Examples/README.md`), the files teach the whole language: the library first, then the tour, whose order follows RULES (§3 the machine, §4 observation, §5 typing, §8 inductive definitions), starting from the paper's first example, then the case studies. They are imported as `Ochr.Examples.Numbers`. Each file opens with what it covers and where RULES defines it; every program or small group has a comment, and a rejected program says which rule rejects it and why. Each regression (a closed false proof, or an accepted program that went wrong, found while designing the rules) sits with the feature whose rule rejects it, under "What goes wrong without these rules", with the ledger switch that lets it back in. A file holds one `ochr` program or a few (programs are checked independently: names, constructors and helpers such as `AddM` are per program). Every program is checked when it is elaborated, and the registry asserts the total number of declarations, so a truncated file fails the build. The library is one block per topic: `Bools` (`Bool`, `IsTrue`), `Logic` (`Dec`, `Void`), `Nats` (`AddM`, `Add`, `AddMZero`, `AddS`, `TailM`), `WordType` (the copy type `Word`) and `Words` (the order `Le`/`Lt`, `LeDec`/`LtDec`, the boolean comparisons `EqB`/`LeB`/`LtB`, `WAdd`, `Sub`, `Pred`, `W(n)`, `ModS`, and facts about them), `Lists` (`List(A)`), `Options` (`Opt(A)` with `IsSome`/`IsNone`), `Boxes` (`Box(A)`), `Fixtures` (what only tests need: `Pick`, `Empty`, `U`, `V`), and the arrays library `Arrays`/`ArrayLemmas`; each program uses the blocks it needs. Each is the one copy: a program that declares its own version does so because that version is its subject, and says so where it declares it (a different `List` or `Box` in `NatLists`, `GenType`, `GlobalRecords`; the order on `Nat` in `CurrentState`; the arrays model of `ArmLocal`). A block that others use holds only what they reuse; runs, headline theorems and `reject def`s are in blocks nothing uses. `Prelude` is used by every block without saying so.

| File | Covers | RULES | Declarations |
|---|---|---|---|
| library | `Bools`, `Logic`, `Nats` (in-place and pure addition, adding zero does nothing, `AddS`, `TailM`), `WordType`, `Words` (the order, comparisons, arithmetic and numerals on `Word`), `Lists`, `Options`, `Boxes`, `Fixtures`; the arrays library is counted with the case studies | §1, §3, §7 | 50 (+4) |
| `Numbers` | evaluation in types, the pure theorem by the in-place lemma; matching on numbers; pairs; calls; built-in names are reserved | §1, §3, §7 | 26 |
| `Borrows` | moving, copying and reborrowing; argument order; the borrow checker ([Access], [Drop]); `Drops`: a place that dies while lent (D65 amended); `Moves`: D53's moves, copy types, `clone`, ghosts, the Fn rule, and a stuck block's captures | §3 | 98 |
| `ReturnedBorrows` | functions returning a borrow (`TailM`); a returned borrow must come from a borrow argument (D44); moving a borrow down, `x := &(*x).f` (reborrow and replace, D67) | §1, §3 [Close] | 33 |
| `ClosingOff` | stuck calls and matches, sealed programs, a borrow chosen by a branch, what a stuck match captures, [Close]'s rows and η for `Unit` (D59), typing a sealed program; closures inside a stuck block; naturality up to resolution | §3 | 55 |
| `Equality` | `Id` and `Eq`: observation, footprints, disjointness, injectivity (pairs included), `J` and its stuck casts (D56); `rewrite h in t` (D60); all owners of a returned borrow are observed (D18), in the order the sides reach them | §4 | 76 |
| `Snapshots` | types and closures are formed once; what a closure or Π-type captures (values, never borrows; capturing ends a live borrow; a Π-type formed by a call keeps its captured proofs' types) | P2, §1, §5 | 27 |
| `Recursion` | `by x`, entry-value recursion, induction hypotheses in the caller's environment; typing a sealed program keeps the [Rec] state | §5 [Def], [Rec] | 29 |
| `CaseSplits` | [Split], dependent matching on a computed type, generalising sealed programs, `split f` on a result the goal is stuck on (D61), scrutinee types, global generalisation records, a refinement belongs to its arm, re-normalising inside Π-types | §5 [Split] | 82 |
| `Functions` | opaque functions, closures, Π-types, comparing functions by observation (D30, D38, D48 (3)); a function type's class and row (D54) | P1, §1, §4 | 63 |
| `Inductives` | lists, binary search trees (keys are `Word`s) (and the paper's trees, whose pure insert runs the in-place one), parameters, strict positivity | §8 | 72 |
| `Propositions` | `False`, `True`, `And`, matching on proofs by type, a stuck zero-arm match (D58), destructuring `let` (D60), subsingleton elimination | §1, §8 | 76 |
| `CurrentState` | proofs about the current, mutated state (E5) | §7 | 16 |
| `Erasure` | erased terms run on a private copy, confinement, erasure decided by syntax (the pre-pass) | P2 | 68 |
| `Universes` | `Prop : Type₁` beside `Type` (D66), no `Type : Type`, no cumulativity, why `&Type` is refused; sorts are syntactic (D55, reviewer-4's programs) | preamble, P2 | 27 |
| `BorrowTypes` | what may be borrowed (D66: `&A` iff `A : Type`) and where `&` may appear (D48); `FnBorrows`: borrowing functions and type variables, a generic swap and bucket; abstract and unsized types, model code (K2, K3) | §1 | 72 |
| `Array`, `ArrayBench`, `Quicksort` | case study: arrays as a library (slices; indices are `Words`'), its lemmas and benchmarks, and in-place quicksort proved sorted and a permutation; indices, lengths and elements are `Word`s (`notes/arrays-library.md`) | all | 162 |
| `HashMap` | case study: Aeneas's resizing hash map, its lookups, length, invariant, resizing and load factor, proved about the in-place code; values of any type `V`, keys and sizes `Word`s, the table an array of lists; each block's results in a `…Tests` companion (`notes/hashmap-case-study.md`) | all | 192 |
| `DependentFields` | dependent fields (D64): a field's type from the earlier fields, writing them in place (open, then repacked), proof fields, restricted injectivity, type functions in field types (K4) and its nesting condition; and a case study, `DepVec`: `Vec(E)` as user code over a fixed-size array of `Opt(E)` cells (push growing it, pop, an element borrow, and lemmas about each) | §8 | 57 (+64) |
| `Sugar` | surface sugar: a destructuring `let` for any one-constructor type, `if`, `match` on a term; their errors, and runs showing each computes as its match; `if` on a block's own `Bool`, and without one | §5 [Split] | 48 (+3, +1) |

1401 declarations in all, the `Prelude`'s 4 and the case studies' 418 (the arrays library's 50 among them) included (the registry's `expectedTotal`). D53 (reads of non-copy data move) is the only read semantics: the old copy-on-read paths, `Config.d53`, `Test.preD53` and the `moves` switch are deleted (`notes/lean-checker.md` §47). `notes/lean-checker.md` §17 maps the old file and program names (`E1`, `V17.LieL`, `Attacks.Knot`, …) to these.

## Rule → function

| Rule (RULES v2.0) | Function (`Ochr/Machine.lean` unless noted) |
|---|---|
| §3 [End ℓ] | `endBorrow` (substitution of every `loan_ℓ` by `substEnv`) |
| §3 [Access] | `accessPath` (loans on the path, including the place itself), `accessInside` (loans inside the content) |
| §3 [Read] | `readPlace` |
| §3 [Borrow] | `borrowPlace` |
| §3 [Assign] | `eval` (`.assign`), `assignPlace` |
| §3 [Let] | `eval` (`.letIn`) |
| §3 [Drop] | `dropTopBind`, `dropValue`, `popFrame`; `endLoansOfTopBind`, `endLoansOfTopTemp` (D65 amended: end a bound borrower, err on one in flight) |
| §3 [Call] | `evalCall`, `callFn`, `runBody`, `endBorrowArgs` |
| §3 [Match] | `evalMatch` (`Nat`), `evalMatchInd` (declared inductives; `scrutType` reads the scrutinee's type `D(ā)`) |
| §3 [Close] | `closeCall` (asserts the precondition), `declKind` (the table's row, from the declared codomain, v1.7) |
| §3 [Seal] | `nfSealed` (the head call is `Term.call _ _ true` and is not eligible for [Close], a neutral-headed one included, D39); `substV` re-normalises after refinement or [End] |
| §3 stuck blocks | `splitArmsThenClose` (arms, annotation, whether every arm is a proof), `closeOffMatch` (Rust-style captures on maximal place prefixes; erased iff every arm is a proof, v1.7) |
| §4 owners, footprint | `owners`, `footprint` (`Ochr/Obs.lean`) |
| §4 observation, `Id` | `observe`, `idType` (the conjunction over the result and the observed places, `andList`, D52); a borrow result in `convFn` is observed through a fresh value (D38) |
| §4 `Eq` computes | `mkEqM` (reflexivity to `True`; the same constructor to the `And` of the equations between its fields at their instantiated types, D52; distinct constructors to `False`, D47), `mkAnd`/`mkTInd` (`And(True, P) ≡ P ≡ And(P, True)`, `Ochr/Basic.lean`), re-applied by `substV` |
| §5 [Call-type] | `callType` |
| §5 [Def] | `checkFix`; top-level definitions in `checkDef` (`Ochr/Check.lean`) |
| §5 [Split] | `checkTail` (tail position), `splitThenClose` (otherwise), `refine`, `generalizeNeutral` (sealed heads; σ gets the place's type; records are global and fresh names never reused, `restoreKeep` in `Env.lean`, D37) |
| §5 [Rec] | `recCheck` (a stack of contexts, one per enclosing function), `headOnly` (f only as a call head) |
| §5 errors | the `err` calls in the functions above |
| §8 declarations | `checkInd` (parameters at generic values, fields at those), `firstOrderTerm` (D36 on field type *terms*: `Nat`, `Unit`, a parameter, a declared inductive applied to first-order types, `Pair` included) (`Ochr/Check.lean`), the `Prelude` block (`Ochr/Prelude.lean`); `fieldTypes` (a constructor's field types at given parameters), `ctorRefinement` ([Split]: fresh values of those types, `⋆` for a proof field) |
| §8 `D(ā)`, constructors | `evalTInd` (arguments in type positions, checked against the parameter telescope; no borrow types, `noBorrowParam`), `evalCtor` (parameters from the fields' types, `unifyParams`, else from the required type, the `hint` of `eval`; a `Prop` inductive's value is `⋆` and erased, `ctorIsProof`, D42) |
| §8 matching on a proof | `byTypeMatch` (syntactic: the arms' constructors are a `Prop` inductive's, or there are none), `scrutType` (the scrutinee's type must be `D(ā)`; a neutral type is an error, D49 (1)), `evalMatchByType` and `checkTail`'s by-type branch (no arms: vacuous, `⋆`; one constructor: its arm; several: every arm checked, the match is `⋆`; an untyped run of a non-subsingleton match is `⋆` without running it), `bindDataFields` (a data field of the proof is a fresh abstract value, a proof field `⋆`, D49 (3)), `largeElim`/`fieldTermIsProp` (subsingletons: no constructors, or one with only proposition fields), `subsingletonMsg` |
| §8 disjointness | `mkEqM`, `distinctCtors` (D47) |
| §8 dependent fields (D64) | resolution puts a constructor's fields in its field types' scope after the parameters (`Ochr/Surface.lean`); `IndDecl.fieldRefs`/`indexFields`/`dependent` (`Ochr/Env.lean`); [Ind]'s telescope and K4 in `checkInd`, `firstOrderTerm`, `paramNestable`, `nestViolation` (`Ochr/Check.lean`); `fieldTele` (field types at given or fresh field values), `fieldTypesOf`, `fieldsGeneric`, `depFieldType` (a field's type from the contents; an open value's by what it holds), `openWrite` ([Open]: invalidating proof fields), `strongUpdate`, `packedErr`/`repackCheck`/`repackAt` ([Repack]), and the restriction in `mkEqM` |
| P1 conversion | `conv`: `==` on normal forms (`Value.beq`, which ignores binder names and constructor values' parameters), function values by their generic call (`convFn`, D30), Π-types under their binders (`convPi`, D48 (3)), the unit laws (`unitTop`, D50) |
| §1 `&A` (D48) | `isDataType` at `&A`'s formation (`evalCore`), `Term.refsOk`/`refTopOk` in `checkDef` (`&` only at the top of a declared type) |
| P2 erased terms | `preFlags` (the erasure pre-pass: decided before the term runs, from its declared type, `declOf`; each binding records what its declared type says, `DeclInfo`), checked against `eval`'s after-the-fact flags under the default rules (flags *erased* and *proof*: a call by its callee's class; `let`/`;`/`match` iff their tail is a proof; proof formers; a variable declared of sort Prop (a flag on its binding: `paramFlags`, `leafProof`), a field declared of a proposition (`fieldIsProof`), a constructor of a `Prop` inductive (`ctorIsProof`), a proof constant, a `λ` returning proofs; an ascription at a declared proposition), `fnClass`/`propDecl`/`declOfDom`/`declOfVal` (a function's class from its codomain term, v1.7), `logEffect`/`settleErased`/`flushPending`/`confinedCopy` (D41: erased runs are confined, judged by the outermost erased term; arguments of erased calls exempt), `evalType` (types on a private copy), `capture` (Π-types and closures close over values, never borrows) |

## Where the rules left a choice

`notes/lean-checker.md` §3 lists every point where RULES was ambiguous, the reading implemented, and whether later rule sets adopted or changed it (C1–C19). The remaining open points are:
- static vs dynamic "moves out of in any arm" (C19);
- the sort of a sealed type (C16);
- Unit η (C14);
- universes (C15);
- J's motive sort (C12);
- calls of sealed function values in untyped code (C18).

RULES v2.1 makes `Nat := Z | S(pred : Nat)` and `Unit := Tt` library declarations too; in this checker they stay built in (§19 of the notes says why: numerals, the `S` notation and `.1` for the predecessor, the machine's `Nat` paths for [Match], [Split] and [Rec], and [Close]'s `Unit` row, which reads a codomain written `Unit` and returns `()`).

Rule bugs found by running the rules (L1–L4, including the uncurried D18 attack; P1, P2 in round 3) are in §1, §4 and §10 there; the v2.0 round (§14) found that D45's subsingleton restriction is not what blocks the `Or` attack's closed `False` in this machine (D42's erasure is), that `And(True, P) ≡ P` as normalisation hid an `And` from a match (now D50), and a v1.9 checker bug (a match's scrutinee type was assumed from its arms). §15 covers reviewer-3 (D48–D50) and the ledger's row classes. One reading remains this checker's own: a function's class is "data" when `propDecl` cannot read a codomain's declared sort (e.g. `q.1`), which is consistent on both paths because blocks follow their arms (§10). The checker has no elaborator: a constructor's omitted parameters are inferred only in checked (typed) code, so a value built by an untyped run from `Nil` does not record `A`.

The ledger (`lake exe tests`, asserted in `Ledger.lean`) labels each row: *soundness* (switching the rule off accepts a closed false proof or a program that goes wrong when run; witnesses named), *false lemma*, *model* (definitions with no set model, but no closed false proof in the suite), *policy* (only programs true under the other rules), or *completeness* (only rejections).
