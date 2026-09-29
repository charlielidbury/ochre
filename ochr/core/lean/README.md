# Ochr core: an executable reference checker for RULES v2.0

A Lean 4 implementation of the calculus in `ochr/core/RULES.md` (rule set v2.1): the machine of §3, observation and `Id` of §4, the typing of §5, and the inductive definitions of §8 (sorts `Prop`/`Type₀`, zero or more constructors, uniform parameters; `Pair`, `False`, `True` and `And` are library declarations, in the `Prelude` block; `Eq` is injective on constructors, D52), with the examples of §7 and every attack found so far as tests, arranged as a tour of the language (`Ochr/Examples/00Std.lean` … `15BorrowTypes.lean`, below). It exists to run the examples, and to find every place where the rules are ambiguous or wrong. Findings are in `ochr/core/notes/lean-checker.md`.

## Build and run

```
cd ochr/core/lean
lake build          # checks every example; a failing verdict or a wrong assertion count fails the build
lake exe tests      # prints every verdict table and the counterfactual ledger; exit 1 on any unexpected verdict
```

Toolchain `leanprover/lean4:v4.33.0` (see `lean-toolchain`), no dependencies. A clean build takes about 55 seconds (most of it the counterfactual ledger: 47 rows, each re-running the suite twice in the interpreter) and prints every verdict table; `lake exe tests` compiles the runner first and prints per-declaration check times (all 467 declarations check in about 22 ms) and the ledger with each row's class.

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

#eval IO.println (run "Numbers" Numbers).show                      -- the verdict table
#eval IO.println ((run "Numbers" Numbers { trace := true }).showTrace "AddMZero")   -- goals, splits, call types
#guard (run "Numbers" Numbers).allAsExpected
```

`def` expects acceptance and `reject def` expects rejection. A block may use other blocks, `ochr Numbers uses Std { … }` (`uses A, B`, optional): it is checked after the declarations the used blocks export, transitively and each block once, namely their own `def`s (not `reject def`s) that are accepted, checked again under the same configuration, so switching a rule off re-decides them too. Its report, verdict assertions and count cover its own declarations only; the names of a block and of the blocks it uses are one namespace, and a clash is an error when the block is elaborated. Blocks are Lean constants (`Ochr.Surface.Block`), so a block in another file is used by importing that file. Match arms are separated by commas, and a trailing comma after the last arm is allowed (`match p { Z => t, S y => u, }`); `|` separates only the constructors of an `inductive` declaration. Line breaks are whitespace. The examples wrap a multi-line body in parentheses under the signature (`:= ( … )`, ordinary grouping), put one arm per line with a trailing comma, wrap an arm of several statements in `( … ),`, put one statement per line (`;` at the end of the line), indent a nested match one step further, align nothing, and keep matches inside types and argument lists on one line without a trailing comma. `inductive List (A : Type) := Nil | Cons(h : A, t : List(A))` declares an inductive type with a parameter; `inductive And (P : Prop) (Q : Prop) : Prop := Intro(l : P, r : Q)` one in `Prop`; `inductive Void : Type` one with no constructors (the sort defaults to `Type`). A type is applied like a call (`List(Nat)`). A constructor takes its type's parameters first (core `C(ā; t̄)`, D49), written `Cons[Nat](1, Nil[Nat])`, or omitted, `Cons(1, Nil)`: omitted parameters are inferred from the fields' types, and those no field determines (`Nil`'s `A`) from the type the context requires (an annotation `(Nil : List(Nat))` or `let x : T = …`, the goal of a tail, a parameter type at a call, a field type in an enclosing constructor, the type of an `Id`). Constructor values record their parameters when known (always in checked code; in an untyped run only when written). `match xs { Nil => …, Cons(h, t) => … }` binds `h`, `t` as the field places `xs.h`, `xs.t`; `match h {}` has no arms. A match whose constructors are a `Prop` inductive's is by the scrutinee's type (RULES §8). Constructor names are unique across a program. `&A` is allowed only for a data type `A` (`Nat`, `Unit`, `×`, an inductive type in `Type`; not a universe, a Π-type, a proposition or a type variable) and only as the whole declared type of a parameter, a result or an annotated term (D48). The library is the block `Prelude` (`Ochr/Prelude.lean`), written in Ochr and checked like any block, which every block uses implicitly: `Pair (A B : Type) := Mk(fst : A, snd : B)`, `False`, `True := I` and `And := Intro(l, r)`. `A × B`, `(a, b)`, `t.1` and `t.2` are notation for `Pair(A, B)`, `Mk(a, b)` and its fields (D52): a pair is taken apart by `match p { Mk(a, b) => … }`, and an abstract pair has no known fields until it is split (no η). `⊤`, `P ∧ Q`, `⟨h, k⟩` and `refl` are notation for `True`, `And(P, Q)`, `Intro(h, k)` and `I`. Its names are in every block's namespace (so no program may declare another `Mk`). `Eq` on two values built by the same constructor computes to the conjunction of the equations between their fields (injectivity, D52), and `Id` to the conjunction of the equations over its result and each observed place. `by x` names the decreasing parameter; a definition without `by` may not call itself. Calls are saturated and written `f(a, …)` with no space before the parenthesis. `S t`, `Id A t u` and `Eq A t u` are written by juxtaposition, and transport by `J(A, a, b, P, h, t)`. Other syntax: `split f in t` and `split f { C(x̄) => t, … }` (D61: in tail position, split the goal on the first result of a call of `f` that it is stuck on: the goal's sealed programs left to right, each followed down the chain of results its run is stuck on), `rewrite h in t` and `rewrite ← h in t` (D60: with `h : Eq A a b`, `t` proves the goal with `b` replaced by `a`, resp. `a` by `b`; the goal must be known: tail position, a call's argument, or `let x : T = (rewrite …);`), `let ⟨x, y, …⟩ = p; u` and `let (x, y) = p; u` (D60: a one-arm match on `And`'s `Intro` or `Pair`'s `Mk`; patterns nest; on a term, a temporary is bound first), `&p`, `*p`, `p.1`, `p := t`, `let x = t; u`, `let x : T = t; u` (for a match, `T` is the block's type), `t; u`, `match p { Z => t, S y => u }` (and `S _`), `Π(x : A) (y : B). C`, `A → B`, `λ(x : A) : B => t`, `fix f (x : A) : B by x := t`, `(t : A)`, `()`, `(t, u)`, `⟨h, k⟩`, `refl`, `⊤`, `P ∧ Q`, `False`, `A × B`, `Nat`, `Unit`, `Prop`, `Type`, and numerals. `Nat` and `Unit` remain built into the checker (RULES v2.1 makes them library declarations too; see "Where the rules left a choice"). `cong f h`, `trans h k` and `symm h` exist as derivable conveniences outside the core. A `λ` or `Π` in the bound position of a `let`, or a `Π` as a result type, needs parentheses.

`Config` switches each turn off one rule, for counterfactual runs: `eraseOnCopy` (P2, v1.3), `multiOwner` (D18), `recGuard` (D17), `accessInside` (D19), `selfHeadOnly` (v1.1 head-only), `argNotBot` (v1.2 temporaries), `generalize` (v1.2 generalise-then-split), `blockMoves` (v1.3 captures), `proofParamsStar` (v1.4 D27), `recNested` ([Rec] inside nested functions), `erasureByDecl` (D28), `matchEndsInside` (D29), `closureConv` (D30), `unboundWithoutBy` (D31), `patternWritesVisible` (D32), `genConsistent` (finding G1), `classBySyntax`, `blockRule`, `seqByProof`, `rowByDecl` (D35), `leafRule` (findings P1, P3), `positivity` (D36), `globalRecords` (D37), `obsBorrow` (D38), `headGuardNeutral` (D39), `genPlaceType` ([Split-gen]'s type), `confine` (D41), `borrowParam` (D44), `capTypes` (captured values keep their types), `byType` (D45: matching on a proof by its type), `subsingleton` (D45), `propValues` (D42 for constructors of `Prop` inductives), `disjoint` (D47), `injective` (D52), `scrutTyped` (a match's scrutinee has its constructors' type), `refData`, `refTop`, `piUnder` (D48 (1)–(3)), `proofDataFields` (D49 (3)), `unitNorm` (on: D50's counterfactual), `confineBodies` (an extension of D41, off by default), `classInType` (D54), `sortsSyntactic` (D55), `jStuck` (D56), `zeroArmStuck` (D58), `p5` (v1's call skipping), `inferRecPos` (v1's inferred decreasing parameter), and `trace`.

## Layout

| File | Contents |
|---|---|
| `Ochr/Syntax.lean` | terms, places, values (§1, §2); de Bruijn indices, binder names as `Hint`s that `==` ignores |
| `Ochr/Basic.lean` | `mkAnd`/`mkTInd` (`And`'s unit laws), `distinctCtors` (D47), traversals |
| `Ochr/Pretty.lean` | printing in the paper's notation |
| `Ochr/Env.lean` | Ω (frames of typed bindings plus temporaries), the machine state and monad |
| `Ochr/Obs.lean` | paths, `owners`, the footprint `W`, observation tuples (the pure half of §4) |
| `Ochr/Machine.lean` | one `mutual` block: the machine, [Seal], [Close], [Split], stuck blocks, observation, `Id`, [Call-type], [Rec], [Def] |
| `Ochr/Check.lean` | programs as sequences of top-level definitions and inductive declarations |
| `Ochr/Prelude.lean` | the library, the `Prelude` block in Ochr (`Pair`, `False`, `True`, `And`), and where the kernel knows these names |
| `Ochr/Surface.lean`, `Ochr/Notation.lean` | named surface terms, their resolution, blocks (`Block`, `uses`, name clashes), the `ochr` command |
| `Ochr/Test.lean` | running a block after its library (`libOf`), verdict tables, traces; attributing a counterfactual flip to a library declaration's home block (`blockFlips`) |
| `Ochr/Examples/00Std.lean` … `15BorrowTypes.lean` | the example programs, as a tour of the language (next section); `00Std.lean` holds `Std`, the definitions the others use |
| `Ochr/Examples/17HashMap.lean` | the case study: Aeneas's verified hash map as one in-place program with its theorems (`notes/hashmap-case-study.md`) |
| `Ochr/Examples/CaseStudyLedger.lean` | the counterfactual ledger for the case study, run by hand (`lake env lean`), not part of `lake build` |
| `Ochr/Examples/Units.lean` | unit tests of machine functions ([Seal], owners, footprint) on hand-built values |
| `Ochr/Examples/Registry.lean` | every program, in reading order, for the runner and the ledger; the case studies (`caseStudies`: checked, counted and timed, but not re-run by the ledger); the total count; the ledger's switches and row classes |
| `Ochr/Examples/Ledger.lean` | the counterfactual ledger, asserted |
| `Tests.lean` | `lake exe tests` |

## The examples: a tour of the language

Read in order, the numbered files teach the whole language; the order follows RULES (§3 the machine, §4 observation, §5 typing, §8 inductive definitions), starting from the paper's first example. Lean module names cannot start with a digit, so they are imported as `Ochr.Examples.«01Numbers»`. Each file opens with what it covers and where RULES defines it; every program or small group has a comment, and a rejected program says which rule rejects it and why. Each regression (a closed false proof, or an accepted program that went wrong, found while designing the rules) sits with the feature whose rule rejects it, under "What goes wrong without these rules", with the ledger switch that lets it back in. A file holds one `ochr` program or a few (programs are checked independently: names, constructors and helpers such as `AddM` are per program). Every program asserts its exact number of declarations. `Std` holds the library definitions several programs need (`AddM`, `Add`, `AddMZero`, `TailM`, `Bool`, `List(A)`, `Box(A)`), and `Fixtures` those only tests need (`Pick`, `Empty`, `U`, `V`); most programs `use` them; a program that declares a different `List` or `Box` of its own (`Lists`, `GenType`, `GlobalRecords`) does not. `Prelude` is used by every block without saying so.

| File | Covers | RULES | Declarations |
|---|---|---|---|
| `00Std` | `Std`: in-place and pure addition, adding zero does nothing, `TailM`, `Bool`, `List(A)`, `Box(A)`; `Fixtures`: `Pick`, `Empty`, `U`/`V`; and the assertions for `Prelude` | §1, §3, §7 | 11 (+4) |
| `01Numbers` | evaluation in types, the pure theorem by the in-place lemma; matching on numbers; pairs; calls | §1, §3, §7 | 20 |
| `02Borrows` | moving, copying and reborrowing; argument order; the borrow checker ([Access], [Drop]) | §3 | 14 |
| `03ReturnedBorrows` | functions returning a borrow (`TailM`); a returned borrow must come from a borrow argument (D44) | §1, §3 [Close] | 20 |
| `04ClosingOff` | stuck calls and matches, sealed programs, a borrow chosen by a branch, what a stuck match captures, [Close]'s rows, typing a sealed program; naturality up to resolution | §3 | 38 |
| `05Equality` | `Id` and `Eq`: observation, footprints, disjointness, injectivity (pairs included), `J` and its stuck casts (D56); `rewrite h in t` (D60); all owners of a returned borrow are observed (D18) | §4 | 57 |
| `06Snapshots` | types and closures are formed once; what a closure or Π-type captures (values, never borrows; capturing ends a live borrow) | P2, §1, §5 | 21 |
| `07Recursion` | `by x`, entry-value recursion, induction hypotheses in the caller's environment; typing a sealed program keeps the [Rec] state | §5 [Def], [Rec] | 29 |
| `08CaseSplits` | [Split], dependent matching on a computed type, generalising sealed programs, `split f` on a result the goal is stuck on (D61), scrutinee types, global generalisation records | §5 [Split] | 35 |
| `09Functions` | opaque functions, closures, Π-types, comparing functions by observation (D30, D38, D48 (3)); a function type's class and row (D54) | P1, §1, §4 | 54 |
| `10Inductives` | lists, binary search trees (and the paper's trees, whose pure insert runs the in-place one), parameters, strict positivity | §8 | 76 |
| `11Propositions` | `False`, `True`, `And`, matching on proofs by type, a stuck zero-arm match (D58), destructuring `let` (D60), subsingleton elimination | §1, §8 | 75 |
| `12CurrentState` | proofs about the current, mutated state (E5) | §7 | 14 |
| `13Erasure` | erased terms run on a private copy, confinement, erasure decided by syntax | P2 | 55 |
| `14Universes` | `Prop : Type`, no `Type : Type`, no cumulativity, why `&Type` is refused; sorts are syntactic (D55, reviewer-4's programs) | preamble, P2 | 25 |
| `15BorrowTypes` | what may be borrowed and where `&` may appear (D48) | §1 | 16 |
| `17HashMap` | case study: Aeneas's resizing hash map, its lookups, length, invariant, resizing and load factor, proved about the in-place code (`notes/hashmap-case-study.md`) | all | 186 |

750 declarations in all, the `Prelude`'s 4 and the case study's 186 included. `notes/lean-checker.md` §17 maps the old file and program names (`E1`, `V17.LieL`, `Attacks.Knot`, …) to these.

## Rule → function

| Rule (RULES v2.0) | Function (`Ochr/Machine.lean` unless noted) |
|---|---|
| §3 [End ℓ] | `endBorrow` (substitution of every `loan_ℓ` by `substEnv`) |
| §3 [Access] | `accessPath` (loans on the path, including the place itself), `accessInside` (loans inside the content) |
| §3 [Read] | `readPlace` |
| §3 [Borrow] | `borrowPlace` |
| §3 [Assign] | `eval` (`.assign`), `assignPlace` |
| §3 [Let] | `eval` (`.letIn`) |
| §3 [Drop] | `dropTopBind`, `dropValue`, `popFrame` |
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
| P1 conversion | `conv`: `==` on normal forms (`Value.beq`, which ignores binder names and constructor values' parameters), function values by their generic call (`convFn`, D30), Π-types under their binders (`convPi`, D48 (3)), the unit laws (`unitTop`, D50) |
| §1 `&A` (D48) | `isDataType` at `&A`'s formation (`evalCore`), `Term.refsOk`/`refTopOk` in `checkDef` (`&` only at the top of a declared type) |
| P2 erased terms | `eval` (flags *erased* and *proof*: a call by its callee's class; `let`/`;`/`match` iff their tail is a proof; proof formers; a variable declared of sort Prop (a flag on its binding: `paramFlags`, `leafProof`), a field declared of a proposition (`fieldIsProof`), a constructor of a `Prop` inductive (`ctorIsProof`), a proof constant, a `λ` returning proofs; an ascription at a declared proposition), `fnClass`/`propDecl`/`declOfDom`/`declOfVal` (a function's class from its codomain term, v1.7), `logEffect`/`settleErased`/`flushPending`/`confinedCopy` (D41: erased runs are confined, judged by the outermost erased term; arguments of erased calls exempt), `evalType` (types on a private copy), `capture` (Π-types and closures close over values, never borrows) |

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
