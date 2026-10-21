# The examples

Every file here is checked when `lake build` elaborates it: a `def` must be accepted, and a `reject def` rejected, or the build fails at the declaration. `Registry.lean` lists every block for the test runner and the counterfactual ledger, and asserts the total number of declarations.

## Reading order

1. **The library.** One file per topic, each a block that uses only what it needs. A block sees the accepted declarations of the blocks it `uses`, transitively, and their names and its own form one namespace. Lean already has constants named `Bool`, `Nat`, `List`, `Option` and `Array`, so the blocks have plural names. The files are singular.

   | File | Block | Contents | Uses |
   |---|---|---|---|
   | `Bool.lean` | `Bools` | `Bool`, `IsTrue` | — |
   | `Logic.lean` | `Logic` | `Dec(P, Q)`, `Void`, `absurdV` (`False`, `True`, `And` are the built-in `Prelude`'s) | — |
   | `Nat.lean` | `Nats` | `AddM`, `Add`, `AddMZero`, `AddMS`, `AddS`, `TailM` (the paper's first example) | — |
   | `Word.lean` | `WordType` | the type `Word` alone | — |
   | | `Words` | `Le`/`Lt` and their lemmas, `LeDec`/`LtDec`, `EqB`/`LeB`/`LtB`, `WAdd`, `Sub`, `Pred`, `W(n)`, `ModS`/`ModLt` | `WordType`, `Bools`, `Logic` |
   | `List.lean` | `Lists` | `List(A)`, `LenL` | `WordType` |
   | `Option.lean` | `Options` | `Opt(A)`, `IsSome`, `IsNone` | — |
   | `Box.lean` | `Boxes` | `Box(A)` | — |
   | `Fixtures.lean` | `Fixtures` | definitions only tests need: `Pick`, `Empty`, `U`/`V` | — |
   | `Array.lean` | `Arrays`, `ArrayLemmas` | the arrays library: the model, the natives, `Swap`/`Replicate`/`Fill`, and the lemma library | `Words`, `Lists`, `Logic` |

   `WordType` is the one file with two blocks. Programs that need only the type, and define their own order or numerals, use it: the paper's trees define their own `Lt`, and `Borrows` has a witness named `W`.

2. **The tour**, in the order of RULES (§3 the machine, §4 observation, §5 typing, §8 inductive definitions):
   - `Numbers`, `Borrows`, `ReturnedBorrows`, `ClosingOff`;
   - `Equality`, `Snapshots`, `Recursion`, `CaseSplits`;
   - `Functions`, `Inductives`, `Propositions`, `CurrentState`;
   - `Erasure`, `Universes`, `BorrowTypes`.

   Each file opens with what it covers and where RULES defines it.

3. **The case studies:**
   - `ArrayBench` explains the arrays library and holds its benchmarks. Its block `ArrayHashMap` is the hash map over an array, which `DepVec` reuses.
   - `Quicksort` is the in-place quicksort, proved sorted and a permutation.
   - `HashMap` is Aeneas's hash map.
   - `DependentFields` covers dependent fields (`DepFields`), with the growable vector and resizable table `DepVec`.

**Infrastructure:**
- `Registry` lists every block, and `Ledger` asserts the counterfactual ledger;
- `CaseStudyLedger` is the case studies' ledger, run by hand;
- `Units` holds unit tests of machine functions;
- `Editor` checks that errors are located;
- `Playground` is the user's own, untracked file.

## Reusable blocks and results

A used block is checked again inside every block that uses it. So a block that other blocks `use` holds only what they reuse: types, operations, model functions and lemmas. Runs, headline theorems and `reject def`s go in blocks that nothing uses. In the library and the tour, no used block needed splitting. `ArrayBench`'s hash map became its own block, `ArrayHashMap`, because `DepVec` uses it and nothing else in the benchmarks. `Units`' `AttrLib` keeps its `reject def Hidden`, because that test is about what a used block exports.

## Old names

Historical notes (`ochr/core/notes/`, `DECISIONS.md`, `ochr/docs/`), commit messages and the scratch probes use the old names:

| Old | New |
|---|---|
| `00Std.lean`: `Std` | `Nat.lean` (`Nats`: `AddM`, `Add`, `AddMZero`, `AddMS`, `AddS`, `TailM`), `Bool.lean` (`Bools`: `Bool`, `IsTrue`), `List.lean` (`Lists`: `List`), `Box.lean` (`Boxes`), `Option.lean` (`Options`), `Logic.lean` (`Logic`: `Dec`, `Void`, `absurdV`), `Word.lean` (`WordType`: `Word`) |
| `00Std.lean`: `Words`, `Fixtures` | `Word.lean` (`Words`), `Fixtures.lean` (`Fixtures`) |
| `01Numbers.lean` … `15BorrowTypes.lean` | `Numbers.lean` … `BorrowTypes.lean`, the same blocks (`10Inductives`' block `Lists` is now `NatLists`) |
| `16Arrays.lean`: `Index` | `Word.lean`'s `Words` (with `Leb` → `LeB`, `Eqb` → `EqB`), and `Dec` in `Logic` |
| `16Arrays.lean`: `Arrays`, `ArrayLemmas` | `Array.lean` (`LenL` moved to `Lists`) |
| `16Arrays.lean`: `ArrayBench` | `ArrayBench.lean`: `ArrayHashMap` (`Entry` … `Size`) and `ArrayBench` (`ModS`, `LeNext`, `ModLt` moved to `Words`) |
| `16Arrays.lean`: `Quicksort` | `Quicksort.lean` |
| `17HashMap.lean`, `18DependentFields.lean` | `HashMap.lean`, `DependentFields.lean` |
