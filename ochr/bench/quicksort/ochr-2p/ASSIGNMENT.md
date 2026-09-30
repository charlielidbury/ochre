# Assignment: verified in-place quicksort in Ochr, with a pure model

## The task

Implement quicksort on an array of words, in place, in the language Ochr, and prove that it sorts, in the two-program style: write a pure functional model of the sort, prove that the model's result is sorted (Q1) and a permutation of its input (Q2), and prove that your in-place program agrees with the model. Q1 and Q2 about the in-place program then follow; that last step is provided.

You work in one file, `Quicksort.lean`. It is a skeleton: the definitions, the signatures, the statements and the tests are given (the FIXED regions, between `FIXED-BEGIN` and `FIXED-END` marker comments), and the holes, written `TODO`, are yours to fill. Add any helper definitions and lemmas you need to the blocks `QuicksortModel` and `QuicksortSolution`, between their FIXED regions.

Ochr is a research language, so you will not have met it before. Read `docs/GUIDE.md` first: it teaches enough of the language to start, in about fifteen minutes. The reference is `docs/RULES.md`, the examples tour is `checker/Ochr/Examples/00Std.lean` to `15BorrowTypes.lean`, and the arrays library you will use is `checker/Ochr/Examples/16Arrays.lean`.

## What is given

In `Quicksort.lean`:

- **The array type.** An array of `n` words is a view `Slice(Word, n)` from the arrays library, and your quicksort takes a borrow of one, `s : &Slice(Word, n)` (Rust's `&mut [u64]`). The length `n` is part of the type and never changes. Element `i` is `Nth(Word, n, s, i, h)`, where `h : Lt(i, n)` proves the index is in bounds.
- **`Sorted(n, s)`** (SPEC §4, sorted): for all `i`, `j` with `i < j < n`, element `i` is at most element `j`. Reading element `i` needs its bound `hi : Lt(i, n)` as well, which `i < j < n` implies; it is an extra hypothesis of the definition, not an extra condition.
- **`Perm(n, a, b)`** (SPEC §4, perm): for every word `x`, `Count(x, n, a) = Count(x, n, b)`, where `Count` is the library's count of the elements equal to `x`.
- **The model's signature** `SortModel (n : Word) (v : Slice(Word, n)) : Slice(Word, n)`, a function on array values.
- **The model's properties** (holes):
  - `SortModelSorted (n : Word) (v : Slice(Word, n)) : Sorted(n, SortModel(n, v))` (Q1 about the model);
  - `SortModelPerm (n : Word) (v : Slice(Word, n)) : Perm(n, SortModel(n, v), v)` (Q2 about the model).
- **The program's signature** `QuickSort (n : Word) (s : &Slice(Word, n)) : Unit`.
- **The agreement** (a hole): `QuickSortAgrees (n : Word) (s : &Slice(Word, n)) : Id Unit (QuickSort(n, s)) (*s := SortModel(n, *s))`. Read it as: running `QuickSort(n, s)` has exactly the effect of writing the model's result into `*s` (same result, same final contents).
- **Q1 and Q2 about the program** (SPEC §5), with their proofs *provided*:
  - Q1, `QuickSortSorted (n : Word) (s : &Slice(Word, n)) : (let c = *s; QuickSort(n, &c); Sorted(n, c))`: take a copy `c` of the array's contents, sort `c` in place with `QuickSort`, and then `c` is sorted;
  - Q2, `QuickSortPerm (n : Word) (s : &Slice(Word, n)) : (let c = *s; QuickSort(n, &c); Perm(n, c, *s))`: the contents afterwards are a permutation of the contents before, which are still `*s`.
  Both are proved from the agreement and the model's properties by the generic lemmas `SortedFromModel` and `PermFromModel` in the block `QuicksortCompose`, which hold for any in-place sort and any model.
- **The tests**, in the block `QuicksortTests`, transcribed from the SPEC's test vectors: 29 arrays of length 0 to 24 with elements below 100 (empty, one element, two in each order, duplicates, sorted, reverse-sorted, all equal, a mixed array, and 20 random ones). Each sorts an array in place with `QuickSort` and compares the whole array with the expected one. The last test, `TestReject_unsorted`, must be rejected: it expects the unsorted input back.
- **The library** (`ArrayLemmas`): the view model (`Nth`, `SetS`, `TakeS`, `DropS`, `JoinS`, `SwapS`), the native operations (`Read`, `Set`, `Swap`, `GetMut`, `WithSplit`, …), the order on words and facts about it (`Le`, `Lt`, `LeDec`, `LtDec`, `LeTrans`, …), and lemmas (`NthSetSame`, `NthSetOther`, `JoinTakeDrop`, `CountJoin`, `CountSet`, `CountSwap`, `SwapIsSwapS`, …). `docs/GUIDE.md` §9 lists them.

## What you write

- In `QuicksortModel`: the body of `SortModel`, any pure helpers, and the proofs `SortModelSorted` and `SortModelPerm`. The model must be **pure**: no borrows (`&`) and no assignment (`p := t`) anywhere in this block; it computes on values. It may use the library's pure functions on views (`Nth`, `SetS`, `SwapS`, `TakeS`, `DropS`, `JoinS`, …), and since it takes a view by value it is model code, which may also match on the view's representation (see `docs/GUIDE.md` §9). The model does not have to be a quicksort, but the agreement will be easiest to prove if it follows the same steps as your program.
- In `QuicksortSolution`: the body of `QuickSort` and any helpers it needs, and the proof `QuickSortAgrees`.

## Requirements on the algorithm

These are checked by a person reading your solution (SPEC §3), not by the grader. They apply to `QuickSort`, the in-place program:

1. **Partition** with the Lomuto or the Hoare scheme, and say which in a comment at your partition function.
2. **Two recursive calls on disjoint borrowed sub-ranges.** After partitioning, sort the part before the pivot and the part after it by two recursive calls, each given a borrow of its own part only. In Ochr that is `WithSplit`, the library's `split_at_mut`: it runs a function on borrows of the first `k` elements and of the rest.
3. **In place.** No copy of the array or of a part of it: runtime code reaches the array only through the library's native operations (the checker enforces this), and does not copy elements out to another structure and back. In particular `QuickSort` may not run `SortModel` and write its result. Auxiliary space is O(1) beyond the recursion.
4. **Nothing else.** No other sorting algorithm, as a fallback or otherwise.

## Forbidden

The grader rejects, in `Quicksort.lean` outside the FIXED regions:

- `TODO` (the hole marker);
- `reject def` (a declaration the checker must reject counts as correct when it fails, so it would turn a failed proof into a pass);
- new `implemented by` functions, and `abstract`, `unsized` or `copy` declarations;
- declaring a name that already exists: a built-in (`Nat`, `Unit`, …), a library name (`Word`, `Lt`, `Count`, …) or a name declared in a FIXED region (the checker itself refuses most of these; `Nat` and `Unit` it would accept, and a FIXED statement could then change meaning);
- in the block `QuicksortModel`: any borrow (`&`) or assignment (`p := t`);
- any Lean outside the `ochr` blocks, a new `ochr` block, and any Lean command inside one (`axiom`, `sorry`, `set_option`, `macro`, `notation`, attributes, `#eval`, `import`, `open`, …);
- code that closes a block early, or opens a comment or string that runs into a FIXED region.

Do not change the checker, the library, the build files or the grader: only `Quicksort.lean` is graded (it is copied into a fresh copy of this directory, and graded there). A proof that relies on a bug in the checker fails the assignment.

## Checking your work

- `lake -q exe check` prints the checker's verdict on every declaration, with the reason for each rejection. `lake -q exe check QuicksortModel` checks only the model (and what it uses); `lake -q exe check QuicksortSolution` skips the tests; `lake -q exe check --trace QuickSortAgrees` shows the checker's view of that declaration's goal.
- `./grade.sh` runs everything the grader checks. Its last line is `GRADE: PASS` or `GRADE: FAIL: <reasons>`, and it lists the remaining holes.

## When you are done

You are done when `./grade.sh` passes. That requires:

1. every FIXED region unchanged;
2. no hole and no forbidden construct left;
3. `Quicksort.lean` builds, and the checker accepts every declaration of every block (your helpers included), except `TestReject_unsorted`, which it must reject;
4. so every test passes, the model and the agreement are proved, and Q1 and Q2 about `QuickSort` follow.

## Why this assignment asks for exactly what the one-program version asks for

This assignment has a sibling, condition `ochr`, in which the same Q1 and Q2 are proved directly about the in-place program, with no model. The two pose the same observable obligations:

- The end result is the same. `QuickSortSorted` and `QuickSortPerm` here are, character for character, the statements the one-program assignment asks you to prove, about the same signature `QuickSort (n : Word) (s : &Slice(Word, n)) : Unit`, and the checker accepts them here only once they are proved.
- Nothing is added to what is observable. The model, its properties and the agreement are the route by which Q1 and Q2 are obtained; the lemmas that turn them into Q1 and Q2 (`SortedFromModel`, `PermFromModel`) are provided and checked, for any sort and any model, so they cost you nothing.
- Nothing is taken away. The agreement pins `QuickSort`'s effect to the model's result exactly, and the model must itself be sorted and a permutation, so a program that passes here also satisfies the one-program assignment, and the tests and the algorithm requirements are identical.

The only difference is the route: here the proofs about sorting are done once on a pure function, and the in-place program is connected to it by the agreement; in the one-program version they are done on the in-place program directly.

## Limitations of the language that affect this task

- **No recursion on a measure.** A recursive function recurses on a declared parameter (`by x`), and every recursive call must pass a strict sub-value of it, such as `k'` in `Succ(k')`. The two parts after a partition are shorter than the array, but their lengths are not sub-values of its length, so neither the program nor the model can recurse on the length directly. The usual workaround is a *fuel* parameter: a `Word` that decreases by one at each recursive call, started at the length, which is always enough. `QuickSort`'s and `SortModel`'s own signatures have no fuel; if you use fuel, they call helpers that take it, and the proofs then include showing that this fuel suffices.
- **No automation.** Every case split, induction and rewrite is written by hand.
- **Unary numbers.** `Word` is unary in the logic, so concrete runs are slow for large numbers; the tests use numbers below 100 and arrays of at most 24 elements. Ochr's `Word` has no upper bound, so there is no overflow to worry about.
- **Borrows of parts of an array** exist only inside `WithSplit`'s function argument, and the recursion happens inside that function (a recursive call may appear inside a closure in the recursive function's body).
- **No projections of stuck pairs**: a model function that returns a pair cannot have its components taken with `.1` in a statement until the pair is a constructor value; return separate results or `match` on the pair.
