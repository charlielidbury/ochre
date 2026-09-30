# Assignment: verified in-place quicksort in Ochr

## The task

Implement quicksort on an array of words, in place, in the language Ochr, and prove that it sorts: its result is sorted (Q1) and is a permutation of its input (Q2). The properties are stated about your in-place program itself. There is no separate specification to write.

You work in one file, `Quicksort.lean`. It is a skeleton: the definitions, the signature, the two property statements and the tests are given (the FIXED regions, between `FIXED-BEGIN` and `FIXED-END` marker comments), and the holes, written `TODO`, are yours to fill. Add any helper definitions and lemmas you need to the block `QuicksortSolution`, between its FIXED regions.

Ochr is a research language, so you will not have met it before. Read `docs/GUIDE.md` first: it teaches enough of the language to start, in about fifteen minutes. The reference is `docs/RULES.md`, the examples tour is `checker/Ochr/Examples/00Std.lean` to `15BorrowTypes.lean`, and the arrays library you will use is `checker/Ochr/Examples/16Arrays.lean`.

## What is given

In `Quicksort.lean`:

- **The array type.** An array of `n` words is a view `Slice(Word, n)` from the arrays library, and your quicksort takes a borrow of one, `s : &Slice(Word, n)` (Rust's `&mut [u64]`). The length `n` is part of the type and never changes. Element `i` is `Nth(Word, n, s, i, h)`, where `h : Lt(i, n)` proves the index is in bounds.
- **`Sorted(n, s)`** (SPEC §4, sorted): for all `i`, `j` with `i < j < n`, element `i` is at most element `j`. Reading element `i` needs its bound `hi : Lt(i, n)` as well, which `i < j < n` implies; it is an extra hypothesis of the definition, not an extra condition.
- **`Perm(n, a, b)`** (SPEC §4, perm): for every word `x`, `Count(x, n, a) = Count(x, n, b)`, where `Count` is the library's count of the elements equal to `x`.
- **The signature** `QuickSort (n : Word) (s : &Slice(Word, n)) : Unit`.
- **The statements** (SPEC §5):
  - Q1, `QuickSortSorted (n : Word) (s : &Slice(Word, n)) : (let c = *s; QuickSort(n, &c); Sorted(n, c))`. Read it as: take a copy `c` of the array's contents, sort `c` in place with `QuickSort`, and then `c` is sorted.
  - Q2, `QuickSortPerm (n : Word) (s : &Slice(Word, n)) : (let c = *s; QuickSort(n, &c); Perm(n, c, *s))`: the contents afterwards are a permutation of the contents before, which are still `*s`.
- **The tests**, in the block `QuicksortTests`, transcribed from the SPEC's test vectors: 29 arrays of length 0 to 24 with elements below 100 (empty, one element, two in each order, duplicates, sorted, reverse-sorted, all equal, a mixed array, and 20 random ones). Each sorts an array in place and compares the whole array with the expected one; `refl` proves the comparison when the two are equal. The last test, `TestReject_unsorted`, must be rejected: it expects the unsorted input back.
- **The library** (`ArrayLemmas`): the view model (`Nth`, `SetS`, `TakeS`, `DropS`, `JoinS`), the native operations (`Read`, `Set`, `Swap`, `GetMut`, `WithSplit`, …), the order on words and facts about it (`Le`, `Lt`, `LeDec`, `LtDec`, `LeTrans`, …), and lemmas (`NthSetSame`, `NthSetOther`, `JoinTakeDrop`, `CountJoin`, `CountSet`, `CountSwap`, `SwapIsSwapS`, …). `docs/GUIDE.md` §9 lists them.

## What you write

- The body of `QuickSort`, and any helpers it needs. Whether `QuickSort` itself is recursive is up to you.
- The proofs `QuickSortSorted` and `QuickSortPerm`, and any lemmas they need.

## Requirements on the algorithm

These are checked by a person reading your solution (SPEC §3), not by the grader:

1. **Partition** with the Lomuto or the Hoare scheme, and say which in a comment at your partition function.
2. **Two recursive calls on disjoint borrowed sub-ranges.** After partitioning, sort the part before the pivot and the part after it by two recursive calls, each given a borrow of its own part only. In Ochr that is `WithSplit`, the library's `split_at_mut`: it runs a function on borrows of the first `k` elements and of the rest.
3. **In place.** No copy of the array or of a part of it: runtime code reaches the array only through the library's native operations (the checker enforces this), and does not copy elements out to another structure and back. Auxiliary space is O(1) beyond the recursion.
4. **Nothing else.** No other sorting algorithm, as a fallback or otherwise.

## Forbidden

The grader rejects, in `Quicksort.lean` outside the FIXED regions:

- `TODO` (the hole marker);
- `reject def` (a declaration the checker must reject counts as correct when it fails, so it would turn a failed proof into a pass);
- new `implemented by` functions, and `abstract`, `unsized` or `copy` declarations;
- declaring a name that already exists: a built-in (`Nat`, `Unit`, …), a library name (`Word`, `Lt`, `Count`, …) or a name declared in a FIXED region (the checker itself refuses most of these; `Nat` and `Unit` it would accept, and a FIXED statement could then change meaning);
- any Lean outside the `ochr` blocks, a new `ochr` block, and any Lean command inside one (`axiom`, `sorry`, `set_option`, `macro`, `notation`, attributes, `#eval`, `import`, `open`, …);
- code that closes the block `QuicksortSolution` early, or opens a comment or string that runs into a FIXED region.

Do not change the checker, the library, the build files or the grader: only `Quicksort.lean` is graded (it is copied into a fresh copy of this directory, and graded there). A proof that relies on a bug in the checker fails the assignment.

## Checking your work

- `lake -q build` elaborates your file; the checker runs as each block is elaborated and reports every rejected declaration as an error, with the reason.
- `lake -q exe check` prints the checker's verdict on every declaration, with the reason for each rejection. `lake -q exe check QuicksortSolution` skips the tests; `lake -q exe check --trace QuickSortSorted` shows the checker's view of that declaration's goal.
- `./grade.sh` runs everything the grader checks. Its last line is `GRADE: PASS` or `GRADE: FAIL: <reasons>`, and it lists the remaining holes.

## When you are done

You are done when `./grade.sh` passes. That requires:

1. every FIXED region unchanged;
2. no hole and no forbidden construct left;
3. `Quicksort.lean` builds, and the checker accepts every declaration of `QuicksortSpec`, `QuicksortSolution` (your helpers included) and `QuicksortTests`, except `TestReject_unsorted`, which it must reject;
4. so every test passes, and Q1 and Q2 are proved.

## The sibling assignment

This assignment has a sibling, condition `ochr-2p`, which asks for the same Q1 and Q2, character for character, about the same `QuickSort`, but obtained in the two-program style: a pure model of the sort, the model's properties, and a proof that the in-place program agrees with the model. The observable obligations are the same; only the route to them differs. Here you prove Q1 and Q2 directly about the in-place program.

## Limitations of the language that affect this task

- **No recursion on a measure.** A recursive function recurses on a declared parameter (`by x`), and every recursive call must pass a strict sub-value of it, such as `k'` in `Succ(k')`. The two parts after a partition are shorter than the array, but their lengths are not sub-values of its length, so quicksort cannot recurse on the length directly. The usual workaround is a *fuel* parameter: a `Word` that decreases by one at each recursive call, started at the length, which is always enough. `QuickSort`'s own signature has no fuel; if you use fuel, `QuickSort` calls a helper that takes it, and Q1 then includes showing that this fuel suffices.
- **No automation.** Every case split, induction and rewrite is written by hand.
- **Unary numbers.** `Word` is unary in the logic, so concrete runs are slow for large numbers; the tests use numbers below 100 and arrays of at most 24 elements. Ochr's `Word` has no upper bound, so there is no overflow to worry about.
- **Borrows of parts of an array** exist only inside `WithSplit`'s function argument, and the recursion happens inside that function (a recursive call may appear inside a closure in the recursive function's body).
- **Element borrows** (`GetMut`) exist only for `Word` elements, which is the case here.
