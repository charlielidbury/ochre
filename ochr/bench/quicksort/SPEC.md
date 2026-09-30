# Quicksort: the system-neutral assignment

This is the one specification that every quicksort package transcribes. Each package's `ASSIGNMENT.md` restates it in the package's own notation and cites the property numbers used here (Q1, Q2, …). The only system-specific part of this file is the correspondence table at the end, where each package records which declaration states each property.

The task: implement quicksort on an array of words, in place, with the two recursive calls made on two disjoint borrowed sub-ranges, and prove that the result is sorted and is a permutation of the input.

## 1. Values

- 𝕎 = {0, 1, …, 2⁶⁴ − 1}, the unsigned machine words (Rust `u64`, Ochr `Word`), ordered by the usual `≤`.
- An array `a` of length `n` is a sequence `a[0], …, a[n − 1]` of words. `|a| = n`.
- Ochr's `Word` is unbounded, so in Ochr 𝕎 is all of ℕ. This changes nothing below: sorting only compares.

## 2. Operation (FIXED signature)

    quicksort(a : &mut Array(𝕎))

It sorts `a` in place and returns nothing. The array's type is the system's native one for a mutable sequence of words: a Rust slice `&mut [u64]` (`rust`, `aeneas`, `verus`), whatever Ochr's arrays library provides (`ochr`, `ochr-2p`), a Lean `Array UInt64` or `Vector UInt64 n` (`lean`). The length never changes.

A system that cannot yet express recursion on a decreasing measure (Ochr today) may give `quicksort` an extra fuel argument, a natural number bounding the recursion depth. Q1 and Q2 are then stated with the fuel equal to the length of the array, which is always enough. This is a limitation of the language, recorded in the package, and not part of the task.

## 3. Algorithm requirements (checked by a human reader, not by the grader)

- **A1 (partition).** Choose a pivot and partition the range with the Lomuto or the Hoare scheme. The solver says which in a comment at the partition function.
- **A2 (two disjoint recursive calls).** After partitioning, the range is split into two disjoint sub-ranges that are borrowed separately (in the style of Rust's `split_at_mut`) and each is sorted by a recursive call. The pivot's final position, if the scheme has one, belongs to neither.
- **A3 (in place).** No copy of the array or of a sub-range is made (no copy out and copy back, no temporary array). Auxiliary space is O(1) beyond the recursion.
- **A4 (nothing extra).** No library sort, selection or permutation routine, and no other sorting algorithm as a fallback (for example insertion sort on small ranges).

The `lean` condition has no borrows: there, A2 means the recursive calls sort the two disjoint index ranges `[lo, p)` and `[p + 1, hi)` (or Hoare's split) of the one array, and A3 means updates are the operations that are in place when the array is unshared (`Array.swap`, `Array.set` and similar).

## 4. Definitions (FIXED)

Both are provided in every package, transcribed from here. A system whose library has an equivalent notion (for example Verus's multisets or `Seq::sorted`) may state the property with that notion instead, and the correspondence table must then justify why it is equivalent.

- **sorted.** `sorted(a) :⟺ ∀ i j. i < j < |a| ⟹ a[i] ≤ a[j]`.
- **count.** `count(x, a) := |{ i | i < |a| ∧ a[i] = x }|`, the number of positions holding `x`. Defined by recursion over the positions (or the list) in each system.
- **perm.** `perm(a, b) :⟺ ∀ x ∈ 𝕎. count(x, a) = count(x, b)`.

Equal counts for every word imply equal lengths, and in place the lengths are equal anyway.

## 5. Properties

For every array `a`, let `a₀` be its contents before `quicksort(&mut a)` and `a₁` its contents after.

- **Q1.** `sorted(a₁)`.
- **Q2.** `perm(a₁, a₀)`.

Where the signature takes fuel (§2), both are stated for fuel `= |a₀|`, so they include that this much fuel is enough.

Both properties are total: `quicksort` returns normally, that is, it terminates, does not panic (no out-of-bounds index) and does not overflow. In a system where every function terminates and nothing can fail (Ochr, pure Lean) this is automatic. Where the system can express failure or divergence (Aeneas's `Result`, Verus's checks for panics, overflow and `decreases`), the FIXED statements include it, for example `quicksort a = ok a′` in Aeneas.

## 6. Tests

`tests.json` holds the test vectors. Every package runs all of them, transcribed mechanically from the JSON (by a script, where practical).

The file holds a list of `cases`, each `{"name", "input", "expected"}`: sorting `input` in place must leave exactly `expected`.
- Hand-picked cases: empty, one element, two elements in each order, duplicates, already sorted, reverse-sorted, all equal, and a short mixed array with repeated pivot values.
- 20 pseudo-random arrays from a fixed seed, of lengths from 0 to 64 (64 included), with values up to 99, some of them drawn from 0–3 so that duplicates are frequent.

Values are at most 99 so that systems with unary numbers (Ochr) can run the tests. The expected outputs were computed by an independent oracle (Python's `sorted`, in `_reference/gen_tests.py`), and the unverified Rust reference in `_reference/` passes all of them.

## 7. Correspondence table

Each package fills in its own table: for each item, the file and declaration that states it. Say how the statement differs from §4–§5 where it does (for example, fuel, or a library notion used for `sorted` or `perm`, with the justification of the equivalence).

### ochr

| Id | File | Declaration | Notes |
|---|---|---|---|
| quicksort (signature) | | | |
| sorted | | | |
| count, perm | | | |
| Q1 | | | |
| Q2 | | | |
| Partition scheme | | | |

### ochr-2p

| Id | File | Declaration | Notes |
|---|---|---|---|
| quicksort (signature) | | | |
| sorted | | | |
| count, perm | | | |
| Model and agreement | | | |
| Q1 | | | |
| Q2 | | | |
| Partition scheme | | | |

### aeneas

| Id | File | Declaration | Notes |
|---|---|---|---|
| quicksort (signature) | | | |
| sorted | | | |
| count, perm | | | |
| Q1 | | | |
| Q2 | | | |
| Partition scheme | | | |

### verus

| Id | File | Declaration | Notes |
|---|---|---|---|
| quicksort (signature) | | | |
| sorted | | | |
| count, perm | | | |
| Q1 | | | |
| Q2 | | | |
| Partition scheme | | | |

### lean

| Id | File | Declaration | Notes |
|---|---|---|---|
| quicksort (signature) | | | |
| sorted | | | |
| count, perm | | | |
| Q1 | | | |
| Q2 | | | |
| Partition scheme | | | |

### rust

The `rust` condition has no properties. It implements the same signature and runs the same tests.

| Id | File | Declaration | Notes |
|---|---|---|---|
| quicksort (signature) | | | |
| Tests | | | |
| Partition scheme | | | |
