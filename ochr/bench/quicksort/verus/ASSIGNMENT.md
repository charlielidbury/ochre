# Assignment: a verified in-place quicksort in Verus

## 1. The task

Implement quicksort on a slice of `u64` in Rust, in place, and prove it correct with [Verus](docs/verus-guide/SUMMARY.md): the result is sorted, and it is a permutation of the input. After partitioning, the two sides are sorted by recursive calls on two disjoint sub-slices, borrowed separately as with `split_at_mut`.

All your work goes in one file, `src/quicksort.rs`. It already contains the skeleton: the definitions of `sorted` and `perm`, the signature of `quicksort` with its specification, and the tests. Your job is to fill in the hole so that the file verifies, compiles and passes the tests.

You are done when `./grade.sh` prints a last line starting with `GRADE: PASS` (section 8).

## 2. What is provided (FIXED)

The parts of `src/quicksort.rs` between a `// FIXED-BEGIN <id>` line and the matching `// FIXED-END <id>` line are FIXED. You must not change them in any way, not even whitespace. They are:

- **The definitions** `sorted(s)` and `perm(a, b)` on `Seq<u64>` (section 4).
- **The signature of `quicksort(a: &mut [u64])`** with its `ensures` contract (section 4).
- **The tests** (section 6), after the `verus!` block.

## 3. What you write (the hole)

- The body of `quicksort`, currently `todo!()`. Verus reports it as `precondition not satisfied`, because a panic's precondition is `false`.
- Anything else you need: a partition function, a recursive sorting function, spec functions, proof functions (lemmas), loop invariants, `decreases` clauses and `proof { ... }` blocks.

`quicksort` may itself be the recursive function, or it may call one of yours. Loops are allowed (the partition will usually be a loop); the requirement on recursion is only that the two sides are sorted by two recursive calls (section 5).

**Where you may add code.** Anywhere inside the `verus! { ... }` block that is outside the FIXED regions: new items before or after the FIXED ones, and attributes on a line directly before a `// FIXED-BEGIN` line (they then apply to that item, for example `#[verifier::rlimit(20)]`). A `decreases` clause may go between the `// FIXED-END quicksort` line and the function body, if you make `quicksort` itself recursive. Do not put code outside the `verus!` block, and do not wrap FIXED items in modules or other items: the grader refers to them by name.

## 4. The required properties

The properties are numbered as in the system-neutral specification of this assignment (Q1 and Q2). In the contract, `old(a)@` is the contents of the slice when the call starts and `final(a)@` its contents when the call ends, both as a `Seq<u64>` (see `docs/verus-guide/mutable-references.md` for `old` and `final`).

| Id | Property | Where |
|---|---|---|
| Q1 | the result is sorted | `quicksort`: `sorted(final(a)@)` |
| Q2 | the result is a permutation of the input | `quicksort`: `perm(final(a)@, old(a)@)` |

The definitions:
- `sorted(s)`: `forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]`.
- `perm(a, b)`: `a.to_multiset() == b.to_multiset()`. Here `s.to_multiset()` is `vstd`'s multiset of the elements of `s`, so `s.to_multiset().count(x)` is the number of positions of `s` that hold `x`, and two multisets are equal exactly when every count agrees. So `perm(a, b)` says that every value occurs equally often in `a` and in `b`. `vstd`'s `seq_lib.rs` and `multiset.rs` have the lemmas about `to_multiset` (for example what `update`, `push` and `+` do to it).

Verus checks total correctness: no panics, no arithmetic overflow, every index in bounds, and every loop and recursive function terminates (it needs a `decreases` clause).

## 5. The algorithm

A human reader checks these requirements; the grader does not.

- **A1 (partition).** Choose a pivot and partition the range with the Lomuto or the Hoare scheme. Say which in a comment at the partition function.
- **A2 (two disjoint recursive calls).** After partitioning, split the slice into two disjoint sub-slices borrowed separately (for example with `split_at_mut`, or with sub-slice borrows such as `&mut a[..p]` and `&mut a[p + 1..]`), and sort each by a recursive call. The pivot's final position, if the scheme has one, belongs to neither.
- **A3 (in place).** No copy of the slice or of a sub-slice (no copy out and copy back, no temporary array). Auxiliary space is O(1) beyond the recursion.
- **A4 (nothing extra).** No library sort, selection or permutation routine, and no other sorting algorithm as a fallback (for example insertion sort on small ranges).

`vstd` specifies `split_at_mut` in `docs/vstd/std_specs/slice.rs`: after `let (l, r) = a.split_at_mut(mid);`, `l@` and `r@` are the two halves of `a@`, and `final(a)@ == final(l)@ + final(r)@`.

## 6. The tests

The FIXED `tests` region, after the `verus!` block, holds the tests. They are plain Rust (not verified), and they run in the binary that `./grade.sh` compiles. Each of the 29 cases sorts a fresh copy of an input and compares it with the expected output: empty, one element, two elements in each order, duplicates, already sorted, reverse-sorted, all equal, a short mixed array with repeated pivot values, and 20 pseudo-random arrays of lengths 0 to 24.

## 7. Allowed and forbidden

You may use anything in `vstd` in specifications and proofs, including `Seq`, `Multiset` and their lemmas, and the slice operations Verus supports in executable code (indexing, `len`, `split_at_mut`, sub-slice borrows).

`./grade.sh` rejects any of the following outside the FIXED regions:
- the holes: `todo!()`, `unimplemented!()`, `arbitrary()`;
- escape hatches: `assume(...)`, `admit()`, `assume_specification`, `axiom`, `unsafe`, `#[verifier::external_body]`, `#[verifier::external]`, `#[verifier::external_fn_specification]` and the other external-specification attributes, `#[verifier::assume_termination]`, `#[verifier::exec_allows_no_decreases_clause]`;
- any `#[verifier::...]` attribute other than these, none of which weakens checking: `opaque`, `rlimit`, `spinoff_prover`, `nonlinear`, `bit_vector`, `integer_ring`, `loop_isolation`, `auto_ext_equal`, `ext_equal`, `inline`, `memoize`, `truncate`, `type_invariant`, `when_used_as_spec`, `allow_in_spec`, `accept_recursive_types`, `reject_recursive_types`, `reject_recursive_types_in_ground_variants`, `no_auto_trigger`, `decreases_by`, `opaque_outside_module`, `prophetic`;
- anything that could stop a FIXED item from being checked, or change what it means: code outside the `verus!` block, a second `verus!` block, `#[cfg(...)]`, `cfg!`, `#[cfg_attr(...)]`, `#[path]`, `#[verus...]` attributes, inner attributes (`#![...]`) other than the `#![trigger ...]` and `#![auto]` of quantifiers, `macro_rules!`, `include!`, `extern crate`, out-of-line modules (`mod m;`), block comments (`/* */`; use `//`), raw strings, and any string literal, macro argument or attribute argument that runs on into a FIXED region;
- library sorting and selection: any `.sort...(...)` method, `sort_by`, `sort_unstable`, `select_nth_unstable` (requirement A4);
- allocation and copying: `Vec`, `vec!`, `Box`, `clone`, `Clone`, `to_vec`, `to_owned`, `clone_from_slice`, `copy_from_slice`, `copy_within` (requirement A3);
- library collections: `std::collections`, `vstd::hash_map` and the like, and `vstd::contrib::exec_spec`;
- `std::process`.

To make sure the FIXED contract and definitions are the ones in force, `./grade.sh` appends a short *witness* to a copy of your file before verifying it: grader-owned code that calls `quicksort` and asserts Q1 and Q2 with its own copies of `sorted` and `perm`. The witness verifies whenever the FIXED items are intact; you do not need to do anything for it.

## 8. Checking your work

Run `./grade.sh` in this directory. It finds the pinned Verus by itself (from the nix store). It runs four checks, and runs all of them even when one fails:
1. every FIXED region is byte-identical to the skeleton's;
2. no hole or forbidden construct remains (it prints each one with its line number);
3. `verus --no-cheating` verifies your file with the witness appended. It verifies `target/graded_quicksort.rs`, a copy of `src/quicksort.rs` with the witness added at the end, so the line numbers in error messages are those of your file;
4. `verus --no-verify --compile` compiles your file, and the binary runs the tests. The tests run even when verification fails, so you can test your code before its proofs are done.

Its last line is the verdict: `GRADE: PASS (...)` or `GRADE: FAIL (<reasons>; ...)`, with the number of non-blank lines outside the FIXED regions.

While you work, you can run Verus directly for faster feedback. `nix develop` in this directory gives a shell with `verus` (version 0.2026.09.27.3cf1832, pinned by `flake.nix`) on the path. `verus src/quicksort.rs` verifies the file, `verus src/quicksort.rs --verify-root --verify-function <name>` verifies one function, and `--expand-errors` explains a failing postcondition in more detail. The grader uses `--no-cheating`.

The grade of record is taken by running a pristine copy of `grade.sh`, with the pristine skeleton, on your `src/quicksort.rs` alone (the file listed in `SOLUTION_FILES`). Changes to any other file do not count.

## 9. What counts as done

Your solution is complete when both hold:
1. `./grade.sh` passes (its last line starts `GRADE: PASS`);
2. a human reader confirms that the code is the required algorithm (A1 to A4 in section 5) and that it does not game the grader: the only changes to the skeleton are the hole filled in and helper items added.

## 10. Documentation

This directory has no network access. The documentation is in `docs/` (see `docs/README.md`):
- `docs/verus-guide/`: the Verus guide, as markdown; start from `SUMMARY.md`. Mutable references, `old` and `final` are in `mutable-references.md`.
- `docs/vstd/`: the source of `vstd`, Verus's standard library, with the specifications of slices under `std_specs/slice.rs`.
