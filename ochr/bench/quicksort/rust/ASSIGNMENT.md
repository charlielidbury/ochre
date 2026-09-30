# Assignment: in-place quicksort in Rust

## Overview

Implement quicksort on a mutable slice of 64-bit words, in place, with the two recursive calls made on two disjoint borrowed sub-slices. The public signature is given; you write the body and any helpers. This assignment asks for a working, tested implementation only: there is nothing to prove.

Everything you need is in this directory. Read this file first, then `src/lib.rs`.

## What is provided

| File | What it is | May you edit it? |
|---|---|---|
| `src/lib.rs` | The skeleton: the signature of `quicksort`, with a `todo!()` body | Yes, outside the FIXED region. It is the only file you may edit (it is listed in `SOLUTION_FILES`) |
| `tests/spec.rs` | The tests | No (FIXED file) |
| `Cargo.toml`, `Cargo.lock` | The crate: no dependencies | No (FIXED files) |
| `grade.sh`, `grade_scan.py`, `.grader/`, `SOLUTION_FILES` | The grader | No (the final grade uses an untouched copy) |
| `flake.nix`, `flake.lock` | The toolchain: Rust 1.95.0 (stable) and Python 3 | No |
| `docs/rust/` | Offline Rust documentation (HTML): the Book (`book/`), the standard library (`std/`), the Reference (`reference/`) | Read only |

A FIXED region runs from a comment containing the begin marker to the comment containing the matching end marker (look for `FIXED-` in `src/lib.rs`). Everything inside, the marker lines included, must stay byte-for-byte as it is. Outside it you may write anything that the rules below allow, including private helper functions (the partition, for example). All your code must be in `src/lib.rs`: the final grade copies only that file into a fresh copy of this directory, so anything you put elsewhere is lost (and `grade.sh` rejects any other file under `src/`).

## What to build

### Operation (FIXED signature)

```rust
pub fn quicksort(a: &mut [u64])
```

It sorts `a` in place into ascending order and returns nothing.

### Algorithm requirements

These are checked by a human reader, not by `grade.sh`:

- **A1 (partition).** Choose a pivot and partition the range with the Lomuto or the Hoare scheme. Say which in a comment at your partition function.
- **A2 (two disjoint recursive calls).** After partitioning, split the slice into two disjoint sub-slices that are borrowed separately (for example with `split_at_mut`) and sort each with a recursive call. The pivot's final position, if the scheme has one, belongs to neither.
- **A3 (in place).** No copy of the slice or of a sub-slice (no copy out and copy back, no temporary array). Auxiliary space is O(1) beyond the recursion.
- **A4 (nothing extra).** No library sort, selection or permutation routine, and no other sorting algorithm as a fallback (for example insertion sort on small ranges).

## Tests

`tests/spec.rs` holds 29 tests. Each sorts one input array in place and checks that it then equals the expected output:

- hand-picked cases: empty, one element, two elements in each order, duplicates, already sorted, reverse-sorted, all equal, and a short mixed array with repeated pivot values;
- 20 pseudo-random arrays of lengths 0 to 24, with values up to 99, some drawn from 0–3 so that duplicates are frequent.

## Rules

Forbidden in `src/lib.rs` (outside comments and string literals; the FIXED region is exempt). `grade.sh` rejects:

- holes: `todo!`, `unimplemented!`;
- `unsafe`, `extern`, `asm!`, `global_asm!`, `transmute`, `include!`, `include_str!`, `include_bytes!`, `#[path = ...]`;
- conditional compilation: `cfg` and `cfg_attr` (as in `#[cfg(...)]` and `cfg!`);
- heap allocation and building collections: `Vec`, `vec!`, `Box`, `String`, `alloc`, `collect`, `concat`, `join`, and anything from `std::collections` (the word `collections`), `HashSet`, `BTreeMap`, `BTreeSet`, `LinkedList`, `VecDeque`, `BinaryHeap`;
- copying: `Clone`, `clone`, `cloned`, `to_owned`, `to_vec`, `copy_from_slice`, `clone_from_slice`, `copy_within`;
- library sorts, selections, searches and permutations: `sort`, `sort_unstable`, `sort_by`, `sort_by_key`, `sort_unstable_by`, `sort_unstable_by_key`, `sort_by_cached_key`, `select_nth_unstable` (and its `_by`/`_by_key` forms), `partition_point`, `partition_dedup` (and its forms), `partition_in_place`, `binary_search` (and its forms), `reverse`, `rotate_left`, `rotate_right`, `swap_with_slice`;
- shared ownership and interior mutability: `Rc`, `Arc`, `Cell`, `RefCell`, `UnsafeCell`, `OnceCell`, `Mutex`, `RwLock`.

The check works on words, so do not reuse these names for your own items (call a helper `sort_range`, not `sort`). Also forbidden: any crate dependency (`Cargo.toml` and `Cargo.lock` are FIXED), a `build.rs`, a `.cargo/` directory and a `rust-toolchain` file.

Slice indexing, `len`, `swap(i, j)` on a slice, `split_at_mut` and range sub-slicing (`&mut a[i..j]`) are all allowed.

## How to check your work

```sh
nix develop -c ./grade.sh
```

(`./grade.sh` alone also works when `cargo` is on your `PATH`.) It checks, in order: no holes and no forbidden constructs; the FIXED region and the FIXED files unchanged; `cargo build` succeeds (offline); all 29 tests in `tests/spec.rs` pass. It prints what it found and ends with one line:

```
GRADE: PASS rust/quicksort; ...
```

or `GRADE: FAIL rust/quicksort: <reasons>; ...`. It exits 0 exactly when the verdict is PASS. You can also run the tests directly with `cargo test --offline --test spec`.

## What counts as done

Your work is done when `./grade.sh` prints `GRADE: PASS` and your code meets the algorithm requirements A1–A4. The final grade copies your `src/lib.rs` into a fresh, untouched copy of this directory and runs its `grade.sh` there.
