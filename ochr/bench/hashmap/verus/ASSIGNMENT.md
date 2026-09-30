# Assignment: a verified in-place hash map in Verus

## 1. The task

Implement a fixed-capacity hash map with separate chaining in Rust, and prove it correct with [Verus](docs/verus-guide/SUMMARY.md). The map stores `u64` values under `u64` keys. It has a fixed number of buckets, chosen when it is created, and each bucket is a singly linked list of entries. Every operation works in place.

All your work goes in one file, `src/hashmap.rs`. It already contains the skeleton: the types, the function signatures with their specifications, and the tests. Your job is to fill in the holes so that the file verifies, compiles and passes the tests.

You are done when `./grade.sh` prints a last line starting with `GRADE: PASS` (section 8).

## 2. What is provided (FIXED)

The parts of `src/hashmap.rs` between a `// FIXED-BEGIN <id>` line and the matching `// FIXED-END <id>` line are FIXED. You must not change them in any way, not even whitespace. They are:

- **The representation.** `List`, a bucket: `Nil`, or `Cons(key, value, next)` with the next node in a `Box`. `HashMap`, the map: `slots`, a `Vec<List>` of buckets, and `len`, a `u64` counter.
- **The hash function.** `bucket_index(key, cap)` is `key % cap`, with its proof. The bucket of key `k` is `slots[bucket_index(k, slots.len())]`.
- **The operations**, as signatures with their `requires`/`ensures` contracts (section 4): `new`, `len`, `get`, `insert`, `remove` and `get_mut`.
- **The signatures of three spec functions** whose bodies you write: `inv`, `spec_get` and `spec_len` (section 3).
- **The tests** (section 6), after the `verus!` block.

## 3. What you write (the holes)

- The body of `inv(&self) -> bool`: the representation invariant `Inv`. You choose it; it can be anything that makes the contracts provable.
- The body of `spec_get(&self, key) -> Option<u64>`: what `get` returns, as a spec function.
- The body of `spec_len(&self) -> nat`: what `len` returns, as a spec function.
- The bodies of the six executable functions `new`, `len`, `get`, `insert`, `remove` and `get_mut`.
- Anything else you need: spec functions, proof functions (lemmas), private executable helpers, loop invariants, `decreases` clauses and `proof { ... }` blocks.

Each spec-function hole is currently `arbitrary()` and each executable hole is `todo!()`. Verus reports every `todo!()` as `precondition not satisfied`, because a panic's precondition is `false`.

Why `spec_get` and `spec_len` exist: a Verus specification cannot call an executable function, so the properties cannot mention `get` and `len` directly. Instead they mention `spec_get` and `spec_len`, and the FIXED contracts of `get` and `len` say that the executable functions return exactly `spec_get` and `spec_len`. So every property below is a property of what the real `get` and `len` return. You are free to define `spec_get` and `spec_len` however you like, directly on the buckets or through a model (a `Map<u64, u64>` view, say).

**Where you may add code.** Anywhere inside the `verus! { ... }` block that is outside the FIXED regions: new items before or after the FIXED ones, and attributes on a line directly before a `// FIXED-BEGIN` line (they then apply to that item, for example `#[verifier::rlimit(20)]`). A `decreases` clause may go between a `// FIXED-END` line and the function body. Do not put code outside the `verus!` block, and do not wrap FIXED items in modules or other items: the grader refers to them by name.

## 4. The required properties

The properties are numbered as in the system-neutral specification of this assignment (H1 to H18). In the contracts, for a method taking `&mut self`, `old(self)` is the map when the call starts, `final(self)` is the map when the call ends, and for `get_mut`, `*final(r)` is the value the caller leaves behind the returned borrow `r` (see `docs/verus-guide/mutable-references.md`).

| Id | Property | Where |
|---|---|---|
| H1 | `new(c)` satisfies `inv` | `new`: `m.inv()` |
| H2 | `insert` preserves `inv` | `insert`: `final(self).inv()` |
| H3 | `remove` preserves `inv` | `remove`: `final(self).inv()` |
| H4 | every key is absent from `new(c)` | `new`: `forall\|k\| m.spec_get(k) == None` |
| H5 | after `insert(k, v)`, `k` maps to `v` | `insert`: `final(self).spec_get(key) == Some(value)` |
| H6 | `insert(k, v)` leaves every other key unchanged | `insert`: `forall\|k2\| k2 != key ==> ...` |
| H7 | `insert` returns the old value of `k` | `insert`: `r == old(self).spec_get(key)` |
| H8 | after `remove(k)`, `k` is absent | `remove`: `final(self).spec_get(key) == None` |
| H9 | `remove(k)` leaves every other key unchanged | `remove`: `forall\|k2\| k2 != key ==> ...` |
| H10 | `remove` returns the old value of `k` | `remove`: `r == old(self).spec_get(key)` |
| H11 | `len(new(c)) = 0` | `new`: `m.spec_len() == 0` |
| H12 | `insert` adds 1 to `len` iff the key was absent | `insert`: the `spec_len` clause |
| H13 | `remove` takes 1 from `len` iff the key was present | `remove`: the `spec_len` clause |
| H14 | writing `w` through `get_mut(k)` makes `k` map to `w` and leaves other keys unchanged (as `insert(k, w)` would) | `get_mut`: the two `spec_get` clauses |
| H15 | ... and leaves `len` unchanged (as `insert(k, w)` would, `k` being present) | `get_mut`: the `spec_len` clause |
| H16 | ... and preserves `inv` | `get_mut`: `final(self).inv()` |

The ties between the spec functions and the code are `len`: `n == self.spec_len()` and `get`: `r == self.spec_get(key)`.

Points to note:
- `get` and `len` take `&self`, so Rust's type system already guarantees that they leave the map unchanged. (In the neutral specification these are H17 and H18; here they need no proof.)
- Every operation except `new` requires `inv`. Verus proves that code cannot panic, so `get` must know that the capacity is non-zero before it computes `key % cap`, and only the invariant can tell it. Every property above is stated for maps satisfying the invariant, so this loses nothing.
- `insert` requires `spec_len() < u64::MAX`, so that the `u64` counter `len` cannot overflow. This is the one extra hypothesis the specification allows for bounded integers.
- Verus checks total correctness: no panics, no arithmetic overflow, every index in bounds, and every loop and recursive function terminates (it needs a `decreases` clause).
- `get_mut` requires the key to be present, because a borrow cannot be returned inside an `Option` in every system this assignment is posed in.

## 5. The algorithm

A human reader checks these requirements; the grader does not.

- **A1 (hashing).** Every operation on key `k` reads or changes only the bucket `slots[bucket_index(k, cap)]` and the `len` field. No operation scans other buckets.
- **A2 (in place).** Operations change the map in place. No operation copies the table or a bucket, or rebuilds a bucket from a copy. A new entry may go at either end of its bucket, at your choice. `remove` unlinks the node.
- **A3 (nothing extra).** No auxiliary structure (a second table, a list of keys, a cache), no resizing, and no library map, set or association list. `new(cap)` makes exactly `cap` buckets, and the number never changes.

## 6. The tests

The FIXED `tests` region, after the `verus!` block, holds the tests. They are plain Rust (not verified), and they run in the binary that `./grade.sh` compiles. There are five sequences of operations, each starting from `HashMap::new(cap)`:
- `scripted`, on capacity 4: collisions (several keys in one bucket), overwriting with the previous value returned, removing a key at the head, middle and end of a bucket, removing an absent key, removing twice, writing through `get_mut` then reading with `get` (the same key and a neighbour in the same bucket), `insert` after `get_mut`, and re-inserting a removed key;
- `random-cap1`, `random-cap3`, `random-cap4` and `random-cap7`: 50 pseudo-random operations each, on capacities 1, 3, 4 and 7.

After every operation the test checks the result (for `get`, `insert` and `remove`) and then `len`, 474 checks in all.

## 7. Allowed and forbidden

You may use anything in `vstd` in specifications and proofs, including `Seq`, `Map`, `Set` and `Multiset`, and the `Vec` and `Option` operations Verus supports in executable code.

`./grade.sh` rejects any of the following outside the FIXED regions:
- the holes: `todo!()`, `unimplemented!()`, `arbitrary()`;
- escape hatches: `assume(...)`, `admit()`, `assume_specification`, `axiom`, `unsafe`, `#[verifier::external_body]`, `#[verifier::external]`, `#[verifier::external_fn_specification]` and the other external-specification attributes, `#[verifier::assume_termination]`, `#[verifier::exec_allows_no_decreases_clause]`;
- any `#[verifier::...]` attribute other than these, none of which weakens checking: `opaque`, `rlimit`, `spinoff_prover`, `nonlinear`, `bit_vector`, `integer_ring`, `loop_isolation`, `auto_ext_equal`, `ext_equal`, `inline`, `memoize`, `truncate`, `type_invariant`, `when_used_as_spec`, `allow_in_spec`, `accept_recursive_types`, `reject_recursive_types`, `reject_recursive_types_in_ground_variants`, `no_auto_trigger`, `decreases_by`, `opaque_outside_module`, `prophetic`;
- anything that could stop a FIXED item from being checked, or change what it means: code outside the `verus!` block, a second `verus!` block, `#[cfg(...)]`, `cfg!`, `#[cfg_attr(...)]`, `#[path]`, `#[verus...]` attributes, inner attributes (`#![...]`) other than the `#![trigger ...]` and `#![auto]` of quantifiers, `macro_rules!`, `include!`, `extern crate`, out-of-line modules (`mod m;`), block comments (`/* */`; use `//`), raw strings, and any string literal, macro argument or attribute argument that runs on into a FIXED region;
- library maps and sets in any form: `std::collections` (`HashMap`, `HashSet`, `BTreeMap`, `BTreeSet`, `VecDeque`), `vstd::hash_map`, `vstd::hash_set`, `HashMapWithView` and the like, and `vstd::contrib::exec_spec`;
- copying: `clone`, `Clone`, `to_vec`, `to_owned` (requirement A2);
- `std::process`.

To make sure the FIXED contracts are the ones in force, `./grade.sh` appends a short *witness* to a copy of your file before verifying it: grader-owned functions that call each FIXED function and assert its FIXED postconditions. The witness verifies whenever the FIXED items are intact; you do not need to do anything for it.

## 8. Checking your work

Run `./grade.sh` in this directory. It finds the pinned Verus by itself (from the nix store). It runs four checks, and runs all of them even when one fails:
1. every FIXED region is byte-identical to the skeleton's;
2. no hole or forbidden construct remains (it prints each one with its line number);
3. `verus --no-cheating` verifies your file with the witness appended. It verifies `target/graded_hashmap.rs`, a copy of `src/hashmap.rs` with the witness added at the end, so the line numbers in error messages are those of your file;
4. `verus --no-verify --compile` compiles your file, and the binary runs the tests. The tests run even when verification fails, so you can test your code before its proofs are done.

Its last line is the verdict: `GRADE: PASS (...)` or `GRADE: FAIL (<reasons>; ...)`, with the number of non-blank lines outside the FIXED regions.

While you work, you can run Verus directly for faster feedback. `nix develop` in this directory gives a shell with `verus` (version 0.2026.09.27.3cf1832, pinned by `flake.nix`) on the path. `verus src/hashmap.rs` verifies the file, `verus src/hashmap.rs --verify-root --verify-function <name>` verifies one function, and `--expand-errors` explains a failing postcondition in more detail. The grader uses `--no-cheating`.

The grade of record is taken by running a pristine copy of `grade.sh`, with the pristine skeleton, on your `src/hashmap.rs` alone (the file listed in `SOLUTION_FILES`). Changes to any other file do not count.

## 9. What counts as done

Your solution is complete when both hold:
1. `./grade.sh` passes (its last line starts `GRADE: PASS`);
2. a human reader confirms that the code is the required algorithm (A1 to A3 in section 5) and that it does not game the grader: the only changes to the skeleton are the holes filled in and helper items added.

## 10. Documentation

This directory has no network access. The documentation is in `docs/` (see `docs/README.md`):
- `docs/verus-guide/`: the Verus guide, as markdown; start from `SUMMARY.md`. Mutable references, `old` and `final` are in `mutable-references.md`.
- `docs/vstd/`: the source of `vstd`, Verus's standard library, with the specifications of `Vec`, `Option`, `Box` and slices under `std_specs/`.
