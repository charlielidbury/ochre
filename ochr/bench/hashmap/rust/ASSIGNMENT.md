# Assignment: a fixed-capacity hash map in Rust

## Overview

Implement a hash map from 64-bit keys to values of any type `V`, with a fixed number of buckets and separate chaining, operating in place. `V` has no trait bounds: the code may not compare, hash, order, clone or default values, only move them and hand out references to them. The representation and the public API are given; you write the bodies of the six operations. This assignment asks for a working, tested implementation only: there is nothing to prove.

Everything you need is in this directory. Read this file first, then `src/lib.rs`.

## What is provided

| File | What it is | May you edit it? |
|---|---|---|
| `src/lib.rs` | The skeleton: the representation, the `bucket_index` hash function and the six operation signatures, each with a `todo!()` body | Yes, outside the FIXED regions. It is the only file you may edit (it is listed in `SOLUTION_FILES`) |
| `tests/spec.rs` | The tests | No (FIXED file) |
| `Cargo.toml`, `Cargo.lock` | The crate: no dependencies | No (FIXED files) |
| `grade.sh`, `grade_scan.py`, `.grader/`, `SOLUTION_FILES` | The grader | No (the final grade uses an untouched copy) |
| `flake.nix`, `flake.lock` | The toolchain: Rust 1.95.0 (stable) and Python 3 | No |
| `docs/rust/` | Offline Rust documentation (HTML): the Book (`book/`), the standard library (`std/`), the Reference (`reference/`) | Read only |

A FIXED region runs from a comment containing the begin marker to the comment containing the matching end marker (look for `FIXED-` in `src/lib.rs`). Everything inside, the marker lines included, must stay byte-for-byte as it is. Outside the FIXED regions you may write anything that the rules below allow, including private helper functions and private methods. All your code must be in `src/lib.rs`: the final grade copies only that file into a fresh copy of this directory, so anything you put elsewhere is lost (and `grade.sh` rejects any other file under `src/`).

## What to build

### Representation (FIXED)

```rust
pub enum List<V> {                   // a bucket: a singly linked list of entries
    Cons(u64, V, Box<List<V>>),      // key, value, rest of the bucket
    Nil,
}

pub struct HashMap<V> {
    slots: Vec<List<V>>,             // the buckets; slots.len() is the capacity
    len: u64,                        // the number of keys in the map
}

pub fn bucket_index(key: u64, cap: usize) -> usize {
    (key % (cap as u64)) as usize
}
```

The capacity is chosen by `new` and never changes: there is no resizing. The bucket of key `k` is `slots[bucket_index(k, slots.len())]`, that is `k mod capacity`; `bucket_index` is provided and is the only hash function.

### Operations (FIXED signatures)

All are methods of `impl<V> HashMap<V>`.

| Operation | Meaning | Requires |
|---|---|---|
| `HashMap::new(cap: usize) -> HashMap<V>` | An empty map with `cap` empty buckets and `len = 0`. | `cap > 0` (you may panic otherwise) |
| `len(&self) -> u64` | The number of keys in the map. | |
| `get(&self, key: u64) -> Option<&V>` | A shared reference to the value `key` is bound to, or `None` if `key` is unbound. | |
| `insert(&mut self, key: u64, value: V) -> Option<V>` | Binds `key` to `value`; returns the value `key` was bound to before, moved out of the map, or `None`. | |
| `remove(&mut self, key: u64) -> Option<V>` | Unbinds `key`; returns the value it was bound to, moved out of the map, or `None`. | |
| `get_mut(&mut self, key: u64) -> &mut V` | A mutable borrow of the value stored for `key`. Writing `w` through it has the same effect as `insert(key, w)`. | `key` is present (you may panic otherwise) |

### Algorithm requirements

These are checked by a human reader, not by `grade.sh`:

- **A1 (hashing).** Every operation on key `k` reads or changes only the bucket `slots[bucket_index(k, slots.len())]` and the `len` field. No operation scans other buckets.
- **A2 (in place).** Operations change the map in place. No operation copies the table or a bucket, or rebuilds a bucket from a copy. A new entry may go at either end of its bucket, as you choose. `remove` unlinks the node.
- **A3 (nothing extra).** No auxiliary structure (a second table, a list of keys, a cache), no resizing, and no library map, set or association list.

## Tests

`tests/spec.rs` holds five tests, one per sequence of operations, all with values of type `u64` (`V := u64`; `get` is compared as `Some(&v)`). Each starts from `HashMap::new(cap)` and applies its operations in order to that one map, checking the result of every `get`, `insert` and `remove` and the value of `len()` after every operation; a `get_mut` step writes a value through the returned borrow.

- `scripted` (capacity 4): collisions (several keys in one bucket), overwriting with the previous value returned, removing a key at the head, middle and end of a bucket, removing an absent key, removing twice, writing through `get_mut` then reading with `get` (the same key and a neighbour in the same bucket), `insert` after `get_mut`, and re-inserting a removed key.
- `random_cap1`, `random_cap3`, `random_cap4`, `random_cap7`: 50 pseudo-random operations each, over a key space about three times the capacity. With capacity 1 every key shares one bucket.

## Rules

Forbidden in `src/lib.rs` (outside comments and string literals; the FIXED regions are exempt). `grade.sh` rejects:

- holes: `todo!`, `unimplemented!`;
- `unsafe`, `extern`, `asm!`, `global_asm!`, `transmute`, `include!`, `include_str!`, `include_bytes!`, `#[path = ...]`;
- conditional compilation: `cfg` and `cfg_attr` (as in `#[cfg(...)]` and `cfg!`);
- library collections: anything from `std::collections` (the word `collections`), `HashSet`, `BTreeMap`, `BTreeSet`, `LinkedList`, `VecDeque`, `BinaryHeap`;
- shared ownership and interior mutability: `Rc`, `Arc`, `Cell`, `RefCell`, `UnsafeCell`, `OnceCell`, `Mutex`, `RwLock`;
- copying: `Clone` (no `Clone` impls or derives), `clone`, `cloned`, `to_owned`, `to_vec`.

The check works on words, so do not reuse these names for your own items. Also forbidden: any crate dependency (`Cargo.toml` and `Cargo.lock` are FIXED), a `build.rs`, a `.cargo/` directory and a `rust-toolchain` file.

`std::mem::replace`, `std::mem::take`, `std::mem::swap`, `Box`, `Vec` (for the slots) and `Option` are all allowed.

## How to check your work

```sh
nix develop -c ./grade.sh
```

(`./grade.sh` alone also works when `cargo` is on your `PATH`.) It checks, in order: no holes and no forbidden constructs; every FIXED region and FIXED file unchanged; `cargo build` succeeds (offline); all five tests in `tests/spec.rs` pass. It prints what it found and ends with one line:

```
GRADE: PASS rust/hashmap; ...
```

or `GRADE: FAIL rust/hashmap: <reasons>; ...`. It exits 0 exactly when the verdict is PASS. You can also run the tests directly with `cargo test --offline --test spec`.

## What counts as done

Your work is done when `./grade.sh` prints `GRADE: PASS` and your code meets the algorithm requirements A1–A3. The final grade copies your `src/lib.rs` into a fresh, untouched copy of this directory and runs its `grade.sh` there.
