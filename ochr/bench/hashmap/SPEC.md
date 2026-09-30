# Hashmap: the system-neutral assignment

This is the one specification that every hashmap package transcribes. Each package's `ASSIGNMENT.md` restates it in the package's own notation and cites the property numbers used here (H1, H2, …). The only system-specific part of this file is the correspondence table at the end, where each package records which declaration states each property.

The task: implement a fixed-capacity hash map with separate chaining, operating in place, and prove that it behaves like a finite map, as observed through `get` and `len`.

## 1. Values

- 𝕎 = {0, 1, …, 2⁶⁴ − 1}, the unsigned machine words (Rust `u64`, Ochr `Word`). Keys and values are both words.
- Opt(𝕎) = {None} ∪ {Some(w) | w ∈ 𝕎}.
- Arithmetic inside the properties (`len(m) + 1`, `len(m) − 1`) is ordinary arithmetic on ℕ. The implementation's `len` counter is a word; see the bounded-integer allowance in §5.

Ochr's `Word` is unbounded, so in Ochr 𝕎 is all of ℕ and no overflow can occur. This is a known difference and is recorded in the protocol (`../README.md`), not compensated for.

## 2. Representation (FIXED)

A map `m` with capacity `c` (where `c ≥ 1`) is a record of two parts:

- `slots`: an array of exactly `c` buckets. The capacity is chosen by `new` and never changes afterwards: there is no resize. A system may carry `c` in the type (for example `Array(Bucket, c)`) or read it back as the length of the array, but it is not a separate mutable field.
- `len`: a word.

A bucket is a singly linked list of entries, each node owned by the previous one (in Rust, `Box`):

    Bucket ::= Nil | Cons(key : 𝕎, value : 𝕎, next : Bucket)

The bucket of key `k` is `slots[idx(k)]`, where

    idx(k) = k mod c.

`idx` is FIXED and provided in every package. It is the only hash function.

## 3. Operations (FIXED signatures)

`&mut` marks an argument that the operation changes in place.

| Operation | Signature | Precondition |
|---|---|---|
| new | `new(c : 𝕎) → Map` | `c ≥ 1` |
| len | `len(m : Map) → 𝕎` | |
| get | `get(m : Map, k : 𝕎) → Opt(𝕎)` | |
| insert | `insert(m : &mut Map, k : 𝕎, v : 𝕎) → Opt(𝕎)` | see §5 for bounded integers |
| remove | `remove(m : &mut Map, k : 𝕎) → Opt(𝕎)` | |
| get_mut | `get_mut(m : &mut Map, k : 𝕎) → &mut 𝕎` | `get(m, k) ≠ None` |

What they mean, informally (§5 is the formal statement):
- `new(c)` is an empty map with `c` empty buckets and `len = 0`.
- `len(m)` is the number of keys in the map.
- `get(m, k)` is `Some(v)` if `k` is bound to `v`, and `None` otherwise.
- `insert(m, k, v)` binds `k` to `v` and returns the value `k` was bound to before, or `None`.
- `remove(m, k)` unbinds `k` and returns the value it was bound to, or `None`.
- `get_mut(m, k)` returns a mutable borrow of the value stored for `k`. It requires `k` to be present because not every system can return a borrow inside an `Option` (Ochr cannot).

In systems whose type system allows `get` and `len` to change the map (Ochr, which has only mutable borrows), `get` and `len` take the map by borrow. Properties H17 and H18 say they leave it unchanged.

A system without borrows (`lean`) expresses `get_mut` in its most direct functional form: a function that takes `m`, `k` and `w` and returns the map with `w` written into `k`'s entry, found by the same walk down `k`'s bucket that `get_mut` does. H14–H16 are then stated about that function, and the correspondence table says so.

## 4. Algorithm requirements (checked by a human reader, not by the grader)

- **A1 (hashing).** Every operation on key `k` reads or changes only the bucket `slots[idx(k)]` and the `len` field. No operation scans other buckets.
- **A2 (in place).** Operations change the map in place. No operation copies the table or a bucket, or rebuilds a bucket from a copy. A new entry may go at either end of its bucket, at the implementer's choice. `remove` unlinks the node.
- **A3 (nothing extra).** No auxiliary structure (a second table, a list of keys, a cache), no resizing, and no library map, set or association list.

The `lean` condition has no memory model: there, A2 means the table array is updated with the operations that are in place when the array is unshared (`Array.set`, `Array.modify` and similar), and buckets are immutable lists by nature.

## 5. Properties

The solver defines a predicate `Inv(m)` on maps. It is a hole in every verified package, and may be any predicate that makes the properties below provable. Every property is universally quantified over capacities `c ≥ 1`, maps `m`, keys `k`, `k′`, and words `v`, `w`.

Notation. For a mutating operation, `op(m, …) ⇝ (m′, r)` means: running `op` in place on `m` leaves the map `m′` and returns `r`. For `get_mut`, `m[k ≔ w]` is the map after running `*get_mut(&mut m, k) = w` (write `w` through the returned borrow) and letting the borrow end.

**Invariant.**
- **H1.** `Inv(new(c))`.
- **H2.** `Inv(m) ∧ insert(m, k, v) ⇝ (m′, r)  ⟹  Inv(m′)`.
- **H3.** `Inv(m) ∧ remove(m, k) ⇝ (m′, r)  ⟹  Inv(m′)`.

(The invariant after `get_mut` is H16.)

**Lookup after each operation.**
- **H4.** `get(new(c), k) = None`.
- **H5.** `Inv(m) ∧ insert(m, k, v) ⇝ (m′, r)  ⟹  get(m′, k) = Some(v)`.
- **H6.** `Inv(m) ∧ k′ ≠ k ∧ insert(m, k, v) ⇝ (m′, r)  ⟹  get(m′, k′) = get(m, k′)`.
- **H7.** `Inv(m) ∧ insert(m, k, v) ⇝ (m′, r)  ⟹  r = get(m, k)`.
- **H8.** `Inv(m) ∧ remove(m, k) ⇝ (m′, r)  ⟹  get(m′, k) = None`.
- **H9.** `Inv(m) ∧ k′ ≠ k ∧ remove(m, k) ⇝ (m′, r)  ⟹  get(m′, k′) = get(m, k′)`.
- **H10.** `Inv(m) ∧ remove(m, k) ⇝ (m′, r)  ⟹  r = get(m, k)`.

**Length after each operation.**
- **H11.** `len(new(c)) = 0`.
- **H12.** `Inv(m) ∧ insert(m, k, v) ⇝ (m′, r)  ⟹  len(m′) = len(m) + 1` if `get(m, k) = None`, and `len(m′) = len(m)` otherwise.
- **H13.** `Inv(m) ∧ remove(m, k) ⇝ (m′, r)  ⟹  len(m′) = len(m) − 1` if `get(m, k) ≠ None`, and `len(m′) = len(m)` otherwise.

**Writing through `get_mut` is `insert`.** Assume `Inv(m)`, `get(m, k) ≠ None`, and `insert(m, k, w) ⇝ (m₂, r)`. Then:
- **H14.** `get(m[k ≔ w], k′) = get(m₂, k′)` for every key `k′`.
- **H15.** `len(m[k ≔ w]) = len(m₂)`.
- **H16.** `Inv(m[k ≔ w])`.

**Observers do not change the map.**
- **H17.** `get(m, k) ⇝ (m′, r)  ⟹  m′ = m` (equality of the representation).
- **H18.** `len(m) ⇝ (m′, r)  ⟹  m′ = m`.

H17 and H18 are stated only where the type system does not already guarantee them. Where `get` and `len` take the map by shared reference (Rust `&self`: `rust`, `aeneas`, `verus`) or are pure functions (`lean`), the package omits them and says so in its correspondence table.

**Bounded integers.** In a system whose `len` is a bounded machine word, the properties that run `insert` (H2, H5, H6, H7, H12, and H14–H16) may additionally assume `len(m) < 2⁶⁴ − 1`, and `insert` may require it. No other extra hypothesis is allowed.

## 6. Tests

`tests.json` holds the test vectors. Every package runs all of them, transcribed mechanically from the JSON (by a script, where practical).

The file holds a list of `sequences`. Each sequence starts from `new(cap)` and applies its `ops` in order to that one map. Each op is one object:

| `op` | fields | meaning |
|---|---|---|
| `"insert"` | `key`, `value`, `expect`, `len` | `insert(m, key, value)` returns `expect` |
| `"get"` | `key`, `expect`, `len` | `get(m, key)` returns `expect` |
| `"remove"` | `key`, `expect`, `len` | `remove(m, key)` returns `expect` |
| `"get_mut"` | `key`, `value`, `len` | write `value` through `get_mut(m, key)`; `key` is always present |

`expect` is `null` for None and a number `w` for `Some(w)`. `len` is the expected `len(m)` after the op. Some ops carry a `note` saying what they test; transcription may ignore it.

The sequences are:
- `scripted`: on `new(4)`, written by hand. It covers collisions (several keys in one bucket), overwriting with the previous value returned, removing a key at the head, middle and end of a bucket, removing an absent key, removing twice, writing through `get_mut` then reading with `get` (the same key and a neighbour in the same bucket), `insert` after `get_mut`, and re-inserting a removed key.
- `random-cap1`, `random-cap3`, `random-cap4`, `random-cap7`: 50 pseudo-random ops each (200 in total), from a fixed seed, over a key space about three times the capacity, so buckets hold several keys and overwrites and absent removals are common. With capacity 1 every key shares one bucket.

Keys are at most 23 and values at most 99, so that systems with unary numbers (Ochr) can run the tests. The expected results were computed by an independent oracle (Python's `dict`, in `_reference/gen_tests.py`), and the unverified Rust reference in `_reference/` passes all of them.

## 7. Correspondence table

Each package fills in its own table: for each property, the file and declaration that states it. Write "omitted: guaranteed by the type system" for H17 and H18 where that applies, and say how the statement differs from §5 where it does (for example, an extra bounded-integer hypothesis, or a statement on a copy of the map).

### ochr

| Id | File | Declaration | Notes |
|---|---|---|---|
| Representation, `idx` | | | |
| new, len, get, insert, remove, get_mut | | | |
| Inv | | | |
| H1 | | | |
| H2 | | | |
| H3 | | | |
| H4 | | | |
| H5 | | | |
| H6 | | | |
| H7 | | | |
| H8 | | | |
| H9 | | | |
| H10 | | | |
| H11 | | | |
| H12 | | | |
| H13 | | | |
| H14 | | | |
| H15 | | | |
| H16 | | | |
| H17 | | | |
| H18 | | | |

### ochr-2p

| Id | File | Declaration | Notes |
|---|---|---|---|
| Representation, `idx` | | | |
| new, len, get, insert, remove, get_mut | | | |
| Model and agreement | | | |
| Inv | | | |
| H1 | | | |
| H2 | | | |
| H3 | | | |
| H4 | | | |
| H5 | | | |
| H6 | | | |
| H7 | | | |
| H8 | | | |
| H9 | | | |
| H10 | | | |
| H11 | | | |
| H12 | | | |
| H13 | | | |
| H14 | | | |
| H15 | | | |
| H16 | | | |
| H17 | | | |
| H18 | | | |

### aeneas

| Id | File | Declaration | Notes |
|---|---|---|---|
| Representation, `idx` | | | |
| new, len, get, insert, remove, get_mut | | | |
| Inv | | | |
| H1 | | | |
| H2 | | | |
| H3 | | | |
| H4 | | | |
| H5 | | | |
| H6 | | | |
| H7 | | | |
| H8 | | | |
| H9 | | | |
| H10 | | | |
| H11 | | | |
| H12 | | | |
| H13 | | | |
| H14 | | | |
| H15 | | | |
| H16 | | | |
| H17 | | | |
| H18 | | | |

### verus

| Id | File | Declaration | Notes |
|---|---|---|---|
| Representation, `idx` | | | |
| new, len, get, insert, remove, get_mut | | | |
| Inv | | | |
| H1 | | | |
| H2 | | | |
| H3 | | | |
| H4 | | | |
| H5 | | | |
| H6 | | | |
| H7 | | | |
| H8 | | | |
| H9 | | | |
| H10 | | | |
| H11 | | | |
| H12 | | | |
| H13 | | | |
| H14 | | | |
| H15 | | | |
| H16 | | | |
| H17 | | | |
| H18 | | | |

### lean

| Id | File | Declaration | Notes |
|---|---|---|---|
| Representation, `idx` | | | |
| new, len, get, insert, remove, get_mut | | | |
| Inv | | | |
| H1 | | | |
| H2 | | | |
| H3 | | | |
| H4 | | | |
| H5 | | | |
| H6 | | | |
| H7 | | | |
| H8 | | | |
| H9 | | | |
| H10 | | | |
| H11 | | | |
| H12 | | | |
| H13 | | | |
| H14 | | | |
| H15 | | | |
| H16 | | | |
| H17 | | | |
| H18 | | | |

### rust

The `rust` condition has no properties. It implements the same representation and API and runs the same tests.

| Id | File | Declaration | Notes |
|---|---|---|---|
| Representation, `idx` | | | |
| new, len, get, insert, remove, get_mut | | | |
| Tests | | | |
