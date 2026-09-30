# Hashmap: the system-neutral assignment

This is the one specification that every hashmap package transcribes. Each package's `ASSIGNMENT.md` restates it in the package's own notation and cites the property numbers used here (H1, H2, …). The only system-specific part of this file is the correspondence table at the end, where each package records which declaration states each property.

The task: implement a fixed-capacity hash map from word keys to values of an arbitrary type `V`, with separate chaining, operating in place, and prove that it behaves like a finite map, as observed through `get` and `len`.

## 1. Keys and values

- 𝕎 = {0, 1, …, 2⁶⁴ − 1}, the unsigned machine words (Rust `u64`, Ochr `Word`). Keys are words.
- Values have an arbitrary type `V`, a type parameter of the map. The implementation and the proofs must work for every `V`: nothing may assume that values can be compared, hashed, ordered, cloned or given a default. In Rust, Verus and Aeneas, `V` has no trait bounds.
- Opt(X) = {None} ∪ {Some(x) | x ∈ X}.
- Arithmetic inside the properties (`len(m) + 1`, `len(m) − 1`) is ordinary arithmetic on ℕ. The implementation's `len` counter is a word; see the bounded-integer allowance in §5.

Ochr's `Word` is unbounded, so in Ochr 𝕎 is all of ℕ and no overflow can occur. This is a known difference and is recorded in the protocol (`../README.md`), not compensated for.

## 2. Representation (FIXED)

A map `m : Map(V)` with capacity `c` (where `c ≥ 1`) is a record of two parts:

- `slots`: an array of exactly `c` buckets. The capacity is chosen by `new` and never changes afterwards: there is no resize. A system may carry `c` in the type (for example `Array(Bucket(V), c)`) or read it back as the length of the array, but it is not a separate mutable field.
- `len`: a word.

A bucket is a singly linked list of entries, each node owned by the previous one (in Rust, `Box`):

    Bucket(V) ::= Nil | Cons(key : 𝕎, value : V, next : Bucket(V))

The bucket of key `k` is `slots[idx(k)]`, where

    idx(k) = k mod c.

`idx` is FIXED and provided in every package. It is the only hash function.

## 3. Operations (FIXED signatures)

`&mut` marks an argument that the operation changes in place, and `&` a shared, read-only borrow.

| Operation | Signature | Precondition |
|---|---|---|
| new | `new(c : 𝕎) → Map(V)` | `c ≥ 1` |
| len | `len(m : &Map(V)) → 𝕎` | |
| get | `get(m : &Map(V), k : 𝕎) → Opt(&V)`, or `→ Opt(V)` (see below) | |
| insert | `insert(m : &mut Map(V), k : 𝕎, v : V) → Opt(V)` | see §5 for bounded integers |
| remove | `remove(m : &mut Map(V), k : 𝕎) → Opt(V)` | |
| get_mut | `get_mut(m : &mut Map(V), k : 𝕎) → &mut V` | `get(m, k) ≠ None` |

What they mean, informally (§5 is the formal statement):
- `new(c)` is an empty map with `c` empty buckets and `len = 0`.
- `len(m)` is the number of keys in the map.
- `get(m, k)` gives the value `k` is bound to, or `None` if `k` is unbound.
- `insert(m, k, v)` binds `k` to `v` and returns the value `k` was bound to before, moved out of the map, or `None`.
- `remove(m, k)` unbinds `k` and returns the value it was bound to, moved out of the map, or `None`.
- `get_mut(m, k)` returns a mutable borrow of the value stored for `k`. It requires `k` to be present because not every system can return a borrow inside an `Option` (Ochr cannot).

**The form of `get`.** `get` returns the value at `k` in each system's natural read-only form:
- `rust`, `aeneas`, `verus`: a shared reference into the map, `get(m : &Map(V), k) → Option<&V>`. It is not `V: Clone` with a copy: Rust's `Clone` is an arbitrary user implementation, so nothing lets Aeneas or Verus prove that a generic `clone` returns an equal value, and `get`'s properties would become unprovable.
- `ochr`: by value, `get(m : &Map(V), k) → Opt(V)`, returning a copy made with Ochr's built-in `clone`, which is a real copy and runs no user code. Ochr has only mutable borrows, so the map is passed by `&` and H17 says `get` leaves it unchanged; the same holds for `len` and H18.
- `lean`: by value, as a pure function `get : Map V → 𝕎 → Option V`.

`get_mut` returns `&mut V` in Rust, Verus and Aeneas, and `&V` in Ochr, whose `&` is mutable. Ochr's `&V` for a type parameter `V` needs rule D66 (`&A` for every `A : Type₀`), which is not on `ochr-core` yet; until it lands, the Ochr packages keep their current form of `get_mut` and say so in their correspondence rows.

**The observed value.** In the properties, `get(m, k)` stands for the value it observes, an element of Opt(V): where `get` returns `Option<&V>`, the value the reference points to (in Aeneas's translation and in Verus's specifications, a shared reference already is its value). Equality on `V` is the logic's own equality.

A system without borrows (`lean`) expresses `get_mut` in its most direct functional form: a function that takes `m`, `k` and `w : V` and returns the map with `w` written into `k`'s entry, found by the same walk down `k`'s bucket that `get_mut` does. H14–H16 are then stated about that function, and the correspondence table says so.

## 4. Algorithm requirements (checked by a human reader, not by the grader)

- **A1 (hashing).** Every operation on key `k` reads or changes only the bucket `slots[idx(k)]` and the `len` field. No operation scans other buckets.
- **A2 (in place).** Operations change the map in place. No operation copies the table or a bucket, or rebuilds a bucket from a copy. A new entry may go at either end of its bucket, at the implementer's choice. `remove` unlinks the node. `get` copies nothing where it returns a reference; in Ochr it copies only the one value it returns.
- **A3 (nothing extra).** No auxiliary structure (a second table, a list of keys, a cache), no resizing, and no library map, set or association list.

The `lean` condition has no memory model: there, A2 means the table array is updated with the operations that are in place when the array is unshared (`Array.set`, `Array.modify` and similar), and buckets are immutable lists by nature.

## 5. Properties

The solver defines a predicate `Inv(m)` on maps. It is a hole in every verified package, and may be any predicate that makes the properties below provable. Every property is universally quantified over value types `V`, capacities `c ≥ 1`, maps `m : Map(V)`, keys `k`, `k′`, and values `v`, `w : V`. `get(m, k)` in a property is the observed value (§3).

Every property is total: the operations it runs return normally under their preconditions, that is, they terminate, do not panic and do not overflow. In a system where every function terminates and nothing can fail (Ochr, pure Lean) this is automatic. Where the system can express failure or divergence (Aeneas's `Result`, Verus's checks for panics, overflow and `decreases`), the FIXED statements include it, for example `insert m k v = ok (r, m′)` in Aeneas.

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

H17 and H18 are stated only where the type system does not already guarantee them. Where `get` and `len` take the map by shared reference (Rust `&self`: `rust`, `aeneas`, `verus`) or are pure functions (`lean`), the package omits them and says so in its correspondence table. Ochr states them, since its `get` and `len` take the map by mutable borrow.

**Bounded integers.** In a system whose `len` is a bounded machine word, the properties that run `insert` (H2, H5, H6, H7, H12, and H14–H16) may additionally assume `len(m) < 2⁶⁴ − 1`, and `insert` may require it. No other extra hypothesis is allowed.

## 6. Tests

`tests.json` holds the test vectors. Every package runs all of them, transcribed mechanically from the JSON (by a script, where practical). The tests instantiate the value type as words, `V := 𝕎` (`u64`, Ochr's `Word`), and compare the observed value of `get` (§3).

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
| Representation, `idx` | `ochr/HashMap.lean` | `Bucket`, `MapOf`, `Map`, `Idx`, `IdxLt` (region `header`, block `HashMapSpec`) | **Pending D66.** Values are `Word` for now: `Bucket := BNil | BCons(key : Word, value : Word, next : Bucket)`, `MapGet` returns an `Opt` of a `Word` (a copy) and `MapGetMut` a `&Word`. The generic `Bucket(V)`, with `get → Opt(V)` by `clone` and `get_mut → &V`, replaces it when D66 (`&A` for every `A : Type₀`) is on ochr-core, and `SlotMut` goes then. `Map(cap) = MapOf(Cells(Bucket, cap))`, i.e. `MkMap(slots : Array(Bucket, cap), len : Word)`: the capacity is in the type (a field cannot yet be `Array(Bucket, cap)` directly, so `MapOf` takes the array's model type as a parameter). `Idx(cap, k)` is `k mod cap` by counting; `IdxLt` its bound. Also provided: `Opt`, `IsSome`, `Grow`, `Shrink`, `EqDec` (key comparison with evidence), and `SlotMut`, a native borrow of bucket `i` (the library's `GetMut` at element type `Bucket`, since `&E` is not yet well formed for a type variable). |
| new, len, get, insert, remove, get_mut | `ochr/HashMap.lean` | `MapNew`, `MapLen`, `MapGet`, `MapInsert`, `MapRemove`, `MapGetMut` (regions `new` … `get_mut`) | Pending D66 (above): at `V` = `Word`. `MapNew (cap) (h : Lt(Zero, cap))`; the others take `m : &Map(cap)`, `MapLen` and `MapGet` too (no shared borrows). `MapGetMut` requires `h : IsSome(GetOf(cap, *m, k))`. `GetOf`, `LenOf` (provided) run `MapGet`, `MapLen` on a copy of a map value; the properties observe through them. |
| Inv | `ochr/HashMap.lean` | `Inv` (region `inv`) | A hole: `Inv (cap : Word) (m : Map(cap)) : Prop`. |
| H1 | `ochr/HashMap.lean` | `InvNew` (region `H1`) | `Inv(cap, MapNew(cap, h))`. |
| H2 | `ochr/HashMap.lean` | `InvInsert` (region `H2`) | `(let c = *m; MapInsert(cap, &c, k, v); Inv(cap, c))` under `hm : Inv(cap, *m)`: every mutating property runs the operation on a copy `c` of the map `*m` and observes `c`. |
| H3 | `ochr/HashMap.lean` | `InvRemove` (region `H3`) | Likewise for `MapRemove`. |
| H4 | `ochr/HashMap.lean` | `GetNew` (region `H4`) | `Eq Opt (GetOf(cap, MapNew(cap, h), k)) None`. |
| H5 | `ochr/HashMap.lean` | `GetInsertSame` (region `H5`) | `Eq Opt (let c = *m; MapInsert(cap, &c, k, v); GetOf(cap, c, k)) (Some(v))`. |
| H6 | `ochr/HashMap.lean` | `GetInsertOther` (region `H6`) | `k′ ≠ k` is `ne : Π(e : Eq Word k2 k). False`; the right side is `GetOf(cap, *m, k2)`, the map before. |
| H7 | `ochr/HashMap.lean` | `InsertReturnsGet` (region `H7`) | `Eq Opt (let c = *m; MapInsert(cap, &c, k, v)) (GetOf(cap, *m, k))`. |
| H8 | `ochr/HashMap.lean` | `GetRemoveSame` (region `H8`) | As H5, for `MapRemove`, `= None`. |
| H9 | `ochr/HashMap.lean` | `GetRemoveOther` (region `H9`) | As H6, for `MapRemove`. |
| H10 | `ochr/HashMap.lean` | `RemoveReturnsGet` (region `H10`) | As H7, for `MapRemove`. |
| H11 | `ochr/HashMap.lean` | `LenNew` (region `H11`) | `Eq Word (LenOf(cap, MapNew(cap, h))) Zero`. |
| H12 | `ochr/HashMap.lean` | `LenInsert` (region `H12`) | `Eq Word (let c = *m; MapInsert(cap, &c, k, v); LenOf(cap, c)) (Grow(GetOf(cap, *m, k), LenOf(cap, *m)))`, `Grow(g, l)` = `l + 1` if `g = None`, else `l`. No bound on `len`: `Word` is unbounded. |
| H13 | `ochr/HashMap.lean` | `LenRemove` (region `H13`) | `Shrink(g, l)` = `l − 1` (the library's truncated `Sub`) if `g ≠ None`, else `l`. |
| H14 | `ochr/HashMap.lean` | `GetMutGet` (region `H14`) | Compares `GetOf(cap, c, k2)` after `let r = MapGetMut(cap, &c, k, hk); *r := w` with `GetOf(cap, c, k2)` after `MapInsert(cap, &c, k, w)`, each on its own copy `c` of `*m`. |
| H15 | `ochr/HashMap.lean` | `GetMutLen` (region `H15`) | Likewise with `LenOf`. |
| H16 | `ochr/HashMap.lean` | `GetMutInv` (region `H16`) | `(let c = *m; let r = MapGetMut(cap, &c, k, hk); *r := w; Inv(cap, c))`, with `hk : IsSome(GetOf(cap, *m, k))`. |
| H17 | `ochr/HashMap.lean` | `GetUnchanged` (region `H17`) | Stated, since `MapGet` takes `&`: `Eq (Map(cap)) (let c = *m; MapGet(cap, &c, k); c) (*m)`, for every map (no `Inv`). |
| H18 | `ochr/HashMap.lean` | `LenUnchanged` (region `H18`) | Likewise with `MapLen`. |

### ochr-2p

| Id | File | Declaration | Notes |
|---|---|---|---|
| Representation, `idx` | `ochr-2p/HashMap.lean` | `Bucket`, `MapOf`, `Map`, `Idx`, `IdxLt` (region `header`, block `HashMapSpec`) | Pending D66, as `ochr`. As `ochr`, plus `SlotsOf` and `LenField`, a map value's buckets (as a view) and length field, for the abstraction. |
| new, len, get, insert, remove, get_mut | `ochr-2p/HashMap.lean` | `MapNew`, `MapLen`, `MapGet`, `MapInsert`, `MapRemove`, `MapGetMut` (regions `new` … `get_mut`) | Pending D66, as `ochr`. As `ochr`. |
| Model and agreement | `ochr-2p/HashMap.lean` | block `HashMapModel`: `MMap`, `MNew`, `MLen`, `MGet`, `MInsert`, `MRemove`, `MWrite`, `MInv`, `Abs`; `MGetNew` (M4), `MGetInsertSame` (M5), `MGetInsertOther` (M6), `MGetRemoveSame` (M8), `MGetRemoveOther` (M9), `MLenNew` (M11), `MLenInsert` (M12), `MLenRemove` (M13), `MWriteGet` (M14), `MWriteLen` (M15). Block `HashMapSolution`: `AbsInv`, `AbsNew`, `AgreeLen`, `AgreeGet`, `AgreeInsert`, `AgreeInsertResult`, `AgreeRemove`, `AgreeRemoveResult`, `AgreeWrite` | The model is the solver's pure finite map (no borrows, no assignment in its block; the grader checks), with a model invariant `MInv` (may be `⊤`); M4–M15 are H4–H15 about it (H7 and H10 have none: the agreement says `insert` and `remove` return `MGet` of the model before). `Abs(cap, s, len)` maps a map's buckets (a view) and length to the model; `AbsOf(cap, m)` applies it to a map value. The agreement holds under the concrete `Inv`, and `AbsInv : Inv(m) ⟹ MInv(AbsOf(m))`. H1–H3 and H16–H18 concern the in-place map only and remain the solver's, as in `ochr`. |
| Inv | `ochr-2p/HashMap.lean` | `Inv` (region `inv`) | A hole, as `ochr`: the invariant on maps, needed by the agreement. |
| H1 | `ochr-2p/HashMap.lean` | `InvNew` (region `H1`) | As `ochr`. |
| H2 | `ochr-2p/HashMap.lean` | `InvInsert` (region `H2`) | As `ochr`. |
| H3 | `ochr-2p/HashMap.lean` | `InvRemove` (region `H3`) | As `ochr`. |
| H4 | `ochr-2p/HashMap.lean` | `GetNew` (region `H4`) | The `ochr` statement, character for character; its proof is provided, an instance of `GetNewFrom` (block `HashMapCompose`, generic in the operations and the model, checked). |
| H5 | `ochr-2p/HashMap.lean` | `GetInsertSame` (region `H5`) | The `ochr` statement, character for character; its proof is provided, an instance of `GetInsertSameFrom` (block `HashMapCompose`, generic in the operations and the model, checked). |
| H6 | `ochr-2p/HashMap.lean` | `GetInsertOther` (region `H6`) | The `ochr` statement, character for character; its proof is provided, an instance of `GetInsertOtherFrom` (block `HashMapCompose`, generic in the operations and the model, checked). |
| H7 | `ochr-2p/HashMap.lean` | `InsertReturnsGet` (region `H7`) | The `ochr` statement, character for character; its proof is provided, an instance of `InsertReturnsGetFrom` (block `HashMapCompose`, generic in the operations and the model, checked). |
| H8 | `ochr-2p/HashMap.lean` | `GetRemoveSame` (region `H8`) | The `ochr` statement, character for character; its proof is provided, an instance of `GetRemoveSameFrom` (block `HashMapCompose`, generic in the operations and the model, checked). |
| H9 | `ochr-2p/HashMap.lean` | `GetRemoveOther` (region `H9`) | The `ochr` statement, character for character; its proof is provided, an instance of `GetRemoveOtherFrom` (block `HashMapCompose`, generic in the operations and the model, checked). |
| H10 | `ochr-2p/HashMap.lean` | `RemoveReturnsGet` (region `H10`) | The `ochr` statement, character for character; its proof is provided, an instance of `RemoveReturnsGetFrom` (block `HashMapCompose`, generic in the operations and the model, checked). |
| H11 | `ochr-2p/HashMap.lean` | `LenNew` (region `H11`) | The `ochr` statement, character for character; its proof is provided, an instance of `LenNewFrom` (block `HashMapCompose`, generic in the operations and the model, checked). |
| H12 | `ochr-2p/HashMap.lean` | `LenInsert` (region `H12`) | The `ochr` statement, character for character; its proof is provided, an instance of `LenInsertFrom` (block `HashMapCompose`, generic in the operations and the model, checked). |
| H13 | `ochr-2p/HashMap.lean` | `LenRemove` (region `H13`) | The `ochr` statement, character for character; its proof is provided, an instance of `LenRemoveFrom` (block `HashMapCompose`, generic in the operations and the model, checked). |
| H14 | `ochr-2p/HashMap.lean` | `GetMutGet` (region `H14`) | The `ochr` statement, character for character; its proof is provided, an instance of `GetMutGetFrom` (block `HashMapCompose`, generic in the operations and the model, checked). |
| H15 | `ochr-2p/HashMap.lean` | `GetMutLen` (region `H15`) | The `ochr` statement, character for character; its proof is provided, an instance of `GetMutLenFrom` (block `HashMapCompose`, generic in the operations and the model, checked). |
| H16 | `ochr-2p/HashMap.lean` | `GetMutInv` (region `H16`) | As `ochr`. |
| H17 | `ochr-2p/HashMap.lean` | `GetUnchanged` (region `H17`) | As `ochr`. |
| H18 | `ochr-2p/HashMap.lean` | `LenUnchanged` (region `H18`) | As `ochr`. |

### aeneas

| Id | File | Declaration | Notes |
|---|---|---|---|
| Representation, `idx` | `aeneas/rust/src/lib.rs` | `List`, `HashMap`, `bucket_index` (region `types`) | `List ::= Cons(u64, u64, Box<List>) \| Nil`; `HashMap { slots: Vec<List>, len: u64 }`, capacity = `slots.len()`; `bucket_index(key, cap) = (key % (cap as u64)) as usize`, body FIXED. The Lean models `hashmap.List` and `hashmap.HashMap` are generated by Aeneas (`aeneas/lean/Hashmap/Code/Types.lean`, regenerated by every `grade.sh`). |
| new, len, get, insert, remove, get_mut | `aeneas/rust/src/lib.rs` | `HashMap::new`, `len`, `get`, `insert`, `remove`, `get_mut` (regions of the same names) | `new(cap: usize)`: Aeneas's `usize` has a platform width of 32 or 64 bits, so a `u64` capacity would need an extra hypothesis `cap ≤ usize::MAX`. `get` and `len` take `&self`. `get_mut` returns `&mut u64` and panics on an absent key. The statements are about the generated models `HashMap.new`, `HashMap.impl.len` (Aeneas renames `len`, which clashes with the field's projection), `HashMap.get`, `HashMap.insert`, `HashMap.remove` and `HashMap.get_mut`: a `&mut self` operation returns the new map as the last component of its result, and `get_mut` returns `(x, back)`, with `m[k ≔ w]` = `back w`. |
| Inv | `aeneas/lean/Hashmap/Properties.lean` | `hashmap.Inv` (region `Inv`; body a hole) | `def Inv (m : HashMap) : Prop`. |
| H1 | `aeneas/lean/Hashmap/Properties.lean` | `H1_inv_new` | `HashMap.new c ⦃ m => Inv m ⦄` for `0 < c.val`. Every statement is total: `f x ⦃ r => P r ⦄` is Aeneas's total-correctness triple (the call returns `ok r`: it terminates, does not panic, does not overflow). |
| H2 | `aeneas/lean/Hashmap/Properties.lean` | `H2_inv_insert` | Assumes `Inv m` and `hlen : HashMap.impl.len m ⦃ n => n.val < U64.max ⦄`, the bounded-integer allowance, also assumed by H5–H7, H12, H14 and H15. |
| H3 | `aeneas/lean/Hashmap/Properties.lean` | `H3_inv_remove` |  |
| H4 | `aeneas/lean/Hashmap/Properties.lean` | `H4_get_new` | `HashMap.new c ⦃ m => ∀ k, HashMap.get m k = ok none ⦄`. |
| H5 | `aeneas/lean/Hashmap/Properties.lean` | `H5_get_insert_same` | `HashMap.insert m k v ⦃ r m' => HashMap.get m' k = ok (some v) ⦄`. |
| H6 | `aeneas/lean/Hashmap/Properties.lean` | `H6_get_insert_other` | `HashMap.get m' k' = HashMap.get m k'` for `k' ≠ k`, an equality of `Result`s (under `Inv`, `get` succeeds, by H7). |
| H7 | `aeneas/lean/Hashmap/Properties.lean` | `H7_insert_returns_old` | `HashMap.get m k = ok r`. |
| H8 | `aeneas/lean/Hashmap/Properties.lean` | `H8_get_remove_same` |  |
| H9 | `aeneas/lean/Hashmap/Properties.lean` | `H9_get_remove_other` |  |
| H10 | `aeneas/lean/Hashmap/Properties.lean` | `H10_remove_returns_old` | `HashMap.get m k = ok r`. |
| H11 | `aeneas/lean/Hashmap/Properties.lean` | `H11_len_new` | `HashMap.impl.len m = ok 0#u64`. |
| H12 | `aeneas/lean/Hashmap/Properties.lean` | `H12_len_insert` | `∃ n n' g, len m = ok n ∧ len m' = ok n' ∧ get m k = ok g ∧ (if g = none then n'.val = n.val + 1 else n'.val = n.val)`. |
| H13 | `aeneas/lean/Hashmap/Properties.lean` | `H13_len_remove` | The same shape, with `n'.val + 1 = n.val` when `g ≠ none` (no truncated subtraction). |
| H14 | `aeneas/lean/Hashmap/Properties.lean` | `H14_get_mut_get` | The precondition `get(m, k) ≠ None` is `hk : ∃ v, HashMap.get m k = ok (some v)`. Statement: `HashMap.get_mut m k ⦃ x back => HashMap.insert m k w ⦃ r m₂ => ∀ k', HashMap.get (back w) k' = HashMap.get m₂ k' ⦄ ⦄`. |
| H15 | `aeneas/lean/Hashmap/Properties.lean` | `H15_get_mut_len` | `HashMap.impl.len (back w) = HashMap.impl.len m₂`, inside the same two triples. |
| H16 | `aeneas/lean/Hashmap/Properties.lean` | `H16_get_mut_inv` | `HashMap.get_mut m k ⦃ x back => Inv (back w) ⦄`: stated without running `insert` and without `hlen`, so slightly stronger than §5. |
| H17 |  |  | Omitted: guaranteed by the type system. `get` takes `&self`, and its model `HashMap.get : HashMap → U64 → Result (Option U64)` returns no map. |
| H18 |  |  | Omitted: guaranteed by the type system. `len` takes `&self`, and its model `HashMap.impl.len : HashMap → Result U64` returns no map. |

### verus

| Id | File | Declaration | Notes |
|---|---|---|---|
| Representation, `idx` | `verus/src/hashmap.rs` | `List`, `HashMap`, `bucket_index` (region `types`) | `List ::= Cons(u64, u64, Box<List>) \| Nil`; `HashMap { slots: Vec<List>, len: u64 }`, capacity = `slots.len()`. `bucket_index(key, cap)` requires `cap > 0` and ensures `i == key % cap` (proved in the skeleton). |
| new, len, get, insert, remove, get_mut | `verus/src/hashmap.rs` | `HashMap::new`, `len`, `get`, `insert`, `remove`, `get_mut` (regions of the same names) | `new(cap: usize)`, since a `Vec`'s length is a `usize`. `get` and `len` take `&self`. Every operation except `new` requires `inv()`: Verus proves that nothing panics, `key % cap` needs `cap > 0`, and only `Inv` supplies it; every property is stated under `Inv` anyway. A Verus specification cannot call an executable function, so the FIXED contracts of `get` and `len` say they return `spec_get(key)` and `spec_len()`, two spec functions whose bodies are holes like `Inv`; every property is stated through them, and so holds of what the executable `get` and `len` return. |
| Inv | `verus/src/hashmap.rs` | `HashMap::inv` (region `inv`; body a hole) | `pub closed spec fn inv(&self) -> bool`. The holes `spec_get` and `spec_len` (regions `spec_get`, `spec_len`) are the solver's too. |
| H1 | `verus/src/hashmap.rs` | `new`: `m.inv()` |  |
| H2 | `verus/src/hashmap.rs` | `insert`: `final(self).inv()` | `insert` requires `old(self).spec_len() < u64::MAX` (the bounded-integer allowance), for all of H2, H5–H7 and H12. |
| H3 | `verus/src/hashmap.rs` | `remove`: `final(self).inv()` |  |
| H4 | `verus/src/hashmap.rs` | `new`: `forall\|k: u64\| m.spec_get(k) == None::<u64>` |  |
| H5 | `verus/src/hashmap.rs` | `insert`: `final(self).spec_get(key) == Some(value)` | `old(self)` is m, `final(self)` is m′, `r` is r. |
| H6 | `verus/src/hashmap.rs` | `insert`: `forall\|k2: u64\| k2 != key ==> final(self).spec_get(k2) == old(self).spec_get(k2)` |  |
| H7 | `verus/src/hashmap.rs` | `insert`: `r == old(self).spec_get(key)` |  |
| H8 | `verus/src/hashmap.rs` | `remove`: `final(self).spec_get(key) == None::<u64>` |  |
| H9 | `verus/src/hashmap.rs` | `remove`: `forall\|k2: u64\| k2 != key ==> final(self).spec_get(k2) == old(self).spec_get(k2)` |  |
| H10 | `verus/src/hashmap.rs` | `remove`: `r == old(self).spec_get(key)` |  |
| H11 | `verus/src/hashmap.rs` | `new`: `m.spec_len() == 0` |  |
| H12 | `verus/src/hashmap.rs` | `insert`: `final(self).spec_len() == if old(self).spec_get(key) is None { old(self).spec_len() + 1 } else { old(self).spec_len() }` | `spec_len` is a `nat`. |
| H13 | `verus/src/hashmap.rs` | `remove`: `final(self).spec_len() == if old(self).spec_get(key) is Some { old(self).spec_len() - 1 } else { old(self).spec_len() as int }` | Compared in `int`. |
| H14 | `verus/src/hashmap.rs` | `get_mut`: `final(self).spec_get(key) == Some(*final(r))` and `forall\|k2: u64\| k2 != key ==> final(self).spec_get(k2) == old(self).spec_get(k2)` | Stated in closed form with Verus's prophecy operator `final`: `*final(r)` is the w the caller leaves behind the borrow r, and `final(self)` is m[k ≔ w] once the borrow ends. The right-hand sides are what H5 and H6 give for insert(m, k, w). |
| H15 | `verus/src/hashmap.rs` | `get_mut`: `final(self).spec_len() == old(self).spec_len()` | Closed form: len(m₂) = len(m) by H12, since `get_mut` requires `k` present (`old(self).spec_get(key) is Some`). |
| H16 | `verus/src/hashmap.rs` | `get_mut`: `final(self).inv()` |  |
| H17 |  |  | omitted: guaranteed by the type system (`get(&self, key)`). |
| H18 |  |  | omitted: guaranteed by the type system (`len(&self)`). |

### lean

| Id | File | Declaration | Notes |
|---|---|---|---|
| Representation, `idx` | `lean/Solution.lean` | `Bench.Bucket`, `Bench.HashMap`, `Bench.HashMap.idx` (region `repr`) | `Bucket := List (UInt64 × UInt64)`, an immutable list; `slots : Array Bucket`, capacity `slots.size`; `len : UInt64`; `idx m k = k.toNat % m.slots.size`. `Check.lean` restates the structure and `idx`. |
| new, len, get, insert, remove, get_mut | `lean/Solution.lean` | `HashMap.new`, the field `HashMap.len`, `HashMap.get`, `HashMap.insert`, `HashMap.remove`, `HashMap.modify` | Pure functions: `insert` and `remove` return `(m′, r)`. `len` is the structure field, so it is not a hole. `get_mut` has no pure counterpart; its most direct functional form is `modify m k w`, the map with `w` written into `k`'s entry (§3), and H14–H16 are stated about it. Must be total: no `partial`, no panicking `!` operations. |
| Inv | `lean/Solution.lean` | `HashMap.Inv` (region `Inv`) | A hole: `def Inv (m : HashMap) : Prop := sorry`. |
| H1 | `lean/Solution.lean` | `inv_new` | `∀ c, 1 ≤ c → Inv (new c)`. |
| H2 | `lean/Solution.lean` | `inv_insert` | Adds `m.len.toNat < 2 ^ 64 - 1` (the bounded-integer allowance: `len` is a `UInt64`). |
| H3 | `lean/Solution.lean` | `inv_remove` | As §5. |
| H4 | `lean/Solution.lean` | `get_new` | `1 ≤ c → (new c).get k = none`. |
| H5 | `lean/Solution.lean` | `get_insert_self` | Adds `m.len.toNat < 2 ^ 64 - 1` (the bounded-integer allowance: `len` is a `UInt64`). |
| H6 | `lean/Solution.lean` | `get_insert_ne` | Adds `m.len.toNat < 2 ^ 64 - 1` (the bounded-integer allowance: `len` is a `UInt64`). |
| H7 | `lean/Solution.lean` | `insert_result` | Adds `m.len.toNat < 2 ^ 64 - 1` (the bounded-integer allowance: `len` is a `UInt64`). |
| H8 | `lean/Solution.lean` | `get_remove_self` | As §5. |
| H9 | `lean/Solution.lean` | `get_remove_ne` | As §5. |
| H10 | `lean/Solution.lean` | `remove_result` | As §5. |
| H11 | `lean/Solution.lean` | `len_new` | `1 ≤ c → (new c).len = 0`. |
| H12 | `lean/Solution.lean` | `len_insert` | Lengths compared in ℕ via `UInt64.toNat`, as an `if m.get k = none then … else …`. Adds `m.len.toNat < 2 ^ 64 - 1` (the bounded-integer allowance: `len` is a `UInt64`). |
| H13 | `lean/Solution.lean` | `len_remove` | Lengths compared in ℕ via `UInt64.toNat` (truncated subtraction, which the `if` guards). |
| H14 | `lean/Solution.lean` | `get_modify` | About `m.modify k w` in place of `m[k ≔ w]`. Adds `m.len.toNat < 2 ^ 64 - 1` (the bounded-integer allowance: `len` is a `UInt64`). |
| H15 | `lean/Solution.lean` | `len_modify` | About `m.modify k w`; equality of `UInt64`s. Adds `m.len.toNat < 2 ^ 64 - 1` (the bounded-integer allowance: `len` is a `UInt64`). |
| H16 | `lean/Solution.lean` | `inv_modify` | About `m.modify k w`. Adds `m.len.toNat < 2 ^ 64 - 1` (the bounded-integer allowance: `len` is a `UInt64`). |
| H17 | | | Omitted: `get` is a pure function, so it cannot change the map. |
| H18 | | | Omitted: `len` is a pure function (the field projection), so it cannot change the map. |

### rust

The `rust` condition has no properties. It implements the same representation and API and runs the same tests.

| Id | File | Declaration | Notes |
|---|---|---|---|
| Representation, `idx` | `rust/src/lib.rs` | `List`, `HashMap`, `bucket_index` (region `types`) | Byte-for-byte the Rust of the `aeneas` package's skeleton (only the module doc comment differs): `enum List { Cons(u64, u64, Box<List>), Nil }`, `slots: Vec<List>`, `len: u64`, `bucket_index(key, cap) = key % cap`. |
| new, len, get, insert, remove, get_mut | `rust/src/lib.rs` | `HashMap::new(cap: usize)`, `len(&self)`, `get(&self, key)`, `insert(&mut self, key, value)`, `remove(&mut self, key)`, `get_mut(&mut self, key) -> &mut u64` | Same signatures as `aeneas`. `new` and `get_mut` may panic when their precondition fails. |
| Tests | `rust/tests/spec.rs` | `scripted`, `random_cap1`, `random_cap3`, `random_cap4`, `random_cap7` | Transcribed from `tests.json` by `rust/tools/gen_tests.py`, one `#[test]` per sequence; `grade.sh` requires all 5 to pass. |
