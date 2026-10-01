# Assignment: a verified in-place hash map in Ochr

## The task

Implement a fixed-capacity hash map from word keys to values of any type `V`, with separate chaining, operating in place, in the language Ochr, and prove that it behaves like a finite map, as observed through `contains`, `get` and `len` (properties H1–H18). The properties are stated about your in-place operations themselves. There is no separate specification to write.

You work in one file, `HashMap.lean`. It is a skeleton: the representation, the provided functions, the signatures, the property statements and the tests are given (the FIXED regions, between `FIXED-BEGIN` and `FIXED-END` marker comments), and the holes, written `?`, are yours to fill (the build shows each hole's goal as a warning: the bindings in scope, then `⊢ goal`): the operations, your invariant `Inv`, and the proofs. Add any helper definitions and lemmas you need to the block `HashMapSolution`, between its FIXED regions.

Ochr is a research language, so you will not have met it before. Read `docs/GUIDE.md` first: it teaches enough of the language to start, in about fifteen minutes. The reference is `docs/RULES.md`, the examples tour is `checker/Ochr/Examples/00Std.lean` to `15BorrowTypes.lean`, and the arrays library the map is built on is `checker/Ochr/Examples/16Arrays.lean`.

## The representation (given, SPEC §2)

Everything is generic in the value type `V : Type`; nothing may assume that values can be compared, hashed or copied.

- `Opt(V)`, `None | Some(val : V)`: what `insert` and `remove` return. `IsSomeB(V, o)` is whether it holds a value.
- `Bucket(V)`, `BNil | BCons(key : Word, value : V, next : Bucket(V))`: a singly linked list of entries, each node owning the next.
- `Map(V, cap)`: a map of capacity `cap`, the value `MkMap(slots, len)`, where `slots` is an array of exactly `cap` buckets (`Array(Bucket(V), cap)`) and `len` is a word. The capacity is part of the type and never changes; there is no resizing. (The type is written `MapOf(Cells(Bucket(V), cap))`; it is the same thing.)
- `Idx(cap, k)`, the bucket of key `k`: `k mod cap`. `IdxLt(cap, k, h) : Lt(Idx(cap, k), cap)` is its bound, given `h : Lt(Zero, cap)`.
- `EqDec(a, b)`, key comparison that returns the evidence: `Yes(e)` with `e : Eq(Word, a, b)`, or `No(ne)` with `ne : Π(e : Eq(Word, a, b)). False`. The library's boolean `Eqb` is also available.
- Bucket `i` is reached in place through the arrays library's element borrow, `GetMut(Bucket(V), cap, s, i, h) : &Bucket(V)`, where the view of the array field is `AsSlice(Bucket(V), cap, &slots)`. It is the only way for runtime code to reach a bucket.
- `IsTrue(b)` is the proposition that the boolean `b` is `true`. `Grow(c, l)` is `l + 1` if `c` is `false` and `l` otherwise; `Shrink(c, l)` is `l − 1` if `c` is `true` and `l` otherwise. They state H12 and H13, with `c` = `contains(m, k)`.

## The operations (signatures given, SPEC §3)

| SPEC | Ochr |
|---|---|
| `new(c)`, requires `c ≥ 1` | `MapNew (V : Type) (cap : Word) (h : Lt(Zero, cap)) : Map(V, cap)` |
| `len(m)` | `MapLen (V : Type) (cap : Word) (m : &Map(V, cap)) : Word` |
| `contains(m, k)` | `MapContains (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) : Bool` |
| `get(m, k)`, requires `k` present | `MapGet (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (h : Contains(V, cap, *m, k)) : &V` |
| `insert(m, k, v)`, returns the previous value, moved out | `MapInsert (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V) : Opt(V)` |
| `remove(m, k)`, returns the removed value, moved out | `MapRemove (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) : Opt(V)` |
| `get_mut(m, k)`, requires `k` present | `MapGetMut (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (h : Contains(V, cap, *m, k)) : &V` |

Ochr has only mutable borrows, so `MapLen`, `MapContains` and `MapGet` take the map by `&` too; H17 and H18 say they leave it unchanged. `get` returns a borrow of the stored value, used read-only: neither `get` nor `get_mut` copies or moves a value (a plain read in Ochr moves, and `clone` would deep-copy an arbitrary `V`). `ContainsOf(V, cap, m, k)` and `LenOf(V, cap, m)` (given) run `MapContains` and `MapLen` on a copy of a map value, and `Contains(V, cap, m, k)` is `IsTrue(ContainsOf(V, cap, m, k))`: they are what the properties observe.

## The properties (statements given, SPEC §5)

`Inv (V : Type) (cap : Word) (m : Map(V, cap)) : Prop` is your invariant: any predicate that makes the properties provable. Every property is quantified over `V`, `cap`, a map `*m` (a borrow `m : &Map(V, cap)`), keys `k`, `k2` and values `v`, `w : V`. A property about an operation runs it on a copy of the map: in `(let c = *m; MapInsert(V, cap, &c, k, v); ContainsOf(V, cap, c, k))`, `c` is a copy of the map, `MapInsert` changes `c` in place, and `ContainsOf(V, cap, c, k)` asks whether `k` is in `c` afterwards; `*m` is still the map before. A property about the value at a key reads it through `MapGet` inside the statement, `clone(*MapGet(V, cap, &c, k, h))`, given a proof `h` that the key is present (statements are not run, so this copies nothing at run time). SPEC §3 splits each property that mentions `get` into a part about `contains` (a) and a part about the value (b).

| SPEC | Declaration | Statement (informally) |
|---|---|---|
| H1 | `InvNew` | `Inv(new(c))` |
| H2 | `InvInsert` | `Inv(m)` ⟹ `Inv` after `insert(m, k, v)` |
| H3 | `InvRemove` | `Inv(m)` ⟹ `Inv` after `remove(m, k)` |
| H4 | `ContainsNew` | `contains(new(c), k) = false` |
| H5a | `ContainsInsertSame` | `Inv(m)` ⟹ after `insert(m, k, v)`, `contains(m′, k) = true` |
| H5b | `GetInsertSame` | `Inv(m)` ⟹ after `insert(m, k, v)`, the value read through `get(m′, k)` is `v` |
| H6a | `ContainsInsertOther` | `Inv(m)`, `k2 ≠ k` ⟹ after `insert(m, k, v)`, `contains(m′, k2) = contains(m, k2)` |
| H6b | `GetInsertOther` | … and, when `k2` is present, the value read through `get` at `k2` is the same |
| H7a | `InsertReturnsContains` | `Inv(m)` ⟹ `insert(m, k, v)` returns `None` exactly when `k` was absent |
| H7b | `InsertReturnsGet` | `Inv(m)`, `k` present ⟹ `insert(m, k, v)` returns `Some` of the value read through `get(m, k)` |
| H8 | `ContainsRemoveSame` | `Inv(m)` ⟹ after `remove(m, k)`, `contains(m′, k) = false` |
| H9a | `ContainsRemoveOther` | `Inv(m)`, `k2 ≠ k` ⟹ after `remove(m, k)`, `contains(m′, k2) = contains(m, k2)` |
| H9b | `GetRemoveOther` | … and, when `k2` is present, the value read through `get` at `k2` is the same |
| H10a | `RemoveReturnsContains` | `Inv(m)` ⟹ `remove(m, k)` returns `None` exactly when `k` was absent |
| H10b | `RemoveReturnsGet` | `Inv(m)`, `k` present ⟹ `remove(m, k)` returns `Some` of the value read through `get(m, k)` |
| H11 | `LenNew` | `len(new(c)) = 0` |
| H12 | `LenInsert` | `Inv(m)` ⟹ after `insert(m, k, v)`, `len(m′) = Grow(contains(m, k), len(m))` |
| H13 | `LenRemove` | `Inv(m)` ⟹ after `remove(m, k)`, `len(m′) = Shrink(contains(m, k), len(m))` |
| H14a | `GetMutContains` | `Inv(m)`, `k` present ⟹ after writing `w` through `get_mut(m, k)`, every `contains(·, k2)` is as after `insert(m, k, w)` |
| H14b | `GetMutGet` | … and every value read through `get` at a present `k2` |
| H15 | `GetMutLen` | … and `len` is as after `insert(m, k, w)` |
| H16 | `GetMutInv` | … and `Inv` holds |
| H17a | `ContainsUnchanged` | `contains(m, k)` leaves the map equal to what it was (for every map) |
| H17b | `GetUnchanged` | `get(m, k)`, its borrow only read and then ended, leaves the map equal to what it was |
| H18 | `LenUnchanged` | `len(m)` leaves the map equal to what it was (for every map) |

`k2 ≠ k` is the hypothesis `ne : Π(e : Eq(Word, k2, k)). False`, and "`k` present" is `h : Contains(V, cap, *m, k)` (or `hk`, for `get_mut`). A (b) property takes the presence proofs its reads need as hypotheses, one for each map read (for example H5b's `h : Contains(V, cap, (let c = *m; MapInsert(V, cap, &c, k, v); c), k)`); its (a) part is what proves them. The exact statements are in `HashMap.lean`.

## The tests (given, SPEC §6)

The block `HashMapTests` holds five test sequences, transcribed from the SPEC's test vectors: `Test_scripted` (51 hand-written ops on capacity 4, covering collisions, overwriting, removing at the head, middle and end of a bucket, absent keys, `get_mut`, and re-inserting), and `Test_random_cap1`, `_cap3`, `_cap4`, `_cap7` (50 pseudo-random ops each). The value type is `Word`. Each starts from `MapNew(Word, cap, refl)`, runs its operations on that one map in order, and records each operation's result and the length after it in a `Trace`, which must equal the expected trace: what `insert` and `remove` returned; for a `get` of an absent key, `contains` (false); for a `get` of a present key, the value read through `MapGet`, whose precondition `refl` proves only if the key is there; for a write through `get_mut`, the length. Keys are below 24 and values below 100. The last test, `TestReject_insert`, must be rejected: it expects a wrong result.

## What you write

- The bodies of `MapNew`, `MapLen`, `MapContains`, `MapGet`, `MapInsert`, `MapRemove` and `MapGetMut`, and any helpers (for example, functions on a single bucket).
- `Inv`.
- The proofs of H1–H18, and any lemmas they need.

## Requirements on the algorithm

These are checked by a person reading your solution (SPEC §4), not by the grader:

1. **Hashing.** Every operation on key `k` reads or changes only the bucket `Idx(cap, k)` (reached through `GetMut`) and the `len` field. No operation scans other buckets.
2. **In place.** Operations change the map in place. No operation copies the table or a bucket, or rebuilds a bucket from a copy: in particular, do not `clone` a bucket or read one out of the array by value. A new entry may go at either end of its bucket, at your choice. `remove` unlinks the node.
3. **Nothing extra.** No auxiliary structure (a second table, a list of keys, a cache) and no resizing.

## Forbidden

The grader rejects, in `HashMap.lean` outside the FIXED regions:

- holes: `?` and `sorry` (a declaration with a hole is accepted with a warning, so the build alone does not show that it is unfinished);
- `reject def` (a declaration the checker must reject counts as correct when it fails, so it would turn a failed proof into a pass);
- new `implemented by` functions, and `abstract`, `unsized` or `copy` declarations;
- declaring a name that already exists: a built-in (`Nat`, `Unit`, …), a library name (`Word`, `Lt`, `Count`, …) or a name declared in a FIXED region (the checker itself refuses most of these; `Nat` and `Unit` it would accept, and a FIXED statement could then change meaning);
- any Lean outside the `ochr` blocks, a new `ochr` block, and any Lean command inside one (`axiom`, `sorry`, `set_option`, `macro`, `notation`, attributes, `#eval`, `import`, `open`, …);
- code that closes the block `HashMapSolution` early, or opens a comment or string that runs into a FIXED region.

Do not change the checker, the library, the build files or the grader: only `HashMap.lean` is graded (it is copied into a fresh copy of this directory, and graded there). A proof that relies on a bug in the checker fails the assignment.

## Checking your work

- `lake -q build` elaborates your file; the checker runs as each block is elaborated and reports every rejected declaration as an error, with the reason.
- `lake -q exe check` prints the checker's verdict on every declaration, with the reason for each rejection. `lake -q exe check HashMapSolution` skips the tests; `lake -q exe check --trace GetInsertSame` shows the checker's view of that declaration's goal.
- `./grade.sh` runs everything the grader checks. Its last line is `GRADE: PASS` or `GRADE: FAIL: <reasons>`, and it lists the remaining holes.

## When you are done

You are done when `./grade.sh` passes. That requires:

1. every FIXED region unchanged;
2. no hole and no forbidden construct left;
3. `HashMap.lean` builds, and the checker accepts every declaration of `HashMapSpec`, `HashMapSolution` (your helpers included) and `HashMapTests`, except `TestReject_insert`, which it must reject;
4. so every test passes, and H1–H18 are proved.

## The sibling assignment

This assignment has a sibling, condition `ochr-2p`, which asks for the same H1–H18, character for character, about the same operations, but obtains H4–H15 in the two-program style: a pure model of a finite map, the model's properties, and a proof that the in-place operations agree with the model. The observable obligations are the same; only the route to them differs. Here you prove H1–H18 directly about the in-place operations.

## Limitations of the language that affect this task

- **No shared borrows.** `MapContains`, `MapGet` and `MapLen` take the map by `&`, which could change it, so H17 and H18 (they do not) are proof obligations here, where Rust's `&self` would make them free. Reading a bucket through a borrow and ending the borrow puts the bucket back, and a proof that the map is unchanged has to follow that borrow down (the library's `GetMutRead` and `GetMutSet` say what a read and a write through an element borrow do).
- **`get` and `get_mut` have a precondition** (`k` present), because Ochr cannot return a borrow inside an `Opt`. Its type mentions `ContainsOf`, your `MapContains` run on a copy.
- **No copies of values.** `V` is arbitrary: an operation moves values (`insert` moves `v` in and the old value out) and never copies one. Statements read values through `get` with `clone`, which costs nothing since statements are not run.
- **The capacity is in the type.** `Map(V, cap)` does not record that `cap ≥ 1` (only `MapNew` requires it), and indexing a bucket needs the bound `IdxLt(cap, k, h)` with `h : Lt(Zero, cap)`. An operation can obtain `h` by testing `cap` (`match cap { Zero => …, Succ(c) => … }`, where `refl` proves `Lt(Zero, Succ(c))`) or with `LtDec(Zero, cap)`; the `Zero` case never happens for a map built by `MapNew`.
- **Only `GetMut` reaches a bucket.** Runtime code may not take the array apart itself (the checker enforces the array abstraction, see `docs/GUIDE.md` §9); statements and proofs may, through the library's model functions (`Nth`, `SetS`, …) on the view.
- **No automation.** Every case split, induction and rewrite is written by hand.
- **Unary numbers.** `Word` is unary in the logic; keys and values in the tests are small. Ochr's `Word` has no upper bound, so `len` cannot overflow and `insert` needs no bound on `len`.
- **Statements about copies.** Each property runs the operation on a copy `c` of the map `*m` and observes `c`; in a system with shared references or pure functions the same property would mention the map before and after directly.
