# Assignment: a verified in-place hash map in Ochr, with a pure model

## The task

Implement a fixed-capacity hash map from word keys to values of any type `V`, with separate chaining, operating in place, in the language Ochr, and prove that it behaves like a finite map, as observed through `contains`, `get` and `len` (properties H1–H18), in the two-program style: write a pure functional model of a finite map, prove the map properties about the model, and prove that your in-place operations agree with the model. H4–H15 about the in-place operations then follow; that step is provided. H1–H3 and H16–H18 are about the in-place map itself and you prove them directly.

You work in one file, `HashMap.lean`. It is a skeleton: the representation, the provided functions, the signatures, the statements and the tests are given (the FIXED regions, between `FIXED-BEGIN` and `FIXED-END` marker comments), and the holes, written `?`, are yours to fill (the build shows each hole's goal as a warning: the bindings in scope, then `⊢ goal`). Add any helper definitions and lemmas you need to the blocks `HashMapModel` and `HashMapSolution`, between their FIXED regions.

Ochr is a research language, so you will not have met it before. Read `docs/GUIDE.md` first: it teaches enough of the language to start, in about fifteen minutes. The reference is `docs/RULES.md`, the examples tour is `checker/Ochr/Examples/00Std.lean` to `15BorrowTypes.lean`, and the arrays library the map is built on is `checker/Ochr/Examples/16Arrays.lean`.

## The representation (given, SPEC §2)

Everything is generic in the value type `V : Type`; nothing may assume that values can be compared, hashed or copied.

- `Opt(V)`, `None | Some(val : V)`: what `insert` and `remove` return. `IsSomeB(V, o)` is whether it holds a value.
- `Bucket(V)`, `BNil | BCons(key : Word, value : V, next : Bucket(V))`: a singly linked list of entries, each node owning the next.
- `Map(V, cap)`: a map of capacity `cap`, the value `MkMap(slots, len)`, where `slots` is an array of exactly `cap` buckets (`Array(Bucket(V), cap)`) and `len` is a word. The capacity is part of the type and never changes; there is no resizing. (The type is written `MapOf(Cells(Bucket(V), cap))`; it is the same thing.)
- `Idx(cap, k)`, the bucket of key `k`: `k mod cap`. `IdxLt(cap, k, h) : Lt(Idx(cap, k), cap)` is its bound, given `h : Lt(Zero, cap)`.
- `EqDec(a, b)`, key comparison that returns the evidence: `Yes(e)` with `e : Eq(Word, a, b)`, or `No(ne)` with `ne : Π(e : Eq(Word, a, b)). False`. The library's boolean `Eqb` is also available.
- Bucket `i` is reached in place through the arrays library's element borrow, `GetMut(Bucket(V), cap, s, i, h) : &Bucket(V)`, where the view of the array field is `AsSlice(Bucket(V), cap, &slots)`. It is the only way for runtime code to reach a bucket.
- For the model: `SlotsOf(V, cap, m)`, the buckets of a map value as a view, and `LenField(V, cap, m)`, its length field. `SlotsOf` returns a view by value, so it is model code: it can be used in statements and in other model code, not at runtime.
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

## The model (block `HashMapModel`: signatures and statements given, definitions and proofs yours)

The model must be **pure**: no borrows (`&`) and no assignment (`p := t`) anywhere in the block; it computes on values. Declare the data types it needs in the block (an association list of keys and values, for example). Everything is generic in the value type `V`.

| Declaration | What it is |
|---|---|
| `MMap (V : Type) : Type` | the model's type |
| `MNew (V : Type) : MMap(V)` | the model of `new(c)`: the empty map |
| `MLen (V : Type) (a : MMap(V)) : Word` | the model of `len` |
| `MGet (V : Type) (a : MMap(V)) (k : Word) : Opt(V)` | the model of a lookup: `Some` of the value bound to `k`, or `None`; `contains` is whether it is `Some`, and `get` the value in it (by the agreement below) |
| `MInsert (V : Type) (a : MMap(V)) (k : Word) (v : V) : MMap(V)` | the map after `insert` (the value `insert` returns is `MGet(V, a, k)`, by the agreement below) |
| `MRemove (V : Type) (a : MMap(V)) (k : Word) : MMap(V)` | the map after `remove` (likewise, it returns `MGet(V, a, k)`) |
| `MWrite (V : Type) (a : MMap(V)) (k : Word) (w : V) : MMap(V)` | the map after writing `w` through `get_mut(·, k)` |
| `MInv (V : Type) (a : MMap(V)) : Prop` | the model's invariant: whatever the properties below need (it may be `⊤`) |
| `Abs (V : Type) (cap : Word) (s : Slice(Bucket(V), cap)) (len : Word) : MMap(V)` | the abstraction: the model of a map, from its buckets (a view) and its length field; `AbsOf(V, cap, m)` (given) applies it to a map value |

The model's properties (the H-properties about the model; each under `h : MInv(V, a)` except those about `MNew`):

| Id | Declaration | Statement |
|---|---|---|
| M4 | `MGetNew` | `MGet(MNew, k) = None` |
| M5 | `MGetInsertSame` | `MGet(MInsert(a, k, v), k) = Some(v)` |
| M6 | `MGetInsertOther` | `k2 ≠ k` ⟹ `MGet(MInsert(a, k, v), k2) = MGet(a, k2)` |
| M8 | `MGetRemoveSame` | `MGet(MRemove(a, k), k) = None` |
| M9 | `MGetRemoveOther` | `k2 ≠ k` ⟹ `MGet(MRemove(a, k), k2) = MGet(a, k2)` |
| M11 | `MLenNew` | `MLen(MNew) = 0` |
| M12 | `MLenInsert` | `MLen(MInsert(a, k, v)) = Grow(IsSomeB(MGet(a, k)), MLen(a))` |
| M13 | `MLenRemove` | `MLen(MRemove(a, k)) = Shrink(IsSomeB(MGet(a, k)), MLen(a))` |
| M14 | `MWriteGet` | `IsTrue(IsSomeB(MGet(a, k)))` ⟹ `MGet(MWrite(a, k, w), k2) = MGet(MInsert(a, k, w), k2)` |
| M15 | `MWriteLen` | `IsTrue(IsSomeB(MGet(a, k)))` ⟹ `MLen(MWrite(a, k, w)) = MLen(MInsert(a, k, w))` |

(H7 and H10, the values `insert` and `remove` return, need no model property: the agreement says they return the model's `MGet` before the operation.)

## The program (block `HashMapSolution`)

Yours: the operations, `Inv`, and these proofs. Every statement is quantified over `V`, `cap`, a map `*m` (a borrow `m : &Map(V, cap)`), keys `k`, `k2` and values `v`, `w : V`; a statement about an operation runs it on a copy `c` of the map, as in `(let c = *m; MapInsert(V, cap, &c, k, v); AbsOf(V, cap, c))`, and `*m` is still the map before.

| Id | Declaration | Statement (informally) |
|---|---|---|
| | `Inv (V : Type) (cap : Word) (m : Map(V, cap)) : Prop` | your invariant on maps |
| | `AbsInv` | `Inv(m)` ⟹ `MInv(AbsOf(m))` |
| H1 | `InvNew` | `Inv(new(c))` |
| H2 | `InvInsert` | `Inv(m)` ⟹ `Inv` after `insert(m, k, v)` |
| H3 | `InvRemove` | `Inv(m)` ⟹ `Inv` after `remove(m, k)` |
| agreement | `AbsNew` | `AbsOf(new(c)) = MNew` |
| agreement | `AgreeLen` | `Inv(m)` ⟹ `len(m) = MLen(AbsOf(m))` |
| agreement | `AgreeContains` | `Inv(m)` ⟹ `contains(m, k) = IsSomeB(MGet(AbsOf(m), k))` |
| agreement | `AgreeGet` | `Inv(m)`, `k` present ⟹ `Some` of the value read through `get(m, k)` is `MGet(AbsOf(m), k)` |
| agreement | `AgreeInsert` | `Inv(m)` ⟹ `AbsOf` after `insert(m, k, v)` is `MInsert(AbsOf(m), k, v)` |
| agreement | `AgreeInsertResult` | `Inv(m)` ⟹ `insert(m, k, v)` returns `MGet(AbsOf(m), k)` |
| agreement | `AgreeRemove` | `Inv(m)` ⟹ `AbsOf` after `remove(m, k)` is `MRemove(AbsOf(m), k)` |
| agreement | `AgreeRemoveResult` | `Inv(m)` ⟹ `remove(m, k)` returns `MGet(AbsOf(m), k)` |
| agreement | `AgreeWrite` | `Inv(m)`, `k` present ⟹ `AbsOf` after writing `w` through `get_mut(m, k)` is `MWrite(AbsOf(m), k, w)` |
| H16 | `GetMutInv` | `Inv(m)`, `k` present ⟹ `Inv` after writing `w` through `get_mut(m, k)` |
| H17a | `ContainsUnchanged` | `contains(m, k)` leaves the map equal to what it was (for every map) |
| H17b | `GetUnchanged` | `get(m, k)`, its borrow only read and then ended, leaves the map equal to what it was |
| H18 | `LenUnchanged` | `len(m)` leaves the map equal to what it was (for every map) |

Provided (statements and proofs FIXED, at the end of the block): H4 `ContainsNew`, H5a `ContainsInsertSame`, H5b `GetInsertSame`, H6a `ContainsInsertOther`, H6b `GetInsertOther`, H7a `InsertReturnsContains`, H7b `InsertReturnsGet`, H8 `ContainsRemoveSame`, H9a `ContainsRemoveOther`, H9b `GetRemoveOther`, H10a `RemoveReturnsContains`, H10b `RemoveReturnsGet`, H11 `LenNew`, H12 `LenInsert`, H13 `LenRemove`, H14a `GetMutContains`, H14b `GetMutGet`, H15 `GetMutLen`. Each is an instance of a generic lemma in the block `HashMapCompose` (for example `GetInsertSameFrom`), which derives the property about any operations from their agreement with any model that has the model property; they are checked once your declarations are. Their statements are the one-program assignment's, character for character; SPEC §3 splits each property that mentions `get` into a part about `contains` (a) and a part about the value read through `get` (b).

`k2 ≠ k` is the hypothesis `ne : Π(e : Eq(Word, k2, k)). False`, and "`k` present" is `hk : Contains(V, cap, *m, k)`. The exact statements are in `HashMap.lean`.

## The tests (given, SPEC §6)

The block `HashMapTests` holds five test sequences, transcribed from the SPEC's test vectors: `Test_scripted` (51 hand-written ops on capacity 4, covering collisions, overwriting, removing at the head, middle and end of a bucket, absent keys, `get_mut`, and re-inserting), and `Test_random_cap1`, `_cap3`, `_cap4`, `_cap7` (50 pseudo-random ops each). The value type is `Word`. Each starts from `MapNew(Word, cap, refl)`, runs its operations on that one map in order, and records each operation's result and the length after it in a `Trace`, which must equal the expected trace: what `insert` and `remove` returned; for a `get` of an absent key, `contains` (false); for a `get` of a present key, the value read through `MapGet`, whose precondition `refl` proves only if the key is there; for a write through `get_mut`, the length. Keys are below 24 and values below 100. The last test, `TestReject_insert`, must be rejected: it expects a wrong result.

## Requirements on the algorithm

These are checked by a person reading your solution (SPEC §4), not by the grader. They apply to the in-place operations:

1. **Hashing.** Every operation on key `k` reads or changes only the bucket `Idx(cap, k)` (reached through `GetMut`) and the `len` field. No operation scans other buckets.
2. **In place.** Operations change the map in place. No operation copies the table or a bucket, or rebuilds a bucket from a copy: in particular, do not `clone` a bucket or read one out of the array by value, and do not run the model and write its result back. A new entry may go at either end of its bucket, at your choice. `remove` unlinks the node.
3. **Nothing extra.** No auxiliary structure (a second table, a list of keys, a cache) and no resizing.

## Forbidden

The grader rejects, in `HashMap.lean` outside the FIXED regions:

- holes: `?` and `sorry` (a declaration with a hole is accepted with a warning, so the build alone does not show that it is unfinished);
- `reject def` (a declaration the checker must reject counts as correct when it fails, so it would turn a failed proof into a pass);
- new `implemented by` functions, and `abstract`, `unsized` or `copy` declarations;
- declaring a name that already exists: a built-in (`Nat`, `Unit`, …), a library name (`Word`, `Lt`, `Count`, …) or a name declared in a FIXED region (the checker itself refuses most of these; `Nat` and `Unit` it would accept, and a FIXED statement could then change meaning);
- in the block `HashMapModel`: any borrow (`&`) or assignment (`p := t`);
- any Lean outside the `ochr` blocks, a new `ochr` block, and any Lean command inside one (`axiom`, `sorry`, `set_option`, `macro`, `notation`, attributes, `#eval`, `import`, `open`, …);
- code that closes a block early, or opens a comment or string that runs into a FIXED region.

Do not change the checker, the library, the build files or the grader: only `HashMap.lean` is graded (it is copied into a fresh copy of this directory, and graded there). A proof that relies on a bug in the checker fails the assignment.

## Checking your work

- `lake -q build` elaborates your file; the checker runs as each block is elaborated and reports every rejected declaration as an error, with the reason.
- `lake -q exe check` prints the checker's verdict on every declaration, with the reason for each rejection. `lake -q exe check HashMapModel` checks only the model (and what it uses); `lake -q exe check HashMapSolution` skips the tests; `lake -q exe check --trace AgreeGet` shows the checker's view of that declaration's goal.
- `./grade.sh` runs everything the grader checks. Its last line is `GRADE: PASS` or `GRADE: FAIL: <reasons>`, and it lists the remaining holes.

## When you are done

You are done when `./grade.sh` passes. That requires:

1. every FIXED region unchanged;
2. no hole and no forbidden construct left;
3. `HashMap.lean` builds, and the checker accepts every declaration of every block (your helpers included), except `TestReject_insert`, which it must reject;
4. so every test passes, the model's properties and the agreement are proved, and H1–H18 about the in-place operations hold.

## Why this assignment asks for exactly what the one-program version asks for

This assignment has a sibling, condition `ochr`, in which H1–H18 are proved directly about the in-place operations, with no model. The two pose the same observable obligations:

- The end result is the same. All eighteen declarations `InvNew` … `LenUnchanged` here are, character for character, the statements the one-program assignment asks for, about the same signatures, and the checker accepts the provided H4–H15 only once your agreement and model proofs are accepted. H1–H3 and H16–H18 are your proofs in both.
- Nothing is added to what is observable. The model, its properties, `AbsInv` and the agreement are the route by which H4–H15 are obtained; the generic lemmas that turn them into H4–H15 are provided and checked, for any operations and any model, so they cost you nothing.
- Nothing is taken away. Your invariant `Inv` plays the same role in both (H1–H3 and H16 are the same obligations), the tests and the algorithm requirements are identical, and a solution that passes here also satisfies every property the one-program assignment states.

The only difference is the route: here the map properties are proved once about a pure model, and the in-place operations are connected to it by the agreement; in the one-program version they are proved about the in-place operations directly.

## Limitations of the language that affect this task

- **No shared borrows.** `MapContains`, `MapGet` and `MapLen` take the map by `&`, which could change it, so H17 and H18 (they do not) are proof obligations here, where Rust's `&self` would make them free. Reading a bucket through a borrow and ending the borrow puts the bucket back, and a proof that the map is unchanged has to follow that borrow down (the library's `GetMutRead` and `GetMutSet` say what a read and a write through an element borrow do).
- **`get` and `get_mut` have a precondition** (`k` present), because Ochr cannot return a borrow inside an `Opt`. Its type mentions `ContainsOf`, your `MapContains` run on a copy.
- **No copies of values.** `V` is arbitrary: an operation moves values and never copies one. Statements read values through `get` with `clone`, which costs nothing since statements are not run.
- **The capacity is in the type.** `Map(V, cap)` does not record that `cap ≥ 1` (only `MapNew` requires it), and indexing a bucket needs the bound `IdxLt(cap, k, h)` with `h : Lt(Zero, cap)`. An operation can obtain `h` by testing `cap` (`match cap { Zero => …, Succ(c) => … }`, where `refl` proves `Lt(Zero, Succ(c))`) or with `LtDec(Zero, cap)`; the `Zero` case never happens for a map built by `MapNew`.
- **Only `GetMut` reaches a bucket.** Runtime code may not take the array apart itself (the checker enforces the array abstraction, see `docs/GUIDE.md` §9). The model, statements and proofs may: `Abs` takes the buckets as a view by value, so it is model code and may match on the view's representation or use the library's `Nth`.
- **No projections of stuck pairs**: a function that returns a pair cannot have its components taken with `.1` in a statement until the pair is a constructor value; this is why the model's operations return the new map only.
- **No automation.** Every case split, induction and rewrite is written by hand.
- **Unary numbers.** `Word` is unary in the logic; keys and values in the tests are small. Ochr's `Word` has no upper bound, so `len` cannot overflow and `insert` needs no bound on `len`.
- **Statements about copies.** Each property runs the operation on a copy `c` of the map `*m` and observes `c`; in a system with shared references or pure functions the same property would mention the map before and after directly.
