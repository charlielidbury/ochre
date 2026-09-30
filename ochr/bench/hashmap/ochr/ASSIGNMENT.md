# Assignment: a verified in-place hash map in Ochr

## The task

Implement a fixed-capacity hash map with separate chaining, operating in place, in the language Ochr, and prove that it behaves like a finite map, as observed through `get` and `len` (properties H1–H18). The properties are stated about your in-place operations themselves. There is no separate specification to write.

You work in one file, `HashMap.lean`. It is a skeleton: the representation, the provided functions, the signatures, the property statements and the tests are given (the FIXED regions, between `FIXED-BEGIN` and `FIXED-END` marker comments), and the holes, written `?`, are yours to fill (the build shows each hole's goal as a warning: the bindings in scope, then `⊢ goal`): the operations, your invariant `Inv`, and the proofs. Add any helper definitions and lemmas you need to the block `HashMapSolution`, between its FIXED regions.

Ochr is a research language, so you will not have met it before. Read `docs/GUIDE.md` first: it teaches enough of the language to start, in about fifteen minutes. The reference is `docs/RULES.md`, the examples tour is `checker/Ochr/Examples/00Std.lean` to `15BorrowTypes.lean`, and the arrays library the map is built on is `checker/Ochr/Examples/16Arrays.lean`.

## The representation (given, SPEC §2)

- `Opt`, `None | Some(val : Word)`: the result of a lookup. `IsSome(o)` is the proposition `o ≠ None`.
- `Bucket`, `BNil | BCons(key : Word, value : Word, next : Bucket)`: a singly linked list of entries, each node owning the next.
- `Map(cap)`: a map of capacity `cap`, the value `MkMap(slots, len)`, where `slots` is an array of exactly `cap` buckets (`Array(Bucket, cap)`) and `len` is a word. The capacity is part of the type and never changes; there is no resizing. (The type is written `MapOf(Cells(Bucket, cap))`, because a field cannot yet have the type `Array(Bucket, cap)`; it is the same thing.)
- `Idx(cap, k)`, the bucket of key `k`: `k mod cap`. `IdxLt(cap, k, h) : Lt(Idx(cap, k), cap)` is its bound, given `h : Lt(Zero, cap)`.
- `EqDec(a, b)`, key comparison that returns the evidence: `Yes(e)` with `e : Eq Word a b`, or `No(ne)` with `ne : Π(e : Eq Word a b). False`. The library's boolean `Eqb` is also available.
- `SlotMut(cap, s, i, h) : &Bucket`, a borrow of bucket `i` of the view `s` (the arrays library's `GetMut` at the element type `Bucket`). It is the only way for runtime code to reach a bucket in place; the view of the array field is `AsSlice(Bucket, cap, &slots)`.
- `Grow(g, l)` is `l + 1` if `g` is `None` and `l` otherwise; `Shrink(g, l)` is `l − 1` if `g` is `Some(_)` and `l` otherwise. They state H12 and H13.

## The operations (signatures given, SPEC §3)

| SPEC | Ochr |
|---|---|
| `new(c)`, requires `c ≥ 1` | `MapNew (cap : Word) (h : Lt(Zero, cap)) : Map(cap)` |
| `len(m)` | `MapLen (cap : Word) (m : &Map(cap)) : Word` |
| `get(m, k)` | `MapGet (cap : Word) (m : &Map(cap)) (k : Word) : Opt` |
| `insert(m, k, v)`, returns the previous value | `MapInsert (cap : Word) (m : &Map(cap)) (k : Word) (v : Word) : Opt` |
| `remove(m, k)`, returns the removed value | `MapRemove (cap : Word) (m : &Map(cap)) (k : Word) : Opt` |
| `get_mut(m, k)`, requires `k` present | `MapGetMut (cap : Word) (m : &Map(cap)) (k : Word) (h : IsSome(GetOf(cap, *m, k))) : &Word` |

Ochr has only mutable borrows, so `MapLen` and `MapGet` take the map by `&` too; H17 and H18 say they leave it unchanged. `GetOf(cap, m, k)` and `LenOf(cap, m)` (given) run `MapGet` and `MapLen` on a copy of a map value: they are what the properties observe.

## The properties (statements given, SPEC §5)

`Inv (cap : Word) (m : Map(cap)) : Prop` is your invariant: any predicate that makes the properties provable. Every property is quantified over `cap`, a map `*m` (a borrow `m : &Map(cap)`), keys `k`, `k2` and words `v`, `w`. A property about an operation runs it on a copy of the map: in `(let c = *m; MapInsert(cap, &c, k, v); GetOf(cap, c, k))`, `c` is a copy of the map, `MapInsert` changes `c` in place, and `GetOf(cap, c, k)` looks `k` up afterwards; `*m` is still the map before.

| SPEC | Declaration | Statement (informally) |
|---|---|---|
| H1 | `InvNew` | `Inv(new(c))` |
| H2 | `InvInsert` | `Inv(m)` ⟹ `Inv` after `insert(m, k, v)` |
| H3 | `InvRemove` | `Inv(m)` ⟹ `Inv` after `remove(m, k)` |
| H4 | `GetNew` | `get(new(c), k) = None` |
| H5 | `GetInsertSame` | `Inv(m)` ⟹ after `insert(m, k, v)`, `get(m′, k) = Some(v)` |
| H6 | `GetInsertOther` | `Inv(m)`, `k2 ≠ k` ⟹ after `insert(m, k, v)`, `get(m′, k2) = get(m, k2)` |
| H7 | `InsertReturnsGet` | `Inv(m)` ⟹ `insert(m, k, v)` returns `get(m, k)` |
| H8 | `GetRemoveSame` | `Inv(m)` ⟹ after `remove(m, k)`, `get(m′, k) = None` |
| H9 | `GetRemoveOther` | `Inv(m)`, `k2 ≠ k` ⟹ after `remove(m, k)`, `get(m′, k2) = get(m, k2)` |
| H10 | `RemoveReturnsGet` | `Inv(m)` ⟹ `remove(m, k)` returns `get(m, k)` |
| H11 | `LenNew` | `len(new(c)) = 0` |
| H12 | `LenInsert` | `Inv(m)` ⟹ after `insert(m, k, v)`, `len(m′) = Grow(get(m, k), len(m))` |
| H13 | `LenRemove` | `Inv(m)` ⟹ after `remove(m, k)`, `len(m′) = Shrink(get(m, k), len(m))` |
| H14 | `GetMutGet` | `Inv(m)`, `k` present ⟹ after writing `w` through `get_mut(m, k)`, every `get(·, k2)` is as after `insert(m, k, w)` |
| H15 | `GetMutLen` | … and `len` is as after `insert(m, k, w)` |
| H16 | `GetMutInv` | … and `Inv` holds |
| H17 | `GetUnchanged` | `get(m, k)` leaves the map equal to what it was (for every map) |
| H18 | `LenUnchanged` | `len(m)` leaves the map equal to what it was (for every map) |

`k2 ≠ k` is the hypothesis `ne : Π(e : Eq Word k2 k). False`. The exact statements are in `HashMap.lean`.

## The tests (given, SPEC §6)

The block `HashMapTests` holds five test sequences, transcribed from the SPEC's test vectors: `Test_scripted` (51 hand-written ops on capacity 4, covering collisions, overwriting, removing at the head, middle and end of a bucket, absent keys, `get_mut`, and re-inserting), and `Test_random_cap1`, `_cap3`, `_cap4`, `_cap7` (50 pseudo-random ops each). Each starts from `MapNew(cap, refl)`, runs its operations on that one map in order, and records each operation's result and the length after it in a `Trace`, which must equal the expected trace. Keys are below 24 and values below 100. The last test, `TestReject_insert`, must be rejected: it expects a wrong result.

## What you write

- The bodies of `MapNew`, `MapLen`, `MapGet`, `MapInsert`, `MapRemove` and `MapGetMut`, and any helpers (for example, functions on a single bucket).
- `Inv`.
- The proofs of H1–H18, and any lemmas they need.

## Requirements on the algorithm

These are checked by a person reading your solution (SPEC §4), not by the grader:

1. **Hashing.** Every operation on key `k` reads or changes only the bucket `Idx(cap, k)` (reached through `SlotMut`) and the `len` field. No operation scans other buckets.
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

- **No shared borrows.** `MapGet` and `MapLen` take the map by `&`, which could change it, so H17 and H18 (they do not) are proof obligations here, where Rust's `&self` would make them free. Reading a bucket through a borrow and ending the borrow puts the bucket back, and a proof that the map is unchanged has to follow that borrow down (the library's `GetMutSet` is an example of reasoning about an element borrow).
- **`get_mut` has a precondition** (`k` present), because Ochr cannot return a borrow inside an `Opt`. Its type mentions `GetOf`, your `MapGet` run on a copy.
- **The capacity is in the type.** `Map(cap)` does not record that `cap ≥ 1` (only `MapNew` requires it), and indexing a bucket needs the bound `IdxLt(cap, k, h)` with `h : Lt(Zero, cap)`. An operation can obtain `h` by testing `cap` (`match cap { Zero => …, Succ(c) => … }`, where `refl` proves `Lt(Zero, Succ(c))`) or with `LtDec(Zero, cap)`; the `Zero` case never happens for a map built by `MapNew`.
- **Only `SlotMut` reaches a bucket.** Runtime code may not take the array apart itself (the checker enforces the array abstraction, see `docs/GUIDE.md` §9); statements and proofs may, through the library's model functions (`Nth`, `SetS`, …) on the view.
- **No automation.** Every case split, induction and rewrite is written by hand.
- **Unary numbers.** `Word` is unary in the logic; keys and values in the tests are small. Ochr's `Word` has no upper bound, so `len` cannot overflow and `insert` needs no bound on `len`.
- **Statements about copies.** Each property runs the operation on a copy `c` of the map `*m` and observes `c`; in a system with shared references or pure functions the same property would mention the map before and after directly.
