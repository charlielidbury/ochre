# Assignment: a verified fixed-capacity hash map in Lean 4

## Overview

Implement a hash map from 64-bit keys to values of any type `V : Type`, with a fixed number of buckets and separate chaining, as pure functions in Lean 4, and prove that it behaves like a finite map, as observed through `get` and `len`. The representation, the signatures and the property statements are given. You write the function bodies, choose an invariant `Inv`, and prove the properties.

Everything you need is in this directory. Read this file first, then `Solution.lean`.

## What is provided

| File | What it is | May you edit it? |
|---|---|---|
| `Solution.lean` | The skeleton: the representation, `idx`, the signatures, `Inv` and the property statements, each followed by a `sorry` | Yes, outside the FIXED regions |
| `Tests.lean` | The tests | No (FIXED file) |
| `Check.lean` | Restates every FIXED definition and theorem in a fresh module and checks the axioms your proofs use | No (FIXED file) |
| `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | The project: Lean `v4.31.0` and Mathlib (tag `v4.31.0`), already built under `.lake/` | No (FIXED files) |
| `grade.sh`, `grade_scan.py`, `.grader/`, `SOLUTION_FILES` | The grader | No (the final grade uses an untouched copy) |
| `flake.nix`, `flake.lock` | The toolchain: elan (which runs the Lean named in `lean-toolchain`) and Python 3 | No |
| `docs/` | Offline Lean documentation, as source text: *Theorem Proving in Lean 4*, *Functional Programming in Lean*, and the *Lean Language Reference* | Read only |

The sources of Lean's core library are under the toolchain (`$(elan which lean)/../../src/lean`), and those of Mathlib and its dependencies are under `.lake/packages/`. You may use anything in them.

A FIXED region runs from a comment containing the begin marker to the comment containing the matching end marker (look for `FIXED-` in `Solution.lean`). Everything inside, the marker lines included, must stay byte-for-byte as it is. Outside the FIXED regions you may write anything that the rules below allow: definitions, lemmas and imports. All your code must be in `Solution.lean`, the only file listed in `SOLUTION_FILES`: the final grade copies only that file into a fresh copy of this directory, so anything you put elsewhere is lost (and `grade.sh` rejects any other `.lean` file).

## What to build

### Representation (FIXED)

```lean
abbrev Bucket (V : Type) := List (UInt64 × V)   -- a bucket: a list of (key, value) entries

structure HashMap (V : Type) where
  slots : Array (Bucket V)                      -- the buckets; slots.size is the capacity
  len : UInt64                                  -- the number of keys in the map

def HashMap.idx (m : HashMap V) (k : UInt64) : Nat := k.toNat % m.slots.size
```

The value type `V` is arbitrary: nothing may assume that values can be compared, hashed, ordered or given a default (no `[DecidableEq V]`, `[BEq V]`, `[Inhabited V]` and so on), only stored and returned.

The capacity is chosen by `new` and never changes: there is no resizing. The bucket of key `k` is `m.slots[m.idx k]`, and `idx` (`k mod capacity`) is the only hash function.

`len` is a machine word (`UInt64`), not a `Nat`, like the keys: this is the natural representation of a counter in a map from words to words, and it keeps the arithmetic the same as in an implementation in a systems language. The price is overflow: `len + 1` wraps at 2⁶⁴. So every property that runs `insert` may assume `m.len.toNat < 2 ^ 64 - 1` (the map is not full), and properties that do arithmetic on lengths do it in `Nat`, through `UInt64.toNat`.

### Operations (FIXED signatures)

All in namespace `Bench.HashMap`, with `variable {V : Type}`. A map is updated by returning the new map.

| Operation | Meaning | Requires |
|---|---|---|
| `new (cap : UInt64) : HashMap V` | An empty map with `cap` empty buckets and `len = 0`. | `1 ≤ cap` |
| `HashMap.len` (the structure field) | The number of keys in the map. | |
| `get (m : HashMap V) (k : UInt64) : Option V` | `some v` if `k` is bound to `v`, `none` otherwise. | |
| `insert (m : HashMap V) (k : UInt64) (v : V) : HashMap V × Option V` | The map with `k` bound to `v`, and the value `k` was bound to before, or `none`. | |
| `remove (m : HashMap V) (k : UInt64) : HashMap V × Option V` | The map with `k` unbound, and the value it was bound to, or `none`. | |
| `modify (m : HashMap V) (k : UInt64) (w : V) : HashMap V` | The map with `w` written into the entry of `k`, found by walking down `k`'s bucket. It is the pure counterpart of writing `w` through a mutable borrow `get_mut(m, k)` of the value stored for `k`, which a language with borrows would offer. | `m.get k ≠ none` (what it returns otherwise is up to you) |

Every operation is total: it terminates (Lean checks this) and cannot panic (see the rules below).

### Algorithm requirements

These are checked by a human reader, not by `grade.sh`:

- **A1 (hashing).** Every operation on key `k` reads or changes only the bucket `m.slots[m.idx k]` and the `len` field. No operation scans other buckets.
- **A2 (in place).** Update the table with the operations that work in place when the array is unshared (`Array.set`, `Array.modify`, `Array.modifyOp` and similar), never by rebuilding it (no `Array.map`, `toList`/`ofList` round trip and so on). Buckets are immutable lists; a new entry may go at either end of its bucket, as you choose.
- **A3 (nothing extra).** No auxiliary structure (a second table, a list of keys, a cache), no resizing, and no library map or set.

## Properties (FIXED statements)

You define the invariant `Inv : HashMap V → Prop` (a hole: any predicate that makes the properties provable), then prove the sixteen theorems below. In `Solution.lean` each starts with `∀ {V : Type}` and names its variables' types; otherwise they are stated exactly as here; `m' := (m.insert k v).1` and so on are just shorthand in this table.

| Id | Theorem | Statement |
|---|---|---|
| H1 | `inv_new` | `1 ≤ c → Inv (new c : HashMap V)` |
| H2 | `inv_insert` | `Inv m → m.len.toNat < 2 ^ 64 - 1 → Inv (m.insert k v).1` |
| H3 | `inv_remove` | `Inv m → Inv (m.remove k).1` |
| H4 | `get_new` | `1 ≤ c → (new c : HashMap V).get k = none` |
| H5 | `get_insert_self` | `Inv m → m.len.toNat < 2 ^ 64 - 1 → (m.insert k v).1.get k = some v` |
| H6 | `get_insert_ne` | `Inv m → m.len.toNat < 2 ^ 64 - 1 → k' ≠ k → (m.insert k v).1.get k' = m.get k'` |
| H7 | `insert_result` | `Inv m → m.len.toNat < 2 ^ 64 - 1 → (m.insert k v).2 = m.get k` |
| H8 | `get_remove_self` | `Inv m → (m.remove k).1.get k = none` |
| H9 | `get_remove_ne` | `Inv m → k' ≠ k → (m.remove k).1.get k' = m.get k'` |
| H10 | `remove_result` | `Inv m → (m.remove k).2 = m.get k` |
| H11 | `len_new` | `1 ≤ c → (new c : HashMap V).len = 0` |
| H12 | `len_insert` | `Inv m → m.len.toNat < 2 ^ 64 - 1 → (m.insert k v).1.len.toNat = if m.get k = none then m.len.toNat + 1 else m.len.toNat` |
| H13 | `len_remove` | `Inv m → (m.remove k).1.len.toNat = if m.get k ≠ none then m.len.toNat - 1 else m.len.toNat` |
| H14 | `get_modify` | `Inv m → m.len.toNat < 2 ^ 64 - 1 → m.get k ≠ none → (m.modify k w).get k' = (m.insert k w).1.get k'` |
| H15 | `len_modify` | `Inv m → m.len.toNat < 2 ^ 64 - 1 → m.get k ≠ none → (m.modify k w).len = (m.insert k w).1.len` |
| H16 | `inv_modify` | `Inv m → m.len.toNat < 2 ^ 64 - 1 → m.get k ≠ none → Inv (m.modify k w)` |

In words: `Inv` holds of every map built by the operations; `get` after `insert`/`remove` sees the change at the same key and nothing else changes; `insert` and `remove` return the old `get`; `len` counts keys; and `modify` has the same effect as `insert` on every `get`, on `len` and on `Inv`. Since the functions are pure, `get` and `len` cannot change the map, so there is nothing to prove about that.

## Tests

`Tests.lean` holds five sequences of operations, all with values of type `UInt64` (`V := UInt64`). Each starts from `new cap` and applies its operations in order to one map, checking the result of every `get`, `insert` and `remove` and the value of `len` after every operation; a `get_mut` step runs `modify`.

- `scripted` (capacity 4): collisions (several keys in one bucket), overwriting with the previous value returned, removing a key at the head, middle and end of a bucket, removing an absent key, removing twice, writing through `get_mut` then reading with `get` (the same key and a neighbour in the same bucket), `insert` after `get_mut`, and re-inserting a removed key.
- `random-cap1`, `random-cap3`, `random-cap4`, `random-cap7`: 50 pseudo-random operations each, over a key space about three times the capacity. With capacity 1 every key shares one bucket.

Run them with `lake env lean --run Tests.lean` (after `lake build Solution`). The functions must therefore be computable.

## Rules

Mathlib is allowed: import any of it (the skeleton imports all of it). Recursion by `termination_by`/`decreasing_by` is allowed; `partial def` is not.

Forbidden in `Solution.lean` (outside comments, string literals and the FIXED regions). `grade.sh` rejects:

- holes: `sorry`;
- escape hatches: `admit`, `axiom`, `opaque`, `partial`, `native_decide`, `decide +native`, `ofReduceBool`, `ofReduceNat`, `trustCompiler`, `implemented_by`, `extern`, and anything containing `unsafe`;
- metaprogramming and anything that could change what a FIXED statement means: `macro`, `macro_rules`, `syntax`, `elab`, `elab_rules`, `notation`, `infix`, `infixl`, `infixr`, `prefix`, `postfix`, `instance` (including `attribute [instance]` and `deriving instance`), `default_instance`, `unif_hint`, `export`, `run_cmd`, `run_elab`, `run_meta`, `#eval`, `#exit`, `initialize`, `init`, `addDecl`, `getEnv`, `modifyEnv`, `setEnv`, the elaborator attributes (`command_elab`, `term_elab` and their `builtin_` forms, `env_extension`), and the meta-level types (`CommandElab`, `CommandElabM`, `TermElab`, `TermElabM`, `TacticM`, `MetaM`, `CoreM`, `Environment`, `Declaration`, `ConstantInfo`, `IO`, `EIO`, `BaseIO`);
- operations that can panic at run time, since every operation must be total: `xs[i]!`, `panic!`, `unreachable!`, `assert!`, and the `!` forms `get!`, `getElem!`, `head!`, `tail!`, `back!`, `last!`, `getLast!`, `pop!`, `max!`, `min!`, `find!`, `fst!`, `snd!`, `set!`, `swap!`, `modify!`, `insertAt!`, `eraseIdx!`, `extract!`, `toNat!`, `ofNat!`. Use `xs[i]` with a proof of `i < xs.size`, `xs[i]?`, `getD`, `swapIfInBounds`, `setIfInBounds`, `Array.modify` and the like instead;
- `set_option`, except `maxHeartbeats`, `maxRecDepth`, `synthInstance.*`, `linter.*`, `pp.*`, `trace.*`, `profiler*`, `diagnostics*`, `exponentiation.*`, `autoImplicit` and `relaxedAutoImplicit`;
- library maps, sets and association lists (the map must be the FIXED representation): the words `Std`, `Batteries`, `DHashMap`, `HashSet`, `RBMap`, `RBSet`, `TreeMap`, `DTreeMap`, `TreeSet`, `AssocList`, `PersistentHashMap`, `AList`, `Finmap`, and `Lean.HashMap`.

The check works on the components of names, so do not reuse these words for your own definitions.

## How to check your work

```sh
nix develop -c ./grade.sh
```

(`./grade.sh` alone also works when `lake` is on your `PATH`.) It checks, in order:

1. no holes and no forbidden constructs;
2. every FIXED region, and every FIXED file, unchanged;
3. `lake build Solution` succeeds;
4. `lake build Check` succeeds: every FIXED definition and theorem is exactly as fixed (restated in a fresh module that opens the skeleton's namespaces, so a declaration of yours that shadows a name used in a FIXED statement makes the restatement ambiguous and fails), your solution declares no global instance about existing types (the `SizeOf` and `deriving` instances Lean generates for your own types are fine) and no axiom, opaque constant or meta code, and every FIXED theorem depends on no axioms beyond `propext`, `Classical.choice` and `Quot.sound` (the `#print axioms` check);
5. the Lean kernel re-checks every declaration of your solution (`leanchecker`);
6. all five test sequences pass.

It prints what it found and ends with one line, `GRADE: PASS lean/hashmap; ...` or `GRADE: FAIL lean/hashmap: <reasons>; ...`, and exits 0 exactly when the verdict is PASS. A full run takes a minute or two, mostly loading Mathlib.

## What counts as done

Your work is done when `./grade.sh` prints `GRADE: PASS` and your code meets the algorithm requirements A1–A3. The final grade copies your `Solution.lean` into a fresh, untouched copy of this directory and runs its `grade.sh` there.
