# Assignment: verified in-place quicksort in Lean 4

## Overview

Implement quicksort on an array of 64-bit words as a pure Lean 4 function that updates the array in place (Lean does this whenever the array is not shared), and prove that the result is sorted and is a permutation of the input. The signature, the definitions of `sorted` and `perm`, and the property statements are given. You write the implementation and the proofs.

Everything you need is in this directory. Read this file first, then `Solution.lean`.

## What is provided

| File | What it is | May you edit it? |
|---|---|---|
| `Solution.lean` | The skeleton: `sorted`, `count`, `perm`, the signature of `quicksort` and the two property statements, each followed by a `sorry` | Yes, outside the FIXED regions |
| `Tests.lean` | The tests | No (FIXED file) |
| `Check.lean` | Restates every FIXED definition and theorem in a fresh module and checks the axioms your proofs use | No (FIXED file) |
| `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | The project: Lean `v4.31.0` and Mathlib (tag `v4.31.0`), already built under `.lake/` | No (FIXED files) |
| `grade.sh`, `grade_scan.py`, `.grader/`, `SOLUTION_FILES` | The grader | No (the final grade uses an untouched copy) |
| `flake.nix`, `flake.lock` | The toolchain: elan (which runs the Lean named in `lean-toolchain`) and Python 3 | No |
| `docs/` | Offline Lean documentation, as source text: *Theorem Proving in Lean 4*, *Functional Programming in Lean*, and the *Lean Language Reference* | Read only |

The sources of Lean's core library are under the toolchain (`$(elan which lean)/../../src/lean`), and those of Mathlib and its dependencies are under `.lake/packages/`. You may read anything in them.

A FIXED region runs from a comment containing the begin marker to the comment containing the matching end marker (look for `FIXED-` in `Solution.lean`). Everything inside, the marker lines included, must stay byte-for-byte as it is. Outside the FIXED regions you may write anything that the rules below allow: definitions, lemmas and imports. All your code must be in `Solution.lean`, the only file listed in `SOLUTION_FILES`: the final grade copies only that file into a fresh copy of this directory, so anything you put elsewhere is lost (and `grade.sh` rejects any other `.lean` file).

## What to build

### Operation (FIXED signature)

```lean
def Bench.quicksort (a : Array UInt64) : Array UInt64
```

It returns `a` sorted into ascending order. It has the same length as `a`. It is total: it terminates (Lean checks this) and cannot panic (see the rules below).

### Algorithm requirements

These are checked by a human reader, not by `grade.sh`:

- **A1 (partition).** Choose a pivot and partition the range with the Lomuto or the Hoare scheme, swapping elements of the one array (`Array.swap`, `Array.swapIfInBounds`, `Array.set` and similar, which work in place when the array is unshared). Say which scheme in a comment at your partition function.
- **A2 (two disjoint recursive calls).** After partitioning a range `[lo, hi)` of the array, sort the two disjoint sub-ranges (for Lomuto with the pivot ending at `p`: `[lo, p)` and `[p + 1, hi)`) with two recursive calls on the same array. The pivot's final position, if the scheme has one, belongs to neither.
- **A3 (in place).** No copy of the array or of a sub-range (no `extract`, no `toList`/`ofList` round trip, no temporary array, no `push`/`append` to build a result). Auxiliary space is O(1) beyond the recursion.
- **A4 (nothing extra).** No library sort, selection or permutation routine, and no other sorting algorithm as a fallback (for example insertion sort on small ranges).

Recursion on a decreasing measure (`termination_by hi - lo`, with `decreasing_by` if needed) is expected.

## Definitions (FIXED)

```lean
def sorted (a : Array UInt64) : Prop :=
  ∀ (i j : Nat) (hij : i < j) (hj : j < a.size), a[i]'(Nat.lt_trans hij hj) ≤ a[j]

def count (x : UInt64) : List UInt64 → Nat
  | [] => 0
  | y :: ys => (if y = x then 1 else 0) + count x ys

def perm (a b : Array UInt64) : Prop :=
  ∀ x : UInt64, count x a.toList = count x b.toList
```

`count x l` is the number of positions of `l` holding `x`, and `perm a b` says every word occurs equally often in `a` and `b`. You may relate them to library notions (for example `List.count` or `List.Perm`) in your own lemmas.

## Properties (FIXED statements)

| Id | Theorem | Statement |
|---|---|---|
| Q1 | `quicksort_sorted` | `∀ (a : Array UInt64), sorted (quicksort a)` |
| Q2 | `quicksort_perm` | `∀ (a : Array UInt64), perm (quicksort a) a` |

## Tests

`Tests.lean` holds 29 cases. Each sorts one input array and checks that the result equals the expected output:

- hand-picked cases: empty, one element, two elements in each order, duplicates, already sorted, reverse-sorted, all equal, and a short mixed array with repeated pivot values;
- 20 pseudo-random arrays of lengths 0 to 24, with values up to 99, some drawn from 0–3 so that duplicates are frequent.

Run them with `lake env lean --run Tests.lean` (after `lake build Solution`). The function must therefore be computable.

## Rules

Mathlib is allowed: import any of it (the skeleton imports all of it). Recursion by `termination_by`/`decreasing_by` is allowed; `partial def` is not.

Forbidden in `Solution.lean` (outside comments, string literals and the FIXED regions). `grade.sh` rejects:

- holes: `sorry`;
- escape hatches: `admit`, `axiom`, `opaque`, `partial`, `native_decide`, `decide +native`, `ofReduceBool`, `ofReduceNat`, `trustCompiler`, `implemented_by`, `extern`, and anything containing `unsafe`;
- metaprogramming and anything that could change what a FIXED statement means: `macro`, `macro_rules`, `syntax`, `elab`, `elab_rules`, `notation`, `infix`, `infixl`, `infixr`, `prefix`, `postfix`, `instance` (including `attribute [instance]` and `deriving instance`), `default_instance`, `unif_hint`, `export`, `run_cmd`, `run_elab`, `run_meta`, `#eval`, `#exit`, `initialize`, `init`, `addDecl`, `getEnv`, `modifyEnv`, `setEnv`, the elaborator attributes (`command_elab`, `term_elab` and their `builtin_` forms, `env_extension`), and the meta-level types (`CommandElab`, `CommandElabM`, `TermElab`, `TermElabM`, `TacticM`, `MetaM`, `CoreM`, `Environment`, `Declaration`, `ConstantInfo`, `IO`, `EIO`, `BaseIO`);
- operations that can panic at run time, since every operation must be total: `xs[i]!`, `panic!`, `unreachable!`, `assert!`, and the `!` forms `get!`, `getElem!`, `head!`, `tail!`, `back!`, `last!`, `getLast!`, `pop!`, `max!`, `min!`, `find!`, `fst!`, `snd!`, `set!`, `swap!`, `modify!`, `insertAt!`, `eraseIdx!`, `extract!`, `toNat!`, `ofNat!`. Use `xs[i]` with a proof of `i < xs.size`, `xs[i]?`, `getD`, `swapIfInBounds`, `setIfInBounds`, `Array.modify` and the like instead;
- `set_option`, except `maxHeartbeats`, `maxRecDepth`, `synthInstance.*`, `linter.*`, `pp.*`, `trace.*`, `profiler*`, `diagnostics*`, `exponentiation.*`, `autoImplicit` and `relaxedAutoImplicit`;
- library sorts: the words `qsort`, `qsortOrd`, `insertionSort`, `mergeSort`, `heapSort`, `sort`, `sortDedup`, `orderedInsert`, `binInsert`, `binInsertM`.

The check works on the components of names, so do not reuse these words for your own definitions.

## How to check your work

```sh
nix develop -c ./grade.sh
```

(`./grade.sh` alone also works when `lake` is on your `PATH`.) It checks, in order:

1. no holes and no forbidden constructs;
2. every FIXED region, and every FIXED file, unchanged;
3. `lake build Solution` succeeds;
4. `lake build Check` succeeds: every FIXED definition and theorem is exactly as fixed (restated in a fresh module that opens the skeleton's namespaces, so a declaration of yours that shadows a name used in a FIXED statement makes the restatement ambiguous and fails), your solution declares no global instance about existing types (the `SizeOf` and `deriving` instances Lean generates for your own types are fine) and no axiom, opaque constant or meta code, and both theorems depend on no axioms beyond `propext`, `Classical.choice` and `Quot.sound` (the `#print axioms` check);
5. the Lean kernel re-checks every declaration of your solution (`leanchecker`);
6. all 29 test cases pass.

It prints what it found and ends with one line, `GRADE: PASS lean/quicksort; ...` or `GRADE: FAIL lean/quicksort: <reasons>; ...`, and exits 0 exactly when the verdict is PASS. A full run takes a minute or two, mostly loading Mathlib.

## What counts as done

Your work is done when `./grade.sh` prints `GRADE: PASS` and your code meets the algorithm requirements A1–A4. The final grade copies your `Solution.lean` into a fresh, untouched copy of this directory and runs its `grade.sh` there.
