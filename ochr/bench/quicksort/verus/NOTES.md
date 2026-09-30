# Maintainer notes: the Verus quicksort package

For whoever runs the benchmark or writes it up. `make-sandbox.sh` does not copy this file into sandboxes. The shared design is `ochr/docs/05-agent-effort-benchmark.md`, and the protocol is `ochr/bench/README.md`.

These are the five fairness points raised when this package and its hashmap twin were built, with team-lead's ruling on each (2026-09-30). The same five notes are in `../../hashmap/verus/NOTES.md`; each note says which problem it mainly concerns.

## 1. `spec_get` and `spec_len` are holes (hashmap)

A Verus specification cannot call an executable function, so the properties H1–H16 cannot mention `get` and `len` directly. The skeleton states them through two spec functions, `spec_get(&self, key) -> Option<u64>` and `spec_len(&self) -> nat`. The FIXED contracts of the executable `get` and `len` say they return exactly these values (`r == self.spec_get(key)`, `n == self.spec_len()`), so every property still holds of what the real `get` and `len` return.

Their bodies are holes, like `inv`, so the solver writes them: a spec-level lookup over the bucket, or a `Map<u64, u64>` view. This is a small second program next to the executable code. That second program is the cost the benchmark measures (the "two-program" setup), so it would be wrong to hand it to the solver as FIXED.

A hole here cannot weaken the task. The FIXED contracts of `get` and `len` pin the spec functions to the code, `new` must establish `inv`, and every mutating operation must preserve it. So whatever the solver defines, the verified properties transfer to the executable observers.

**Ruling:** keep them as holes.

## 2. The Verus guide's BST tutorial stays in the sandbox (mainly hashmap)

The Verus guide's flagship worked example is a verified binary-search-tree map container (`container_bst*.md` and `container_bst_all_source.md` in `docs/verus-guide/`). It covers a `Map` view, a well-formedness invariant, and insert/delete over `Option<Box<Node>>` with `final(...)` specifications.

It is not a hash map, so the exclusion rule ("Verus's examples of hash maps or sorting") does not cover it. It is the tool's own tutorial, which every condition gets the equivalent of. It is, however, a closer structural analogue to the hashmap task than generic documentation would be, and a write-up should say so.

**Ruling:** keep it; it is the tool's own documentation.

## 3. vstd is included as it is (both problems)

`docs/vstd/` is the pinned vstd source, byte-identical to the library the solution links against; `make-sandbox.sh` diffs it. It contains two things a reader should know about:
- `hash_map.rs`, `hash_set.rs` and `std_specs/hash.rs`: spec wrappers (`HashMapWithView` and similar) over Rust's `std::collections::HashMap`. They show how a library map is specified with a `Map` view. Using them, or any library map, in the solution is forbidden by `grade.sh`.
- `seq_lib.rs`: a spec-level verified merge sort (`Seq::sort_by`, `merge_sorted_with`, `lemma_sort_by_ensures`), plus multiset lemmas (`to_multiset_ensures`, `to_multiset_update` and others). Calling a sort in executable code is forbidden. The multiset lemmas are what a quicksort proof is expected to use.

vstd is the standard library, not an example, so it is not removed. The Lean condition likewise ships its standard library.

**Ruling:** vstd as it is.

## 4. Sub-slice borrows satisfy A2 (quicksort)

The quicksort requirement A2 asks for two recursive calls on disjoint sub-ranges "borrowed separately (in the style of Rust's `split_at_mut`)". The quicksort ASSIGNMENT accepts either of two forms:
- `split_at_mut`, which vstd specifies with `final`;
- sub-slice borrows such as `&mut a[..p]` and `&mut a[p + 1..]`.

Both borrow disjoint ranges separately, in place, with no copy. A human reader checks A2; the grader does not.

**Ruling:** sub-slice borrows are fine.

## 5. Totality (both problems)

Verus proves total correctness: no panics, no arithmetic overflow, every index in bounds, and termination of every loop and recursive function through `decreases` clauses. `grade.sh` forbids `#[verifier::exec_allows_no_decreases_clause]` and `#[verifier::assume_termination]`, and runs `--no-cheating`.

This matches the SPEC's §5, which says every property is total. It is the same bar as pure Lean, where every function terminates. It is stricter than Ochr, which bounds recursion by fuel: the Ochr quicksort states its properties at fuel equal to the length, and proving that the fuel suffices takes the place of the termination proof.

In this package, `quicksort` has no fuel argument. The solver proves termination with a `decreases` clause, which may be placed right after the FIXED signature if `quicksort` itself recurses. Index arithmetic (pivot positions, `hi - 1` and the like) must be proved free of underflow.

**Ruling:** totality as stated.

## Other things a reader should know

- **`perm` is vstd's multiset equality.** It is defined as `a.to_multiset() == b.to_multiset()` rather than a hand-written `count`: this is how Verus users state permutation, and vstd's multiset lemmas apply to it. `maint/perm_equiv.rs` machine-checks that it equals the SPEC's count-based `perm`.
- **The grader's witness.** `grade.sh` appends grader-owned functions (the witness) to a copy of the solution before verifying it. They call every FIXED function under its FIXED preconditions and assert its FIXED postconditions, so a FIXED contract neutralised from outside its region fails verification. This is the README §8 check that the FIXED items were really verified.
- **Validation.** `maint/validate.sh` re-runs all of the package's validation: the untouched skeleton fails naming its holes, and planted cheats are each rejected for the expected reason.
