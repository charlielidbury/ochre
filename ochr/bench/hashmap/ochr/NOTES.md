# Maintainer notes: the Ochr hashmap packages (`ochr`, `ochr-2p`)

For whoever runs the benchmark or writes it up. `make-sandbox.sh` does not copy this file into sandboxes. The shared design is `ochr/docs/05-agent-effort-benchmark.md`, the protocol is `ochr/bench/README.md` (§14 covers which checker revision a trial uses), and the shared tooling is `ochr/bench/common/ochr/`. The same notes are in `../ochr-2p/NOTES.md`.

## Design decisions

- **The capacity lives in the type.** `Map(cap) = MapOf(Cells(Bucket, cap))`, i.e. `MkMap(slots : Array(Bucket, cap), len : Word)`. `MapOf` takes the array's model type as a parameter, because a field cannot yet have the type `Array(Bucket, cap)` (the arrays library's `[K4]`).
- **Provided in `HashMapSpec`:**
  - `Opt` and `IsSome`;
  - `Grow` and `Shrink`, the right-hand sides of H12 and H13;
  - `Idx` (`k mod cap` by counting) with its bound `IdxLt`, standing in for the `%` and its bound that other systems get from their libraries or automation;
  - `EqDec`, key comparison with evidence;
  - `SlotMut`, the library's `GetMut` at element type `Bucket` (`implemented by "ochr_arr_get_mut"`). It is needed because `&E` is not yet well formed for a type variable, and it is the only way for runtime code to reach a bucket in place.
- **Names.** The operations are `MapNew`, `MapLen`, `MapGet`, `MapInsert`, `MapRemove` and `MapGetMut`, because the arrays library already declares `GetMut`. `GetOf` and `LenOf` run `MapGet` and `MapLen` on a copy of a map value; the properties observe through them.
- **Properties run on a copy.** Every property runs the operation on a copy (`let c = *m; op(cap, &c, …); …`). H17 and H18 are stated as `Eq (Map(cap)) (let c = *m; MapGet(cap, &c, k); c) (*m)`, for every map.
- **Tests.** Each of the five sequences is one test: the ops run on one map, and their results and lengths are collected in a `Trace` and compared with the expected trace. There is one negative test. With an unverified implementation the set takes about 1.5 s in the compiled checker.
- **`ochr-2p` is generated.** `common/ochr/gen_hashmap_2p.py` builds it from `ochr`, so the representation, signatures, H1–H18 statements and tests are byte-identical.
- **What `ochr-2p` adds:**
  - the pure model: `MMap`, `MNew`, `MLen`, `MGet`, `MInsert`, `MRemove`, `MWrite` and `MInv`, and `Abs`, which works on a map's buckets as a view and so is a model function;
  - M4–M15, the H-properties about the model;
  - `AbsOf`, provided, via `SlotsOf(cap, clone(m))` and `LenField`;
  - the agreement, under the concrete `Inv`: `AbsNew`, `AgreeLen`, `AgreeGet`, `AgreeInsert(+Result)`, `AgreeRemove(+Result)` and `AgreeWrite`;
  - `AbsInv`.
- **How H4–H15 are proved in `ochr-2p`.** They are provided as instances of twelve generic lemmas (`HashMapCompose`), generic in the operations and the model. All twelve instantiations were checked against two stub worlds: `Inv` = `MInv` = `False`, which covers H5–H10 and H12–H15, and a `⊤` world that covers H4 and H11. H1–H3 and H16–H18 concern the in-place map only, and the solver proves them in both conditions.
- **Why the model operations return only the new map.** The checker has no projections of stuck pairs. The values `insert` and `remove` return are tied to `MGet` by `AgreeInsertResult` and `AgreeRemoveResult`, which is why H7 and H10 have no model property.

## Ways the language makes this condition harder or different

1. **No automation.** Every case split, induction and rewrite is written by hand. This is the largest confound in any cross-system comparison. `ochr` against `ochr-2p` is immune to it.
2. **No shared borrows.** `MapGet` and `MapLen` take `&`, so H17 and H18 are real obligations: the proof follows the `SlotMut` borrow down and shows the bucket is put back. Rust's `&self` makes them free.
3. **`get_mut` precondition.** `IsSome(GetOf(cap, *m, k))` is hard to thread down to the bucket level. In a throwaway implementation, returning a fallback borrow (for example of `len`) in the unreachable case was the easy route. `ASSIGNMENT.md` does not hint at it.
4. **`Map(cap)` does not record `cap ≥ 1`.** Each operation has to test `cap` (or use `LtDec`) to get `IdxLt`'s premise. `ASSIGNMENT.md` says how.
5. **No projections of stuck pairs.** This shaped the `ochr-2p` model interface (above).
6. **The `ochr-2p` interface is large.** It has 9 model definitions, 10 model lemmas, 8 agreements and `AbsInv`, against 18 properties in `ochr`. That is inherent to data refinement onto an abstract map, but the FIXED choices shape the ablation:
   - the model operations return only the new state;
   - `Abs` works on views;
   - there is a separate model invariant.
7. **Unary `Word`.** Keys are at most 23 and values at most 99 for every condition, and concrete runs are slow for large numbers.
8. **Unbounded `Word`.** `len` cannot overflow, so there is no bounded-integer allowance, unlike Aeneas and Verus.
9. **Checker soundness.** The checker is a prototype, and earlier revisions had closed proofs of `False`. The human check and README §14 (re-grade on the latest checker) guard against solutions that rely on a bug. Redeclaring `Nat` or `Unit` is accepted by the checker; the grader forbids redeclaring any built-in, library or FIXED name.
10. **Moving target.** Planned changes (for example D66: `&A` for any `A : Type₀`) would make `SlotMut` unnecessary and can change the typing of the skeletons.

## When the checker or library changes

- In both packages, run `python3 ../../common/ochr/gen_tests.py HashMap.lean --check`.
- Run `python3 ../../common/ochr/gen_hashmap_2p.py --check`.
- Make a fresh sandbox and check that `grade.sh` fails on the untouched skeleton for holes only.
- Re-check `HashMapCompose` (12/12 accepted) and the provided instantiations, with the stub worlds described above.
- Re-run the tests against an unverified implementation, kept outside the repository.

## Validation done (2026-09-30, `ochr-core` 5e8dd8c0)

- Statements type-check with stub implementations.
- The composition lemmas are accepted, and the instantiations were checked.
- All sequences pass with a throwaway unverified implementation, which is not in the repository.
- `grade.sh` fails on the untouched skeleton and names the holes.
- Planted cheats are each caught with a specific reason:
  - a Lean `axiom` outside the block;
  - a `reject def`;
  - `sorry`;
  - an edited FIXED region;
  - `implemented by`;
  - a block comment hiding a FIXED region;
  - closing the block early;
  - redeclaring a built-in (`Unit`, `Nat`), library (`Lt`) or FIXED (`GetOf`) name;
  - in `ochr-2p`, `&` or assignment in the model.
- The sandbox grep finds none of the case studies.
- No verified solution was written.
