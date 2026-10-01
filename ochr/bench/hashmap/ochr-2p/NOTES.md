# Maintainer notes: the Ochr hashmap packages (`ochr`, `ochr-2p`)

For whoever runs the benchmark or writes it up. `make-sandbox.sh` does not copy this file into sandboxes. The shared design is `ochr/docs/05-agent-effort-benchmark.md`, the protocol is `ochr/bench/README.md` (§14 covers which checker revision a trial uses), and the shared tooling is `ochr/bench/common/ochr/`. The same notes are in `../ochr-2p/NOTES.md`.

## The generic value type (D66, docs/09 §6)

The SPEC is generic in the value type `V` (2adc7147), with Ochr's read API amended at c04914fd, and both packages now follow it (docs/09 §6, lane arrays-e, 2026-10-01): `Bucket(V)`; `contains(&m, k) : Bool`; `get(&m, k, h : Contains(*m, k)) : &V`, a borrow used read-only, with the key required present as for `get_mut`; `insert`/`remove → Opt(V)`, the value moved out; `get_mut → &V`. Buckets are reached through the arrays library's generic `GetMut(Bucket(V), …)`; `SlotMut` is gone. Properties that mention `get` are split into a part about `contains` (a) and a part about the value read through `get` (b), as SPEC §3 says; a (b) property takes the presence proofs its reads need as hypotheses. A test's `get` op with `expect: null` checks that `contains` is false; with `expect: w`, it reads the value through `MapGet` (whose precondition `refl` proves only when the key is present) and compares it with `w`.

## Design decisions

- **The capacity lives in the type.** `Map(V, cap) = MapOf(Cells(Bucket(V), cap))`, i.e. `MkMap(slots : Array(Bucket(V), cap), len : Word)`. `MapOf` takes the array's model type as a parameter.
- **Provided in `HashMapSpec`:**
  - `Opt(V)`, `IsSomeB` (whether an `Opt` holds a value) and `IsTrue` (a boolean as a proposition);
  - `Grow` and `Shrink`, the right-hand sides of H12 and H13, over `contains(m, k)`;
  - `Idx` (`k mod cap` by counting) with its bound `IdxLt`, standing in for the `%` and its bound that other systems get from their libraries or automation;
  - `EqDec`, key comparison with evidence.
- **Names.** The operations are `MapNew`, `MapLen`, `MapContains`, `MapGet`, `MapInsert`, `MapRemove` and `MapGetMut`, because the arrays library already declares `GetMut`. `ContainsOf` and `LenOf` run `MapContains` and `MapLen` on a copy of a map value, and `Contains(V, cap, m, k)` is `IsTrue(ContainsOf(V, cap, m, k))`; the properties observe through them, and through `clone(*MapGet(…))` for values.
- **Properties run on a copy.** Every property runs the operation on a copy (`let c = *m; op(V, cap, &c, …); …`). H17a, H17b and H18 are stated as `Eq(Map(V, cap), (let c = *m; MapContains(V, cap, &c, k); c), *m)` (and likewise for a read-only `get`, and for `len`), for every map.
- **Tests.** Each of the five sequences is one test at `V := Word`: the ops run on one map, and their results and lengths are collected in a `Trace` (`TOp` for insert and remove, `THas` for an absent get, `TGet` for a present one, `TWrite` for get_mut) and compared with the expected trace. There is one negative test. With an unverified implementation the grade takes about 18 s in a sandbox.
- **`ochr-2p` is generated.** `common/ochr/gen_hashmap_2p.py` builds it from `ochr`, so the representation, signatures, H1–H18 statements and tests are byte-identical.
- **What `ochr-2p` adds:**
  - the pure model, generic in `V`: `MMap(V)`, `MNew`, `MLen`, `MGet` (an `Opt(V)`), `MInsert`, `MRemove`, `MWrite` and `MInv`, and `Abs`, which works on a map's buckets as a view and so is a model function;
  - M4–M15, the H-properties about the model;
  - `AbsOf`, provided, via `SlotsOf(V, cap, clone(m))` and `LenField`;
  - the agreement, under the concrete `Inv`: `AbsNew`, `AgreeLen`, `AgreeContains`, `AgreeGet` (`Some` of the value read through get is `MGet`), `AgreeInsert(+Result)`, `AgreeRemove(+Result)` and `AgreeWrite`;
  - `AbsInv`.
- **How H4–H15 are proved in `ochr-2p`.** They are provided as instances of eighteen generic lemmas (`HashMapCompose`), one per (a) or (b) part, generic in the operations and the model; each parameter is itself generic in `V` (a `Π(V : Type). …`), so the instances pass the solver's declarations by name. The lemmas are proved (all accepted): an (a) part rewrites with `AgreeContains` and the model property, and a (b) part chains `AgreeGet`, the agreement of the operation and the model property with `trans`, which `Eq` on two `Some`s turns into the equation of the values. H1–H3 and H16–H18 concern the in-place map only, and the solver proves them in both conditions.
- **Why the model operations return only the new map.** The checker has no projections of stuck pairs. The values `insert` and `remove` return are tied to `MGet` by `AgreeInsertResult` and `AgreeRemoveResult`, which is why H7 and H10 have no model property.

## Ways the language makes this condition harder or different

1. **No automation.** Every case split, induction and rewrite is written by hand. This is the largest confound in any cross-system comparison. `ochr` against `ochr-2p` is immune to it.
2. **No shared borrows.** `MapContains`, `MapGet` and `MapLen` take `&`, so H17 and H18 are real obligations: the proof follows the `GetMut` borrow down and shows the bucket is put back. Rust's `&self` makes them free.
3. **`get` and `get_mut` preconditions.** `Contains(V, cap, *m, k)` must reach the bucket level. In the throwaway implementation it passes straight through: with `MapContains` written as `BContains` of the bucket borrow, the precondition of a bucket-level get, `IsTrue(BContainsV(V, *b, k))`, is the same type by evaluation (the bucket is the same sealed read). `ASSIGNMENT.md` does not hint at it.
4. **`Map(V, cap)` does not record `cap ≥ 1`.** Each operation has to test `cap` (or use `LtDec`) to get `IdxLt`'s premise. `ASSIGNMENT.md` says how.
5. **No projections of stuck pairs.** This shaped the `ochr-2p` model interface (above).
6. **The `ochr-2p` interface is large.** It has 9 model definitions, 10 model lemmas, 9 agreements and `AbsInv`, against 25 property declarations in `ochr`. That is inherent to data refinement onto an abstract map, but the FIXED choices shape the ablation:
   - the model operations return only the new state;
   - `Abs` works on views;
   - there is a separate model invariant.
7. **Unary `Word`.** Keys are at most 23 and values at most 99 for every condition, and concrete runs are slow for large numbers.
8. **Unbounded `Word`.** `len` cannot overflow, so there is no bounded-integer allowance, unlike Aeneas and Verus.
9. **Checker soundness.** The checker is a prototype, and earlier revisions had closed proofs of `False`. The human check and README §14 (re-grade on the latest checker) guard against solutions that rely on a bug. Redeclaring `Nat` or `Unit` is accepted by the checker; the grader forbids redeclaring any built-in, library or FIXED name.
10. **Moving target.** Changes to the checker or the arrays library can change the typing of the skeletons (docs/09 removed the read and write natives: a read through `GetMut` is a sealed program at an unknown index, so proofs use `GetMutRead`/`GetMutSet`).

## When the checker or library changes

- In both packages, run `python3 ../../common/ochr/gen_tests.py HashMap.lean --check`.
- Run `python3 ../../common/ochr/gen_hashmap_2p.py --check`.
- Make a fresh sandbox and check that `grade.sh` fails on the untouched skeleton for holes only.
- Check that `HashMapCompose` is still accepted (18/18) and the provided instantiations type-check.
- Re-run the tests against an unverified implementation, kept outside the repository.

## Validation done (2026-10-01, the generic API, lane arrays-e)

- In a sandbox of each package, the untouched skeleton grades as failing on its holes only (it names them; the five tests fail only because the operations are holes), and every FIXED declaration is accepted, including in `ochr-2p` the eighteen `HashMapCompose` lemmas and the eighteen provided instances.
- With a throwaway unverified implementation (association-list buckets, `Inv := ⊤`, outside the repository), all five sequences pass and the negative test is rejected, in both packages.
- No verified solution was written (as for the word-valued version).

## Earlier validation (2026-09-30, `ochr-core` 5e8dd8c0, the word-valued packages)

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
