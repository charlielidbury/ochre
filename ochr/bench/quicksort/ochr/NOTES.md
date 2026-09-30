# Maintainer notes: the Ochr quicksort packages (`ochr`, `ochr-2p`)

For whoever runs the benchmark or writes it up. `make-sandbox.sh` does not copy this file into sandboxes. The shared design is `ochr/docs/05-agent-effort-benchmark.md`, the protocol is `ochr/bench/README.md` (§14 covers which checker revision a trial uses), and the shared tooling is `ochr/bench/common/ochr/`. The same notes are in `../ochr-2p/NOTES.md`.

## Design decisions

- **No fuel in the signature.** `QuickSort (n : Word) (s : &Slice(Word, n)) : Unit` is the SPEC signature. SPEC §2 allows a fuel argument; leaving it out lets the solver choose. Ochr has only structural recursion, so the solver writes a fuel helper, and Q1 then includes showing that fuel = length suffices. `ASSIGNMENT.md` says so.
- **Statements run the program on a copy.** Q1 is `(let c = *s; QuickSort(n, &c); Sorted(n, c))`, and Q2 is `(…; Perm(n, c, *s))`, where `*s` is the contents before.
- **Definitions.** `Sorted` is the SPEC's pairwise definition, with one extra hypothesis: the bound `hi : Lt(i, n)` that reading `a[i]` needs, which `i < j < n` implies. `Perm` uses the library's `Count`, whose lemmas (`CountSwap`, `CountJoin`, `CountSet`) the solver may use. Those lemmas are library, not solution.
- **`ochr-2p` equivalence is mechanical.** `QuickSortSorted` and `QuickSortPerm` are the `ochr` statements, character for character, with proofs provided. The provided lemmas are `SortedFromModel` and `PermFromModel` (block `QuicksortCompose`), generic in the sort and the model. Instantiating them was checked against a stub sort and against the repo's case-study `QS`, with the hypotheses as parameters.
- **The pure model.** It is `SortModel(n, v : Slice(Word, n))`, a model function on views. The grader forbids `&` and assignment in the block `QuicksortModel`.
- **Tests.** The 29 SPEC cases are transcribed by `common/ochr/gen_tests.py`, each as a whole-array `Id` comparison, plus one negative test (`TestReject_unsorted`). They take about 6 s in the compiled checker with a Lomuto quicksort at fuel = length.

## Ways the language makes this condition harder or different

1. **No automation.** Every case split, induction and rewrite is written by hand. This is the largest confound in any cross-system comparison. `ochr` against `ochr-2p` is immune to it.
2. **No recursion on a measure.** The solver needs fuel, plus a proof that fuel = length is enough.
3. **Sub-borrows only through `WithSplit`.** The two recursive calls happen inside the closure passed to `WithSplit`. A closure that hands the recursion on to a nested closure may need `clone`, because a closure may not move a captured value out.
4. **Unary `Word`.** Tests are capped at 24 elements and values below 99 for every condition (bench-spec, 72ced6c2). The uncapped set (64 elements) took about 100 s.
5. **Element borrows.** `&E` is not yet well formed for a type variable `E`, so the library's `GetMut` exists only for `Word` elements, which is enough here.
6. **No projections of stuck pairs.** `t.1` on a pair that is not yet a constructor value is an error. This matters for the model if it returns pairs.
7. **Checker soundness.** The checker is a prototype, and earlier revisions had closed proofs of `False`. The human check and README §14 (re-grade on the latest checker) guard against solutions that rely on a bug.
8. **Moving target.** Planned changes (for example D66: `Prop : Type₁`, and `&A` for any `A : Type₀`) can change the library or the typing of the skeletons.

## When the checker or library changes

- Run `python3 ../../common/ochr/gen_tests.py Quicksort.lean --check` in both packages.
- Make a fresh sandbox (`./make-sandbox.sh DEST`) and check that `DEST/grade.sh` fails on the untouched skeleton for holes only: every FIXED statement should be rejected only for `unknown constant TODO`, `QuickSort`, `SortModel` and the like.
- Re-check the generic lemmas in `QuicksortCompose`; they must be accepted.
- If a library block used by the skeleton is renamed or split, `common/ochr/sandbox.py` extracts blocks by name and fails loudly when one is missing.
- If a new case-study name appears, add it to `FORBIDDEN` in `sandbox.py`.

## Validation done (2026-09-30, `ochr-core` 5e8dd8c0)

- Statements type-check with stub implementations.
- The composition lemmas are accepted, and their instantiations were checked.
- All test vectors pass with the case-study sort.
- `grade.sh` fails on the untouched skeleton and names the holes.
- Planted cheats are each caught with a specific reason:
  - a Lean `axiom` outside the block;
  - a `reject def`;
  - `sorry`;
  - an edited FIXED region;
  - `implemented by`;
  - a block comment hiding a FIXED region;
  - closing the block early;
  - redeclaring a built-in (`Unit`, `Nat`), library (`Lt`) or FIXED (`Sorted`) name;
  - in `ochr-2p`, `&` or assignment in the model.
- The sandbox grep finds none of the case studies.
- No verified solution was written.
