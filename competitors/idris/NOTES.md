# Idris 2 — quicksort, fully proven (sorted ∧ permutation)

Two files:

- **`Quicksort.idr`** — the headline deliverable: quicksort on `List Nat` with a
  **complete machine-checked proof** that the output is **sorted** AND a
  **permutation** of the input. No `sorry` / `believe_me` / `assert_total` /
  `assert_smaller` / `idris_crash` / `really_believe_me` / postulate anywhere.
- **`QuicksortLinear.idr`** — the original in-place QTT/linear-array version,
  kept as the "QTT can't express disjointness" data point. It runs and is
  memory-safe by linearity, but its functional spec cannot even be *stated*
  over `Data.Linear.Array.LinArray` (see "Why the linear route can't carry the
  proof" below), so it is not proven.

## Exact build / verify commands

Type-check + build both modules (the command the flake's `buildPhase` runs):

```
nix develop ./competitors/idris -c idris2 --build competitors/idris/quicksort.ipkg
```

Reproducible derivation (same thing, sandboxed):

```
nix build ./competitors/idris#quicksort
```

Type-check **just the proof file**:

```
nix develop ./competitors/idris -c idris2 --check competitors/idris/Quicksort.idr
```

Confirm the headline theorems are total and complete (no holes):

```
nix develop ./competitors/idris -c sh -c \
  'cd competitors/idris && printf ":total quicksortSorted\n:total quicksortPerm\n" | idris2 --no-banner Quicksort.idr'
# => Quicksort.quicksortSorted is total
# => Quicksort.quicksortPerm is total
```

Run the demo (sorts `[5,2,9,1,5,6,3,8,7,0,4]`):

```
nix develop ./competitors/idris -c sh -c \
  'cd competitors/idris && idris2 --build quicksort.ipkg && ./build/exec/quicksort'
# => sorted: [0, 1, 2, 3, 4, 5, 5, 6, 7, 8, 9]
```

(Flake note: Nix flakes only see git-tracked files; the orchestrator must
`git add competitors/idris/` before `nix build` / `nix develop` against this
sub-flake will evaluate. Everything here is verified working against the pinned
`idris2-0.7.0`, which ships `contrib`.)

## What is proven (the theorems)

The two headline theorems, exported from `Quicksort.idr`:

```idris
||| The output of `quicksort` is sorted (ascending).
quicksortSorted : (xs : List Nat) -> Sorted (quicksort xs)

||| The output of `quicksort` is a permutation (multiset-equal) of the input.
quicksortPerm   : (xs : List Nat) -> Perm xs (quicksort xs)
```

with the specifications:

```idris
-- ascending-ness: each head is <= every later element, tail itself sorted
data Sorted : List Nat -> Type where
  SNil  : Sorted []
  SCons : All (\y => LTE x y) xs -> Sorted xs -> Sorted (x :: xs)

-- multiset equality via occurrence counts; this IS "ys is a permutation of xs"
cnt  : Nat -> List Nat -> Nat                 -- number of occurrences
Perm : List Nat -> List Nat -> Type
Perm xs ys = (v : Nat) -> cnt v xs = cnt v ys
```

`Perm` as "every value occurs equally often in both lists" is a standard,
faithful characterisation of permutation: two finite lists are
multiset-equal iff one is a permutation of the other. Both theorems, the worker
`qsAux`, and `quicksort` itself are reported **total** by the checker (verified
with `:total`), so the proofs are genuine — not stuck on holes or admitted.

### Proof architecture

- **Permutation** is tracked by occurrence counts (`cnt`). Every list operation
  used has a clean counting lemma: `countAppend` (count distributes over `++`),
  `countSplit` (partition halves account for each element exactly once),
  `partitionPerm`, and `consShift` (pivot moves from the front to between the
  halves). These compose with `permCons` / `permAppend` / `permTrans`. Because
  `Perm xs ys` is a *reducible function type*, Idris can't recover the list
  arguments from a `Perm`-typed value by unification, so the combinators take
  the lists as explicit arguments.
- **Sortedness** is rebuilt at the join: `sortedJoin` proves
  `Sorted (lo ++ pivot :: hi)` from the two sorted halves plus the bounds
  `All (<= pivot) lo` and `All (>= pivot) hi`.
- **Bounds survive sorting.** After recursively sorting a partition half the
  result is a *permutation* of that half, so its bound must be re-derived. The
  `BoundedBy p xs = (v) -> cnt v xs ≠ 0 -> p v` formulation transports across a
  `Perm` for free (`boundedPerm`) — same multiset ⇒ same occurring values ⇒ same
  bound — and then reifies into a full `All p` proof (`boundedToAll`).
- **Termination** is structural: `qsAux` recurses on a `Nat` fuel ≥ the list
  length, with `leLength` / `gtLength` proving the partition halves are no
  longer than the input so the fuel always suffices. No `assert_smaller`.
- Boolean `<=`/`==` on `Nat` are reflected into propositional `LTE` / `=` by
  hand (`lteTrue`, `lteFalse`, `eqNatSound`, …) so every branch reduces
  predictably.

## Representation: why `List Nat`, and why the linear route can't carry the proof

The previous deliverable used `Data.Linear.Array.LinArray Int`, the linear
mutable-array type. **That representation makes the spec unstateable, never mind
unprovable:**

- `LinArray` carries **no length in its type** and **no element invariants**.
  There is nowhere to hang `Sorted` or `Perm`.
- Its reads are `mread : (1 _) -> Int -> Res (Maybe t) (...)` — `Int`-indexed and
  returning `Maybe` (out-of-range ⇒ `Nothing`). So you can't even talk about
  "the element at index i" as a total, in-range value inside a proof.
- The linear handle is consumed and replaced on every read/write, so the
  array's *contents* are never a first-class value a theorem can range over —
  only the opaque handle is.

To get a machine-checked proof we need the data and its invariants to live *in
types*. We therefore prove over an inductive `List Nat`, where:

- `Nat` is a concrete decidable total order (clean `LTE`), and
- every operation (`le`, `gt`, `++`, `cnt`) reduces definitionally, which is
  what lets the equational proofs go through.

`Nat` (not machine `Int`) is deliberate: `LTE`/`==` reflection and the counting
lemmas all rely on structural recursion over `Nat`, which `Int` (a primitive)
does not offer.

### Closeness to in-place / index-based quicksort

Per the brief, we kept the divide-and-conquer **shape**: the input is
partitioned into a `<= pivot` half (`le`) and a `> pivot` half (`gt`), the two
halves are sorted by independent recursive calls, and the results are
recombined as `lo ++ pivot :: hi`. That is genuine quicksort, not a `List` merge
or insertion sort in disguise. What we gave up — and the brief permitted — is
*mutation in place*: the halves are produced by two passes over one list rather
than by mutating disjoint sub-ranges of one buffer. The proof wins; in a pure
dependently-typed setting an index-into-`Vect`-with-`Fin` in-place version buys
nothing for the proof and costs a great deal of `Fin`/bounds bookkeeping.

## The original comparison point (still valid, see `QuicksortLinear.idr`)

The in-place QTT version is preserved. The key observation is unchanged and is
*why* it can't be proven here:

**QTT uniqueness gives temporal safety but not spatial reasoning.** A linear
`LinArray` handle is guaranteed to be used exactly once (no aliasing, no
use-after-free), but the type system cannot express that two *index ranges over
the same live array* are disjoint. There is no `split_at_mut` analogue — you
cannot conjure two disjoint `&mut` sub-views from one quantity-1 value. So in
the linear version the two partition halves are sorted **sequentially on one
handle**, their disjointness a runtime fact about indices that the checker never
sees. Rust borrows (`split_at_mut`) and Low* separation (`disjoint`/`modifies`)
both make sub-region disjointness *static and checkable*, which is exactly what
would let the two recursive halves be reasoned about — including proven — while
mutating in place. Idris/QTT cannot, so the in-place version is memory-safe but
unverifiable, and the proof had to move to a value-typed representation.

## Friction encountered (proof side)

1. **`Perm` is a reducible alias, so it's not injective for unification.**
   `permTrans`/`permCons`/`permAppend` had to take the list arguments
   explicitly — Idris cannot recover `xs`,`ys` from a value of type
   `Perm xs ys` because that type reduces to a function type.
2. **Boolean vs propositional order.** Prelude `<=`/`==` on `Nat` are `Bool`;
   every proof step needs them reflected into `LTE`/`=`. `0 <= y` and `S k <= 0`
   don't reduce for abstract arguments, so the reflection lemmas must case-split
   on both operands (and dispatch the impossible `True = False` cases via
   `Uninhabited`).
3. **`let`-bound dependent pairs.** Binding `(out ** (s, p)) = qsAux …` in a
   `let` failed to parse; the recursive results had to be scrutinised with
   nested `case` instead.
4. **Bound re-derivation after sort.** The subtle proof step: sorting a
   partition half *permutes* it, so `All (<= pivot)` on the original half does
   not directly give `All (<= pivot)` on the sorted result. The `BoundedBy`
   (count-based) phrasing is what makes that bound ride across the permutation
   cleanly.

## Friction encountered (original linear version, `QuicksortLinear.idr`)

- **No length in the type / `Maybe` reads** — already the headline blocker above.
- **Linearity ⊗ control flow.** Plain/pattern `let` elaborate their RHS at the
  enclosing multiplicity, which rejects a quantity-1 variable; keep the handle
  in linear position by destructuring every step with the `Res` `#`-pattern.
- **Misleading linearity error under name ambiguity.** A helper named `swap`
  failed only because of a clash with `Builtin.swap`; the resolver reported a
  bogus "use of linear name in non-linear context". Renaming to `swapAt` fixed
  it.
- **No destructor for `LinArray`.** A quantity-1 handle can't be dropped;
  `toIArray` (freeze to immutable `IArray`) is the only way to finish.
