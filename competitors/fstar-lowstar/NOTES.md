# F* / Low* — in-place quicksort (NOTES)

## TL;DR

Fully verified in-place quicksort in **Low\*** over a mutable `LowStar.Buffer`,
extracted to **C via KaRaMeL** and compiled with **gcc**. The complete
functional spec is machine-checked with **no admits**:

- **memory safety** (Low\* typing),
- **modifies / disjoint-range framing** (`modifies (loc_buffer_from_to b lo hi)`),
- **permutation** (multiset-equality, `FStar.Seq.Properties.permutation`),
- **sortedness** (`forall i<=j. b[i] <= b[j]` over the sorted range).

Partition scheme: **Lomuto**, pivot = last element of the range.

## Toolchain + the `--cmi` version trap (which fix)

Per-folder Nix flake (`flake.nix` + `.envrc`, `use flake`). Pinned revs:

| Tool     | Rev / version                          | Source              |
|----------|----------------------------------------|---------------------|
| F\*      | **2026.03.24** (OCaml 5.4.1)           | `nixpkgs.fstar`     |
| KaRaMeL  | **`25027047c3f0`** (2025-03-19)        | `fetchFromGitHub`   |
| z3       | from `fstar.z3`                        | `nixpkgs`           |
| gcc      | nixpkgs default                        | `nixpkgs`           |

**Fix used: (A) — pin an F\* that still accepts `--cmi`, but realised through
nixpkgs instead of an F\* source build.**

The documented trap: KaRaMeL's `krmllib/Makefile` invokes `fstar.exe ... --cmi`,
and F\* later renamed `--cmi` → `--no_cmi` (commit `cbdfb8ea`, "Make --cmi
default to ON"), so a *current* F\* dies building krmllib with
`unrecognized option '--cmi'`.

Rather than build F\* from source (~10-20 min, no binary cache) and bisect for a
`--cmi`-accepting rev, I observed that **`nixpkgs.fstar` is already a cached
binary that still accepts `--cmi`** (the rename landed after the pinned
nixpkgs's F\*). So:

- The flake feeds **that one nixpkgs F\*** to KaRaMeL's derivation
  (`.nix/karamel.nix`, vendored from KaRaMeL upstream with the `fstar` input
  rewired). The **same** F\* both builds `krmllib` and verifies `Quicksort.fst`
  — a single shared F\*, exactly the intent of fix (A).
- KaRaMeL is pinned to `25027047c3f0`, the commit just before the F\*
  2025.03.25 tag, so its krmllib matches the F\* ulib. (The flake's locked
  nixpkgs actually resolves `fstar` to 2026.03.24, which *also* still accepts
  `--cmi` and verifies cleanly; KaRaMeL is built against that same F\*, so they
  stay consistent. Confirmed via `nix derivation show` — krmllib was built with
  `fstar-2026.03.24`.)

No F\* source build, no krmllib `Makefile` patch for `--cmi`.

### Two small KaRaMeL-build patches that *were* needed (in `.nix/karamel.nix`)

1. **`str`**: `lib/KString.ml` uses the stdlib `Str` module but `lib/dune` (at
   this rev) doesn't declare `str` as a dune library → link error
   `No implementations provided for ... Str`. Added `str` to `lib/dune` via
   `postPatch`.
2. **krmllib SMT admits**: re-verifying KaRaMeL's *trusted* C support library
   `krmllib` with this F\* trips a postcondition proof in the unrelated example
   module `LowStar.Lib.AssocList`. We don't depend on krmllib's proofs (only its
   extracted C headers/runtime), so the derivation sets
   `OTHERFLAGS=--admit_smt_queries true` **for the krmllib build only**. Our own
   quicksort is verified separately, with **no admits**.

## Exact commands

```sh
# enter the toolchain (puts fstar.exe, krml, gcc on PATH; sets KRML_HOME)
nix develop          # or: direnv allow

# 1. verify  2. extract C  3. compile  4. run (all via the Makefile)
make                 # == make run

# individually:
make verify          # fstar.exe --include $KRML_HOME/krmllib --z3rlimit 400 Quicksort.fst
make extract         # krml -skip-linking -skip-compilation -tmpdir out -no-prefix Quicksort Quicksort.fst
make compile         # gcc -O2 -Wall -I out -I $KRML_HOME/include -I $KRML_HOME/krmllib/dist/minimal out/Quicksort.c driver.c -o out/quicksort_test
make run             # ./out/quicksort_test  ->  "OK: sorted"
```

Building the KaRaMeL toolchain (first `nix develop`) takes a few minutes
(KaRaMeL OCaml build + krmllib). F\* itself is fetched from the binary cache.

## What is proven vs type-checked vs only compiled

| Property                                              | Status                          |
|-------------------------------------------------------|---------------------------------|
| Memory safety of all buffer accesses                  | **proven** (Low\* typing)       |
| `modifies (loc_buffer_from_to b lo hi)` (range frame) | **proven**                      |
| Permutation: output is a multiset-permutation of input| **proven** (count-based)        |
| Sortedness: output range is ascending                 | **proven**                      |
| Extraction to C (KaRaMeL)                             | **extracts**                    |
| C compiles (gcc -O2 -Wall, no warnings)               | **compiles**                    |
| C actually sorts (runtime smoke test, `driver.c`)     | **runs, passes**                |

No `admit`/`assume` anywhere in `Quicksort.fst`. The only admits in the whole
build are the krmllib SMT admits described above, which are in KaRaMeL's trusted
support library, not in the quicksort.

The extracted `out/Quicksort.c` is the genuine in-place algorithm: **zero heap
allocations** (`grep -c malloc out/Quicksort.c == 0`), the partition is a tail-
recursive scan, quicksort is two recursive calls on adjacent index ranges.

## How the disjoint-mutable-split is expressed (the comparison point)

This is the crux of the cross-system comparison.

**There are no sub-buffer *values* threaded through the recursion.** The buffer
`b` stays a single `LowStar.Buffer.buffer`. The "two disjoint mutable halves"
`[lo, p)` and `[p+1, hi)` are **index ranges over the same `b`**. Disjointness
is therefore *not* a typing/borrow fact — it is discharged **logically**, by the
heap + separation logic:

- Each call carries `modifies (loc_buffer_from_to b lo hi) h0 h1` — it touches
  *only* its range. `swap`, `partition`, `part_scan`, and `quicksort` each prove
  their `loc_buffer_from_to` clause; the single-index `swap`'s `loc_buffer b`
  effect is narrowed to a sub-range with `modifies_loc_buffer_from_to_intro`
  plus `swap_frame_lo'/swap_frame_hi` (the swap leaves indices outside the range
  untouched).
- When `quicksort` sorts the high half, the proof that the *already-sorted* low
  half stays intact is an explicit location-algebra argument:
  `loc_disjoint_loc_buffer_from_to` (the two ranges are disjoint *as locations*)
  + `modifies_buffer_from_to_elim` (so the low slice is byte-for-byte unchanged
  across the high recursion) + `loc_includes_loc_buffer_from_to` (so the three
  sub-modifies compose into one range modifies).

### The explicit-separation cost vs borrows

The whole `sortedness_glue` lemma (~80 lines) is a tax that an ownership/borrow
model would not levy:

- **Framing.** ~6 `modifies_buffer_from_to_elim` / `loc_disjoint` /
  `loc_includes` invocations *per recursive step* just to state "the other half
  didn't change". In Aeneas (borrows) or Idris (uniqueness) this is structural:
  you hand each recursive call a `&mut` to its own half / a unique view, and the
  type system *guarantees* the halves can't alias — there is nothing to prove.
- **Multiset preservation across a sub-range.** Because the proof works on the
  *whole-buffer* `as_seq`, "sorting the low half preserves the pivot bound on
  the low half" needs a count-based `perm_preserves_all_pred` lemma plus
  slice/count plumbing (`lemma_count_slice`, `lemma_index_slice`,
  `middle_perm`). With true sub-arrays the half would be its own value and these
  reindexing lemmas would largely vanish.
- **Pivot stability.** That `b[p]` survives both recursive calls is *three*
  separate `lemma_index_slice` frame facts (head of the frozen suffix `[p,n)`,
  last of the frozen prefix `[0,p+1)`), versus "the pivot isn't in either
  borrowed half" being a one-liner under borrows.

So Low\*'s answer to the partition step is: **the separation is real and fully
machine-checked, but it is paid for in explicit `modifies`/`loc` bookkeeping and
in slice-vs-absolute-index multiset lemmas** — precisely the overhead Ochre's
borrow-based model aims to discharge for free.

## Proof structure (`Quicksort.fst`)

- `swap` + `swap_is_permutation` — the only mutator; each swap is a
  transposition, so permutation comes "for free" from `lemma_swap_permutes`.
- `part_scan` — recursive Lomuto scan, maintains the loop invariant
  (`all_le`/`all_gt` regions around the pivot) and the range modifies.
- `partition` — runs the scan, parks the pivot at `store`, proves the partition
  property `[lo,p) <= b[p] <= (p+1,hi)`.
- `perm_preserves_all_pred`, `count_of_index`, `middle_perm`,
  `all_le_slice`/`all_ge_slice`, `sorted_range_frame` — the multiset/slice glue
  lemmas (the "Z3 won't do multisets unaided" obligations, discharged by
  counting).
- `sortedness_glue` — assembles whole-range sortedness from the two sorted
  halves + the cross-half pivot bounds, by case analysis on `(i,j)`.
- `quicksort` — the driver: partition, recurse on `[lo,p)` and `[p+1,hi)`,
  thread the framing + permutation + sortedness.

## Friction encountered

- The `--cmi` trap (above). Resolved by *not* building F\* and leaning on
  nixpkgs's cached, still-`--cmi`-accepting F\*.
- KaRaMeL `25027047`'s `lib/dune` missing `str`; krmllib AssocList proof failing
  under a newer F\* (both worked around in `.nix/karamel.nix`).
- `B.len b` is `GTot`, so it cannot be `let`-bound in a `Stack` function body
  (GHOST vs STATE) — inline it directly into the (ghost) framing-lemma calls.
- Range predicates had to be `unfold` for the slice-vs-absolute-index bridge
  lemmas (`all_le_slice` etc.) to see through to the underlying quantifiers.
- Sortedness needed `--z3rlimit 400`; the framing-only version verifies at the
  default rlimit.
