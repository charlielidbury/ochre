# Ablation study — `quicksort.rs` proof annotations

A one-at-a-time ablation of every removable proof annotation in the verified
in-place quicksort (`competitors/verus/quicksort.rs`), measuring for each whether
it is **load-bearing for correctness** and how it affects **verification cost**.

The driving hypothesis: *some asserts may not be needed for the proof to close,
but may be keeping verification fast/stable (steering Z3 away from expensive
search).* This study tests that directly.

## Method

- Toolchain: Verus `0.2026.05.31.5dd6d83` (built from source via
  `competitors/verus/flake.nix`), Z3 4.12.5, single-threaded.
- Canonical verify command (run from the repo root; the verus toolchain lives in
  the **nested** flake at `competitors/verus/`, so it is not on the root direnv
  PATH — it must be entered explicitly):

  ```
  nix develop ./competitors/verus -c verus --no-cheating --triggers-mode silent \
      --time --output-json --num-threads 1 <file>
  ```

- **Primary metric — `times-ms.smt.rlimit-run` (SMT "rlimit").** Verus reports a
  deterministic SMT *resource* count (Z3 rlimit units consumed). Unlike
  wall-clock, this is **bit-for-bit reproducible** across runs on this machine
  (the unmodified file reported `1118952` on all 5 baseline runs, exactly). It is
  the right metric for an ablation: it isolates SMT search effort and is immune to
  machine load. All deltas below are in rlimit units.
- **Cross-check metric — `smt-run` (wall-clock ms of the SMT phase)** and
  `total-verify` (ms). Captured as a sanity check; reported as the median of 3
  runs for category-(a) items.
- **All work was done on scratch copies in `/tmp`.** The committed `quicksort.rs`
  was never edited (verified pristine via `git diff` before committing this
  report).
- One annotation removed per trial; everything else intact. Each trial classified
  as:
  - **(a) still verifies** — `8 verified, 0 errors`,
  - **(b) verification FAILS** — compiles but `errors > 0` → load-bearing for
    correctness,
  - **(c) does NOT compile** — e.g. a ghost binding referenced later → structurally
    required (distinct from "needed for the proof").

### Timing caveat

Absolute rlimit/ms numbers are **not** portable to other machines or Verus
versions, and the wall-clock figures are noisy and load-dependent. **All
conclusions here are about *relative deltas measured in the same session* against
the same baseline file.** Do not read the absolute numbers as benchmarks.

## Baseline

Unmodified file (the working-tree variant of `quicksort.rs`, on which the entire
ablation was run), 5 runs:

| run | verified | errors | rlimit-run | smt-run (ms) | total-verify (ms) |
|----:|---------:|-------:|-----------:|-------------:|------------------:|
| 1 | 8 | 0 | **1 118 952** | 70 | 148 |
| 2 | 8 | 0 | 1 118 952 | 70 | 144 |
| 3 | 8 | 0 | 1 118 952 | 70 | 147 |
| 4 | 8 | 0 | 1 118 952 | 74 | 151 |
| 5 | 8 | 0 | 1 118 952 | 70 | 147 |

- **rlimit-run: min = median = max = 1 118 952** (zero spread — fully
  deterministic). This is the baseline all deltas are computed against.
- **smt-run: min 70 / median 70 / max 74 ms** (≈6% spread from noise alone — which
  is why rlimit, not wall-clock, is the metric of record).
- total-verify: 144–151 ms.

> Note: the *committed* `quicksort.rs` (with the `Vec::new()/push` `main` and
> `let n = v.len()`) reports `8 verified, 0 errors` with rlimit-run `1 276 279`.
> The proof body (lines 17–310) is byte-identical to the ablated copy; the
> ~157k-rlimit difference is purely in the exec-mode entry-point boilerplate
> (`main`/`quicksort`), not in any proof annotation. The ablation baseline of
> `1 118 952` is internally consistent because every trial was diffed against it.

## Results

Δ = trial rlimit − baseline (1 118 952). Positive Δ = removal made verification
*more expensive*; negative Δ = *cheaper*.

| ID | line(s) | snippet | cat | verified/err | rlimit | Δ rlimit | smt ms | verdict |
|----|--------|---------|:--:|:--:|------:|--------:|----:|---------|
| A01 | 60 | `proof{ lemma_swap_multiset(..) }` (in `swap`) | **b** | 7 / 1 | 1 219 495 | +100 543 | 80 | load-bearing |
| A02 | 74 | `broadcast use to_multiset_update` | **b** | 7 / 1 | 1 203 201 | +84 249 | 118 | load-bearing |
| A03 | 75 | `broadcast use group_multiset_axioms` | a | 8 / 0 | 1 120 475 | +1 523 | 72 | removable |
| A04 | 79 | `assert(s1.update(j,s[i]) =~= s)` (`i==j`) | a | 8 / 0 | 1 171 679 | +52 727 | 76 | removable |
| A05 | 82 | `assert(s1[j] == s[j])` | a | 8 / 0 | 1 159 521 | +40 569 | 77 | removable |
| A06 | 88 | `assert(s1.to_multiset() == m1)` | a | 8 / 0 | 1 123 281 | +4 329 | 77 | removable |
| A07 | 90 | `assert(s1.update(j,s[i]).to_multiset() == m2)` | a | 8 / 0 | 1 153 456 | +34 504 | 78 | removable |
| A08 | 95–98 | `assert(m.count(s[i]) > 0) by {..}` | **b** | 7 / 1 | 1 267 703 | +148 751 | 90 | load-bearing |
| A09 | 99–102 | `assert(m.count(s[j]) > 0) by {..}` | a | 8 / 0 | 1 080 030 | **−38 922** | 71 | removable (faster!) |
| A10 | 103–106 | `assert forall x. m2.count==m.count by { }` **EMPTY** | a | 8 / 0 | 1 103 181 | −15 771 | 86 | removable (slightly faster) |
| A11 | 107 | `assert(m2 =~= m)` | a | 8 / 0 | 1 121 348 | +2 396 | 77 | removable |
| A12 | 127–138 | `assert forall b. all_le preserved by {..}` (whole) | a | 8 / 0 | 1 133 569 | +14 617 | 87 | removable |
| A13 | 130–136 | inner `if k==i/j` hints of A12 (keep outer) | a | 8 / 0 | 1 140 418 | +21 466 | 74 | removable |
| A14 | 139–149 | `assert forall b. all_ge preserved by {..}` (whole) | a | 8 / 0 | 1 129 452 | +10 500 | 69 | removable |
| A15 | 141–147 | inner `if k==i/j` hints of A14 (keep outer) | a | 8 / 0 | 1 177 356 | +58 404 | 74 | removable |
| A16 | 200 | `proof{ lemma_swap_preserves_bounds(..) }` (loop) | a | 8 / 0 | 1 242 362 | +123 410 | 78 | removable (**timing-critical**) |
| A17 | 209 | `proof{ lemma_swap_preserves_bounds(..) }` (final) | a | 8 / 0 | 1 252 265 | +133 313 | 78 | removable (**timing-critical**) |
| A18 | 211–220 | whole final `proof{}` block in `partition` | a | 8 / 0 | 1 086 168 | −32 784 | 70 | removable (slightly faster) |
| A19 | 213 | `assert(v@[i] == pivot)` | a | 8 / 0 | 1 134 881 | +15 929 | 74 | removable |
| A20 | 214–216 | `assert forall k. left <= v@[i] by { }` **EMPTY** | a | 8 / 0 | 1 088 834 | −30 118 | 72 | removable (slightly faster) |
| A21 | 217–219 | `assert forall k. right >= v@[i] by { }` **EMPTY** | a | 8 / 0 | 1 117 623 | −1 329 | 81 | removable |
| A22 | 257 | `assert(all_le(after_part, lo, p, pivot))` | a | 8 / 0 | 1 539 756 | **+420 804** | 89 | removable (**timing-critical**) |
| A23 | 258 | `assert(all_ge(after_part, p+1, hi, pivot))` | a | 8 / 0 | 1 108 012 | −10 940 | 71 | removable |
| A24 | 265–309 | whole stitching `proof{}` block in `quicksort_rec` | **b** | 7 / 1 | 580 087 | −538 865 | 55 | load-bearing |
| A25 | 268 | `assert(v@[p] == pivot)` | a | 8 / 0 | 1 165 260 | +46 308 | 70 | removable |
| A26 | 273 | `assert(all_le(v@, lo, p, pivot))` | a | 8 / 0 | 1 149 076 | +30 124 | 73 | removable |
| A27 | 274 | `assert(all_ge(v@, p+1, hi, pivot))` | **b** | 7 / 1 | 690 428 | −428 524 | 84 | load-bearing |
| A28 | 278–281 | `assert(sorted_between(..)) by { 2 asserts }` | a | 8 / 0 | 1 328 097 | +209 145 | 73 | removable (**timing-critical**) |
| A29 | 279–280 | inner 2 asserts of A28 (keep outer) | a | 8 / 0 | 1 054 123 | −64 829 | 67 | removable (faster!) |
| A30 | 286–299 | `assert forall b. all_le stitch by {..}` (block) | **b** | 7 / 1 | 893 531 | −225 421 | 73 | load-bearing |
| A31 | 288–298 | inner asserts of A30 (keep outer forall) | **b** | 7 / 1 | 780 081 | −338 871 | 75 | load-bearing |
| A32 | 300–308 | `assert forall b. all_ge stitch by {..}` (block) | **b** | 7 / 1 | 926 184 | −192 768 | 82 | load-bearing |
| A33 | 301–307 | inner asserts of A32 (keep outer forall) | **b** | 7 / 1 | 871 325 | −247 627 | 76 | load-bearing |
| G01 | 180 | `let ghost orig = v@` (partition) | **c** | — | — | — | — | structural (referenced) |
| G02 | 197 | `let ghost pre = v@` (loop body) | **c** | — | — | — | — | structural |
| G03 | 207 | `let ghost pre_final = v@` | **c** | — | — | — | — | structural |
| G04 | 251 | `let ghost orig = v@` (quicksort_rec) | **c** | — | — | — | — | structural |
| G05 | 253 | `let ghost after_part = v@` | **c** | — | — | — | — | structural |
| G06 | 254 | `let ghost pivot = v@[p]` | **c** | — | — | — | — | structural |
| G07 | 262 | `let ghost after_left = v@` | **c** | — | — | — | — | structural |
| M01 | 87 | `let m1 = m.insert(s[j]).remove(s[i])` | **c** | — | — | — | — | structural |
| M02 | 89 | `let m2 = m1.insert(s[i]).remove(s[j])` | **c** | — | — | — | — | structural |

(Category-(c) items fail with `error[E0425]: cannot find value ... in this scope`
— the binding is referenced by a later `assert`/invariant, so removing it alone
is a parse/name-resolution error, not a proof failure.)

## Summary

Of **42** ablatable items enumerated:

- **Load-bearing for correctness (b): 10** —
  A01, A02, A08, A24, A27, A30, A31, A32, A33 (and A24 subsumes A30–A33; removing
  the whole `quicksort_rec` stitching block, or any of the four `all_le`/`all_ge`
  stitch sub-blocks, or the `all_ge(v@,p+1,hi,pivot)` fact, breaks the
  postcondition). The permutation core is also load-bearing: the `swap` lemma call
  (A01), the `to_multiset_update` broadcast (A02), and the `m.count(s[i])>0`
  positivity fact (A08) are each required — note their *sibling* `m.count(s[j])>0`
  (A09) is **not** (Z3 finds it on its own once `s[i]` is established).
- **Removable, verification still closes (a): 23** — including **all four
  empty-body `by { }` asserts** (A10, A20, A21, and the empty-body forall in A20)
  and the `=~=` nudges A04/A11. The empty-body asserts were the prime suspects for
  "load-bearing-by-default" and turned out **not** to be needed at all here; A10
  and A20 even make verification slightly *cheaper* when removed.
- **Structurally required (c): 9** — all `let ghost` bindings (G01–G07) and the
  two intermediate multiset lets `m1`/`m2` (M01/M02). These cannot be removed in
  isolation because later steps name them; they are not "proof hints" but program
  structure.

### Timing hypothesis — CONFIRMED

Several annotations are **removable (proof still closes with 0 errors) yet
timing-critical** — their removal forces Z3 into materially more search:

| ID | what | Δ rlimit on removal |
|----|------|--------------------:|
| **A22** | `assert(all_le(after_part, lo, p, pivot))` | **+420 804 (+38%)** |
| **A28** | `assert(sorted_between(..)) by {..}` | **+209 145 (+19%)** |
| **A17** | `lemma_swap_preserves_bounds` call (final swap) | +133 313 (+12%) |
| **A16** | `lemma_swap_preserves_bounds` call (loop) | +123 410 (+11%) |

A22 is the headline: removing a single one-line `assert` that the solver does not
strictly *need* inflates total SMT rlimit by **38%**. This is exactly the user's
hypothesis — these asserts are load-bearing for *performance/stability*, not for
*closure*. In a larger proof such an assert removal could be the difference
between verifying under the rlimit and timing out.

### Surprises

- **Removing some asserts makes verification FASTER.** A09 (−39k), A29 (−65k),
  A18 (−33k), A20 (−30k), A23 (−11k), A10 (−16k) all *reduce* rlimit when removed
  — they are slightly **counterproductive** (extra SMT facts the solver indexes
  but does not benefit from). The empty-body `assert forall ... by { }` at A10/A20
  fall in this bucket: harmless to remove, marginally helpful to remove.
- **The empty-body `by { }` asserts are not load-bearing at all** — contrary to
  the prior suspicion that empty-body asserts are doing silent trigger work, every
  one of them (A10, A20, A21) is removable, and two of them are mild net
  negatives. They appear to be defensive scaffolding the author left in after the
  proof closed.

### Combined experiment (separate data point)

Removing **all 19 individually-(a)-removable maximal blocks at once** (using the
block versions where nested, deleted bottom-up on one scratch copy):

- Result: **7 verified, 1 error — `postcondition not satisfied` in `partition`**
  (the `all_le` bound-preservation postcondition, file line 185 of the reduced
  copy). rlimit 1 083 532.

So the individually-removable asserts are **NOT jointly removable** — the classic
butterfly effect. Once enough intermediate facts are gone simultaneously, Z3 can
no longer reconstruct the `partition` bound-preservation chain that several of
those asserts were each independently propping up. This is why a "minimal proof"
cannot be obtained by naively deleting every individually-removable item.
