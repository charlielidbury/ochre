# Aeneas — in-place quicksort (Rust → Charon → Aeneas → Lean, **proven**)

This is the full Aeneas soundness chain: an in-place Rust quicksort is translated
by Charon → Aeneas into a pure Lean model, and **that generated model is proved
sorted + permutation in Lean**, using Aeneas's own proof framework. The theorem
is stated about the *generated* function, so proving it certifies the Rust.

## Layout

```
competitors/aeneas/
├── flake.nix              # charon + aeneas + cargo (nightly) + elan
├── .envrc                 # use flake
├── quicksort/             # the Rust crate (Lomuto partition + split_at_mut)
│   ├── src/lib.rs
│   ├── Cargo.toml
│   └── quicksort.llbc     # Charon output (committed artifact)
├── lean-gen/
│   └── Quicksort.lean     # Aeneas-generated functional model (the artifact)
└── lean-proof/            # the certified Lean project
    ├── lean-toolchain     # leanprover/lean4:v4.30.0-rc2  (Aeneas's pin)
    ├── lakefile.lean      # require aeneas from git (backends/lean) + Mathlib
    ├── lake-manifest.json # exact dep revisions (Mathlib v4.30.0-rc2, …)
    ├── Quicksort.lean     # VERBATIM copy of lean-gen/Quicksort.lean
    └── QuicksortProof.lean# total-correctness proof about the generated def
```

## Toolchain

Two independent toolchains, both from the per-folder Nix flake
(`competitors/aeneas/flake.nix`, entered via direnv / `nix develop`):

- **Charon** `0.1.209` + **Aeneas** `0.1.0` (`github:AeneasVerif/{charon,aeneas}`,
  with `aeneas.inputs.charon.follows = "charon"` so LLBC versions match), plus a
  **fenix** Rust nightly for `cargo`. These produce the LLBC and the Lean model.
- **elan** (from nixpkgs) for the **proof** project. The proof imports the real
  `Aeneas` Lean library, which pins Lean **v4.30.0-rc2** and `require`s
  **Mathlib** — neither is in nixpkgs, so elan fetches the toolchain named in
  `lean-proof/lean-toolchain` and `lake` fetches prebuilt Mathlib `.olean`s via
  `lake exe cache get`. This is an *isolated sandbox* toolchain
  (`ELAN_HOME=lean-proof/.elan`); it does **not** touch the repo-root Lean 4.16
  used by the Och formalization.

The `lean-proof/lakefile.lean` depends on Aeneas's Lean runtime directly from
git at the same revision the flake's `aeneas` input resolves to
(`601ef6f…`, `backends/lean` subdir), so the proof typechecks against exactly
the runtime shipped here. Nothing is vendored into the repo.

## Exact commands

From `competitors/aeneas/` (inside `nix develop` / direnv):

```sh
# 1. Compile + test the Rust crate
cd quicksort
cargo build
cargo test

# 2. Rust -> LLBC.  --preset=aeneas is MANDATORY (Aeneas rejects plain LLBC).
charon cargo --preset=aeneas                 # writes quicksort.llbc

# 3. LLBC -> Lean functional model
aeneas -backend lean quicksort.llbc -dest ../lean-gen   # writes ../lean-gen/Quicksort.lean
cp ../lean-gen/Quicksort.lean ../lean-proof/Quicksort.lean   # the proof imports it verbatim

# 4. Typecheck the generated model AND the proof, against the real Aeneas+Mathlib
cd ../lean-proof
lake update                                  # resolve deps + fetch Mathlib olean cache (minutes)
lake build                                   # builds Aeneas lib, the generated model, and the proof
```

`lake build` prints, for the headline theorem:

```
'Aeneas.Std.quicksort_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
```

i.e. only Lean's three standard axioms — **no `sorry`, no extra axiom,
no `native_decide`** anywhere in the proof.

## What is proven vs translated vs compiled

| Stage | Status |
|---|---|
| Rust crate compiles (`cargo build`) + unit tests (`cargo test`) | ✅ |
| Charon → LLBC (`quicksort.llbc`) | ✅ produced |
| Aeneas → Lean model (`lean-gen/Quicksort.lean`) | ✅ produced |
| **Generated Lean model typechecks against the real `Aeneas` + Mathlib** | ✅ (`lake build Quicksort`) |
| **Sortedness + Permutation, proved ON the generated `quicksort.quicksort`** | ✅ **machine-checked, no holes** |

The certified theorem (`competitors/aeneas/lean-proof/QuicksortProof.lean`):

```lean
theorem quicksort_correct (s : Slice Std.U32) :
    quicksort.quicksort s ⦃ s' =>
      List.Pairwise (· ≤ ·) s'.val ∧ s'.val.Perm s.val ⦄ :=
  quicksort_spec s
```

`quicksort.quicksort` is the *generated* `Slice U32 → Result (Slice U32)`,
`partial_fixpoint` function (imported from `Quicksort.lean`, byte-identical to
`lean-gen/Quicksort.lean`) — not a re-implementation.

**This is total correctness.** The Aeneas triple `e ⦃ s' => P s' ⦄` unfolds to
`theta e P`, and `theta` maps both `fail` and `div` to `False`. So proving the
triple establishes simultaneously that the generated function (a) never panics,
(b) never diverges (it terminates with `ok s'`), and (c) the result `s'` is
sorted ascending and is a `List.Perm` of the input. Termination is not assumed:
even though the generated definition is `partial_fixpoint` (Aeneas does not
synthesize a measure for the slice recursion), the proof supplies the missing
well-founded argument itself — strong induction on `s.length` in `quicksort_spec`
and `loop.spec_decr_nat` (measure `(len-1) - j`) for the Lomuto loop.

### Proof structure (all in `QuicksortProof.lean`)

- `set_set_perm'` / `swap_val'` / `swap_props` — the generated `Slice.swap`
  (two `Slice.update`s) is a permutation and updates the two indices pointwise.
- `partition_loop_body_spec` — one Lomuto step preserves the loop invariant
  (`[0,i) ≤ pivot`, `[i,j) > pivot`, permutation, `s[len-1]` untouched) and
  strictly decreases `(len-1)-j`. Proved with `step` against the `Aeneas.Std`
  `@[step]` specs.
- `partition_loop_spec` — lifts the body spec over the `loop` combinator via the
  library's `loop.spec_decr_nat`.
- `partition_spec` — the whole `partition` returns `(p, s')` with `p < len`,
  `s' ~ s`, and the pivot-split bounds (`∀k<p, s'[k] ≤ s'[p]` and
  `∀ p<k<len, s'[p] ≤ s'[k]`). Uses `partition_loop_spec` + the final swap.
- `quicksort_spec` — strong induction on `s.length`; uses `partition_spec`,
  `split_at_mut.spec` (twice), the inductive hypothesis on each disjoint half,
  and the two back-functions to reconstruct the result. Then `List.Perm` and
  `List.Pairwise (·≤·)` of `lo1 ++ pivot :: upper1` from the partition bounds.

## The key comparison artifact: how `split_at_mut` appears (and how it is proven)

In the Rust source (`quicksort/src/lib.rs`):

```rust
let (lo, hi) = s.split_at_mut(p);   // two disjoint &mut [u32] views
quicksort(lo);
let (_pivot, upper) = hi.split_at_mut(1);
quicksort(upper);
```

Aeneas translates each `split_at_mut` into a **forward value + a backward
continuation** (`lean-gen/Quicksort.lean`):

```lean
let (p1, split_at_mut_back) ← core.slice.Slice.split_at_mut s1 p
let (lo, hi) := p1
let lo1 ← quicksort lo
let (p2, split_at_mut_back1) ← core.slice.Slice.split_at_mut hi 1#usize
let (_pivot, upper) := p2
let upper1 ← quicksort upper
let hi1 := split_at_mut_back1 (_pivot, upper1)
ok (split_at_mut_back (lo1, hi1))
```

Observations, now backed by the proof:

1. **The mutable borrow is a pure pair `(p1, back)`.** `p1 = (lo, hi)` is the
   forward projection (the two halves' contents); `back : (Slice × Slice) → Slice`
   re-propagates the mutated halves into the parent when the borrows end. In the
   proof, the Aeneas library's `split_at_mut.spec` gives `lo = take p s1`,
   `hi = drop p s1`, and `(back (lo', hi')).val = lo'.val ++ hi'.val` once the
   lengths match. So `back` is *provably* the write-back `(++)`.

2. **No separation-logic obligation.** There is no `disjoint`, no `modifies`.
   Disjointness of the two `&mut` halves was discharged once, for free, by the
   Rust borrow checker (Charon would not emit this LLBC otherwise). The proof
   never reasons about aliasing — it manipulates `take`/`drop`/`++` on pure
   lists. This is the sharp contrast with Low\*/F\* (explicit heap `disjoint`/
   `modifies`) and Idris/QTT (uniqueness on a single live view).

3. **Nesting composes by closure nesting, LIFO.** The inner `split_at_mut hi 1`
   yields its own `back1`, applied *first* (`hi1 := back1 (_pivot, upper1)`),
   then fed to the outer `back (lo1, hi1)`. In the proof these compose as
   `lo1.val ++ (pivot.val ++ upper1.val)`, mirroring the reverse-order borrow
   give-backs. This nested `++` is exactly what the permutation/sortedness
   arguments are run over.

4. **`partial_fixpoint`, no synthesized measure.** Aeneas emits the recursion in
   the `Result` divergence monad without a termination argument. Getting from
   "translated" to "total correctness" therefore required supplying the
   well-founded recursion (length-decrease) by hand — which is precisely the
   `IH`/`loop.spec_decr_nat` machinery in the proof. This is real, non-trivial
   work that the toolchain leaves to the user, and it is the main friction below.

## Friction encountered

- **`--preset=aeneas` is mandatory and only surfaces at the Aeneas step**, not
  the Charon step: a plain `charon cargo` produces a `.llbc` Charon accepts but
  Aeneas rejects.
- **Lean-version / Mathlib coupling.** Aeneas tracks a fast-moving Lean RC
  (`v4.30.0-rc2`) and pulls Mathlib. This cannot share the Ochre repo-root Lean
  4.16 toolchain, so the proof lives in its own elan-managed sandbox with its own
  `lean-toolchain`. `lake exe cache get` makes Mathlib a minutes-long download
  (prebuilt oleans) rather than an hours-long source build, which is essential.
- **`partial_fixpoint` ⇒ not total out of the box.** The generated model is in
  `Result`; the termination/well-foundedness argument is the user's job. The
  Lomuto loop needed an explicit invariant + measure (`loop.spec_decr_nat`), and
  the recursion needed strong induction on slice length.
- **`split_at_mut.spec` postcondition shape.** The generated return type is the
  left-associated `((Slice × Slice) × BackFn)`, which the `⦃ ⦄` binder sugar
  can't fully destructure (it only right-associates products), so the spec keeps
  projectors — a minor papercut when applying it with `step`.
- **The Aeneas Std Lean library itself contains a few `sorry`s** (in
  `Std/Slice.lean`, `Std/String*.lean`) for unrelated primitives. These are
  upstream and do **not** infect our theorem: `#print axioms quicksort_correct`
  reports only `propext / Classical.choice / Quot.sound` — had any used `sorry`
  been on the dependency path, `sorryAx` would appear there.

## Note on the earlier hand-written model

A previous iteration shipped a hand-written, `filter`-based `List Nat` quicksort
with its own sorted+perm proof. That is **not** the certified result and has been
removed: it was a *different* algorithm with no refinement link to the generated
translation, so proving it said nothing about the Rust. The result that counts is
`quicksort_correct` above, stated about the generated `quicksort.quicksort`.
