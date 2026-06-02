# Verus — in-place quicksort

Machine-checked **in-place quicksort over `&mut Vec<u64>`**, proving **both**
halves of the shared spec:

1. **Sortedness** of the output, and
2. **Permutation** (multiset-equality) of output vs input.

No `assume`, no `admit`, no `external_body` on the algorithm — the verification
derivation is run with `--no-cheating`, so the build *fails* if any such escape
hatch is ever introduced. `8 verified, 0 errors`.

## Verify command

```
# devShell (verus on PATH):
nix develop ./competitors/verus -c verus --version
nix develop ./competitors/verus -c verus competitors/verus/quicksort.rs

# or run verification as a pure derivation (fails the build unless 0 errors,
# and rejects any assume/admit/external_body via --no-cheating):
nix build ./competitors/verus#quicksort

# the verus toolchain alone:
nix build ./competitors/verus#verus
```

Result: `verification results:: 8 verified, 0 errors`.

## The proved `ensures`

Top-level entry point:

```rust
pub fn quicksort(v: &mut Vec<u64>)
    ensures
        final(v).len() == old(v).len(),
        sorted_between(final(v)@, 0, final(v)@.len() as int),   // (1) sorted
        final(v)@.to_multiset() == old(v)@.to_multiset(),       // (2) permutation
```

where `sorted_between(s, lo, hi) == forall i j. lo<=i<=j<hi ==> s[i] <= s[j]`.

The recursion (`quicksort_rec`) and the partition carry the same multiset
postcondition plus framing (`forall k outside [lo,hi). final[k] == old[k]`) and a
**bound-preservation** clause used to stitch `left <= pivot <= right` across the
recursive calls:

```rust
fn partition(v: &mut Vec<u64>, lo: usize, hi: usize) -> (p: usize)
    ensures
        lo <= p < hi,
        all_le(final(v)@, lo, p,      final(v)@[p]),  // left  <= pivot
        all_ge(final(v)@, p+1, hi,    final(v)@[p]),  // right >= pivot
        forall|k| outside [lo,hi) ==> final(v)@[k] == old(v)@[k],
        final(v)@.to_multiset() == old(v)@.to_multiset(),
        forall|b: u64| all_le(old(v)@, lo, hi, b) ==> all_le(final(v)@, lo, hi, b),
        forall|b: u64| all_ge(old(v)@, lo, hi, b) ==> all_ge(final(v)@, lo, hi, b);
```

## How the in-place mutation / disjoint partition was expressed

Verus verifies **native Rust in place**: there is no functional translation and
no separate heap model. The vector is a real `&mut Vec<u64>`; mutation is real
`v.set(i, x)` / indexing; the abstract state is the `Seq<u64>` *view* `v@`, and
the SMT backend reasons about that `Seq` directly.

**The disjoint-mutable split (the README focal point) is expressed by
index sub-ranges of ONE mutable borrow**, *not* by `split_at_mut` /
split-borrows. Lomuto partition operates on `v[lo..hi]` with two indices `i`
(boundary: `v[lo..i] <= pivot`) and `j` (scan), and the loop invariant pins down
exactly which indices each phase may have touched:

```rust
invariant
    all_le(v@, lo, i, pivot),
    all_ge(v@, i, j, pivot),
    forall|k| outside [lo,hi) ==> v@[k] == orig[k],   // framing
    v@.to_multiset() == orig.to_multiset(),           // running permutation
```

Recursion then calls `quicksort_rec(v, lo, p)` and `quicksort_rec(v, p+1, hi)` on
the **same** `&mut Vec`, with the sub-ranges' disjointness witnessed entirely by
the *framing postcondition* (`elements outside [lo,hi) are untouched`) rather than
by the borrow checker carving the buffer into two aliases. This is the key
contrast point below: Verus expresses "disjoint mutable halves" as **integer
index reasoning under one borrow**, discharged by SMT, instead of as a
type/permission-level split.

The permutation core is one lemma, `lemma_swap_multiset`: a swap is two `Seq`
`update`s that trade values, and `to_multiset` is invariant under it. Proved from
vstd's `to_multiset_update` (`s.update(i,a).to_multiset() ==
s.to_multiset().insert(a).remove(s[i])`) applied twice + the multiset count
axioms (`group_multiset_axioms`): the inserted `s[i],s[j]` cancel the removed
`s[i],s[j]`. Every other permutation fact (loop, partition, both recursive calls,
final result) is the SMT solver *transitively chaining* this single swap lemma
through `==` on `to_multiset()`.

## Toolchain / packaging

Verus is **not** in nixpkgs, and there is no community flake / cachix binary
cache for it (the upstream repo only ships a non-hermetic `tools/shell.nix` that
expects a system `rustup` and downloads z3 over the network). So we build Verus
**from source** via its `vargo` build system, off a content-addressed
`fetchFromGitHub` of the pinned release tag — **no** `fetchurl` of a prebuilt
`*-x86-linux.zip`. Because the input is *source*, the derivation is portable:
`meta.platforms = lib.platforms.unix` and it goes through `eachDefaultSystem`, so
it is not nailed to `x86_64-linux` the way a prebuilt release archive is. (Only
`x86_64-linux` has actually been built/tested here, but nothing in the flake
hard-codes the platform.)

How the source build is wired:

- **Pin.** `verusRev = 5dd6d836…` is the commit behind the
  `release/0.2026.05.31.5dd6d83` tag. The Verus version string embeds the short
  sha (`…5dd6d83`), so `verusVersion` and `verusRev` stay in lock-step and the
  toolchain that checks `quicksort.rs` is exactly the release version — the proof
  stays in sync with the pin.
- **Rust toolchain.** Upstream `rust-toolchain.toml` pins stable `1.95.0` with
  `rustc-dev` + `llvm-tools`; we provide that via `rust-overlay`
  (`rust-bin.stable."1.95.0"` with `rustc-dev`, `rust-src`, `llvm-tools-preview`).
  `rust_verify` is a **rustc driver** that links `librustc_driver-<hash>.so`; the
  from-source build links the **bit-identical** `librustc_driver-6108105cd7e839cf.so`
  out of this very toolchain (visible in the build's autoPatchelf log), and the
  flake asserts at install time that the toolchain provides that exact soname.
- **rustup shim.** `vargo` (and the `verus` launcher) shell out to `rustup`
  (`rustup show active-toolchain`, `rustup toolchain list`, `rustup run <tc> -- …`).
  We have no rustup; a tiny `writeShellScriptBin "rustup"` shim implements exactly
  those subcommands, pointing `LD_LIBRARY_PATH`/`RUSTC` at the nix toolchain. The
  same shim is used both at **build** time (so `vargo build` works) and at
  **run** time (wrapped onto the launchers' PATH).
- **Offline cargo.** The whole workspace builds offline against an
  `importCargoLock` vendor dir (`source/Cargo.lock`); the one git dependency
  (`utaal/getopts`) gets its FOD hash supplied via `outputHashes`. A generated
  `$CARGO_HOME/config.toml` redirects crates.io + that git source to the vendor
  dir. `vargo` itself has its **own** `Cargo.lock` (a few crates not in the
  workspace lock, e.g. `filetime`), so it is built as a **separate**
  `rustPlatform.buildRustPackage` (with `cargoRoot = "vargo"` because the lock
  lives in `tools/vargo`, and the whole `tools/` tree as `src` because
  `vargo/main.rs` does `#[path = "../../common/consts.rs"]`).
- **z3 from source.** Verus pins **z3 4.12.5** and `vargo` verifies vstd against
  it (with a version check on by default). We build z3 4.12.5 from source
  (`fetchFromGitHub`, not a prebuilt z3 binary) so the whole toolchain stays
  multi-platform and the proof runs against the *exact* solver a stock Verus
  install uses. z3 4.12.5 predates gcc-15 and fails to compile with it (a
  `-Werror=template-body` regression in `static_matrix.h`), so its derivation is
  pinned to `gcc13Stdenv`; the produced binary is unaffected.
- **vstd.** `vargo build --release` builds `rust_verify`, the support libs, the
  `verus`/`cargo-verus` launchers, and then **verifies + compiles vstd** (this
  step runs verus, hence needs z3). vstd verifies clean: `1690 verified, 0 errors`.
- `autoPatchelfHook` fixes the freshly built ELF interpreters/rpaths (with the
  rust toolchain added as a `runtimeDependencies` so it finds `librustc_driver`).
  The result is a self-contained `verus` on PATH.

Verify: `nix build ./competitors/verus#verus` (builds the toolchain),
`nix build ./competitors/verus#quicksort` (`8 verified, 0 errors`).

The `#quicksort` derivation additionally puts a C compiler on PATH because Verus
runs rustc's lifetime/borrow check (which links) on the proof code.

## Friction / expressivity ceiling

- **New mut-ref semantics.** This Verus build defaults to the new mutable-
  reference model: a `&mut` parameter in a postcondition must be disambiguated as
  `final(v)` (vs `old(v)`); bare `v@` in `ensures` is now an error. Minor but a
  real migration tax.
- **No off-the-shelf swap/permutation lemma in `vstd`.** vstd has the building
  blocks (`to_multiset_update`, `to_multiset_ensures`, the multiset count axioms)
  but not a ready "swapping two indices preserves the multiset" lemma, so the
  permutation core had to be assembled by hand. Not hard, but not free.
- **Trigger fragility.** The bound-preservation clauses
  (`forall|b: u64| all_le(..) ==> all_le(..)`) draw low-confidence
  auto-trigger warnings; they verify, but this is exactly the kind of
  SMT-quantifier-instantiation babysitting that defines the Verus experience.
  The stitching proof in `quicksort_rec` is ~20 lines of explicit `assert(..)`
  steps hand-feeding the solver the decomposition `[lo,p) + pivot + [p+1,hi)`.
- **Where Verus runs out of road (for the paper).** Verus is *very* well-suited
  to this problem — both spec halves go through cleanly — and that is itself the
  comparison datum: the cost is paid in **SMT-encoding discipline** (triggers,
  `=~=` extensional-equality nudges, manual lemma chaining), not in the memory
  model. The aliasing/disjointness story is essentially *invisible*: there is no
  separation logic and no linearity obligation, because "two disjoint mutable
  halves" is just an integer-index framing fact (`untouched outside [lo,hi)`)
  that the solver discharges automatically. The ceiling Verus hits is the
  classic SMT one — proofs that need induction or quantifier reasoning the solver
  won't find on its own require explicit ghost lemmas and trigger steering — not
  an expressivity ceiling in *what can be stated* about in-place mutation.

## The sharp three-way comparison

| System    | "disjoint mutable halves" is…                                   | proof engine |
|-----------|------------------------------------------------------------------|--------------|
| **Verus** | an **integer-index framing fact** under one `&mut` borrow, discharged by **SMT directly on native Rust** + `Seq`/`Multiset` views | Z3, with manual trigger/lemma steering |
| Aeneas    | disjointness from the Rust **borrow checker**, then reasoned about in a **functional (Lean) translation** | Lean tactics on translated pure code |
| Low\*     | explicit **separation logic**: `disjoint`/`modifies` clauses over an explicit heap | F\* + SMT, separation-logic framing |

Verus's distinctive position: it neither translates to a pure functional model
(Aeneas) nor reasons over an explicit heap with separation (Low\*). It verifies
the *actual* mutable Rust, with the array's `Seq` view as the only abstraction,
and gets disjointness "for free" from index-range framing — pushing essentially
all the difficulty onto the SMT solver rather than onto a memory/aliasing logic.
