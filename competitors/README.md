# Competitor deep-dive: in-place quicksort

A controlled comparison of how three verification ecosystems handle the same
problem — **in-place quicksort on a mutable array** — so we can contrast their
memory/aliasing models, specification languages, and toolchains against Ochre's
goals.

The deliberately-chosen focal point is the **partition / `split_at_mut` step**:
one mutable buffer is split into two *disjoint* mutable halves that are mutated
independently and recombined. This is exactly the place the three memory models
diverge:

| System        | Mutation / aliasing model                          |
|---------------|----------------------------------------------------|
| Idris 2 (QTT) | Linearity / uniqueness — single live mutable view  |
| F* / Low*     | Explicit heap + separation (`disjoint`, `modifies`)|
| Aeneas        | Ownership / borrows — disjointness from borrowck    |

## The common task

Implement **in-place quicksort** (Hoare or Lomuto partition is fine — state
which) over a mutable array of machine integers.

Algorithm constraints (keep them the same across all three):

- **In place**: O(1) auxiliary heap beyond the recursion stack.
- The partition step must split the buffer into two **disjoint mutable
  sub-ranges** that are sorted by recursive calls (this is the whole point —
  do not sidestep it with a copy-out/copy-back).

## The common specification

Each implementation should target the same functional spec, to whatever depth
the system idiomatically allows:

1. **Sortedness**: the output array is sorted (ascending).
2. **Permutation**: the output is a permutation (multiset-equal) of the input.

"How far each system gets" toward a *machine-checked* proof of (1) and (2) is
itself a comparison data point — record it honestly in the per-folder NOTES.

## Per-folder deliverable

Each `competitors/<system>/` should contain:

- The implementation + spec, **compiling/verifying** under the repo's Nix
  toolchain (added to the root `flake.nix` devShell, available via direnv).
- A `NOTES.md` recording: exact build/verify command, what was proven vs only
  type-checked vs only compiled, how the disjoint-mutable-split was expressed,
  and friction encountered. This is the material for the write-up.

## Status

- [ ] `aeneas/` — Rust + Charon + Aeneas → Lean
- [ ] `fstar-lowstar/` — F* / Low* → C via KaRaMeL
- [ ] `idris/` — Idris 2 with linear mutable arrays
