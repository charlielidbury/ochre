import Lake
open Lake DSL

-- Depend on the Aeneas Lean runtime library directly from the AeneasVerif/aeneas
-- repo (the `backends/lean` subdirectory), pinned to the exact revision used by
-- the per-folder Nix flake's `aeneas` input. It transitively `require`s
-- Mathlib @ v4.30.0-rc2. Fetch the prebuilt Mathlib oleans with
-- `lake exe cache get` (see NOTES.md) — do NOT build Mathlib from source.
require aeneas from git
  "https://github.com/AeneasVerif/aeneas.git" @ "601ef6f79e036a031b55b0bb44baa5c83f8b006a" / "backends" / "lean"

package «aeneas-quicksort-proof» {}

-- The Aeneas-generated model, copied verbatim from `../lean-gen/Quicksort.lean`.
@[default_target] lean_lib «Quicksort» {}

-- The total-correctness proof about the GENERATED `quicksort.quicksort`.
@[default_target] lean_lib «QuicksortProof» {}
