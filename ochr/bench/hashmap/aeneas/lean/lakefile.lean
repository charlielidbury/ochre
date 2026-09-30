import Lake
open Lake DSL

-- The Aeneas Lean library, vendored from the pinned Aeneas source by setup.sh
-- (never edited). Mathlib and the rest come in through its own manifest.
require aeneas from "../vendor/aeneas/backends/lean"

package «hashmap» {}

@[default_target] lean_lib «Hashmap» {}
