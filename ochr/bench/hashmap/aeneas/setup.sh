#!/usr/bin/env bash
# ./setup.sh
# One-time preparation of this package (needs the network; not for the assessed
# agent, whose sandbox is made ready by make-sandbox.sh):
#   1. build the pinned toolchain (.tools, from flake.nix);
#   2. vendor the allowed part of the pinned Aeneas source into vendor/aeneas
#      (the Lean library, docs and tutorial; never its tests/), Charon's
#      docs into vendor/charon-docs, and the Lean books into vendor/lean-docs;
#   3. fetch Mathlib's pre-built cache and build the Aeneas Lean library;
#   4. translate and build the skeleton (its holes show up as sorry warnings).
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=env.sh
. "$here/env.sh"
src="$(nix build "$here#aeneas-src" --no-link --print-out-paths)"
if [ "$(cat "$here/vendor/aeneas/REV" 2>/dev/null)" != "$(cat "$src/REV")" ]; then
  echo "[setup] vendoring Aeneas $(cat "$src/REV")"
  rm -rf "$here/vendor/aeneas"
  mkdir -p "$here/vendor"
  cp -r "$src" "$here/vendor/aeneas"
  chmod -R u+w "$here/vendor/aeneas"
fi
docs="$(nix build "$here#charon-docs" --no-link --print-out-paths)"
rm -rf "$here/vendor/charon-docs"
cp -r "$docs" "$here/vendor/charon-docs"
chmod -R u+w "$here/vendor/charon-docs"
books="$(nix build "$here#lean-docs" --no-link --print-out-paths)"
rm -rf "$here/vendor/lean-docs"
cp -r "$books" "$here/vendor/lean-docs"
chmod -R u+w "$here/vendor/lean-docs"
cd "$here/lean"
echo "[setup] Mathlib cache"
lake exe cache get
echo "[setup] building the Aeneas library (several minutes the first time)"
lake build Aeneas
"$here/translate.sh"
echo "[setup] building the skeleton"
lake build
echo "[setup] done. ./grade.sh grades the package; ./make-sandbox.sh DEST makes an agent sandbox."
