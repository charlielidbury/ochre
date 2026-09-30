#!/usr/bin/env bash
# ./translate.sh [DIR]
# Rust -> Charon -> Aeneas -> Lean: regenerates lean/Hashmap/Code/{Types,Funs}.lean
# from rust/src. Run it after every change to the Rust, before `lake build`.
# grade.sh runs it on its own copy of your files, so a stale model never passes.
set -euo pipefail
crate=hashmap   # the Rust crate (rust/Cargo.toml) and the Lean namespace
mod=Hashmap     # the Lean library; the translation goes to lean/$mod/Code
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
dir="$(cd "${1:-$here}" && pwd)"
# shellcheck source=env.sh
. "$here/env.sh"
mkdir -p "$dir/build"
rm -f "$dir/build/$crate.llbc"
echo "[1/2] charon cargo --preset=aeneas"
( cd "$dir/rust" && CARGO_TARGET_DIR="$dir/build/charon-target" charon cargo --preset=aeneas --dest-file "$dir/build/$crate.llbc" )
echo "[2/2] aeneas -backend lean"
rm -rf "$dir/lean/$mod/Code"
aeneas -backend lean "$dir/build/$crate.llbc" -dest "$dir/lean" -subdir "$mod/Code" -split-files -abort-on-error -no-progress-bar
# Aeneas emits *_Template.lean files only when the crate uses external
# (opaque) definitions; a solution must not need any.
if ls "$dir/lean/$mod/Code/"*External* >/dev/null 2>&1; then
  echo "translate.sh: the translation has external (opaque) definitions: $(ls "$dir/lean/$mod/Code/"*External*)" >&2
  exit 1
fi
echo "OK: lean/$mod/Code regenerated"
