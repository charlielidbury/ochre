#!/usr/bin/env bash
# ./make-sandbox.sh DEST
# Makes DEST (absent or empty) a self-contained copy of this package for an
# assessed agent, containing exactly:
#   - the package's own sources (a fixed list: ASSIGNMENT.md, the skeleton, the
#     grader, translate.sh, env.sh, the flake), and pristine copies of them in
#     grader/orig for grade.sh to compare against;
#   - grader/check_fixed.py (from ../../common);
#   - vendor/aeneas: the allowed part of the pinned Aeneas source (Lean library,
#     pre-built; docs; tutorial). Never Aeneas's tests/;
#   - vendor/charon-docs: Charon's documentation;
#   - lean/.lake/packages: Mathlib and its dependencies, pre-built, as pinned;
#   - .elan: the Lean toolchain named by lean/lean-toolchain;
#   - .tools: a symlink to the Nix store path of the pinned tools (charon, aeneas,
#     the Rust nightly, elan, python3). The runner must make exactly the store
#     paths listed in DEST/.tools-closure readable, and nothing else of the store.
# Nothing else from this repository. It ends by checking the exclusions.
set -euo pipefail
mod=Hashmap
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
dest="${1:?usage: ./make-sandbox.sh DEST}"
if [ -e "$dest" ] && [ -n "$(ls -A "$dest")" ]; then echo "make-sandbox.sh: $dest is not empty" >&2; exit 2; fi
# shellcheck source=env.sh
. "$here/env.sh"
if [ ! -f "$here/vendor/aeneas/REV" ] || [ ! -f "$here/vendor/charon-docs/REV" ] || [ ! -d "$here/lean/.lake/packages/mathlib/.lake/build" ]; then
  echo "make-sandbox.sh: run ./setup.sh first" >&2; exit 2
fi
mkdir -p "$dest"
dest="$(cd "$dest" && pwd)"

copy_sources() {  # the package's own source files, by explicit list
  local t=$1
  mkdir -p "$t/rust/src" "$t/rust/tests" "$t/lean/$mod"
  cp "$here"/{ASSIGNMENT.md,SOLUTION_FILES,grade.sh,translate.sh,env.sh,flake.nix,flake.lock,.gitignore} "$t/"
  cp "$here/rust/Cargo.toml" "$t/rust/"
  cp "$here"/rust/src/*.rs "$t/rust/src/"
  cp "$here"/rust/tests/*.rs "$t/rust/tests/"
  cp "$here"/lean/{lakefile.lean,lake-manifest.json,lean-toolchain,$mod.lean} "$t/lean/"
  cp "$here/lean/$mod/"*.lean "$t/lean/$mod/"
}
copy_sources "$dest"
copy_sources "$dest/grader/orig"
cp "$here"/grader/{grade.py,package.json} "$dest/grader/"
cp "$here/../../common/check_fixed.py" "$dest/grader/"

echo "[sandbox] pre-built libraries"
mkdir -p "$dest/vendor" "$dest/lean/.lake"
cp -a --reflink=auto "$here/vendor/aeneas" "$here/vendor/charon-docs" "$dest/vendor/"
cp -a --reflink=auto "$here/lean/.lake/packages" "$dest/lean/.lake/"

echo "[sandbox] Lean toolchain"
tc="$(sed 's|/|--|; s|:|---|' "$here/lean/lean-toolchain")"
mkdir -p "$dest/.elan/toolchains"
cp -a --reflink=auto "${ELAN_HOME:-$HOME/.elan}/toolchains/$tc" "$dest/.elan/toolchains/"

echo "[sandbox] tools"
tools="$(readlink -f "$here/.tools")"
ln -s "$tools" "$dest/.tools"
# The Lean toolchain as elan installs it on NixOS is patched to use a few store
# paths (glibc, the C compiler wrapper); they join the closure.
elan_refs="$(grep -rhoaE '/nix/store/[a-z0-9]{32}-[^/ "]+' "$dest/.elan" | sort -u | while read -r p; do [ -e "$p" ] && echo "$p"; done)"
# shellcheck disable=SC2086
nix-store -qR "$tools" $elan_refs | sort -u > "$dest/.tools-closure"

echo "[sandbox] checking exclusions"
bad=0
check() {  # check DESCRIPTION COMMAND...: the command must print nothing
  local out; out="$("${@:2}" 2>/dev/null | head -5 || true)"
  if [ -n "$out" ]; then echo "  FAIL: $1:"; echo "$out" | sed 's/^/    /'; bad=1; else echo "  ok: $1"; fi
}
check "no Aeneas tests/ directory" find "$dest/vendor" -path '*/tests*'
check "no hashmap or sort source outside the skeleton and the general libraries" \
  find "$dest" \( -path "$dest/lean/$mod" -o -path "$dest/lean/$mod.lean" -o -path "$dest/grader/orig" -o -path "$dest/lean/.lake" -o -path "$dest/.elan" \) -prune \
    -o -type f \( -name '*.lean' -o -name '*.rs' \) \( -iname '*hash*map*' -o -iname '*sort*' \) -print
check "none of Aeneas's hashmap test definitions anywhere (sandbox, Mathlib, Lean core)" \
  grep -rlE --include='*.lean' 'allocate_slots|move_elements_from_list|insert_no_resize|try_resize|hash_key' "$dest"
check "no Lean file in the tools closure" \
  bash -c 'for p in $(cat "$1"); do find "$p" -name "*.lean" -print -quit; done' _ "$dest/.tools-closure"
check "no Ochr sources, paper or competitor code" \
  grep -rlE --include='*.lean' --include='*.rs' --include='*.typ' --include='*.md' 'Ochr|ochr/core|competitors/' "$dest"
check "no reference implementation" find "$dest" -name '_reference'
check "every symlink out of the sandbox points into .tools-closure" \
  bash -c 'find "$1" -type l -lname "/*" ! -lname "$1/*" -printf "%l\n" | while read -r t; do
    grep -qxF "$(echo "$t" | cut -d/ -f1-4)" "$1/.tools-closure" || echo "$t"; done' _ "$dest"
echo "  note: general libraries with hashmap or sort files (allowed, as for every Lean condition):"
echo "    $(find "$dest/lean/.lake/packages" "$dest/.elan" -type f -name '*.lean' \( -iname '*hash*map*' -o -iname '*sort*' -o -path '*HashMap*' \) | wc -l) files in Mathlib/Batteries/Lean core (e.g. List.mergeSort lemmas, Std.HashMap lemmas)"
if [ $bad -ne 0 ]; then echo "make-sandbox.sh: exclusion check failed" >&2; exit 1; fi
echo "[sandbox] ready: $dest ($(wc -l < "$dest/.tools-closure") store paths in .tools-closure)"
