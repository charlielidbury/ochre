# Sourced by translate.sh, grade.sh and setup.sh: puts the pinned toolchain on PATH.
#   .tools/  the Nix closure of charon, aeneas, the Rust nightly, elan, python3
#            (built from flake.nix on first use; pre-built in a sandbox)
#   .elan/   the Lean toolchain named in lean/lean-toolchain (a sandbox ships it;
#            outside a sandbox elan's usual home is used)
pkg="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
if [ ! -x "$pkg/.tools/bin/charon" ]; then
  echo "env.sh: building the pinned toolchain (nix build .#tools); this happens once" >&2
  nix build "$pkg#tools" -o "$pkg/.tools" || { echo "env.sh: nix build failed" >&2; return 1; }
fi
export PATH="$pkg/.tools/bin:$PATH"
if [ -d "$pkg/.elan" ]; then export ELAN_HOME="$pkg/.elan"; fi
# Never let lake or cargo reach the network during grading.
export CARGO_NET_OFFLINE=true
