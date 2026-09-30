#!/usr/bin/env bash
# make-sandbox.sh DEST: a fresh directory for an assessed agent.
#
# It holds the package (the skeleton, ASSIGNMENT.md, grade.sh, the nix flake),
# Mathlib and its dependencies with their built oleans (.lake/packages, copied
# with reflinks where the filesystem allows), a pristine copy of the skeleton
# and check_fixed.py under .grader/ (so that ./grade.sh works inside the
# sandbox), and the offline Lean books under docs/. It holds nothing else from
# the benchmark repository: not tests.json, SPEC.md, tools/ or any other
# condition. The Lean toolchain itself (leanprover/lean4:v4.31.0) must already
# be installed in elan; the sandbox needs no network. The final grade is always
# given by the repository's own grade.sh, run on DEST: ./grade.sh DEST.
set -euo pipefail

HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
DEST=${1:?usage: make-sandbox.sh DEST}
[ ! -e "$DEST" ] || { echo "make-sandbox: $DEST already exists" >&2; exit 1; }

FILES=(ASSIGNMENT.md SOLUTION_FILES Solution.lean Check.lean Tests.lean lakefile.toml lake-manifest.json lean-toolchain
       flake.nix flake.lock grade.sh grade_scan.py .gitignore)

# Mathlib's oleans, fetched once into the package (needs the network, here only).
if [ ! -d "$HERE/.lake/packages/mathlib/.lake/build" ]; then
  ( cd "$HERE" && lake exe cache get )
fi
( cd "$HERE" && elan which lean >/dev/null 2>&1 ) || { echo "make-sandbox: the Lean toolchain in lean-toolchain is not installed" >&2; exit 1; }

mkdir -p "$DEST/.grader/pristine" "$DEST/.lake"
DEST=$(cd "$DEST" && pwd)
for f in "${FILES[@]}"; do
  cp -r "$HERE/$f" "$DEST/"
  cp -r "$HERE/$f" "$DEST/.grader/pristine/"
done
cp "$HERE/../../common/check_fixed.py" "$DEST/.grader/"
cp -r --reflink=auto "$HERE/.lake/packages" "$DEST/.lake/"

# The docs: a nix store path, kept alive by the out-link.
nix build "path:$HERE#docs" --out-link "$DEST/docs"

# Self-check: nothing excluded made it in, and the skeleton builds on its own.
if find "$DEST" -path "$DEST/.lake" -prune -o -path "$DEST/docs" -prune -o \
     \( -name tests.json -o -name SPEC.md -o -name '_reference' -o -name tools \) -print | grep -q .; then
  echo "make-sandbox: excluded files found in $DEST" >&2; exit 1
fi
( cd "$DEST" && lake build Solution >/dev/null 2>&1 ) \
  || { echo "make-sandbox: the skeleton does not build in $DEST" >&2; exit 1; }
rm -rf "$DEST/.lake/build"
echo "make-sandbox: $DEST ready (the agent runs \`nix develop -c ./grade.sh\` there)"
