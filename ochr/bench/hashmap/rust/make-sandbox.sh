#!/usr/bin/env bash
# make-sandbox.sh DEST: a fresh directory for an assessed agent.
#
# It holds the package (the skeleton, ASSIGNMENT.md, grade.sh, the nix flake),
# a pristine copy of the skeleton and check_fixed.py under .grader/ (so that
# ./grade.sh works inside the sandbox), and the offline Rust documentation under
# docs/rust (the Book, the standard library API and the Reference, as HTML). It
# holds nothing else from the benchmark repository: not tests.json, SPEC.md,
# tools/ or any other condition. The final grade is always given by the
# repository's own grade.sh, run on DEST: ./grade.sh DEST.
set -euo pipefail

HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
DEST=${1:?usage: make-sandbox.sh DEST}
[ ! -e "$DEST" ] || { echo "make-sandbox: $DEST already exists" >&2; exit 1; }

FILES=(ASSIGNMENT.md SOLUTION_FILES Cargo.toml Cargo.lock flake.nix flake.lock grade.sh grade_scan.py .gitignore src tests)

mkdir -p "$DEST/.grader/pristine" "$DEST/docs"
DEST=$(cd "$DEST" && pwd)
for f in "${FILES[@]}"; do
  cp -r "$HERE/$f" "$DEST/"
  cp -r "$HERE/$f" "$DEST/.grader/pristine/"
done
cp "$HERE/../../common/check_fixed.py" "$DEST/.grader/"

# The docs: a nix store path, kept alive by the out-link.
nix build "path:$HERE#docs" --out-link "$DEST/docs/rust"

# Self-check: nothing excluded made it in, and the skeleton builds on its own.
if find "$DEST" -path "$DEST/docs" -prune -o \( -name tests.json -o -name SPEC.md -o -name '_reference' -o -name tools -o -name target \) -print | grep -q .; then
  echo "make-sandbox: excluded files found in $DEST" >&2; exit 1
fi
( cd "$DEST" && nix develop "path:$DEST" -c cargo build --offline --locked --quiet 2>/dev/null ) \
  || { echo "make-sandbox: the skeleton does not build in $DEST" >&2; exit 1; }
rm -rf "$DEST/target"
echo "make-sandbox: $DEST ready (the agent runs \`nix develop -c ./grade.sh\` there)"
