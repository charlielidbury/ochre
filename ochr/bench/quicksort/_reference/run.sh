#!/usr/bin/env bash
# Validate ../tests.json: (1) it is exactly what the independent oracle
# gen_tests.py produces, and (2) the unverified Rust reference passes every
# expected result in it. Uses cargo from PATH, else from nixpkgs.
set -euo pipefail
cd "$(dirname "$0")"
python3 gen_tests.py | cmp -s - ../tests.json \
  || { echo "tests.json is stale: rerun python3 gen_tests.py > ../tests.json"; exit 1; }
echo "tests.json matches gen_tests.py"
if command -v cargo >/dev/null; then
  cargo run --quiet --release -- ../tests.json
else
  nix shell nixpkgs#cargo nixpkgs#rustc -c cargo run --quiet --release -- ../tests.json
fi
