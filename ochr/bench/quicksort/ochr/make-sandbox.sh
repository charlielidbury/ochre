#!/usr/bin/env bash
# make-sandbox.sh DEST [--no-build]
#
# Build a fresh sandbox for this assignment in DEST: this package, the Ochr checker with its
# examples tour and the arrays library (case studies removed), the language reference and
# guide, and the grader's tools. See ../../common/ochr/sandbox.py.
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo="$(cd "$here/../../../.." && pwd)"
exec python3 "$here/../../common/ochr/sandbox.py" --package "$here" \
  --checker "$repo/ochr/core/lean" --rules "$repo/ochr/core/RULES.md" "$@"
