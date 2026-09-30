#!/usr/bin/env bash
# ./grade.sh [SOLUTION_DIR]
# Exits 0 iff the solution builds, has no holes or escape hatches, keeps every
# FIXED region byte-identical, passes all tests, and proves every theorem.
# The last line printed is the verdict. Details: ASSIGNMENT.md, "How to check
# your work"; the logic is in grader/grade.py.
set -uo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=env.sh
. "$here/env.sh" || exit 2
exec python3 "$here/grader/grade.py" "$@"
