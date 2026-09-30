#!/usr/bin/env bash
# grade.sh: grade this assignment. The last line is `GRADE: PASS ...` or `GRADE: FAIL: <reasons>`.
#
# In a sandbox:       ./grade.sh         grades the solution in this directory.
# In the repository:  ./grade.sh [DIR]   makes a fresh sandbox, copies the files listed in
#                     SOLUTION_FILES from DIR (default: this package, i.e. the skeleton) into
#                     it, and grades them there. This is the authoritative grade. The sandbox is made
#                     from the commit OCHR_BENCH_REV (default HEAD): checker, library, package, grader.
set -uo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
if [ -f "$here/tools/grade_ochr.py" ]; then
  exec python3 "$here/tools/grade_ochr.py" --root "$here"
fi
src="$(cd "${1:-$here}" && pwd)"
tmp="$(mktemp -d)"
[ -n "${KEEP_SANDBOX:-}" ] || trap 'rm -rf "$tmp"' EXIT
if ! "$here/make-sandbox.sh" ${OCHR_BENCH_REV:+--rev "$OCHR_BENCH_REV"} "$tmp/sandbox" >&2; then
  echo "GRADE: FAIL: could not make a sandbox"
  exit 1
fi
while IFS= read -r f; do
  [ -n "$f" ] && cp "$src/$f" "$tmp/sandbox/$f"
done < "$here/SOLUTION_FILES"
"$tmp/sandbox/grade.sh"
