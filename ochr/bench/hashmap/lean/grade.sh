#!/usr/bin/env bash
# Grade a solution of this package: ./grade.sh [DIR]
#
# DIR is the solution directory (default: the directory this script is in).
# Exits 0 iff the solution passes. The last line of output is the verdict,
# starting `GRADE: PASS` or `GRADE: FAIL`. The checks, in order:
#   1. no holes (sorry) and no forbidden construct in the files listed in
#      SOLUTION_FILES (the list is in ASSIGNMENT.md and grade_scan.py), and no
#      other .lean file;
#   2. every FIXED region of Solution.lean is byte-identical to the original,
#      and the FIXED files (Check.lean, Tests.lean, lakefile.toml,
#      lean-toolchain, lake-manifest.json) are unchanged;
#   3. `lake build Solution` succeeds;
#   4. `lake build Check` succeeds: the FIXED definitions and theorem
#      statements are exactly as fixed (restated in a fresh module), the
#      solution declares no global instance about existing types and no
#      axiom, opaque constant or meta code, and every FIXED theorem uses no
#      axioms beyond propext, Classical.choice and Quot.sound;
#   5. the kernel re-checks every declaration of the solution (leanchecker);
#   6. every test sequence in Tests.lean passes.
# The originals come from .grader/pristine/ in a sandbox, and from this
# script's own directory in the benchmark repository.
set -uo pipefail

PROFILE=hashmap        # grade_scan.py profile
TESTS_OK="tests: 5/5 sequences passed"

HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
DIR=$(cd "${1:-$HERE}" && pwd) || { echo "grade: no such directory: ${1:-}"; exit 2; }

# The toolchain: re-run inside the package's nix shell if lake is missing.
if ! command -v lake >/dev/null 2>&1 || ! command -v python3 >/dev/null 2>&1; then
  if [ -z "${GRADE_IN_NIX:-}" ] && command -v nix >/dev/null 2>&1; then
    GRADE_IN_NIX=1 exec nix develop "path:$HERE" -c "$0" "$@"
  fi
  echo "grade: lake and python3 must be on PATH (run inside \`nix develop\`)"; exit 2
fi

if [ -d "$HERE/.grader" ]; then
  PRISTINE="$HERE/.grader/pristine"; CHECK_FIXED="$HERE/.grader/check_fixed.py"
else
  PRISTINE="$HERE"; CHECK_FIXED="$HERE/../../common/check_fixed.py"
fi
SCAN="$PRISTINE/grade_scan.py"
[ -f "$PRISTINE/SOLUTION_FILES" ] || { echo "grade: $PRISTINE/SOLUTION_FILES is missing"; exit 2; }
FIXED_FILES=(Check.lean Tests.lean lakefile.toml lean-toolchain lake-manifest.json)

fail=()
note() { printf '%s\n' "$*"; }
# Show a build log without the noise: errors and the lines that follow them.
show() { grep -v '^✔\|^⣿\|^info: \|^⚠ \[\|^warning: .*declaration uses .sorry.\|^Build completed' | head -"${1:-60}"; }

cd "$DIR"
# The solution: the files in SOLUTION_FILES, and the modules they are.
mapfile -t SRC < "$PRISTINE/SOLUTION_FILES"
mapfile -t MODS < <(printf '%s\n' "${SRC[@]}" | sed 's/\.lean$//; s#/#.#g')

note "== 1. holes and forbidden constructs"
python3 "$SCAN" "$PROFILE" "${SRC[@]}"
case $? in
  0) ;;
  1) fail+=("holes remain") ;;
  *) fail+=("forbidden constructs") ;;
esac
# Only the files in SOLUTION_FILES are graded; code anywhere else would be lost.
while IFS= read -r f; do
  f=${f#./}
  case " ${FIXED_FILES[*]} ${SRC[*]} " in *" $f "*) ;; *) note "$f: not in SOLUTION_FILES (put all your code in ${SRC[*]})"; fail+=("stray file $f") ;; esac
done < <(find . -name '*.lean' -not -path './.lake/*' -not -path './.grader/*')

note "== 2. FIXED regions and files"
pairs=(); for f in "${SRC[@]}"; do pairs+=("$PRISTINE/$f" "$f"); done
python3 "$CHECK_FIXED" "${pairs[@]}" || fail+=("FIXED region changed")
for f in "${FIXED_FILES[@]}"; do
  cmp -s "$PRISTINE/$f" "$f" || { note "$f: FIXED file changed or missing"; fail+=("$f changed"); }
done

note "== 3. build"
if out=$(lake build Solution 2>&1); then
  note "== 4. FIXED statements and axioms"
  if out=$(lake build Check 2>&1); then
    note "Check: FIXED definitions and statements as fixed; no instances about existing types; no axioms, opaque constants or meta code; axioms within propext, Classical.choice, Quot.sound"
  else
    printf '%s\n' "$out" | grep '^error' | head -40
    fail+=("FIXED theorems not proved")
  fi
  note "== 5. kernel re-check"
  if out=$(lake env leanchecker "${MODS[@]}" 2>&1); then
    note "leanchecker: ${MODS[*]} replayed"
  else
    printf '%s\n' "$out" | tail -20
    fail+=("kernel re-check failed")
  fi
  note "== 6. tests"
  out=$(lake env lean --run Tests.lean 2>&1); status=$?
  printf '%s\n' "$out" | tail -40
  if [ $status -ne 0 ] || ! printf '%s\n' "$out" | grep -qx "$TESTS_OK"; then
    fail+=("tests failed")
  fi
else
  printf '%s\n' "$out" | show 60
  fail+=("build failed")
fi

# The secondary metric: non-blank lines outside FIXED regions of SOLUTION_FILES,
# counted as check_fixed.py counts them.
lines=$(python3 - "$PRISTINE" "${SRC[@]}" <<'EOF'
import os, re, sys
pristine, files = sys.argv[1], sys.argv[2:]
marker = re.compile(r"(?<![\w-])FIXED-(BEGIN|END)(?![\w-])")
def outside(path):
    n, inside = 0, False
    for line in open(path, encoding="utf-8"):
        m = marker.search(line)
        if m: inside = m.group(1) == "BEGIN"
        elif not inside and line.strip(): n += 1
    return n
sol = sum(outside(f) for f in files)
skel = sum(outside(os.path.join(pristine, f)) for f in files if os.path.exists(os.path.join(pristine, f)))
print(f"non-blank lines outside FIXED regions: skeleton {skel}, solution {sol}")
EOF
)

if [ ${#fail[@]} -eq 0 ]; then
  note "GRADE: PASS lean/$PROFILE; $lines"
  exit 0
else
  note "GRADE: FAIL lean/$PROFILE: $(IFS=';'; echo "${fail[*]}" | sed 's/;/; /g'); $lines"
  exit 1
fi
