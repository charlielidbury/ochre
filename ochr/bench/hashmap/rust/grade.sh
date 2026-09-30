#!/usr/bin/env bash
# Grade a solution of this package: ./grade.sh [DIR]
#
# DIR is the solution directory (default: the directory this script is in).
# Exits 0 iff the solution passes. The last line of output is the verdict,
# starting `GRADE: PASS` or `GRADE: FAIL`. The checks, in order:
#   1. no holes (todo!, unimplemented!) and no forbidden construct in the
#      files listed in SOLUTION_FILES (the list is in ASSIGNMENT.md and
#      grade_scan.py), and no other source file under src/;
#   2. every FIXED region is byte-identical to the original, and the FIXED
#      files (Cargo.toml, Cargo.lock, tests/spec.rs) are unchanged; no build.rs,
#      .cargo/ or rust-toolchain file;
#   3. `cargo build` succeeds, offline, with no dependencies;
#   4. every test in tests/spec.rs passes.
# The originals come from .grader/pristine/ in a sandbox, and from this
# script's own directory in the benchmark repository.
set -uo pipefail

PROFILE=hashmap        # grade_scan.py profile
SPEC_TESTS=5           # number of #[test] functions in tests/spec.rs

HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
DIR=$(cd "${1:-$HERE}" && pwd) || { echo "grade: no such directory: ${1:-}"; exit 2; }

# The toolchain: re-run inside the package's nix shell if cargo is missing.
if ! command -v cargo >/dev/null 2>&1 || ! command -v python3 >/dev/null 2>&1; then
  if [ -z "${GRADE_IN_NIX:-}" ] && command -v nix >/dev/null 2>&1; then
    GRADE_IN_NIX=1 exec nix develop "path:$HERE" -c "$0" "$@"
  fi
  echo "grade: cargo and python3 must be on PATH (run inside \`nix develop\`)"; exit 2
fi

if [ -d "$HERE/.grader" ]; then
  PRISTINE="$HERE/.grader/pristine"; CHECK_FIXED="$HERE/.grader/check_fixed.py"
else
  PRISTINE="$HERE"; CHECK_FIXED="$HERE/../../common/check_fixed.py"
fi
SCAN="$PRISTINE/grade_scan.py"
[ -f "$PRISTINE/SOLUTION_FILES" ] || { echo "grade: $PRISTINE/SOLUTION_FILES is missing"; exit 2; }

fail=()
note() { printf '%s\n' "$*"; }

cd "$DIR"
mapfile -t SRC < "$PRISTINE/SOLUTION_FILES"

note "== 1. holes and forbidden constructs"
python3 "$SCAN" "$PROFILE" "${SRC[@]}"
case $? in
  0) ;;
  1) fail+=("holes remain") ;;
  *) fail+=("forbidden constructs") ;;
esac
# Only the files in SOLUTION_FILES are graded; code anywhere else would be lost.
while IFS= read -r f; do
  case " ${SRC[*]} " in *" $f "*) ;; *) note "$f: not in SOLUTION_FILES (put all your code in ${SRC[*]})"; fail+=("stray file $f") ;; esac
done < <(find src -type f | sort)

note "== 2. FIXED regions and files"
pairs=(); for f in "${SRC[@]}"; do pairs+=("$PRISTINE/$f" "$f"); done
python3 "$CHECK_FIXED" "${pairs[@]}" || fail+=("FIXED region changed")
for f in Cargo.toml Cargo.lock tests/spec.rs; do
  cmp -s "$PRISTINE/$f" "$f" || { note "$f: FIXED file changed or missing"; fail+=("$f changed"); }
done
for f in build.rs .cargo rust-toolchain rust-toolchain.toml; do
  [ ! -e "$f" ] || { note "$f: not allowed"; fail+=("$f present"); }
done

note "== 3. build"
if out=$(cargo build --offline --locked 2>&1); then
  note "== 4. tests"
  out=$(cargo test --offline --locked --test spec 2>&1); status=$?
  printf '%s\n' "$out" | grep -E '^test |^test result|panicked|assertion|left:|right:' | head -60
  if [ $status -ne 0 ] || ! printf '%s\n' "$out" | grep -q "^test result: ok. $SPEC_TESTS passed; 0 failed"; then
    fail+=("tests failed")
  fi
else
  printf '%s\n' "$out" | grep -v '^warning\|^ *Compiling' | head -60
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
  note "GRADE: PASS rust/$PROFILE; $lines"
  exit 0
else
  note "GRADE: FAIL rust/$PROFILE: $(IFS=';'; echo "${fail[*]}" | sed 's/;/; /g'); $lines"
  exit 1
fi
