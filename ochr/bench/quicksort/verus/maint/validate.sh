#!/usr/bin/env bash
# Maintainer validation for this package (not copied into sandboxes). It:
#   - checks that the FIXED tests region is the transcription of ../tests.json;
#   - builds a sandbox with make-sandbox.sh (which runs the exclusion check);
#   - grades the untouched skeleton in it (must FAIL, naming the holes);
#   - plants cheats in scratch copies and checks that grade.sh rejects each one for the
#     expected reason: (a) an escape hatch in a proof, (b) an edited FIXED region,
#     (c) forbidden constructs, (d) neutralising a FIXED region without editing it,
#     (e) code outside the verus! block.
# Usage: maint/validate.sh [WORKDIR]   (default: a fresh mktemp directory)
set -uo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
NAME="$(basename "$(dirname "$here")")"
work="${1:-$(mktemp -d)}"
rm -rf "$work/sandbox"
ok=0 bad=0

pass() { echo "ok:   $1"; ok=$((ok + 1)); }
fail() { echo "FAIL: $1"; bad=$((bad + 1)); }

python3 "$here/maint/gen_tests.py" --check >/dev/null && pass "tests region matches tests.json" || fail "tests region is stale"
if [ "$NAME" = quicksort ]; then
  verus="$(nix build --no-link --print-out-paths "path:$here#verus")/bin/verus"
  "$verus" --no-cheating "$here/maint/perm_equiv.rs" 2>&1 | grep -q 'verification results:: [0-9]* verified, 0 errors' \
    && pass "perm_equiv.rs: FIXED perm is SPEC's count-based perm" || fail "perm_equiv.rs does not verify"
fi

"$here/make-sandbox.sh" "$work/sandbox" >"$work/make-sandbox.out" 2>&1 \
  && pass "make-sandbox.sh (exclusion check OK)" || { fail "make-sandbox.sh"; cat "$work/make-sandbox.out"; exit 1; }

# expect NAME DIR PATTERN...: grade DIR, require GRADE: FAIL and every PATTERN in the output
expect() {
  local what="$1" dir="$2"; shift 2
  (cd "$dir" && ./grade.sh >grade.out 2>&1)
  local rc=$? missing=""
  tail -1 "$dir/grade.out" | grep -q '^GRADE: FAIL' && [ $rc -ne 0 ] || missing="a GRADE: FAIL verdict"
  for p in "$@"; do grep -qE -- "$p" "$dir/grade.out" || missing="$missing [$p]"; done
  if [ -z "$missing" ]; then pass "$what: $(tail -1 "$dir/grade.out")"; else fail "$what: missing $missing"; fi
}
# cheat NAME PYTHON-EDIT PATTERN...: a scratch copy of the sandbox with the edit applied to s
cheat() {
  local what="$1" edit="$2"; shift 2
  local d="$work/cheat-$what"
  rm -rf "$d"; cp -r "$work/sandbox" "$d"; rm -rf "$d/target"
  python3 - "$d/src/$NAME.rs" "$edit" <<'PY'
import sys
p, edit = sys.argv[1], sys.argv[2]
s = open(p).read()
t = s
exec(edit)
assert s != t, "edit did not apply"
open(p, "w").write(s)
PY
  expect "$what" "$d" "$@"
}

if [ "$NAME" = hashmap ]; then
  expect untouched "$work/sandbox" '^hole: line [0-9]+: todo!\(\)' '^hole: line [0-9]+: arbitrary\(\)' 'scan: 9 hole'
  cheat a-assume 's = s.replace("    // FIXED-END get\n    {\n        todo!()", "    // FIXED-END get\n    {\n        proof { assume(false); }\n        None")' \
    'forbidden: line [0-9]+: assume' 'assume/admit not allowed with --no-cheating'
  cheat b-fixed 's = s.replace("            final(self).spec_get(key) == Some(value), // H5\n", "")' \
    'FIXED region insert changed' 'error: assertion failed'
  cheat c-external 's = s.replace("    // FIXED-BEGIN get\n", "    #[verifier::external_body]\n    // FIXED-BEGIN get\n")' \
    'forbidden: line [0-9]+: #\[verifier::external_body\] attribute' 'external_body/assume_specification not allowed'
  cheat c-stdmap 's = s.replace("// FIXED-BEGIN types\n", "use std::collections::HashMap as StdMap;\n\n// FIXED-BEGIN types\n")' \
    'forbidden: line [0-9]+: std::collections'
  cheat d-comment 's = s.replace("    // FIXED-BEGIN insert\n", "    /*\n    // FIXED-BEGIN insert\n").replace("    // FIXED-END insert\n    {\n        todo!()\n    }\n", "    // FIXED-END insert\n    {\n        todo!()\n    }\n    */\n    pub fn insert(&mut self, key: u64, value: V) -> (r: Option<V>) { None }\n")' \
    'forbidden: line [0-9]+: block comment' 'error: assertion failed'
  cheat e-outside 's = s.replace("// FIXED-END verus-end\n", "// FIXED-END verus-end\nfn helper() {}\n")' \
    'forbidden: line [0-9]+: code outside the verus! block'
else
  expect untouched "$work/sandbox" '^hole: line [0-9]+: todo!\(\)' 'scan: 1 hole'
  cheat a-admit 's = s.replace("// FIXED-END quicksort\n{\n    todo!()", "// FIXED-END quicksort\n{\n    proof { admit(); }")' \
    'forbidden: line [0-9]+: admit' 'assume/admit not allowed with --no-cheating'
  cheat b-fixed 's = s.replace("    a.to_multiset() == b.to_multiset()\n", "    true\n")' \
    'FIXED region defs changed' 'error: assertion failed'
  cheat c-sort 's = s.replace("// FIXED-END quicksort\n{\n    todo!()", "// FIXED-END quicksort\n{\n    a.sort()")' \
    'forbidden: line [0-9]+: library sort'
  cheat c-vec 's = s.replace("// FIXED-END quicksort\n{\n    todo!()", "// FIXED-END quicksort\n{\n    let v: Vec<u64> = a.to_vec();\n    todo!()")' \
    'forbidden: line [0-9]+: allocation' 'forbidden: line [0-9]+: copying'
  cheat d-macro 's = s.replace("// FIXED-BEGIN defs\n", "const _S: &str = stringify!(\n// FIXED-BEGIN defs\n").replace("// FIXED-END defs\n", "// FIXED-END defs\n);\npub open spec fn sorted(s: Seq<u64>) -> bool { true }\npub open spec fn perm(a: Seq<u64>, b: Seq<u64>) -> bool { true }\n")' \
    'forbidden: line [0-9]+: macro or attribute argument runs into a FIXED region'
  cheat e-outside 's = s.replace("// FIXED-END verus-end\n", "// FIXED-END verus-end\nfn helper() {}\n")' \
    'forbidden: line [0-9]+: code outside the verus! block'
fi

echo "validate ($NAME): $ok ok, $bad failed (work dir: $work)"
[ $bad -eq 0 ]
