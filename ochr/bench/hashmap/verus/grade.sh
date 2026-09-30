#!/usr/bin/env bash
# grade.sh: grade the Verus solution in src/hashmap.rs. Exits 0 iff all of:
#   1. every FIXED region is byte-identical to the skeleton's (check_fixed.py);
#   2. no hole and no forbidden construct remains outside the FIXED regions;
#   3. the solution, with the grader's witness appended, verifies with
#      `verus --no-cheating`. The witness restates every FIXED contract through calls,
#      so it verifies only if the FIXED items are in force as written;
#   4. it compiles (`verus --no-verify --compile`), and the binary passes every test
#      transcribed from tests.json. (The tests run even when verification fails.)
# Every check runs even when an earlier one fails. The last line printed is the verdict,
# `GRADE: PASS ...` or `GRADE: FAIL ...`, with the solution's line count (non-blank lines
# outside the FIXED regions).
#
# Environment: VERUS=/path/to/verus overrides the verifier (it must be the pinned
# version below); ORIGINAL=/path/to/skeleton.rs overrides the pristine skeleton.
set -uo pipefail

NAME=hashmap
PIN=0.2026.09.27.3cf1832

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
src="$here/src/$NAME.rs"
out="$here/target"
mkdir -p "$out"

# The pristine skeleton and the FIXED-region checker: in a sandbox they live in
# .grader/; in the benchmark tree the checker is shared and the skeleton is src/ itself.
if [ -d "$here/.grader" ]; then
  checker="$here/.grader/check_fixed.py"
  original="${ORIGINAL:-$here/.grader/skeleton/$NAME.rs}"
else
  checker="$here/../../common/check_fixed.py"
  original="${ORIGINAL:-$src}"
fi

# The pinned verus: $VERUS, else `verus` on PATH if it is the pinned version, else the
# flake's build (offline if it is already in the nix store).
verus="${VERUS:-$(command -v verus || true)}"
if [ -z "$verus" ] || ! "$verus" --version 2>/dev/null | grep -q "$PIN"; then
  [ -n "${VERUS:-}" ] && { echo "GRADE: FAIL (\$VERUS is not verus $PIN)"; exit 2; }
  verus="$(nix build --no-link --print-out-paths "path:$here#verus" 2>/dev/null)/bin/verus"
  [ -x "$verus" ] || { echo "GRADE: FAIL (cannot find verus $PIN; run inside \`nix develop\`)"; exit 2; }
fi

fails=()

echo "== 1. FIXED regions (check_fixed.py)"
fixed_out="$(python3 "$checker" "$original" "$src")"; fixed_rc=$?
echo "$fixed_out"
[ $fixed_rc -eq 0 ] || fails+=("FIXED regions changed")
lines="$(echo "$fixed_out" | sed -n 's/.*solution \([0-9]*\)$/\1/p')"
skel_lines="$(echo "$fixed_out" | sed -n 's/.*skeleton \([0-9]*\), solution.*/\1/p')"

echo "== 2. holes and forbidden constructs"
scan_out="$(python3 - "$src" "$NAME" <<'PY'
import re, sys

path, name = sys.argv[1], sys.argv[2]
lines = open(path, encoding="utf-8", errors="replace").read().split("\n")
holes, bad = [], []

# Split the file into FIXED regions (checked by check_fixed.py) and the solver's chunks
# between them, and find where the verus! body starts and ends.
MARKER = re.compile(r"(?<![\w-])FIXED-(BEGIN|END)(?![\w-])[ \t]*([A-Za-z0-9_.:/-]*)")
inside, chunks, cur, body_start, body_end = False, [], [], None, None
for i, l in enumerate(lines, 1):
    m = MARKER.search(l)
    if m and m.group(1) == "BEGIN":
        inside = True
        chunks.append(cur)
        cur = []
        if m.group(2) == "verus-end":
            body_end = i
    elif m:
        inside = False
        if m.group(2) == "prelude":
            body_start = i
    elif not inside:
        cur.append((i, l))
chunks.append(cur)

# Lex each chunk: drop comments, and reject block comments, raw strings, and string
# literals or macro arguments left open at the end of a chunk (they would swallow the
# FIXED region that follows).
code_lines = {}
for chunk in chunks:
    if not chunk:
        continue
    text = "\n".join(l for _, l in chunk)
    nums = [n for n, _ in chunk]
    line_at = lambda off: nums[text.count("\n", 0, off)]
    out, i, stack = [], 0, []
    while i < len(text):
        c = text[i]
        if text.startswith("//", i):
            j = text.find("\n", i)
            i = len(text) if j < 0 else j
            continue
        if text.startswith("/*", i) or text.startswith("*/", i):
            bad.append((line_at(i), "block comment (use // comments)"))
            i += 2
            continue
        if c == '"':
            if re.search(r"\bb?r#*$", "".join(out[-4:])):
                bad.append((line_at(i), "raw string"))
            j = i + 1
            while j < len(text) and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            if j >= len(text):
                bad.append((line_at(i), "string literal runs into a FIXED region"))
            out.append(text[i:j + 1].replace("\n", " "))
            i = j + 1
            continue
        if c == "'":
            m = re.match(r"'(\\u\{[0-9a-fA-F]+\}|\\.|[^\\'])'", text[i:])
            if m:
                out.append(m.group(0))
                i += len(m.group(0))
                continue
        if c in "([{":
            # a macro's or an attribute's argument, or anything nested in one
            before = "".join(out[-40:])
            swallows = bool(re.search(r"\w\s*!\s*$", before)
                            or (c == "[" and re.search(r"#\s*!?\s*$", before))
                            or any(s for _, s, _ in stack))
            stack.append((c, swallows, i))
        elif c in ")]}" and stack:
            stack.pop()
        out.append(c)
        i += 1
    for _, swallows, off in stack:
        if swallows:
            bad.append((line_at(off), "macro or attribute argument runs into a FIXED region"))
    for k, l in enumerate("".join(out).split("\n")):
        code_lines[nums[k]] = l

if body_start is None or body_end is None:
    bad.append((0, "cannot find the FIXED prelude / verus-end regions"))
else:
    for n, l in code_lines.items():
        if l.strip() and not (body_start < n < body_end):
            bad.append((n, "code outside the verus! block"))

def matches(pat):
    for n, l in sorted(code_lines.items()):
        for m in re.finditer(pat, l):
            yield n, m

for pat, what in [(r"\btodo\s*!", "todo!()"), (r"\bunimplemented\s*!", "unimplemented!()"),
                  (r"\barbitrary\s*\(", "arbitrary()")]:
    holes += [(n, what) for n, _ in matches(pat)]

FORBIDDEN = [
    (r"\bassume\s*\(", "assume"),
    (r"\badmit\s*\(", "admit"),
    (r"\bassume_specification\b", "assume_specification"),
    (r"\baxiom\b", "axiom"),
    (r"\bunsafe\b", "unsafe"),
    (r"\bexternal_body\b|\bexternal_fn_specification\b|\bexternal_type_specification\b", "external specification"),
    (r"\bassume_termination\b|\bexec_allows_no_decreases_clause\b", "termination escape"),
    (r"\bverus\s*!", "a second verus! block"),
    (r"\bmacro_rules\s*!", "macro_rules!"),
    (r"\binclude(_str|_bytes)?\s*!", "include!"),
    (r"\bextern\s+crate\b", "extern crate"),
    (r"\bmod\s+\w+\s*;", "out-of-line module"),
    (r"\bcfg\s*!", "cfg!"),
    (r"\bprocess\s*::", "std::process"),
    (r"\bexec_spec\w*\b|\bcontrib\b", "vstd::contrib::exec_spec"),
    (r"\bcollections\b", "std::collections"),
    (r"\bhash_map\b|\bhash_set\b|\bHashMapWithView\b|\bHashSetWithView\b|\bStringHashMap\b"
     r"|\bStringHashSet\b|\bBTreeMap\b|\bBTreeSet\b|\bVecDeque\b", "library map, set or deque"),
]
EXTRA = {
    "hashmap": [
        (r"\bclone\b|\bClone\b|\bto_vec\b|\bto_owned\b", "copying (clone/to_vec/to_owned)"),
    ],
    "quicksort": [
        (r"\bVec\b|\bvec\s*!|\bBox\b", "allocation (Vec/vec!/Box)"),
        (r"\bclone\b|\bClone\b|\bto_vec\b|\bto_owned\b|\bclone_from_slice\b|\bcopy_from_slice\b"
         r"|\bcopy_within\b", "copying"),
        (r"\.\s*sort\w*\s*\(|\bsort_by\w*\b|\bsort_unstable\w*\b|\bselect_nth_unstable\w*\b",
         "library sort"),
    ],
}
for pat, what in FORBIDDEN + EXTRA.get(name, []):
    bad += [(n, what) for n, _ in matches(pat)]

# Attributes: only these #[verifier::...] attributes may be added; none weakens checking.
ALLOWED = {"opaque", "rlimit", "spinoff_prover", "nonlinear", "bit_vector", "integer_ring",
           "loop_isolation", "auto_ext_equal", "ext_equal", "inline", "memoize", "truncate",
           "type_invariant", "when_used_as_spec", "allow_in_spec", "accept_recursive_types",
           "reject_recursive_types", "reject_recursive_types_in_ground_variants",
           "no_auto_trigger", "decreases_by", "opaque_outside_module", "prophetic"}
for n, m in matches(r"#\s*(!?)\s*\[\s*([A-Za-z_]\w*)\s*(::\s*([A-Za-z_]\w*)|\()?"):
    inner, head, sub = m.group(1), m.group(2), m.group(4)
    if head == "verifier":
        if sub is None:
            bad.append((n, "#[verifier(...)] attribute"))
        elif sub not in ALLOWED:
            bad.append((n, f"#[verifier::{sub}] attribute"))
    elif head.startswith("verus"):
        bad.append((n, f"#[{head}...] attribute"))
    elif head in ("cfg", "cfg_attr", "path"):
        bad.append((n, f"#[{head}] attribute"))
    elif inner and head not in ("trigger", "auto"):
        bad.append((n, f"#![{head}] inner attribute"))

for n, what in sorted(set(holes)):
    print(f"hole: line {n}: {what}")
for n, what in sorted(set(bad)):
    print(f"forbidden: line {n}: {what}")
print(f"scan: {len(set(holes))} hole(s), {len(set(bad))} forbidden construct(s)")
sys.exit(1 if holes or bad else 0)
PY
)"; scan_rc=$?
echo "$scan_out"
nholes="$(echo "$scan_out" | grep -c '^hole:')"
nbad="$(echo "$scan_out" | grep -c '^forbidden:')"
[ "$nholes" -eq 0 ] || fails+=("$nholes hole(s)")
[ "$nbad" -eq 0 ] || fails+=("$nbad forbidden construct(s)")
[ $scan_rc -eq 0 ] || [ "$nholes$nbad" != "00" ] || fails+=("scanner error")

echo "== 3. verify (verus $PIN --no-cheating, with the grader's witness)"
graded="$out/graded_$NAME.rs"
cat "$src" - >"$graded" <<'WITNESS'

// Grader witness, appended by grade.sh (not part of the skeleton or the solution). It
// restates every FIXED contract through calls, so it verifies only if the FIXED items
// are in force exactly as written.
verus! {

fn grader_witness_types(l: List, m: HashMap) {
    match l {
        List::Cons(k, v, next) => {
            let _k: u64 = k;
            let _v: u64 = v;
            let _next: Box<List> = next;
        },
        List::Nil => {},
    }
    let HashMap { slots, len } = m;
    let _slots: Vec<List> = slots;
    let _len: u64 = len;
}

fn grader_witness_bucket_index(key: u64, cap: usize)
    requires
        cap > 0,
{
    let i = bucket_index(key, cap);
    assert(i == key as int % cap as int);
}

fn grader_witness_new(cap: usize, k: u64)
    requires
        cap > 0,
{
    let m = HashMap::new(cap);
    assert(m.inv());
    assert(m.spec_get(k) == None::<u64>);
    assert(m.spec_len() == 0);
}

fn grader_witness_len_get(m: &HashMap, k: u64)
    requires
        m.inv(),
{
    let n = m.len();
    assert(n == m.spec_len());
    let r = m.get(k);
    assert(r == m.spec_get(k));
}

fn grader_witness_insert(m: &mut HashMap, k: u64, v: u64, k2: u64)
    requires
        old(m).inv(),
        old(m).spec_len() < u64::MAX,
        k2 != k,
{
    let ghost m0 = *m;
    let r = m.insert(k, v);
    assert(m.inv());
    assert(m.spec_get(k) == Some(v));
    assert(m.spec_get(k2) == m0.spec_get(k2));
    assert(r == m0.spec_get(k));
    assert(m.spec_len() == if m0.spec_get(k) is None { m0.spec_len() + 1 } else { m0.spec_len() });
}

fn grader_witness_remove(m: &mut HashMap, k: u64, k2: u64)
    requires
        old(m).inv(),
        k2 != k,
{
    let ghost m0 = *m;
    let r = m.remove(k);
    assert(m.inv());
    assert(m.spec_get(k) == None::<u64>);
    assert(m.spec_get(k2) == m0.spec_get(k2));
    assert(r == m0.spec_get(k));
    assert(m.spec_len() == if m0.spec_get(k) is Some { m0.spec_len() - 1 } else { m0.spec_len() as int });
}

fn grader_witness_get_mut(m: &mut HashMap, k: u64, w: u64, k2: u64)
    requires
        old(m).inv(),
        old(m).spec_get(k) is Some,
        k2 != k,
{
    let ghost m0 = *m;
    let r = m.get_mut(k);
    *r = w;
    assert(m.spec_get(k) == Some(w));
    assert(m.spec_get(k2) == m0.spec_get(k2));
    assert(m.spec_len() == m0.spec_len());
    assert(m.inv());
}

} // verus!
WITNESS
(cd "$out" && timeout 3600 "$verus" --no-cheating --triggers-mode silent "$graded") >"$out/verus.log" 2>&1
verus_rc=$?
grep -E "^(error|warning)|^ *--> |^verification results" "$out/verus.log" | head -80
results="$(grep -o 'verification results:: [0-9]* verified, [0-9]* errors' "$out/verus.log" | tail -1)"
if [ $verus_rc -ne 0 ] || ! echo "$results" | grep -q ' 0 errors$'; then
  fails+=("verification failed${results:+ ($results)}")
fi
echo "(verified file: target/graded_$NAME.rs = src/$NAME.rs + witness, same line numbers; full log: target/verus.log)"

echo "== 4. compile and run the tests"
rm -f "$out/$NAME"
(cd "$out" && timeout 1200 "$verus" --no-verify "$src" --compile -o "$out/$NAME") >"$out/compile.log" 2>&1
if [ ! -x "$out/$NAME" ]; then
  grep -E "^(error|warning)|^ *--> " "$out/compile.log" | head -40
  fails+=("compilation failed")
fi
if [ -x "$out/$NAME" ]; then
  test_out="$(timeout 300 "$out/$NAME" 2>&1)"; test_rc=$?
  echo "$test_out" | tail -40
  [ $test_rc -eq 0 ] && echo "$test_out" | grep -q '^tests: [0-9]* passed, 0 failed$' || fails+=("tests failed")
else
  echo "tests not run (no binary; full log: target/compile.log)"
fi

summary="non-blank lines outside FIXED regions: skeleton ${skel_lines:-?}, solution ${lines:-?}"
if [ ${#fails[@]} -eq 0 ]; then
  echo "GRADE: PASS ($NAME, verus $PIN; $summary)"
  exit 0
fi
reasons="$(printf '%s; ' "${fails[@]}")"
echo "GRADE: FAIL ($NAME: ${reasons%; }; $summary)"
exit 1
