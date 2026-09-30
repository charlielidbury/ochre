#!/usr/bin/env python3
"""Check that a solution keeps every FIXED region of the original byte for byte.

    check_fixed.py ORIGINAL SOLUTION [ORIGINAL SOLUTION ...]
    check_fixed.py --self-test

A FIXED region runs from the line containing the token `FIXED-BEGIN <id>` to the
line containing `FIXED-END <id>`, both lines included. The tokens may appear
anywhere on a line, so any comment syntax works (`-- FIXED-BEGIN defs`,
`// FIXED-BEGIN api`, `/* FIXED-BEGIN types */`, `# FIXED-BEGIN x`).
An id is a run of letters, digits and `_.:/-`.

For each pair the solution must have the same regions, with the same ids, in
the same order, each byte-identical to the original's (marker lines, whitespace
and line endings included). Text outside the regions is not checked.
Regions may not nest, and ids are unique within a file.

Exit status: 0 if every pair passes, 1 if a solution changed, added, removed or
reordered a region (or broke its markers), 2 if an original is malformed or has
no FIXED regions, or a file cannot be read. One line per problem goes to stdout.
On success it also prints the number of non-blank lines outside the FIXED
regions, in the originals and in the solutions, for grade.sh to report.
"""
import os
import re
import sys
import tempfile

MARKER = re.compile(rb"(?<![\w-])FIXED-(BEGIN|END)(?![\w-])[ \t]*([A-Za-z0-9_.:/-]*)")


class Malformed(Exception):
    pass


def regions(data):
    """Return [(id, bytes)] for the FIXED regions of `data`, in order."""
    out = []
    open_id, start, buf = None, None, []
    for lineno, line in enumerate(data.splitlines(keepends=True), 1):
        markers = MARKER.findall(line)
        if len(markers) > 1:
            raise Malformed(f"line {lineno}: more than one FIXED marker on a line")
        if markers:
            kind, rid = markers[0][0].decode(), markers[0][1].decode()
            if not rid:
                raise Malformed(f"line {lineno}: FIXED-{kind} without an id")
            if kind == "BEGIN":
                if open_id is not None:
                    raise Malformed(f"line {lineno}: FIXED-BEGIN {rid} inside region {open_id} (opened at line {start})")
                if any(r == rid for r, _ in out):
                    raise Malformed(f"line {lineno}: duplicate region id {rid}")
                open_id, start, buf = rid, lineno, [line]
                continue
            if open_id is None:
                raise Malformed(f"line {lineno}: FIXED-END {rid} without a FIXED-BEGIN")
            if rid != open_id:
                raise Malformed(f"line {lineno}: FIXED-END {rid} closes region {open_id} (opened at line {start})")
            buf.append(line)
            out.append((open_id, b"".join(buf)))
            open_id = None
            continue
        if open_id is not None:
            buf.append(line)
    if open_id is not None:
        raise Malformed(f"region {open_id} (opened at line {start}) has no FIXED-END")
    return out


def outside_lines(data):
    """Non-blank lines outside every FIXED region (a line count for grade.sh to report)."""
    n, inside = 0, False
    for line in data.splitlines():
        m = MARKER.search(line)
        if m:
            inside = m.group(1) == b"BEGIN"
        elif not inside and line.strip():
            n += 1
    return n


def first_difference(a, b):
    """1-based line number, within the region, of the first differing line."""
    la, lb = a.splitlines(keepends=True), b.splitlines(keepends=True)
    for i, (x, y) in enumerate(zip(la, lb), 1):
        if x != y:
            return i
    return min(len(la), len(lb)) + 1


def check_pair(original, solution):
    """Return (status, messages): 0 ok, 1 solution fault, 2 original fault."""
    try:
        with open(original, "rb") as f:
            orig = f.read()
    except OSError as e:
        return 2, [f"{original}: cannot read: {e.strerror}"]
    try:
        want = regions(orig)
    except Malformed as e:
        return 2, [f"{original}: malformed original: {e}"]
    if not want:
        return 2, [f"{original}: original has no FIXED regions (wrong file?)"]
    try:
        with open(solution, "rb") as f:
            sol = f.read()
    except OSError as e:
        return 1, [f"{solution}: cannot read: {e.strerror}"]
    try:
        got = regions(sol)
    except Malformed as e:
        return 1, [f"{solution}: FIXED markers broken: {e}"]

    msgs = []
    want_ids, got_ids = [r for r, _ in want], [r for r, _ in got]
    for rid in want_ids:
        if rid not in got_ids:
            msgs.append(f"{solution}: FIXED region {rid} removed")
    for rid in got_ids:
        if rid not in want_ids:
            msgs.append(f"{solution}: FIXED region {rid} added")
    common_want = [r for r in want_ids if r in got_ids]
    common_got = [r for r in got_ids if r in want_ids]
    if common_want != common_got:
        msgs.append(f"{solution}: FIXED regions reordered: expected {' '.join(common_want)}, found {' '.join(common_got)}")
    got_map = dict(got)
    for rid, body in want:
        if rid in got_map and got_map[rid] != body:
            msgs.append(f"{solution}: FIXED region {rid} changed (first difference at line {first_difference(body, got_map[rid])} of the region)")
    return (1 if msgs else 0), msgs


def main(argv):
    if argv == ["--self-test"]:
        return self_test()
    if not argv or len(argv) % 2:
        print("usage: check_fixed.py ORIGINAL SOLUTION [ORIGINAL SOLUTION ...] | --self-test")
        return 2
    status, n, lines_orig, lines_sol = 0, 0, 0, 0
    for original, solution in zip(argv[0::2], argv[1::2]):
        s, msgs = check_pair(original, solution)
        for m in msgs:
            print(m)
        status = max(status, s)
        if s == 0:
            with open(original, "rb") as f:
                orig = f.read()
            with open(solution, "rb") as f:
                sol = f.read()
            n += len(regions(orig))
            lines_orig += outside_lines(orig)
            lines_sol += outside_lines(sol)
    if status == 0:
        print(f"check_fixed: OK, {n} FIXED regions identical in {len(argv) // 2} file(s); "
              f"non-blank lines outside FIXED regions: skeleton {lines_orig}, solution {lines_sol}")
    return status


ORIGINAL = b"""\
header, free text
-- FIXED-BEGIN defs
def sorted := 1
-- FIXED-END defs
hole := TODO
/* FIXED-BEGIN api */
fn get(k: u64) -> Option<u64>;
/* FIXED-END api */
# FIXED-BEGIN tests
assert get(1) == None
# FIXED-END tests
"""


def self_test():
    cases = [
        ("identical", ORIGINAL, 0),
        ("text outside regions changed", ORIGINAL.replace(b"hole := TODO", b"hole := 42\nlemma aux := rfl")
            .replace(b"header, free text", b""), 0),
        ("CRLF outside regions", ORIGINAL.replace(b"hole := TODO\n", b"hole := 42\r\n"), 0),
        ("region body edited", ORIGINAL.replace(b"sorted := 1", b"sorted := 2"), 1),
        ("trailing space in region", ORIGINAL.replace(b"-> Option<u64>;", b"-> Option<u64>; "), 1),
        ("marker line edited", ORIGINAL.replace(b"/* FIXED-END api */", b"// FIXED-END api"), 1),
        ("region removed", ORIGINAL.replace(b"# FIXED-BEGIN tests\nassert get(1) == None\n# FIXED-END tests\n", b""), 1),
        ("markers removed, body kept", ORIGINAL.replace(b"-- FIXED-BEGIN defs\n", b"").replace(b"-- FIXED-END defs\n", b""), 1),
        ("region added", ORIGINAL + b"-- FIXED-BEGIN extra\nx\n-- FIXED-END extra\n", 1),
        ("regions reordered", b"-- FIXED-BEGIN defs\ndef sorted := 1\n-- FIXED-END defs\n"
            b"# FIXED-BEGIN tests\nassert get(1) == None\n# FIXED-END tests\n"
            b"/* FIXED-BEGIN api */\nfn get(k: u64) -> Option<u64>;\n/* FIXED-END api */\n", 1),
        ("unclosed region", ORIGINAL.replace(b"# FIXED-END tests\n", b""), 1),
        ("nested region", ORIGINAL.replace(b"def sorted := 1\n", b"-- FIXED-BEGIN inner\ndef sorted := 1\n"), 1),
        ("line ending changed in region", ORIGINAL.replace(b"def sorted := 1\n", b"def sorted := 1\r\n"), 1),
    ]
    failures = 0
    with tempfile.TemporaryDirectory() as d:
        orig = os.path.join(d, "orig")
        with open(orig, "wb") as f:
            f.write(ORIGINAL)
        if [r for r, _ in regions(ORIGINAL)] != ["defs", "api", "tests"] or outside_lines(ORIGINAL) != 2:
            print("self-test FAIL: original parsed or counted wrongly")
            failures += 1
        for name, sol_bytes, expect in cases:
            sol = os.path.join(d, "sol")
            with open(sol, "wb") as f:
                f.write(sol_bytes)
            got, msgs = check_pair(orig, sol)
            if got != expect:
                failures += 1
                print(f"self-test FAIL: {name}: expected status {expect}, got {got}: {msgs}")
        bad = os.path.join(d, "bad")
        with open(bad, "wb") as f:
            f.write(b"-- FIXED-END x\n")
        if check_pair(bad, orig)[0] != 2:
            failures += 1
            print("self-test FAIL: malformed original not reported with status 2")
        empty = os.path.join(d, "empty")
        with open(empty, "wb") as f:
            f.write(b"no regions here\n")
        if check_pair(empty, empty)[0] != 2:
            failures += 1
            print("self-test FAIL: original without regions not reported with status 2")
    print(f"check_fixed self-test: {len(cases) + 3 - failures}/{len(cases) + 3} passed")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
