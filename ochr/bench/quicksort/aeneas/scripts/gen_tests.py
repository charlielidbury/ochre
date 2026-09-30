#!/usr/bin/env python3
"""Transcribe ../../tests.json (SPEC.md section 6) into rust/tests/spec.rs.

    scripts/gen_tests.py [TESTS_JSON]

Run once by the package author; the output is committed as a FIXED region.
"""
import json
import os
import sys

here = os.path.dirname(os.path.abspath(__file__))
src = sys.argv[1] if len(sys.argv) > 1 else os.path.join(here, "..", "..", "tests.json")
dst = os.path.join(here, "..", "rust", "tests", "spec.rs")


def ident(name):
    return name.replace("-", "_")


def vec(xs):
    return "vec![" + ", ".join(str(x) for x in xs) + "]"


with open(src) as f:
    data = json.load(f)

out = [
    "// FIXED-BEGIN tests",
    "// Transcribed mechanically from the benchmark's test vectors (tests.json). Do not edit.",
    "use quicksort::quicksort;",
]
for case in data["cases"]:
    out += [
        "",
        "#[test]",
        f"fn {ident(case['name'])}() {{",
        f"    let mut a: Vec<u64> = {vec(case['input'])};",
        "    quicksort(&mut a);",
        f"    let expected: Vec<u64> = {vec(case['expected'])};",
        "    assert_eq!(a, expected);",
        "}",
    ]
out.append("// FIXED-END tests")

os.makedirs(os.path.dirname(dst), exist_ok=True)
with open(dst, "w") as f:
    f.write("\n".join(out) + "\n")
print(f"wrote {dst}: {len(data['cases'])} cases")
