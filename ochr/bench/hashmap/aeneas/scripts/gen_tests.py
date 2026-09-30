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


def opt(x):
    return "None" if x is None else f"Some({x})"


def ident(name):
    return name.replace("-", "_")


with open(src) as f:
    data = json.load(f)

out = [
    "// FIXED-BEGIN tests",
    "// Transcribed mechanically from the benchmark's test vectors (tests.json). Do not edit.",
    "use hashmap::HashMap;",
]
for seq in data["sequences"]:
    out += ["", "#[test]", f"fn {ident(seq['name'])}() {{", f"    let mut m = HashMap::new({seq['cap']});"]
    for i, op in enumerate(seq["ops"]):
        tag = f"{seq['name']} op {i}"
        k = op["key"]
        if op["op"] == "insert":
            out.append(f'    assert_eq!(m.insert({k}, {op["value"]}), {opt(op["expect"])}, "{tag}: insert({k}, {op["value"]})");')
        elif op["op"] == "get":
            out.append(f'    assert_eq!(m.get({k}), {opt(op["expect"])}, "{tag}: get({k})");')
        elif op["op"] == "remove":
            out.append(f'    assert_eq!(m.remove({k}), {opt(op["expect"])}, "{tag}: remove({k})");')
        elif op["op"] == "get_mut":
            out.append(f'    *m.get_mut({k}) = {op["value"]};')
        else:
            sys.exit(f"unknown op {op['op']!r} in {tag}")
        out.append(f'    assert_eq!(m.len(), {op["len"]}, "{tag}: len");')
    out.append("}")
out.append("// FIXED-END tests")

os.makedirs(os.path.dirname(dst), exist_ok=True)
with open(dst, "w") as f:
    f.write("\n".join(out) + "\n")
n = sum(len(s["ops"]) for s in data["sequences"])
print(f"wrote {dst}: {len(data['sequences'])} sequences, {n} ops")
