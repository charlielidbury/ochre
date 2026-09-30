#!/usr/bin/env python3
"""Transcribe ../../tests.json into tests/spec.rs, one #[test] per case.

Run from anywhere: python3 tools/gen_tests.py. The output is a FIXED file: the
whole of tests/spec.rs sits in one FIXED region, so grade.sh rejects any edit.
"""
import json
import pathlib

PKG = pathlib.Path(__file__).resolve().parent.parent
SRC = PKG.parent / "tests.json"
OUT = PKG / "tests" / "spec.rs"


def arr(xs):
    return "[" + ", ".join(f"{x}u64" if i == 0 else str(x) for i, x in enumerate(xs)) + "]"


def main():
    doc = json.loads(SRC.read_text())
    out = [
        "// FIXED-BEGIN tests",
        "// Generated mechanically from the benchmark's test vectors. Do not edit.",
        "// Each test sorts one input in place and checks it against the expected output.",
        "use quicksort::quicksort;",
        "",
    ]
    for case in doc["cases"]:
        name = case["name"].replace("-", "_")
        out.append("#[test]")
        out.append(f"fn {name}() {{")
        if case["input"]:
            out.append(f"    let mut a = {arr(case['input'])};")
            out.append(f"    quicksort(&mut a);")
            out.append(f"    assert_eq!(a, {arr(case['expected'])});")
        else:
            out.append("    let mut a: [u64; 0] = [];")
            out.append("    quicksort(&mut a);")
            out.append("    assert_eq!(a, [0u64; 0]);")
        out.append("}")
        out.append("")
    out.append("// FIXED-END tests")
    OUT.write_text("\n".join(out) + "\n")
    print(f"wrote {OUT.relative_to(PKG)}: {len(doc['cases'])} tests")


if __name__ == "__main__":
    main()
