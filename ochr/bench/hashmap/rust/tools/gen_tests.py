#!/usr/bin/env python3
"""Transcribe ../../tests.json into tests/spec.rs, one #[test] per sequence.

Run from anywhere: python3 tools/gen_tests.py. The output is a FIXED file: the
whole of tests/spec.rs sits in one FIXED region, so grade.sh rejects any edit.
"""
import json
import pathlib

PKG = pathlib.Path(__file__).resolve().parent.parent
SRC = PKG.parent / "tests.json"
OUT = PKG / "tests" / "spec.rs"


def opt(x):
    return "None" if x is None else f"Some({x})"


def main():
    doc = json.loads(SRC.read_text())
    out = [
        "// FIXED-BEGIN tests",
        "// Generated mechanically from the benchmark's test vectors. Do not edit.",
        "// Each test replays one sequence of operations (see ASSIGNMENT.md) on one map, checking the",
        "// result of every op and len() after it.",
        "use hashmap::HashMap;",
        "",
    ]
    names = []
    for seq in doc["sequences"]:
        name = seq["name"].replace("-", "_")
        names.append(name)
        out.append("#[test]")
        out.append(f"fn {name}() {{")
        out.append(f"    let mut m = HashMap::new({seq['cap']});")
        for i, op in enumerate(seq["ops"]):
            k = op["key"]
            if op["op"] == "insert":
                call = f"m.insert({k}, {op['value']})"
                out.append(f"    assert_eq!({call}, {opt(op['expect'])}, \"op {i}: insert({k}, {op['value']})\");")
            elif op["op"] == "get":
                out.append(f"    assert_eq!(m.get({k}), {opt(op['expect'])}, \"op {i}: get({k})\");")
            elif op["op"] == "remove":
                out.append(f"    assert_eq!(m.remove({k}), {opt(op['expect'])}, \"op {i}: remove({k})\");")
            elif op["op"] == "get_mut":
                out.append(f"    *m.get_mut({k}) = {op['value']};")
            else:
                raise ValueError(op["op"])
            out.append(f"    assert_eq!(m.len(), {op['len']}, \"op {i}: len after {op['op']}\");")
        out.append("}")
        out.append("")
    out.append("// FIXED-END tests")
    OUT.write_text("\n".join(out) + "\n")
    print(f"wrote {OUT.relative_to(PKG)}: {len(names)} tests, {sum(len(s['ops']) for s in doc['sequences'])} ops")


if __name__ == "__main__":
    main()
