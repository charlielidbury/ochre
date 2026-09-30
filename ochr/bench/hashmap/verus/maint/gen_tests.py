#!/usr/bin/env python3
"""Transcribe ../tests.json into the FIXED `tests` region of src/hashmap.rs.

Maintainer tool; it is not copied into sandboxes. Run it after tests.json changes:

    python3 maint/gen_tests.py          # rewrite the region
    python3 maint/gen_tests.py --check  # exit 1 if the region is out of date
"""
import json
import pathlib
import re
import sys

PKG = pathlib.Path(__file__).resolve().parent.parent
TESTS = PKG.parent / "tests.json"
SRC = PKG / "src" / "hashmap.rs"

HEADER = """\
// The tests, transcribed mechanically from tests.json (SPEC section 6) by a script.
// They run as ordinary Rust in the compiled binary: `./grade.sh` builds it with
// `verus --compile` and runs it. Each sequence starts from `HashMap::new(cap)`; after
// every op the result (if any) and then `len` are checked.

struct Tally {
    passed: u64,
    failed: u64,
}

impl Tally {
    fn opt(&mut self, what: &str, got: Option<u64>, want: Option<u64>) {
        if got == want {
            self.passed += 1;
        } else {
            self.failed += 1;
            println!("FAIL {what}: got {got:?}, expected {want:?}");
        }
    }

    fn len(&mut self, what: &str, got: u64, want: u64) {
        if got == want {
            self.passed += 1;
        } else {
            self.failed += 1;
            println!("FAIL {what}: len is {got}, expected {want}");
        }
    }
}
"""


def opt(x):
    return "None" if x is None else f"Some({x})"


def fn_name(name):
    return "seq_" + re.sub(r"[^a-z0-9]+", "_", name.lower()).strip("_")


def sequence(seq):
    name = seq["name"]
    out = [f"fn {fn_name(name)}(t: &mut Tally) {{", f"    let mut m = HashMap::new({seq['cap']});"]
    for i, o in enumerate(seq["ops"], 1):
        k = o["key"]
        tag = f"{name} op {i}"
        if o["op"] == "get":
            call = f'let r = m.get({k}); t.opt("{tag}: get({k})", r, {opt(o["expect"])});'
        elif o["op"] == "insert":
            v = o["value"]
            call = f'let r = m.insert({k}, {v}); t.opt("{tag}: insert({k}, {v})", r, {opt(o["expect"])});'
        elif o["op"] == "remove":
            call = f'let r = m.remove({k}); t.opt("{tag}: remove({k})", r, {opt(o["expect"])});'
        elif o["op"] == "get_mut":
            call = f"*m.get_mut({k}) = {o['value']};"
        else:
            raise SystemExit(f"unknown op {o['op']!r} in {name}")
        out.append(f'    {call} let n = m.len(); t.len("{tag}", n, {o["len"]});')
    out.append("}")
    return "\n".join(out)


def region():
    data = json.loads(TESTS.read_text())
    seqs = data["sequences"]
    parts = [HEADER]
    parts += [sequence(s) + "\n" for s in seqs]
    main = ["fn main() {", "    let mut t = Tally { passed: 0, failed: 0 };"]
    main += [f"    {fn_name(s['name'])}(&mut t);" for s in seqs]
    main += [
        '    println!("tests: {} passed, {} failed", t.passed, t.failed);',
        "    if t.failed > 0 {",
        "        std::process::exit(1);",
        "    }",
        "}",
    ]
    parts.append("\n".join(main))
    return "\n".join(parts) + "\n"


def main():
    src = SRC.read_text()
    pat = re.compile(r"(// FIXED-BEGIN tests\n)(.*?)(// FIXED-END tests\n)", re.S)
    m = pat.search(src)
    if not m:
        raise SystemExit("no FIXED tests region in " + str(SRC))
    body = region()
    if "--check" in sys.argv:
        if m.group(2) != body:
            print("tests region is out of date with tests.json")
            sys.exit(1)
        print("tests region matches tests.json")
        return
    SRC.write_text(src[: m.start(2)] + body + src[m.end(2) :])
    print(f"wrote {SRC.relative_to(PKG)} tests region from {TESTS.name}")


if __name__ == "__main__":
    main()
