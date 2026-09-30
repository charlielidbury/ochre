#!/usr/bin/env python3
"""Transcribe ../tests.json into the FIXED `tests` region of src/quicksort.rs.

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
SRC = PKG / "src" / "quicksort.rs"

HEADER = """\
// The tests, transcribed mechanically from tests.json (SPEC section 6) by a script.
// They run as ordinary Rust in the compiled binary: `./grade.sh` builds it with
// `verus --compile` and runs it. Each case sorts a fresh copy of `input` in place
// and compares it with `expected`.

struct Tally {
    passed: u64,
    failed: u64,
}

fn case(t: &mut Tally, name: &str, input: &[u64], expected: &[u64]) {
    let mut a = input.to_vec();
    quicksort(&mut a);
    if a == expected {
        t.passed += 1;
    } else {
        t.failed += 1;
        println!("FAIL {name}: got {a:?}, expected {expected:?}");
    }
}
"""


def arr(xs):
    return "&[" + ", ".join(str(x) for x in xs) + "]"


def region():
    cases = json.loads(TESTS.read_text())["cases"]
    main = ["fn main() {", "    let mut t = Tally { passed: 0, failed: 0 };"]
    for c in cases:
        main.append(f'    case(&mut t, "{c["name"]}", {arr(c["input"])}, {arr(c["expected"])});')
    main += [
        '    println!("tests: {} passed, {} failed", t.passed, t.failed);',
        "    if t.failed > 0 {",
        "        std::process::exit(1);",
        "    }",
        "}",
    ]
    return HEADER + "\n" + "\n".join(main) + "\n"


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
