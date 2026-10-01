#!/usr/bin/env python3
"""Transcribe a problem's tests.json into the tests of an Ochr skeleton.

    gen_tests.py SKELETON.lean [--check]

The problem is read off the skeleton's name (Quicksort.lean or HashMap.lean) and the tests
from ../tests.json next to the package. The generated declarations replace the lines between
`-- BEGIN GENERATED TESTS` and `-- END GENERATED TESTS` (which sit inside a FIXED region).
With --check nothing is written, and the exit status is 1 if the skeleton's tests differ
from what tests.json gives.

Numbers are written `W(n)`, the arrays library's `Word` for the numeral n.

Quicksort (SPEC §6): one test per case. The input and the expected output are array literals
written at their type; the test sorts the input in place and compares the whole array,
`Id(Array(Word, W(n)), (let a : Array(Word, W(n)) = [input]; QuickSort(...); a), ([expected] :
Array(Word, W(n)))) := refl`. One negative test follows: the `mixed` case with its unsorted input
as the expected output, which must be rejected.

Hashmap (SPEC §6): one test per sequence, at `V := Word`. The program starts from
`MapNew(Word, cap, refl)`, runs the ops in order, and collects each op's result and the length
after it in a `Trace`, which is compared with the expected trace: `TOp(r, l, rest)` for insert
and remove (r the returned `Opt(Word)`, l = len); for get, `THas(false, l, rest)` when the key
is absent (`MapContains`), and `TGet(w, l, rest)` when it is present (the value read through
`MapGet`, whose precondition `refl` proves only if the key is there); `TWrite(l, rest)` for a
write through get_mut. One negative test follows: the scripted sequence's first insert with a
wrong expected result.
"""
import json
import os
import sys

BEGIN = "  -- BEGIN GENERATED TESTS\n"
END = "  -- END GENERATED TESTS\n"


def W(n):
    return f"W({n})"


def lit(xs):
    return "[" + ", ".join(W(x) for x in xs) + "]"


def ident(name):
    return "Test_" + "".join(c if c.isalnum() else "_" for c in name)


def quicksort(tests):
    out = []
    for c in tests["cases"]:
        n = len(c["input"])
        out.append(f"  -- {c['name']}: {c['input']} ↦ {c['expected']}\n")
        out.append(f"  def {ident(c['name'])} : Id(Array(Word, {W(n)}), "
                   f"(let a : Array(Word, {W(n)}) = {lit(c['input'])}; QuickSort({W(n)}, AsSlice(Word, {W(n)}, &a)); a), "
                   f"({lit(c['expected'])} : Array(Word, {W(n)}))) := refl\n")
    mixed = next(c for c in tests["cases"] if c["name"] == "mixed")
    n = len(mixed["input"])
    out.append(f"  -- must be rejected: the expected array is the unsorted input {mixed['input']}\n")
    out.append(f"  reject def TestReject_unsorted : Id(Array(Word, {W(n)}), "
               f"(let a : Array(Word, {W(n)}) = {lit(mixed['input'])}; QuickSort({W(n)}, AsSlice(Word, {W(n)}, &a)); a), "
               f"({lit(mixed['input'])} : Array(Word, {W(n)}))) := refl\n")
    return out


def opt(v):
    return "None[Word]" if v is None else f"Some({W(v)})"


def hashmap_prog(seq, ops):
    cap = W(seq["cap"])
    lets, trace = [f"let m = MapNew(Word, {cap}, refl)"], []
    for i, op in enumerate(ops):
        k = W(op["key"])
        if op["op"] == "insert":
            lets.append(f"let r{i} = MapInsert(Word, {cap}, &m, {k}, {W(op['value'])})")
        elif op["op"] == "get" and op["expect"] is None:
            lets.append(f"let r{i} = MapContains(Word, {cap}, &m, {k})")
        elif op["op"] == "get":
            lets.append(f"let r{i} = *MapGet(Word, {cap}, &m, {k}, refl)")
        elif op["op"] == "remove":
            lets.append(f"let r{i} = MapRemove(Word, {cap}, &m, {k})")
        elif op["op"] == "get_mut":
            lets.append(f"*MapGetMut(Word, {cap}, &m, {k}, refl) := {W(op['value'])}")
        else:
            raise SystemExit(f"unknown op {op['op']}")
        lets.append(f"let l{i} = MapLen(Word, {cap}, &m)")
        trace.append((i, op))

    def node(i, op, rest, expected):
        if op["op"] == "get_mut":
            return f"TWrite({W(op['len']) if expected else f'l{i}'}, {rest})"
        if op["op"] == "get" and op["expect"] is None:
            return f"THas({'false' if expected else f'r{i}'}, {W(op['len']) if expected else f'l{i}'}, {rest})"
        if op["op"] == "get":
            return f"TGet({W(op['expect']) if expected else f'r{i}'}, {W(op['len']) if expected else f'l{i}'}, {rest})"
        return f"TOp({opt(op['expect']) if expected else f'r{i}'}, {W(op['len']) if expected else f'l{i}'}, {rest})"
    t = "TEnd"
    for i, op in reversed(trace):
        t = node(i, op, t, False)
    exp = "TEnd"
    for i, op in reversed(trace):
        exp = node(i, op, exp, True)
    return "; ".join(lets + [t]), exp


def hashmap(tests):
    out = []
    for seq in tests["sequences"]:
        prog, exp = hashmap_prog(seq, seq["ops"])
        out.append(f"  -- {seq['name']}: {len(seq['ops'])} ops on new({seq['cap']})\n")
        out.append(f"  def {ident(seq['name'])} : Id(Trace, ({prog}), {exp}) := refl\n")
    seq = next(s for s in tests["sequences"] if s["name"] == "scripted")
    first = next(o for o in seq["ops"] if o["op"] == "insert")
    wrong = dict(first, expect=(first["value"] + 1))
    prog, exp = hashmap_prog(seq, [wrong])
    out.append(f"  -- must be rejected: a fresh map's first insert returns None, not Some\n")
    out.append(f"  reject def TestReject_insert : Id(Trace, ({prog}), {exp}) := refl\n")
    return out


def main(argv):
    check = "--check" in argv
    args = [a for a in argv if a != "--check"]
    if len(args) != 1:
        print(__doc__)
        return 2
    path = os.path.abspath(args[0])
    tests_path = os.path.join(os.path.dirname(os.path.dirname(path)), "tests.json")
    tests = json.load(open(tests_path))
    base = os.path.basename(path)
    if base == "Quicksort.lean":
        body = quicksort(tests)
    elif base == "HashMap.lean":
        body = hashmap(tests)
    else:
        print(f"unknown skeleton {base}")
        return 2
    text = open(path, encoding="utf-8").read()
    if text.count(BEGIN) != 1 or text.count(END) != 1:
        print(f"{path}: needs exactly one BEGIN and one END GENERATED TESTS line")
        return 2
    head, rest = text.split(BEGIN)
    _, tail = rest.split(END)
    new = head + BEGIN + "".join(body) + END + tail
    if check:
        if new != text:
            print(f"{path}: the tests differ from {tests_path}")
            return 1
        print(f"{path}: the tests are {tests_path}, transcribed")
        return 0
    with open(path, "w", encoding="utf-8") as h:
        h.write(new)
    print(f"{path}: wrote {sum(1 for l in body if l.lstrip().startswith(('def', 'reject')))} tests")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
