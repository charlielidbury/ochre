#!/usr/bin/env python3
"""Sizes for the arrays library and the quicksort case study (notes/arrays-library.md §10).

Splits the arrays files (Ochr/Examples/Array.lean, ArrayBench.lean, Quicksort.lean; before the
final layout, 16Arrays.lean) into their declarations (a declaration runs from its
`def`/`inductive` line to the line before the next one, or the end of its `ochr` block),
assigns each to a category by block and by name, and counts code lines and tokens per
category with the comment stripping and tokenizer of hashmap-count.py.

Declarations that moved to the central library are read from there and counted where they
were, so that moving them changes no number: the block `Index` (now `Words` in Word.lean, with
`Dec` in Logic.lean), two of the quicksort's lemmas (`EqBRefl`, `LeOfLt`), `ArrayBench`'s
`ModS`, `LeNext` and `ModLt` (now `Words`'), and `Arrays`' `LenL` (now `Lists`'). `ArrayBench`'s
hash map, now the block `ArrayHashMap`, counts as `ArrayBench`. A name that an arrays block of
the files given still declares (under its old name, `Leb`, `Eqb`, `EqbRefl`) counts there
instead, so older versions count as they did.

The counting rule (docs/12 step 2, 2026-10-21, as for the hash map): the general library is not
counted, and everything written for the case study is. So the two quicksort lemmas now in
`Words` (`EqBRefl`, `LeOfLt`; `EqbRefl` before the rename) are not counted in any version, and
the quicksort's categories hold only what is written for it. `--old-rule` counts them in the
quicksort's categories, as before the rule. `ArrayHashMap` is gone (folded into `HashMap.lean`
with B3's runs); an older file that has it still counts it as `ArrayBench`.

usage: arrays-count.py [--old-rule] [FILE ...]   (default: the current layout; for an old
version, its 16Arrays.lean, with its 00Std.lean when that holds `Words`)
"""
import importlib.util
import os
import re
import sys

here = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("hc", os.path.join(here, "hashmap-count.py"))
hc = importlib.util.module_from_spec(spec)
spec.loader.exec_module(hc)

W = lambda s: s.split()

# the Quicksort block (B2), by the layer each declaration belongs to
QS = {
    "B2 program": W("Scan Partition Recurse QS SortArray"),
    "B2 runs and negative tests": W("SortRun SortRunWrong ContractRun1 ContractRun2 ContractWrong"),
    "B2 spec: Sorted": W("AllLe AllGe Sorted"),
    "B2 proof: perm": W("AddCongL AddCongR CountCong ScanPerm PartitionPerm RecursePerm RecWith QSPerm"),
    "B2 proof: sorted glue": W("""AllGeWeaken AndL AndR AndI AllGeJoin SortedJoin EqBRefl EqBLeLt EqBGeLt
        EqbRefl EqbLeLt EqbGeLt
        CountAboveZero CountBelowZero CountTailZero AllLeOfCounts AllGeOfCounts AllLePerm AllGePerm
        LeSuccFalse RecurseSorted PartK PartV PartLe PartLeft PartPivot PartRight QSSorted"""),
    "B2 proof: partition contract": W("""LeOfLt LtTrans LtLeTrans LtNe LeAntisym LeBLe LeBGt LebLe LebGt NthSwapB
        NthSwapA NthSwapOther AllLeTakeOf AllGeAllOf AllGeDropOf SubPosLt TakeOneDrop NthIdx EndLeft
        EndRight StepJ0 StepJ1 StepJ2 StepJ2F ScanK ScanV ScanLt ScanPivot ScanLeft ScanRight Start0
        Start1 Start2 PartLeProof PartLeftProof PartPivotProof PartRightProof"""),
    "B2 proof: headline": W("QSSortedFull QSCorrect"),
}
# the old block `Index`, now `Words` (and `Std`'s `Dec`) in 00Std.lean
INDEX = W("""Le Lt WAdd W Sub LeB EqB Dec LeDec LtDec LeRefl LeStep LeTrans LeAddL AddRS AddZeroR AddOneR
    SubPos SubOneLe LtNe LeAntisym SubPosLt""")
# quicksort lemmas now in `Words`, counted in the quicksort's categories as before
MOVED = W("EqBRefl LeOfLt")
OLD_NAME = {"LeB": "Leb", "EqB": "Eqb", "EqBRefl": "EqbRefl"}
TO_BENCH = W("ModS LeNext ModLt")
TO_ARRAYS = W("LenL")
LIBRARY_BLOCKS = {"Std", "Words", "WordType", "Logic", "Lists", "Bools"}
ORDER = ["Index", "Arrays", "ArrayLemmas", "ArrayBench"] + list(QS)
DECL = re.compile(r"^  (?:reject )?(?:(?:unsized|abstract|copy) )*(?:def|inductive) ([A-Za-z_][A-Za-z0-9_']*)")
BLOCK = re.compile(r"^ochr (\w+)")


def decls_of(path):
    """The declarations of a file's `ochr` blocks, as (block, name, code lines), each line
    stripped of comments."""
    raw = open(path).read()
    stripped = hc.strip_comments(raw, "ochr").split("\n")
    decls, cur, block = [], None, None
    for i, l in enumerate(raw.split("\n")):
        m = BLOCK.match(l)
        if m:
            block = m.group(1)
            continue
        if block and l.startswith("}"):
            block, cur = None, None
            continue
        if not block:
            continue
        m = DECL.match(l)
        if m:
            cur = [block, m.group(1), []]
            decls.append(cur)
        if cur is not None:
            cur[2].append(i)
    return [(b, n, [stripped[i] for i in idx]) for b, n, idx in decls]


def main():
    ex = os.path.join(here, "..", "lean", "Ochr", "Examples")
    args = sys.argv[1:]
    old_rule = "--old-rule" in args
    args = [a for a in args if a != "--old-rule"]
    files = args or [os.path.join(ex, f) for f in
                             ["Word.lean", "Logic.lean", "List.lean", "Array.lean", "ArrayBench.lean", "Quicksort.lean"]]
    every = [d for f in files for d in decls_of(f)]
    own = [d for d in every if d[0] not in LIBRARY_BLOCKS]
    names = {n for _, n, _ in own}
    def home(n):
        if n in INDEX: return "Index"
        if n in MOVED: return "Quicksort"
        if n in TO_BENCH: return "ArrayBench"
        if n in TO_ARRAYS: return "Arrays"
        return None
    moved = [(home(n), n, ls) for b, n, ls in every if b in LIBRARY_BLOCKS and home(n)
             and n not in names and OLD_NAME.get(n) not in names]
    decls = moved + [("ArrayBench" if b == "ArrayHashMap" else b, n, ls) for b, n, ls in own]
    if not old_rule:
        uncounted = set(MOVED) | {OLD_NAME[n] for n in MOVED if n in OLD_NAME}
        decls = [d for d in decls if not (d[0] == "Quicksort" and d[1] in uncounted)]
    cat = {n: c for c, ns in QS.items() for n in ns}
    totals, missing = {}, []
    for block, name, lines in decls:
        c = block if block != "Quicksort" else cat.get(name)
        if c is None:
            missing.append(name)
            continue
        code = [x for x in lines if x.strip()]
        toks = sum(len(hc.TOKEN.findall(x)) for x in code)
        n, l, t = totals.get(c, (0, 0, 0))
        totals[c] = (n + 1, l + len(code), t + toks)
    if missing:
        print("uncategorised:", " ".join(missing))
    print(f"{'category':32} {'decls':>5} {'lines':>6} {'tokens':>7}")
    for c in ORDER:
        n, l, t = totals.get(c, (0, 0, 0))
        print(f"{c:32} {n:5} {l:6} {t:7}")
    for label, pred in [("B2 proofs: total", lambda k: k.startswith("B2 proof")),
                        ("B2: total", lambda k: k.startswith("B2")),
                        ("all declarations", lambda k: True)]:
        vs = [v for k, v in totals.items() if pred(k)]
        print(f"{label:32} {sum(v[0] for v in vs):5} {sum(v[1] for v in vs):6} {sum(v[2] for v in vs):7}")


if __name__ == "__main__":
    main()
