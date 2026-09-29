#!/usr/bin/env python3
"""Sizes for the arrays library and the quicksort case study (notes/arrays-library.md §10).

Splits Ochr/Examples/16Arrays.lean into its declarations (a declaration runs from its
`def`/`inductive` line to the line before the next one, or the end of its `ochr` block),
assigns each to a category by block and by name, and counts code lines and tokens per
category with the comment stripping and tokenizer of hashmap-count.py.

usage: arrays-count.py [path/to/16Arrays.lean]
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
    "B2 proof: sorted glue": W("""AllGeWeaken AndL AndR AndI AllGeJoin SortedJoin EqbRefl EqbLeLt EqbGeLt
        CountAboveZero CountBelowZero CountTailZero AllLeOfCounts AllGeOfCounts AllLePerm AllGePerm
        LeSuccFalse RecurseSorted PartK PartV PartLe PartLeft PartPivot PartRight QSSorted"""),
    "B2 proof: partition contract": W("""LeOfLt LtTrans LtLeTrans LtNe LeAntisym LebLe LebGt NthSwapB
        NthSwapA NthSwapOther AllLeTakeOf AllGeAllOf AllGeDropOf SubPosLt TakeOneDrop NthIdx EndLeft
        EndRight StepJ0 StepJ1 StepJ2 StepJ2F ScanK ScanV ScanLt ScanPivot ScanLeft ScanRight Start0
        Start1 Start2 PartLeProof PartLeftProof PartPivotProof PartRightProof"""),
    "B2 proof: headline": W("QSSortedFull QSCorrect"),
}
ORDER = ["Index", "Arrays", "ArrayLemmas", "ArrayBench"] + list(QS)
DECL = re.compile(r"^  (?:reject )?(?:def|inductive) ([A-Za-z_][A-Za-z0-9_']*)")
BLOCK = re.compile(r"^ochr (\w+)")


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else os.path.join(here, "..", "lean", "Ochr", "Examples", "16Arrays.lean")
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
    cat = {n: c for c, ns in QS.items() for n in ns}
    totals, missing = {}, []
    for block, name, idx in decls:
        c = block if block != "Quicksort" else cat.get(name)
        if c is None:
            missing.append(name)
            continue
        code = [stripped[i] for i in idx if stripped[i].strip()]
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
