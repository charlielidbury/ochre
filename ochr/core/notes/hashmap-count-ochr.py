#!/usr/bin/env python3
"""The Ochr side of the hashmap case study's table (notes/hashmap-case-study.md).

Splits Ochr/Examples/17HashMap.lean into its declarations (a declaration runs from its
`def`/`inductive` line to the line before the next one, or the end of its `ochr` block),
assigns each to a category by name, and counts code lines and tokens per category with
the same comment stripping and tokenizer as hashmap-count.py.

usage: hashmap-count-ochr.py [path/to/17HashMap.lean]
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

IMPL = W("""Opt Bucket Slots HashMap EqB Lt ModGo Idx Pred WAdd BGet BContains BInsert BRemove BFind
IsSome BGetMut Slot EmptySlots New Get ContainsKey InsertNoResize Remove Clear Len Find GetMut
MoveBucket MoveSlots Resize Insert""")
RUNS = W("W RunLayout RunGet RunGetWrong RunContains RunOverwrite RunCollide RunRemove RunGetMut RunGetMutAbsent RunClear")
# statement vocabulary of the headline theorems: what a reader must trust
SPEC = W("Buckets BLen Count IfNew Shrink Has Unique AllUnique Nowhere OnlyIn Placed Inv NOf NotOver")
# definitions used only inside proofs (lemma statements)
INTERNAL = W("Nth IsNone IfFound OrElse BFindLast SFindLast Fresh FreshS AbsentFrom Apart GUnique")
NEGATIVE = W("InsertFindNoSplit BRemoveFindDup InsertCountNoHyp BGetMoves")
WALLED = W("")   # the three GetMut theorems were walled until D58; now proofs: get_mut
GROUPS = {
    "helpers (keys, arithmetic, equality)": W("""EqBRefl EqBSound EqBTrans EqBContra EqBSymm NeqFlip
        TransO AddMS AddS SymmN AddZero AddAssoc TransN LtS LtAdd LtPred WAddS WAddZero WAddAssoc"""),
    "new, clear": W("""NthEmpty NewFind ClearFind EmptyCount NewCount ClearCount NowhereEmpty OnlyInEmpty
        UniqueEmpty NewInv ClearInv"""),
    "get, contains_key (F1 bridges)": W("BGetFind SlotGetFind GetFind BContainsFind SlotContainsFind ContainsFind"),
    "insert without resize": W("""BInsertFind BInsertFindOther SlotInsertFind SlotInsertFindOther InsertFind
        InsertFindOther BInsertAdded SlotInsertAdded InsertLen BInsertCount SlotInsertCount InsertCount
        BInsertUnique SlotInsertUnique BInsertAbsent NowhereInsert OnlyInOther OnlyInSame SlotInsertPlaced
        InsertInv"""),
    "resize, and insert with resize": W("""MoveBucketInv MoveSlotsInv ResizeInv MoveBucketFind MoveSlotsFind
        BFindLastNone BFindLastUnique NowhereLast OnlyInLast ResizeFind FreshInsert MoveBucketLen FreshMove
        FreshSMove MoveSlotsLen FreshNew FreshSNew NowhereOnlyIn HeadApart AbsentFromOf ApartOfGo TailOnlyIn
        GUniqueOf ResizeLen InsertFindR InsertFindOtherR InsertInvR InsertLenR"""),
    "load factor": W("InsertN MoveBucketN MoveSlotsN ResizeN InsertNotOver NewNotOver RemoveNotOver ClearNotOver"),
    "remove": W("""BRemoveResult BRemoveFind BRemoveFindOther SlotRemoveResult SlotRemoveFind SlotRemoveFindOther
        RemoveResult RemoveFind RemoveFindOther RemoveLen BRemoveCount SlotRemoveCount RemoveCount
        BRemoveUnique SlotRemoveUnique BRemoveAbsent NowhereRemove OnlyInRemove SlotRemovePlaced RemoveInv"""),
    # the pre-D60 direct proofs (BGetMutFind … SlotGetMutPlaced) are listed too, so the
    # script also counts older versions of the file; the current file proves get_mut
    # through GetMutIsInsert
    "get_mut": W("""GetMutLen BGetMutRead BGetMutFind BGetMutFindOther SlotGetMutRead SlotGetMutFind
        SlotGetMutFindOther GetMutRead GetMutFind GetMutFindOther BGetMutCount SlotGetMutCount BGetMutUnique
        SlotGetMutUnique BGetMutAbsent NowhereGetMut OnlyInGetMut SlotGetMutPlaced GetMutInv GetMutNotOver
        BGetMutIsInsert SlotGetMutIsInsert GetMutIsInsert"""),
}
DECL = re.compile(r"^  (?:reject )?(?:def|inductive) ([A-Za-z_][A-Za-z0-9_']*)")


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else os.path.join(here, "..", "lean", "Ochr", "Examples", "17HashMap.lean")
    raw = open(path).read()
    stripped = hc.strip_comments(raw, "ochr").split("\n")
    rawlines = raw.split("\n")
    decls, cur, inside = [], None, False
    for i, l in enumerate(rawlines):
        if re.match(r"^ochr\s", l):
            inside = True
            continue
        if inside and l.startswith("}"):
            inside, cur = False, None
            continue
        if not inside:
            continue
        m = DECL.match(l)
        if m:
            cur = [m.group(1), []]
            decls.append(cur)
        if cur is not None:
            cur[1].append(i)
    cat = {}
    for n in IMPL: cat[n] = "implementation"
    for n in RUNS: cat[n] = "runs (tests)"
    for n in SPEC: cat[n] = "spec: statement vocabulary"
    for n in INTERNAL: cat[n] = "spec: proof-internal definitions"
    for n in NEGATIVE: cat[n] = "negative tests"
    for n in WALLED: cat[n] = "walled (true, rejected)"
    for g, ns in GROUPS.items():
        for n in ns: cat[n] = "proofs: " + g
    totals = {}
    missing = []
    for name, idx in decls:
        c = cat.get(name)
        if c is None:
            missing.append(name)
            continue
        code = [stripped[i] for i in idx if stripped[i].strip()]
        toks = sum(len(hc.TOKEN.findall(x)) for x in code)
        n, l, t = totals.get(c, (0, 0, 0))
        totals[c] = (n + 1, l + len(code), t + toks)
    if missing:
        print("uncategorised:", " ".join(missing))
    print(f"{'category':45} {'decls':>5} {'lines':>6} {'tokens':>7}")
    order = ["implementation", "runs (tests)", "spec: statement vocabulary", "spec: proof-internal definitions"] + \
            ["proofs: " + g for g in GROUPS] + ["negative tests", "walled (true, rejected)"]
    for c in order:
        n, l, t = totals.get(c, (0, 0, 0))
        print(f"{c:45} {n:5} {l:6} {t:7}")
    pn = sum(v[0] for k, v in totals.items() if k.startswith("proofs"))
    pl = sum(v[1] for k, v in totals.items() if k.startswith("proofs"))
    pt = sum(v[2] for k, v in totals.items() if k.startswith("proofs"))
    print(f"{'proofs: total':45} {pn:5} {pl:6} {pt:7}")
    an = sum(v[0] for v in totals.values())
    al = sum(v[1] for v in totals.values())
    at = sum(v[2] for v in totals.values())
    print(f"{'all declarations':45} {an:5} {al:6} {at:7}")


if __name__ == "__main__":
    main()
