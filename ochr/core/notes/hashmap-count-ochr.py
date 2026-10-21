#!/usr/bin/env python3
"""The Ochr side of the hashmap case study's table (notes/hashmap-case-study.md).

Splits Ochr/Examples/HashMap.lean (before the final layout, 17HashMap.lean) into its declarations (a declaration runs from its
`def`/`inductive` line to the line before the next one, or the end of its `ochr` block),
assigns each to a category by name, and counts code lines and tokens per category with
the same comment stripping and tokenizer as hashmap-count.py.

The counting rule (docs/12 step 2, 2026-10-21): the general library (Bool, Logic, Word, List,
Option and Array.lean: `Bools`, `Logic`, `WordType`, `Words`, `Lists`, `Options`, `Arrays`,
`ArrayLemmas`) is not counted, as Aeneas's primitives are not, and everything written for the
hash map is. The definitions the case study wrote for itself until they moved to the library
(`MOVED`: `Opt`, `IsSome`, `EqB`, `LtB`, `Pred`, `WAdd`, `W`, `EqBRefl`, `AddZeroR`, and their
old names `Lt`, `WAddZero`, `WAddS`) are therefore not counted in any version, so that an old
version of the file, which declares them itself, is counted by the same rule. The size of the
library the case study uses is printed below the table, as the uncounted part.

`--old-rule` counts as before the rule: the moved definitions read from the library and counted
where they were (a version of the file that still declares one counts its own).

usage: hashmap-count-ochr.py [--old-rule] [path/to/HashMap.lean [library file ...]]
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

IMPL = W("""Opt Bucket Slots HashMap EqB Lt LtB ModGo Idx IdxLt Pred WAdd BGet BContains BInsert BRemove BFind
IsSome BGetMut Slot EmptySlots New Get ContainsKey InsertNoResize Remove Clear Len Find GetMut
MoveBucket MoveSlots Resize Insert BLookup Lookup MapGetMut Take MoveFrom""")
RUNS = W("W RunLayout RunGet RunGetWrong RunContains RunOverwrite RunCollide RunRemove RunGetMut RunGetMutAbsent RunClear")
# statement vocabulary of the headline theorems: what a reader must trust
SPEC = W("Buckets BLen Count IfNew Shrink Has Unique AllUnique Nowhere OnlyIn Placed Inv NOf NotOver Entries Counted KeysUnique")
# definitions used only inside proofs (lemma statements)
INTERNAL = W("""Nth IsNone IsNoneB IfFound OrElse BFindLast SFindLast Fresh FreshS AbsentFrom Apart GUnique
    NthS EmptyFrom Rest FindLast NowhereL CountL FreshL ApartL GUniqueL""")
NEGATIVE = W("InsertFindNoSplit BRemoveFindDup InsertCountNoHyp BGetMoves BLookupMoves SlotUnbounded ResizeKeepSlots")
WALLED = W("")   # the three GetMut theorems were walled until D58; now proofs: get_mut
GROUPS = {
    "helpers (keys, arithmetic, equality)": W("""EqBRefl EqBSound EqBTrans EqBContra EqBSymm NeqFlip
        TransO AddMS AddS SymmN AddZero AddAssoc TransN LtS LtAdd LtPred WAddS WAddZero AddZeroR WAddAssoc
        LtBS LtBAdd LtBPred"""),
    "new, clear": W("""NthEmpty NewFind ClearFind EmptyCount NewCount ClearCount NowhereEmpty OnlyInEmpty
        UniqueEmpty NewInv ClearInv EmptyLookup"""),
    "get, contains_key (F1 bridges)": W("BGetFind SlotGetFind GetFind BContainsFind SlotContainsFind ContainsFind"),
    "insert without resize": W("""BInsertFind BInsertFindOther SlotInsertFind SlotInsertFindOther InsertFind
        InsertFindOther BInsertAdded SlotInsertAdded InsertLen BInsertCount SlotInsertCount InsertCount
        BInsertUnique SlotInsertUnique BInsertAbsent NowhereInsert OnlyInOther OnlyInSame SlotInsertPlaced
        InsertInv BInsertResult SlotInsertResult InsertResult"""),
    "resize, and insert with resize": W("""MoveBucketInv MoveSlotsInv ResizeInv MoveBucketFind MoveSlotsFind
        BFindLastNone BFindLastUnique NowhereLast OnlyInLast ResizeFind FreshInsert MoveBucketLen FreshMove
        FreshSMove MoveSlotsLen FreshNew FreshSNew NowhereOnlyIn HeadApart AbsentFromOf ApartOfGo TailOnlyIn
        GUniqueOf ResizeLen InsertFindR InsertFindOtherR InsertInvR InsertLenR MoveFromInv TakeV RestSet
        MoveFromFind RestShift NowhereRest NowhereLLast FreshLMove MoveFromLen FreshLNew CountRest ApartOfGoL
        InsertResultR"""),
    "load factor": W("""InsertN MoveBucketN MoveSlotsN ResizeN InsertNotOver NewNotOver RemoveNotOver ClearNotOver
        MoveFromN"""),
    "remove": W("""BRemoveResult BRemoveFind BRemoveFindOther SlotRemoveResult SlotRemoveFind SlotRemoveFindOther
        RemoveResult RemoveFind RemoveFindOther RemoveLen BRemoveCount SlotRemoveCount RemoveCount
        BRemoveUnique SlotRemoveUnique BRemoveAbsent NowhereRemove OnlyInRemove SlotRemovePlaced RemoveInv"""),
    # the pre-D60 direct proofs (BGetMutFind … SlotGetMutPlaced) are listed too, so the
    # script also counts older versions of the file; the current file proves get_mut
    # through GetMutIsInsert
    "get_mut": W("""GetMutLen BGetMutRead BGetMutFind BGetMutFindOther SlotGetMutRead SlotGetMutFind
        SlotGetMutFindOther GetMutRead GetMutFind GetMutFindOther BGetMutCount SlotGetMutCount BGetMutUnique
        SlotGetMutUnique BGetMutAbsent NowhereGetMut OnlyInGetMut SlotGetMutPlaced GetMutInv GetMutNotOver
        BGetMutIsInsert SlotGetMutIsInsert GetMutIsInsert MapGetMutRead"""),
}
# moved to the central library (00Std.lean), counted here as before; the names they had here
MOVED = W("Opt IsSome EqB LtB Pred WAdd W EqBRefl AddZeroR")
OLD_NAME = {"LtB": "Lt", "AddZeroR": "WAddZero"}
# not counted under the rule, in any version: the moved definitions, under their names here and
# in the library (`WAddS` is `Words`' `AddRS`)
UNCOUNTED = set(MOVED) | set(OLD_NAME.values()) | {"WAddS", "AddRS"}
# the general library, whose size is printed as the uncounted part
LIBRARY = ["Bool", "Logic", "Word", "List", "Option", "Array"]
DECL = re.compile(r"^  (?:reject )?(?:copy )?(?:def|inductive) ([A-Za-z_][A-Za-z0-9_']*)")


def decls_of(path, keep=None):
    """The declarations of a file's `ochr` blocks, as (name, code lines), each line stripped
    of comments; only those named in `keep`, if given."""
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
            cur[1].append(stripped[i])
    return [(n, ls) for n, ls in decls if keep is None or n in keep]


def main():
    ex = os.path.join(here, "..", "lean", "Ochr", "Examples")
    args = sys.argv[1:]
    old_rule = "--old-rule" in args
    args = [a for a in args if a != "--old-rule"]
    path = args[0] if args else os.path.join(ex, "HashMap.lean")
    libs = args[1:] or [os.path.join(ex, "Option.lean"), os.path.join(ex, "Word.lean")]
    own = decls_of(path)
    names = {n for n, _ in own}
    if old_rule:
        decls = [d for lib in libs for d in decls_of(lib, MOVED)
                 if d[0] not in names and OLD_NAME.get(d[0]) not in names] + own
    else:
        decls = [d for d in own if d[0] not in UNCOUNTED]
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
    for name, lines in decls:
        c = cat.get(name)
        if c is None:
            missing.append(name)
            continue
        code = [x for x in lines if x.strip()]
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
    # a proof's statement is its declaration up to its `:=`: the share of proof tokens that
    # are statements (each lemma is stated at three levels)
    st = 0
    for name, lines in decls:
        if cat.get(name, "").startswith("proofs"):
            text = "\n".join(lines)
            j = text.find(":=")
            st += len(hc.TOKEN.findall(text[:j] if j >= 0 else text))
    print(f"{'proofs: statements (tokens before :=)':45} {'':5} {'':6} {st:7}  ({100 * st / pt:.1f}% of proof tokens)")
    an = sum(v[0] for v in totals.values())
    al = sum(v[1] for v in totals.values())
    at = sum(v[2] for v in totals.values())
    print(f"{'all declarations':45} {an:5} {al:6} {at:7}")
    # the comparison's total: spec, implementation and proofs (runs and negative tests are
    # tests, as Aeneas's test1 is)
    tn = sum(v[0] for k, v in totals.items() if k.startswith(("implementation", "spec", "proofs")))
    tl = sum(v[1] for k, v in totals.items() if k.startswith(("implementation", "spec", "proofs")))
    tt = sum(v[2] for k, v in totals.items() if k.startswith(("implementation", "spec", "proofs")))
    print(f"{'counted: spec + implementation + proofs':45} {tn:5} {tl:6} {tt:7}")
    if not old_rule and not args:
        lib = [d for f in LIBRARY for d in decls_of(os.path.join(ex, f + ".lean"))]
        ll = sum(len([x for x in ls if x.strip()]) for _, ls in lib)
        lt = sum(len(hc.TOKEN.findall(x)) for _, ls in lib for x in ls if x.strip())
        print(f"{'uncounted: the general library (' + ', '.join(LIBRARY) + ')':45} {len(lib):5} {ll:6} {lt:7}")
        print(f"{'counted + uncounted':45} {tn + len(lib):5} {tl + ll:6} {tt + lt:7}")


if __name__ == "__main__":
    main()
