#!/usr/bin/env python3
"""Build hashmap/ochr-2p/HashMap.lean from hashmap/ochr/HashMap.lean.

    gen_hashmap_2p.py [--check]

The two-program skeleton shares everything observable with the one-program skeleton: the
representation, the provided functions, the operations' signatures, the statements of
H1–H18 and the tests are copied from ../../hashmap/ochr/HashMap.lean, byte for byte. What
it adds: a pure model (the block HashMapModel: the model's type and operations, a model
invariant, the abstraction from a map's buckets to the model, and the model's properties),
the agreement between the operations and the model, and the block HashMapCompose, generic
lemmas (hashmap_compose.py) that derive H4–H15 from the agreement and the model's
properties. H4–H15 are then provided, as instances of those lemmas; H1–H3 and H16–H18 are
about the in-place map only and stay for the solver to prove, as in `ochr`.
With --check, exit 1 if the file differs from what this script would write.
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import hashmap_compose as HC  # noqa: E402

BENCH = os.path.dirname(os.path.dirname(HERE))
SRC = os.path.join(BENCH, "hashmap", "ochr", "HashMap.lean")
DST = os.path.join(BENCH, "hashmap", "ochr-2p", "HashMap.lean")

MARK = re.compile(r"FIXED-(BEGIN|END) (\S+)")


def regions(text):
    """{id: region text, markers included} and the ids in order."""
    out, order, cur, buf = {}, [], None, []
    for line in text.splitlines(keepends=True):
        m = MARK.search(line)
        if m and m.group(1) == "BEGIN":
            cur, buf = m.group(2), [line]
        elif m and m.group(1) == "END":
            buf.append(line)
            out[cur] = "".join(buf)
            order.append(cur)
            cur = None
        elif cur is not None:
            buf.append(line)
    return out, order


def region(rid, body):
    return f"  -- FIXED-BEGIN {rid}\n{body}  -- FIXED-END {rid}\n    ?\n\n"


def provided(rid, body):
    return f"  -- FIXED-BEGIN {rid}\n{body}  -- FIXED-END {rid}\n\n"


def main():
    src = open(SRC, encoding="utf-8").read()
    R, _ = regions(src)

    # --- header: the 1p header up to the end of the Spec block, retitled, plus the model's
    # access to a map's parts
    head = R["header"]
    head = head[:head.index("/-! ## Your solution")]
    head = head.replace("# Verified in-place hash map (condition `ochr`)",
                        "# Verified in-place hash map, two programs (condition `ochr-2p`)")
    head = head.replace("helper definitions and lemmas you need to the block `HashMapSolution`, between its FIXED\nregions.",
                        "helper definitions and lemmas you need to the blocks `HashMapModel` and\n`HashMapSolution`, between their FIXED regions.")
    spec_end = "        Succ(b') => EqDec(a', b'),\n      },\n    }\n  )\n}\n"
    assert spec_end in head
    head = head.replace(spec_end, "        Succ(b') => EqDec(a', b'),\n      },\n    }\n  )\n\n"
        "  -- The parts of a map value, for the model: its buckets as a view (a model function: it\n"
        "  -- returns a view by value, so it runs only in statements and other model code), and\n"
        "  -- its length field.\n"
        "  def SlotsOf (V : Type) (cap : Word) (m : Map(V, cap)) : Slice(Bucket(V), cap) := (\n"
        "    match m {\n      MkMap(slots, len) => match slots {\n        MkArray(s) => s,\n      },\n    }\n  )\n\n"
        "  def LenField (V : Type) (cap : Word) (m : Map(V, cap)) : Word := (\n"
        "    match m {\n      MkMap(slots, len) => len,\n    }\n  )\n}\n", 1)
    out = [head]

    out.append("""/-! ## From the model to the program (FIXED, provided)

H4–H15 about any in-place map follow from its agreement with a pure model and the model's
own properties. These lemmas are that argument, checked, for any operations, model and
invariants (the parameters, each generic in the value type); nothing here is for you to do.
At the end of `HashMapSolution` they are applied to your operations, your model and your
proofs, which gives H4–H15 about your operations, stated exactly as in the one-program
assignment. -/

ochr HashMapCompose uses HashMapSpec {
""")
    out.append(HC.block())
    out.append("}\n\n")

    # --- the model
    out.append("""/-! ## Your model

A pure functional model of a finite map from words to values of type `V`, and its properties.
Pure means: no borrows (`&`) and no assignment (`p := t`) anywhere in this block; the model
computes on values. Declare the data types the model needs here too (an association list, for
example). -/

ochr HashMapModel uses HashMapSpec {
-- FIXED-END header

  -- Your model's data types, pure helper definitions and lemmas go here, and anywhere else
  -- between the FIXED regions of this block.

""")
    out.append(region("model-type", "  -- The model's type.\n  def MMap (V : Type) : Type :=\n"))
    out.append(region("model-new", "  -- The model of new(c): the empty map.\n  def MNew (V : Type) : MMap(V) :=\n"))
    out.append(region("model-len", "  -- The model of len.\n  def MLen (V : Type) (a : MMap(V)) : Word :=\n"))
    out.append(region("model-get", "  -- The model of a lookup: Some of the value bound to `k`, or None. (contains is whether\n"
                      "  -- it is Some, and get the value in it, by AgreeContains and AgreeGet below.)\n"
                      "  def MGet (V : Type) (a : MMap(V)) (k : Word) : Opt(V) :=\n"))
    out.append(region("model-insert", "  -- The model of insert: the map afterwards. (The value insert returns is\n"
                      "  -- MGet(V, a, k), by AgreeInsertResult below.)\n  def MInsert (V : Type) (a : MMap(V)) (k : Word) (v : V) : MMap(V) :=\n"))
    out.append(region("model-remove", "  -- The model of remove: the map afterwards. (The value remove returns is\n"
                      "  -- MGet(V, a, k), by AgreeRemoveResult below.)\n  def MRemove (V : Type) (a : MMap(V)) (k : Word) : MMap(V) :=\n"))
    out.append(region("model-write", "  -- The model of writing `w` through get_mut(m, k): the map afterwards.\n"
                      "  def MWrite (V : Type) (a : MMap(V)) (k : Word) (w : V) : MMap(V) :=\n"))
    out.append(region("model-inv", "  -- The model's invariant: any predicate on models that the properties below need\n"
                      "  -- (it may be ⊤).\n  def MInv (V : Type) (a : MMap(V)) : Prop :=\n"))
    out.append(region("model-abs", "  -- The abstraction: the model of a map, from its buckets (a view, as `SlotsOf` gives\n"
                      "  -- it) and its length field.\n  def Abs (V : Type) (cap : Word) (s : Slice(Bucket(V), cap)) (len : Word) : MMap(V) :=\n"))
    M = [
      ("M4", "the model of a lookup in the empty map", "MGetNew", "(V : Type) (k : Word)", "Eq(Opt(V), MGet(V, MNew(V), k), None[V])"),
      ("M5", "a lookup after insert, at the same key", "MGetInsertSame", "(V : Type) (a : MMap(V)) (k : Word) (v : V) (h : MInv(V, a))", "Eq(Opt(V), MGet(V, MInsert(V, a, k, v), k), Some(v))"),
      ("M6", "a lookup after insert, at another key", "MGetInsertOther", "(V : Type) (a : MMap(V)) (k : Word) (k2 : Word) (v : V) (h : MInv(V, a)) (ne : Π(e : Eq(Word, k2, k)). False)", "Eq(Opt(V), MGet(V, MInsert(V, a, k, v), k2), MGet(V, a, k2))"),
      ("M8", "a lookup after remove, at the same key", "MGetRemoveSame", "(V : Type) (a : MMap(V)) (k : Word) (h : MInv(V, a))", "Eq(Opt(V), MGet(V, MRemove(V, a, k), k), None[V])"),
      ("M9", "a lookup after remove, at another key", "MGetRemoveOther", "(V : Type) (a : MMap(V)) (k : Word) (k2 : Word) (h : MInv(V, a)) (ne : Π(e : Eq(Word, k2, k)). False)", "Eq(Opt(V), MGet(V, MRemove(V, a, k), k2), MGet(V, a, k2))"),
      ("M11", "the length of the empty map", "MLenNew", "(V : Type)", "Eq(Word, MLen(V, MNew(V)), Zero)"),
      ("M12", "the length after insert", "MLenInsert", "(V : Type) (a : MMap(V)) (k : Word) (v : V) (h : MInv(V, a))", "Eq(Word, MLen(V, MInsert(V, a, k, v)), Grow(IsSomeB(V, MGet(V, a, k)), MLen(V, a)))"),
      ("M13", "the length after remove", "MLenRemove", "(V : Type) (a : MMap(V)) (k : Word) (h : MInv(V, a))", "Eq(Word, MLen(V, MRemove(V, a, k)), Shrink(IsSomeB(V, MGet(V, a, k)), MLen(V, a)))"),
      ("M14", "a write has the effect of insert on every lookup", "MWriteGet", "(V : Type) (a : MMap(V)) (k : Word) (w : V) (k2 : Word) (h : MInv(V, a)) (hk : IsTrue(IsSomeB(V, MGet(V, a, k))))", "Eq(Opt(V), MGet(V, MWrite(V, a, k, w), k2), MGet(V, MInsert(V, a, k, w), k2))"),
      ("M15", "... and on the length", "MWriteLen", "(V : Type) (a : MMap(V)) (k : Word) (w : V) (h : MInv(V, a)) (hk : IsTrue(IsSomeB(V, MGet(V, a, k))))", "Eq(Word, MLen(V, MWrite(V, a, k, w)), MLen(V, MInsert(V, a, k, w)))"),
    ]
    for mid, comment, name, params, goal in M:
        sig = f"  def {name} {params} :\n      {goal} :=\n"
        out.append(region(mid, f"  -- {mid} ({'H' + mid[1:]} about the model): {comment}.\n{sig}"))
    out.append("""-- FIXED-BEGIN solution-header
}

/-! ## Your program

The in-place operations, your invariant on maps, the agreement of the operations with the
model, and the properties that are about the in-place map only (H1–H3, H16–H18). H4–H15
then follow, at the end of this block. -/

ochr HashMapSolution uses HashMapModel, HashMapCompose {
  -- The model of a map value (for statements): `Abs` of its buckets and its length field.
  def AbsOf (V : Type) (cap : Word) (m : Map(V, cap)) : MMap(V) := Abs(V, cap, SlotsOf(V, cap, clone(m)), LenField(V, cap, m))
-- FIXED-END solution-header

  -- Your helper definitions and lemmas go here, and anywhere else between the FIXED regions
  -- of this block.

""")
    for rid in ["new", "len", "contains", "get", "insert", "remove", "get_mut", "inv"]:
        out.append(R[rid] + "    ?\n\n")
    out.append(region("abs-inv", "  -- The invariant on maps gives the model's invariant.\n"
                      "  def AbsInv (V : Type) (cap : Word) (m : &Map(V, cap)) (hm : Inv(V, cap, *m)) : MInv(V, AbsOf(V, cap, *m)) :=\n"))
    for rid in ["H1", "H2", "H3"]:
        out.append(R[rid] + "    ?\n\n")
    A = [
      ("agree-new", "new(c) is the empty model", "AbsNew", "(V : Type) (cap : Word) (h : Lt(Zero, cap))", "Eq(MMap(V), AbsOf(V, cap, MapNew(V, cap, h)), MNew(V))"),
      ("agree-len", "len agrees with the model", "AgreeLen", "(V : Type) (cap : Word) (m : &Map(V, cap)) (hm : Inv(V, cap, *m))", "Eq(Word, LenOf(V, cap, *m), MLen(V, AbsOf(V, cap, *m)))"),
      ("agree-contains", "contains agrees with the model", "AgreeContains", "(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : Inv(V, cap, *m))", "Eq(Bool, ContainsOf(V, cap, *m, k), IsSomeB(V, MGet(V, AbsOf(V, cap, *m), k)))"),
      ("agree-get", "the value read through get agrees with the model", "AgreeGet", "(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : Inv(V, cap, *m))\n      (h : Contains(V, cap, *m, k))", "Eq(Opt(V), Some(clone(*MapGet(V, cap, m, k, h))), MGet(V, AbsOf(V, cap, *m), k))"),
      ("agree-insert", "insert agrees with the model: the map afterwards", "AgreeInsert", "(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V) (hm : Inv(V, cap, *m))", "Eq(MMap(V), (let c = *m; MapInsert(V, cap, &c, k, v); AbsOf(V, cap, c)), MInsert(V, AbsOf(V, cap, *m), k, v))"),
      ("agree-insert-result", "... and the value it returns", "AgreeInsertResult", "(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V) (hm : Inv(V, cap, *m))", "Eq(Opt(V), (let c = *m; MapInsert(V, cap, &c, k, v)), MGet(V, AbsOf(V, cap, *m), k))"),
      ("agree-remove", "remove agrees with the model: the map afterwards", "AgreeRemove", "(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : Inv(V, cap, *m))", "Eq(MMap(V), (let c = *m; MapRemove(V, cap, &c, k); AbsOf(V, cap, c)), MRemove(V, AbsOf(V, cap, *m), k))"),
      ("agree-remove-result", "... and the value it returns", "AgreeRemoveResult", "(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : Inv(V, cap, *m))", "Eq(Opt(V), (let c = *m; MapRemove(V, cap, &c, k)), MGet(V, AbsOf(V, cap, *m), k))"),
      ("agree-write", "a write through get_mut agrees with the model", "AgreeWrite", "(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (w : V) (hm : Inv(V, cap, *m))\n      (hk : Contains(V, cap, *m, k))", "Eq(MMap(V), (let c = *m; let r = MapGetMut(V, cap, &c, k, hk); *r := w; AbsOf(V, cap, c)), MWrite(V, AbsOf(V, cap, *m), k, w))"),
    ]
    for rid, comment, name, params, goal in A:
        out.append(region(rid, f"  -- Agreement: {comment}.\n  def {name} {params} :\n      {goal} :=\n"))
    for rid in ["H16", "H17a", "H17b", "H18"]:
        out.append(R[rid] + "    ?\n\n")
    # H4–H15, provided
    args = {"H4": "V cap h k", "H5a": "V cap m k v hm", "H5b": "V cap m k v hm h", "H6a": "V cap m k k2 v hm ne",
            "H6b": "V cap m k k2 v hm ne h h2", "H7a": "V cap m k v hm", "H7b": "V cap m k v hm h", "H8": "V cap m k hm",
            "H9a": "V cap m k k2 hm ne", "H9b": "V cap m k k2 hm ne h h2", "H10a": "V cap m k hm", "H10b": "V cap m k hm h",
            "H11": "V cap h", "H12": "V cap m k v hm", "H13": "V cap m k hm", "H14a": "V cap m k w k2 hm hk",
            "H14b": "V cap m k w k2 hm hk h1 h2", "H15": "V cap m k w hm hk"}
    byH = {H: (name, params) for H, name, _, params, _, _, _ in HC.L}
    for H in ["H4", "H5a", "H5b", "H6a", "H6b", "H7a", "H7b", "H8", "H9a", "H9b", "H10a", "H10b", "H11", "H12", "H13", "H14a", "H14b", "H15"]:
        text = R[H]
        lines = text.splitlines(keepends=True)
        name, params = byH[H]
        inst = HC.instantiation(name, params, args[H].split())
        body = "".join(lines[1:-1])  # comment and statement, without the markers
        out.append(provided(H, body + f"    -- provided: from the model, by {name} (HashMapCompose)\n    {inst}\n"))
    out.append(R["tests"])
    text = "".join(out)
    if "--check" in sys.argv:
        cur = open(DST, encoding="utf-8").read() if os.path.exists(DST) else ""
        if cur != text:
            print(f"{DST} is not what gen_hashmap_2p.py writes")
            return 1
        print(f"{DST}: up to date")
        return 0
    open(DST, "w", encoding="utf-8").write(text)
    print(f"wrote {DST}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
