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
    spec_end = '  ) implemented by "ochr_arr_get_mut"\n}\n'
    assert spec_end in head
    head = head.replace(spec_end, '  ) implemented by "ochr_arr_get_mut"\n\n'
        "  -- The parts of a map value, for the model: its buckets as a view (a model function: it\n"
        "  -- returns a view by value, so it runs only in statements and other model code), and\n"
        "  -- its length field.\n"
        "  def SlotsOf (cap : Word) (m : Map(cap)) : Slice(Bucket, cap) := (\n"
        "    match m {\n      MkMap(slots, len) => match slots {\n        MkArray(s) => s,\n      },\n    }\n  )\n\n"
        "  def LenField (cap : Word) (m : Map(cap)) : Word := (\n"
        "    match m {\n      MkMap(slots, len) => len,\n    }\n  )\n}\n", 1)
    out = [head]

    out.append("""/-! ## From the model to the program (FIXED, provided)

H4–H15 about any in-place map follow from its agreement with a pure model and the model's
own properties. These lemmas are that argument, checked, for any operations, model and
invariants (the parameters); nothing here is for you to do. At the end of `HashMapSolution`
they are applied to your operations, your model and your proofs, which gives H4–H15 about
your operations, stated exactly as in the one-program assignment. -/

ochr HashMapCompose uses HashMapSpec {
""")
    out.append(HC.block())
    out.append("}\n\n")

    # --- the model
    out.append("""/-! ## Your model

A pure functional model of a finite map, and its properties. Pure means: no borrows (`&`)
and no assignment (`p := t`) anywhere in this block; the model computes on values. Declare
the data types the model needs here too (an association list, for example). -/

ochr HashMapModel uses HashMapSpec {
-- FIXED-END header

  -- Your model's data types, pure helper definitions and lemmas go here, and anywhere else
  -- between the FIXED regions of this block.

""")
    out.append(region("model-type", "  -- The model's type.\n  def MMap : Type :=\n"))
    out.append(region("model-new", "  -- The model of new(c): the empty map.\n  def MNew : MMap :=\n"))
    out.append(region("model-len", "  -- The model of len.\n  def MLen (a : MMap) : Word :=\n"))
    out.append(region("model-get", "  -- The model of get.\n  def MGet (a : MMap) (k : Word) : Opt :=\n"))
    out.append(region("model-insert", "  -- The model of insert: the map afterwards. (The value insert returns is\n"
                      "  -- MGet(a, k), by AgreeInsertResult below.)\n  def MInsert (a : MMap) (k : Word) (v : Word) : MMap :=\n"))
    out.append(region("model-remove", "  -- The model of remove: the map afterwards. (The value remove returns is\n"
                      "  -- MGet(a, k), by AgreeRemoveResult below.)\n  def MRemove (a : MMap) (k : Word) : MMap :=\n"))
    out.append(region("model-write", "  -- The model of writing `w` through get_mut(m, k): the map afterwards.\n"
                      "  def MWrite (a : MMap) (k : Word) (w : Word) : MMap :=\n"))
    out.append(region("model-inv", "  -- The model's invariant: any predicate on models that the properties below need\n"
                      "  -- (it may be ⊤).\n  def MInv (a : MMap) : Prop :=\n"))
    out.append(region("model-abs", "  -- The abstraction: the model of a map, from its buckets (a view, as `SlotsOf` gives\n"
                      "  -- it) and its length field.\n  def Abs (cap : Word) (s : Slice(Bucket, cap)) (len : Word) : MMap :=\n"))
    M = [
      ("M4", "the model of get on the empty map", "MGetNew", "(k : Word)", "Eq(Opt, MGet(MNew, k), None)"),
      ("M5", "get after insert, at the same key", "MGetInsertSame", "(a : MMap) (k : Word) (v : Word) (h : MInv(a))", "Eq(Opt, MGet(MInsert(a, k, v), k), Some(v))"),
      ("M6", "get after insert, at another key", "MGetInsertOther", "(a : MMap) (k : Word) (k2 : Word) (v : Word) (h : MInv(a)) (ne : Π(e : Eq(Word, k2, k)). False)", "Eq(Opt, MGet(MInsert(a, k, v), k2), MGet(a, k2))"),
      ("M8", "get after remove, at the same key", "MGetRemoveSame", "(a : MMap) (k : Word) (h : MInv(a))", "Eq(Opt, MGet(MRemove(a, k), k), None)"),
      ("M9", "get after remove, at another key", "MGetRemoveOther", "(a : MMap) (k : Word) (k2 : Word) (h : MInv(a)) (ne : Π(e : Eq(Word, k2, k)). False)", "Eq(Opt, MGet(MRemove(a, k), k2), MGet(a, k2))"),
      ("M11", "the length of the empty map", "MLenNew", "", "Eq(Word, MLen(MNew), Zero)"),
      ("M12", "the length after insert", "MLenInsert", "(a : MMap) (k : Word) (v : Word) (h : MInv(a))", "Eq(Word, MLen(MInsert(a, k, v)), Grow(MGet(a, k), MLen(a)))"),
      ("M13", "the length after remove", "MLenRemove", "(a : MMap) (k : Word) (h : MInv(a))", "Eq(Word, MLen(MRemove(a, k)), Shrink(MGet(a, k), MLen(a)))"),
      ("M14", "a write has the effect of insert on every get", "MWriteGet", "(a : MMap) (k : Word) (w : Word) (k2 : Word) (h : MInv(a)) (hk : IsSome(MGet(a, k)))", "Eq(Opt, MGet(MWrite(a, k, w), k2), MGet(MInsert(a, k, w), k2))"),
      ("M15", "... and on the length", "MWriteLen", "(a : MMap) (k : Word) (w : Word) (h : MInv(a)) (hk : IsSome(MGet(a, k)))", "Eq(Word, MLen(MWrite(a, k, w)), MLen(MInsert(a, k, w)))"),
    ]
    for mid, comment, name, params, goal in M:
        sig = f"  def {name}{(' ' + params) if params else ''} :\n      {goal} :=\n"
        out.append(region(mid, f"  -- {mid} ({'H' + mid[1:]} about the model): {comment}.\n{sig}"))
    out.append("""-- FIXED-BEGIN solution-header
}

/-! ## Your program

The in-place operations, your invariant on maps, the agreement of the operations with the
model, and the properties that are about the in-place map only (H1–H3, H16–H18). H4–H15
then follow, at the end of this block. -/

ochr HashMapSolution uses HashMapModel, HashMapCompose {
  -- The model of a map value (for statements): `Abs` of its buckets and its length field.
  def AbsOf (cap : Word) (m : Map(cap)) : MMap := Abs(cap, SlotsOf(cap, clone(m)), LenField(cap, m))
-- FIXED-END solution-header

  -- Your helper definitions and lemmas go here, and anywhere else between the FIXED regions
  -- of this block.

""")
    for rid in ["new", "len", "get", "insert", "remove", "get_mut", "inv"]:
        out.append(R[rid] + "    ?\n\n")
    out.append(region("abs-inv", "  -- The invariant on maps gives the model's invariant.\n"
                      "  def AbsInv (cap : Word) (m : &Map(cap)) (hm : Inv(cap, *m)) : MInv(AbsOf(cap, *m)) :=\n"))
    for rid in ["H1", "H2", "H3"]:
        out.append(R[rid] + "    ?\n\n")
    A = [
      ("agree-new", "new(c) is the empty model", "AbsNew", "(cap : Word) (h : Lt(Zero, cap))", "Eq(MMap, AbsOf(cap, MapNew(cap, h)), MNew)"),
      ("agree-len", "len agrees with the model", "AgreeLen", "(cap : Word) (m : &Map(cap)) (hm : Inv(cap, *m))", "Eq(Word, LenOf(cap, *m), MLen(AbsOf(cap, *m)))"),
      ("agree-get", "get agrees with the model", "AgreeGet", "(cap : Word) (m : &Map(cap)) (k : Word) (hm : Inv(cap, *m))", "Eq(Opt, GetOf(cap, *m, k), MGet(AbsOf(cap, *m), k))"),
      ("agree-insert", "insert agrees with the model: the map afterwards", "AgreeInsert", "(cap : Word) (m : &Map(cap)) (k : Word) (v : Word) (hm : Inv(cap, *m))", "Eq(MMap, let c = *m; MapInsert(cap, &c, k, v); AbsOf(cap, c), MInsert(AbsOf(cap, *m), k, v))"),
      ("agree-insert-result", "... and the value it returns", "AgreeInsertResult", "(cap : Word) (m : &Map(cap)) (k : Word) (v : Word) (hm : Inv(cap, *m))", "Eq(Opt, let c = *m; MapInsert(cap, &c, k, v), MGet(AbsOf(cap, *m), k))"),
      ("agree-remove", "remove agrees with the model: the map afterwards", "AgreeRemove", "(cap : Word) (m : &Map(cap)) (k : Word) (hm : Inv(cap, *m))", "Eq(MMap, let c = *m; MapRemove(cap, &c, k); AbsOf(cap, c), MRemove(AbsOf(cap, *m), k))"),
      ("agree-remove-result", "... and the value it returns", "AgreeRemoveResult", "(cap : Word) (m : &Map(cap)) (k : Word) (hm : Inv(cap, *m))", "Eq(Opt, let c = *m; MapRemove(cap, &c, k), MGet(AbsOf(cap, *m), k))"),
      ("agree-write", "a write through get_mut agrees with the model", "AgreeWrite", "(cap : Word) (m : &Map(cap)) (k : Word) (w : Word) (hm : Inv(cap, *m))\n      (hk : IsSome(GetOf(cap, *m, k)))", "Eq(MMap, let c = *m; let r = MapGetMut(cap, &c, k, hk); *r := w; AbsOf(cap, c), MWrite(AbsOf(cap, *m), k, w))"),
    ]
    for rid, comment, name, params, goal in A:
        out.append(region(rid, f"  -- Agreement: {comment}.\n  def {name} {params} :\n      {goal} :=\n"))
    for rid in ["H16", "H17", "H18"]:
        out.append(R[rid] + "    ?\n\n")
    # H4–H15, provided
    args = {"H4": ["cap", "h", "k"], "H5": ["cap", "m", "k", "v", "hm"], "H6": ["cap", "m", "k", "k2", "v", "hm", "ne"],
            "H7": ["cap", "m", "k", "v", "hm"], "H8": ["cap", "m", "k", "hm"], "H9": ["cap", "m", "k", "k2", "hm", "ne"],
            "H10": ["cap", "m", "k", "hm"], "H11": ["cap", "h"], "H12": ["cap", "m", "k", "v", "hm"],
            "H13": ["cap", "m", "k", "hm"], "H14": ["cap", "m", "k", "w", "k2", "hm", "hk"], "H15": ["cap", "m", "k", "w", "hm", "hk"]}
    byH = {H: (name, params) for H, name, _, params, _, _, _ in HC.L}
    for H in ["H4", "H5", "H6", "H7", "H8", "H9", "H10", "H11", "H12", "H13", "H14", "H15"]:
        text = R[H]
        lines = text.splitlines(keepends=True)
        name, params = byH[H]
        inst = HC.instantiation(name, params, args[H])
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
