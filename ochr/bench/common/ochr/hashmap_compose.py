"""The HashMapCompose block of hashmap/ochr-2p: generic lemmas that derive H4–H15 about any
in-place map from its agreement with a pure model and the model's properties (used by
gen_hashmap_2p.py)."""
P = {
 "MM": "(MM : Type)",
 "new": "(new : Π(cap : Word) (h : Lt(Zero, cap)). Map(cap))",
 "ins": "(ins : Π(cap : Word) (m : &Map(cap)) (k : Word) (v : Word). Opt)",
 "rem": "(rem : Π(cap : Word) (m : &Map(cap)) (k : Word). Opt)",
 "getOf": "(getOf : Π(cap : Word) (m : Map(cap)) (k : Word). Opt)",
 "lenOf": "(lenOf : Π(cap : Word) (m : Map(cap)). Word)",
 "getMut": "(getMut : Π(cap : Word) (m : &Map(cap)) (k : Word) (h : IsSome(getOf(cap, *m, k))). &Word)",
 "inv": "(inv : Π(cap : Word) (m : Map(cap)). Prop)",
 "absOf": "(absOf : Π(cap : Word) (m : Map(cap)). MM)",
 "mnew": "(mnew : MM)",
 "mget": "(mget : Π(a : MM) (k : Word). Opt)",
 "mlen": "(mlen : Π(a : MM). Word)",
 "minsert": "(minsert : Π(a : MM) (k : Word) (v : Word). MM)",
 "mremove": "(mremove : Π(a : MM) (k : Word). MM)",
 "mwrite": "(mwrite : Π(a : MM) (k : Word) (w : Word). MM)",
 "minv": "(minv : Π(a : MM). Prop)",
 "invNew": "(invNew : Π(cap : Word) (h : Lt(Zero, cap)). inv(cap, new(cap, h)))",
 "invIns": "(invIns : Π(cap : Word) (m : &Map(cap)) (k : Word) (v : Word) (hm : inv(cap, *m)). (let c = *m; ins(cap, &c, k, v); inv(cap, c)))",
 "invRem": "(invRem : Π(cap : Word) (m : &Map(cap)) (k : Word) (hm : inv(cap, *m)). (let c = *m; rem(cap, &c, k); inv(cap, c)))",
 "invWrite": "(invWrite : Π(cap : Word) (m : &Map(cap)) (k : Word) (w : Word) (hm : inv(cap, *m)) (hk : IsSome(getOf(cap, *m, k))).\n        (let c = *m; let r = getMut(cap, &c, k, hk); *r := w; inv(cap, c)))",
 "absInv": "(absInv : Π(cap : Word) (m : &Map(cap)) (hm : inv(cap, *m)). minv(absOf(cap, *m)))",
 "absNew": "(absNew : Π(cap : Word) (h : Lt(Zero, cap)). Eq MM (absOf(cap, new(cap, h))) mnew)",
 "agreeGet": "(agreeGet : Π(cap : Word) (m : &Map(cap)) (k : Word) (hm : inv(cap, *m)). Eq Opt (getOf(cap, *m, k)) (mget(absOf(cap, *m), k)))",
 "agreeLen": "(agreeLen : Π(cap : Word) (m : &Map(cap)) (hm : inv(cap, *m)). Eq Word (lenOf(cap, *m)) (mlen(absOf(cap, *m))))",
 "agreeIns": "(agreeIns : Π(cap : Word) (m : &Map(cap)) (k : Word) (v : Word) (hm : inv(cap, *m)).\n        Eq MM (let c = *m; ins(cap, &c, k, v); absOf(cap, c)) (minsert(absOf(cap, *m), k, v)))",
 "agreeInsRes": "(agreeInsRes : Π(cap : Word) (m : &Map(cap)) (k : Word) (v : Word) (hm : inv(cap, *m)).\n        Eq Opt (let c = *m; ins(cap, &c, k, v)) (mget(absOf(cap, *m), k)))",
 "agreeRem": "(agreeRem : Π(cap : Word) (m : &Map(cap)) (k : Word) (hm : inv(cap, *m)).\n        Eq MM (let c = *m; rem(cap, &c, k); absOf(cap, c)) (mremove(absOf(cap, *m), k)))",
 "agreeRemRes": "(agreeRemRes : Π(cap : Word) (m : &Map(cap)) (k : Word) (hm : inv(cap, *m)).\n        Eq Opt (let c = *m; rem(cap, &c, k)) (mget(absOf(cap, *m), k)))",
 "agreeWrite": "(agreeWrite : Π(cap : Word) (m : &Map(cap)) (k : Word) (w : Word) (hm : inv(cap, *m)) (hk : IsSome(getOf(cap, *m, k))).\n        Eq MM (let c = *m; let r = getMut(cap, &c, k, hk); *r := w; absOf(cap, c)) (mwrite(absOf(cap, *m), k, w)))",
 "m4": "(m4 : Π(k : Word). Eq Opt (mget(mnew, k)) None)",
 "m5": "(m5 : Π(a : MM) (k : Word) (v : Word) (h : minv(a)). Eq Opt (mget(minsert(a, k, v), k)) (Some(v)))",
 "m6": "(m6 : Π(a : MM) (k : Word) (k2 : Word) (v : Word) (h : minv(a)) (ne : Π(e : Eq Word k2 k). False).\n        Eq Opt (mget(minsert(a, k, v), k2)) (mget(a, k2)))",
 "m8": "(m8 : Π(a : MM) (k : Word) (h : minv(a)). Eq Opt (mget(mremove(a, k), k)) None)",
 "m9": "(m9 : Π(a : MM) (k : Word) (k2 : Word) (h : minv(a)) (ne : Π(e : Eq Word k2 k). False).\n        Eq Opt (mget(mremove(a, k), k2)) (mget(a, k2)))",
 "m11": "(m11 : Eq Word (mlen(mnew)) Zero)",
 "m12": "(m12 : Π(a : MM) (k : Word) (v : Word) (h : minv(a)). Eq Word (mlen(minsert(a, k, v))) (Grow(mget(a, k), mlen(a))))",
 "m13": "(m13 : Π(a : MM) (k : Word) (h : minv(a)). Eq Word (mlen(mremove(a, k))) (Shrink(mget(a, k), mlen(a))))",
 "m14": "(m14 : Π(a : MM) (k : Word) (w : Word) (k2 : Word) (h : minv(a)) (hk : IsSome(mget(a, k))).\n        Eq Opt (mget(mwrite(a, k, w), k2)) (mget(minsert(a, k, w), k2)))",
 "m15": "(m15 : Π(a : MM) (k : Word) (w : Word) (h : minv(a)) (hk : IsSome(mget(a, k))).\n        Eq Word (mlen(mwrite(a, k, w))) (mlen(minsert(a, k, w))))",
}
M_ARGS = "(cap : Word) (m : &Map(cap))"
L = []  # (H, name, comment, params, args, goal, proof)
L.append(("H4", "GetNewFrom", "get(new(c), k) = None",
  "MM new getOf inv absOf mnew mget invNew agreeGet absNew m4".split(),
  "(cap : Word) (h : Lt(Zero, cap)) (k : Word)",
  "Eq Opt (getOf(cap, new(cap, h), k)) None",
  ["rewrite ← (let c = new(cap, h); agreeGet(cap, &c, k, invNew(cap, h))) in",
   "rewrite ← absNew(cap, h) in",
   "m4(k)"]))
L.append(("H5", "GetInsertSameFrom", "after insert(m, k, v), get(m′, k) = Some(v)",
  "MM ins getOf inv absOf mget minsert minv invIns agreeGet agreeIns absInv m5".split(),
  M_ARGS + " (k : Word) (v : Word) (hm : inv(cap, *m))",
  "Eq Opt (let c = *m; ins(cap, &c, k, v); getOf(cap, c, k)) (Some(v))",
  ["rewrite ← (let c = *m; ins(cap, &c, k, v); agreeGet(cap, &c, k, invIns(cap, m, k, v, hm))) in",
   "rewrite ← agreeIns(cap, m, k, v, hm) in",
   "m5(absOf(cap, *m), k, v, absInv(cap, m, hm))"]))
L.append(("H6", "GetInsertOtherFrom", "after insert(m, k, v), get(m′, k′) = get(m, k′) for k′ ≠ k",
  "MM ins getOf inv absOf mget minsert minv invIns agreeGet agreeIns absInv m6".split(),
  M_ARGS + " (k : Word) (k2 : Word) (v : Word) (hm : inv(cap, *m)) (ne : Π(e : Eq Word k2 k). False)",
  "Eq Opt (let c = *m; ins(cap, &c, k, v); getOf(cap, c, k2)) (getOf(cap, *m, k2))",
  ["rewrite ← (let c = *m; ins(cap, &c, k, v); agreeGet(cap, &c, k2, invIns(cap, m, k, v, hm))) in",
   "rewrite ← agreeIns(cap, m, k, v, hm) in",
   "rewrite ← agreeGet(cap, m, k2, hm) in",
   "m6(absOf(cap, *m), k, k2, v, absInv(cap, m, hm), ne)"]))
L.append(("H7", "InsertReturnsGetFrom", "insert returns get(m, k)",
  "MM ins getOf inv absOf mget agreeGet agreeInsRes".split(),
  M_ARGS + " (k : Word) (v : Word) (hm : inv(cap, *m))",
  "Eq Opt (let c = *m; ins(cap, &c, k, v)) (getOf(cap, *m, k))",
  ["rewrite ← agreeGet(cap, m, k, hm) in",
   "agreeInsRes(cap, m, k, v, hm)"]))
L.append(("H8", "GetRemoveSameFrom", "after remove(m, k), get(m′, k) = None",
  "MM rem getOf inv absOf mget mremove minv invRem agreeGet agreeRem absInv m8".split(),
  M_ARGS + " (k : Word) (hm : inv(cap, *m))",
  "Eq Opt (let c = *m; rem(cap, &c, k); getOf(cap, c, k)) None",
  ["rewrite ← (let c = *m; rem(cap, &c, k); agreeGet(cap, &c, k, invRem(cap, m, k, hm))) in",
   "rewrite ← agreeRem(cap, m, k, hm) in",
   "m8(absOf(cap, *m), k, absInv(cap, m, hm))"]))
L.append(("H9", "GetRemoveOtherFrom", "after remove(m, k), get(m′, k′) = get(m, k′) for k′ ≠ k",
  "MM rem getOf inv absOf mget mremove minv invRem agreeGet agreeRem absInv m9".split(),
  M_ARGS + " (k : Word) (k2 : Word) (hm : inv(cap, *m)) (ne : Π(e : Eq Word k2 k). False)",
  "Eq Opt (let c = *m; rem(cap, &c, k); getOf(cap, c, k2)) (getOf(cap, *m, k2))",
  ["rewrite ← (let c = *m; rem(cap, &c, k); agreeGet(cap, &c, k2, invRem(cap, m, k, hm))) in",
   "rewrite ← agreeRem(cap, m, k, hm) in",
   "rewrite ← agreeGet(cap, m, k2, hm) in",
   "m9(absOf(cap, *m), k, k2, absInv(cap, m, hm), ne)"]))
L.append(("H10", "RemoveReturnsGetFrom", "remove returns get(m, k)",
  "MM rem getOf inv absOf mget agreeGet agreeRemRes".split(),
  M_ARGS + " (k : Word) (hm : inv(cap, *m))",
  "Eq Opt (let c = *m; rem(cap, &c, k)) (getOf(cap, *m, k))",
  ["rewrite ← agreeGet(cap, m, k, hm) in",
   "agreeRemRes(cap, m, k, hm)"]))
L.append(("H11", "LenNewFrom", "len(new(c)) = 0",
  "MM new lenOf inv absOf mnew mlen invNew agreeLen absNew m11".split(),
  "(cap : Word) (h : Lt(Zero, cap))",
  "Eq Word (lenOf(cap, new(cap, h))) Zero",
  ["rewrite ← (let c = new(cap, h); agreeLen(cap, &c, invNew(cap, h))) in",
   "rewrite ← absNew(cap, h) in",
   "m11"]))
L.append(("H12", "LenInsertFrom", "insert adds one to len if the key was absent",
  "MM ins getOf lenOf inv absOf mget mlen minsert minv invIns agreeGet agreeLen agreeIns absInv m12".split(),
  M_ARGS + " (k : Word) (v : Word) (hm : inv(cap, *m))",
  "Eq Word (let c = *m; ins(cap, &c, k, v); lenOf(cap, c)) (Grow(getOf(cap, *m, k), lenOf(cap, *m)))",
  ["rewrite ← (let c = *m; ins(cap, &c, k, v); agreeLen(cap, &c, invIns(cap, m, k, v, hm))) in",
   "rewrite ← agreeIns(cap, m, k, v, hm) in",
   "rewrite ← agreeGet(cap, m, k, hm) in",
   "rewrite ← agreeLen(cap, m, hm) in",
   "m12(absOf(cap, *m), k, v, absInv(cap, m, hm))"]))
L.append(("H13", "LenRemoveFrom", "remove takes one from len if the key was present",
  "MM rem getOf lenOf inv absOf mget mlen mremove minv invRem agreeGet agreeLen agreeRem absInv m13".split(),
  M_ARGS + " (k : Word) (hm : inv(cap, *m))",
  "Eq Word (let c = *m; rem(cap, &c, k); lenOf(cap, c)) (Shrink(getOf(cap, *m, k), lenOf(cap, *m)))",
  ["rewrite ← (let c = *m; rem(cap, &c, k); agreeLen(cap, &c, invRem(cap, m, k, hm))) in",
   "rewrite ← agreeRem(cap, m, k, hm) in",
   "rewrite ← agreeGet(cap, m, k, hm) in",
   "rewrite ← agreeLen(cap, m, hm) in",
   "m13(absOf(cap, *m), k, absInv(cap, m, hm))"]))
L.append(("H14", "GetMutGetFrom", "writing through get_mut has the effect of insert on every get",
  "MM ins getOf getMut inv absOf mget minsert mwrite minv invIns invWrite agreeGet agreeIns agreeWrite absInv m14".split(),
  M_ARGS + " (k : Word) (w : Word) (k2 : Word) (hm : inv(cap, *m)) (hk : IsSome(getOf(cap, *m, k)))",
  "Eq Opt (let c = *m; let r = getMut(cap, &c, k, hk); *r := w; getOf(cap, c, k2))\n        (let c = *m; ins(cap, &c, k, w); getOf(cap, c, k2))",
  ["rewrite ← (let c = *m; let r = getMut(cap, &c, k, hk); *r := w; agreeGet(cap, &c, k2, invWrite(cap, m, k, w, hm, hk))) in",
   "rewrite ← agreeWrite(cap, m, k, w, hm, hk) in",
   "rewrite ← (let c = *m; ins(cap, &c, k, w); agreeGet(cap, &c, k2, invIns(cap, m, k, w, hm))) in",
   "rewrite ← agreeIns(cap, m, k, w, hm) in",
   "m14(absOf(cap, *m), k, w, k2, absInv(cap, m, hm), (rewrite agreeGet(cap, m, k, hm) in hk))"]))
L.append(("H15", "GetMutLenFrom", "... and on len",
  "MM ins getOf lenOf getMut inv absOf mget mlen minsert mwrite minv invIns invWrite agreeGet agreeLen agreeIns agreeWrite absInv m15".split(),
  M_ARGS + " (k : Word) (w : Word) (hm : inv(cap, *m)) (hk : IsSome(getOf(cap, *m, k)))",
  "Eq Word (let c = *m; let r = getMut(cap, &c, k, hk); *r := w; lenOf(cap, c))\n        (let c = *m; ins(cap, &c, k, w); lenOf(cap, c))",
  ["rewrite ← (let c = *m; let r = getMut(cap, &c, k, hk); *r := w; agreeLen(cap, &c, invWrite(cap, m, k, w, hm, hk))) in",
   "rewrite ← agreeWrite(cap, m, k, w, hm, hk) in",
   "rewrite ← (let c = *m; ins(cap, &c, k, w); agreeLen(cap, &c, invIns(cap, m, k, w, hm))) in",
   "rewrite ← agreeIns(cap, m, k, w, hm) in",
   "m15(absOf(cap, *m), k, w, absInv(cap, m, hm), (rewrite agreeGet(cap, m, k, hm) in hk))"]))

def block():
    out = []
    for H, name, comment, params, args, goal, proof in L:
        out.append(f"  -- {H}: {comment}.")
        out.append(f"  def {name}")
        for p in params:
            out.append("      " + P[p])
        out.append(f"      {args} :")
        out.append(f"      {goal} := (")
        for line in proof:
            out.append("    " + line)
        out.append("  )")
        out.append("")
    return "\n".join(out[:-1]) + "\n"

# instantiation: concrete names for each param
CONCRETE = {"MM": "MMap", "new": "MapNew", "ins": "MapInsert", "rem": "MapRemove", "getOf": "GetOf", "lenOf": "LenOf",
  "getMut": "MapGetMut", "inv": "Inv", "absOf": "AbsOf", "mnew": "MNew", "mget": "MGet", "mlen": "MLen",
  "minsert": "MInsert", "mremove": "MRemove", "mwrite": "MWrite", "minv": "MInv", "invNew": "InvNew",
  "invIns": "InvInsert", "invRem": "InvRemove", "invWrite": "GetMutInv", "absInv": "AbsInv", "absNew": "AbsNew",
  "agreeGet": "AgreeGet", "agreeLen": "AgreeLen", "agreeIns": "AgreeInsert", "agreeInsRes": "AgreeInsertResult",
  "agreeRem": "AgreeRemove", "agreeRemRes": "AgreeRemoveResult", "agreeWrite": "AgreeWrite",
  "m4": "MGetNew", "m5": "MGetInsertSame", "m6": "MGetInsertOther", "m8": "MGetRemoveSame", "m9": "MGetRemoveOther",
  "m11": "MLenNew", "m12": "MLenInsert", "m13": "MLenRemove", "m14": "MWriteGet", "m15": "MWriteLen"}

def instantiation(name, params, argnames):
    return f"{name}({', '.join([CONCRETE[p] for p in params] + argnames)})"

if __name__ == "__main__":
    import sys
    print(block())
