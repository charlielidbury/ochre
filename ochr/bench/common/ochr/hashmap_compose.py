"""The HashMapCompose block of hashmap/ochr-2p: generic lemmas that derive H4–H15 about any
in-place map from its agreement with a pure model and the model's properties (used by
gen_hashmap_2p.py). Everything is generic in the value type: the operations, the model and the
proofs are parameters generic in `V` (as the solver's are), and each lemma is then stated at a
value type `V` of its own."""
P = {
 "MM": "(MM : Π(V : Type). Type)",
 "new": "(new : Π(V : Type) (cap : Word) (h : Lt(Zero, cap)). Map(V, cap))",
 "ins": "(ins : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V). Opt(V))",
 "rem": "(rem : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word). Opt(V))",
 "containsOf": "(containsOf : Π(V : Type) (cap : Word) (m : Map(V, cap)) (k : Word). Bool)",
 "lenOf": "(lenOf : Π(V : Type) (cap : Word) (m : Map(V, cap)). Word)",
 "get": "(get : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (h : IsTrue(containsOf(V, cap, *m, k))). &V)",
 "getMut": "(getMut : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (h : IsTrue(containsOf(V, cap, *m, k))). &V)",
 "inv": "(inv : Π(V : Type) (cap : Word) (m : Map(V, cap)). Prop)",
 "absOf": "(absOf : Π(V : Type) (cap : Word) (m : Map(V, cap)). MM(V))",
 "mnew": "(mnew : Π(V : Type). MM(V))",
 "mget": "(mget : Π(V : Type) (a : MM(V)) (k : Word). Opt(V))",
 "mlen": "(mlen : Π(V : Type) (a : MM(V)). Word)",
 "minsert": "(minsert : Π(V : Type) (a : MM(V)) (k : Word) (v : V). MM(V))",
 "mremove": "(mremove : Π(V : Type) (a : MM(V)) (k : Word). MM(V))",
 "mwrite": "(mwrite : Π(V : Type) (a : MM(V)) (k : Word) (w : V). MM(V))",
 "minv": "(minv : Π(V : Type) (a : MM(V)). Prop)",
 "invNew": "(invNew : Π(V : Type) (cap : Word) (h : Lt(Zero, cap)). inv(V, cap, new(V, cap, h)))",
 "invIns": "(invIns : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V) (hm : inv(V, cap, *m)).\n        (let c = *m; ins(V, cap, &c, k, v); inv(V, cap, c)))",
 "invRem": "(invRem : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : inv(V, cap, *m)).\n        (let c = *m; rem(V, cap, &c, k); inv(V, cap, c)))",
 "invWrite": "(invWrite : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (w : V) (hm : inv(V, cap, *m)) (hk : IsTrue(containsOf(V, cap, *m, k))).\n        (let c = *m; let r = getMut(V, cap, &c, k, hk); *r := w; inv(V, cap, c)))",
 "absInv": "(absInv : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (hm : inv(V, cap, *m)). minv(V, absOf(V, cap, *m)))",
 "absNew": "(absNew : Π(V : Type) (cap : Word) (h : Lt(Zero, cap)). Eq(MM(V), absOf(V, cap, new(V, cap, h)), mnew(V)))",
 "agreeContains": "(agreeContains : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : inv(V, cap, *m)).\n        Eq(Bool, containsOf(V, cap, *m, k), IsSomeB(V, mget(V, absOf(V, cap, *m), k))))",
 "agreeGet": "(agreeGet : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : inv(V, cap, *m)) (h : IsTrue(containsOf(V, cap, *m, k))).\n        Eq(Opt(V), Some(clone(*get(V, cap, m, k, h))), mget(V, absOf(V, cap, *m), k)))",
 "agreeLen": "(agreeLen : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (hm : inv(V, cap, *m)). Eq(Word, lenOf(V, cap, *m), mlen(V, absOf(V, cap, *m))))",
 "agreeIns": "(agreeIns : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V) (hm : inv(V, cap, *m)).\n        Eq(MM(V), (let c = *m; ins(V, cap, &c, k, v); absOf(V, cap, c)), minsert(V, absOf(V, cap, *m), k, v)))",
 "agreeInsRes": "(agreeInsRes : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V) (hm : inv(V, cap, *m)).\n        Eq(Opt(V), (let c = *m; ins(V, cap, &c, k, v)), mget(V, absOf(V, cap, *m), k)))",
 "agreeRem": "(agreeRem : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : inv(V, cap, *m)).\n        Eq(MM(V), (let c = *m; rem(V, cap, &c, k); absOf(V, cap, c)), mremove(V, absOf(V, cap, *m), k)))",
 "agreeRemRes": "(agreeRemRes : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : inv(V, cap, *m)).\n        Eq(Opt(V), (let c = *m; rem(V, cap, &c, k)), mget(V, absOf(V, cap, *m), k)))",
 "agreeWrite": "(agreeWrite : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (w : V) (hm : inv(V, cap, *m)) (hk : IsTrue(containsOf(V, cap, *m, k))).\n        Eq(MM(V), (let c = *m; let r = getMut(V, cap, &c, k, hk); *r := w; absOf(V, cap, c)), mwrite(V, absOf(V, cap, *m), k, w)))",
 "m4": "(m4 : Π(V : Type) (k : Word). Eq(Opt(V), mget(V, mnew(V), k), None[V]))",
 "m5": "(m5 : Π(V : Type) (a : MM(V)) (k : Word) (v : V) (h : minv(V, a)). Eq(Opt(V), mget(V, minsert(V, a, k, v), k), Some(v)))",
 "m6": "(m6 : Π(V : Type) (a : MM(V)) (k : Word) (k2 : Word) (v : V) (h : minv(V, a)) (ne : Π(e : Eq(Word, k2, k)). False).\n        Eq(Opt(V), mget(V, minsert(V, a, k, v), k2), mget(V, a, k2)))",
 "m8": "(m8 : Π(V : Type) (a : MM(V)) (k : Word) (h : minv(V, a)). Eq(Opt(V), mget(V, mremove(V, a, k), k), None[V]))",
 "m9": "(m9 : Π(V : Type) (a : MM(V)) (k : Word) (k2 : Word) (h : minv(V, a)) (ne : Π(e : Eq(Word, k2, k)). False).\n        Eq(Opt(V), mget(V, mremove(V, a, k), k2), mget(V, a, k2)))",
 "m11": "(m11 : Π(V : Type). Eq(Word, mlen(V, mnew(V)), Zero))",
 "m12": "(m12 : Π(V : Type) (a : MM(V)) (k : Word) (v : V) (h : minv(V, a)). Eq(Word, mlen(V, minsert(V, a, k, v)), Grow(IsSomeB(V, mget(V, a, k)), mlen(V, a))))",
 "m13": "(m13 : Π(V : Type) (a : MM(V)) (k : Word) (h : minv(V, a)). Eq(Word, mlen(V, mremove(V, a, k)), Shrink(IsSomeB(V, mget(V, a, k)), mlen(V, a))))",
 "m14": "(m14 : Π(V : Type) (a : MM(V)) (k : Word) (w : V) (k2 : Word) (h : minv(V, a)) (hk : IsTrue(IsSomeB(V, mget(V, a, k)))).\n        Eq(Opt(V), mget(V, mwrite(V, a, k, w), k2), mget(V, minsert(V, a, k, w), k2)))",
 "m15": "(m15 : Π(V : Type) (a : MM(V)) (k : Word) (w : V) (h : minv(V, a)) (hk : IsTrue(IsSomeB(V, mget(V, a, k)))).\n        Eq(Word, mlen(V, mwrite(V, a, k, w)), mlen(V, minsert(V, a, k, w))))",
}
M_ARGS = "(V : Type) (cap : Word) (m : &Map(V, cap))"
INS = "(let c = *m; ins(V, cap, &c, k, v); c)"
REM = "(let c = *m; rem(V, cap, &c, k); c)"
WR = "(let c = *m; let r = getMut(V, cap, &c, k, hk); *r := w; c)"
INSW = "(let c = *m; ins(V, cap, &c, k, w); c)"
# the agreement at the map a statement runs on: after insert, remove, a write, or insert of w
AT_INS = "(let c = *m; ins(V, cap, &c, k, v); {})"
AT_REM = "(let c = *m; rem(V, cap, &c, k); {})"
AT_WR = "(let c = *m; let r = getMut(V, cap, &c, k, hk); *r := w; {})"
AT_INSW = "(let c = *m; ins(V, cap, &c, k, w); {})"
INV_INS = "invIns(V, cap, m, k, v, hm)"
INV_REM = "invRem(V, cap, m, k, hm)"
INV_WR = "invWrite(V, cap, m, k, w, hm, hk)"
INV_INSW = "invIns(V, cap, m, k, w, hm)"
AINV = "absInv(V, cap, m, hm)"
L = []  # (H, name, comment, params, args, goal, proof)
L.append(("H4", "ContainsNewFrom", "contains(new(c), k) = false",
  "MM new containsOf inv absOf mnew mget invNew agreeContains absNew m4".split(),
  "(V : Type) (cap : Word) (h : Lt(Zero, cap)) (k : Word)",
  "Eq(Bool, containsOf(V, cap, new(V, cap, h), k), false)",
  ["rewrite ← (let c = new(V, cap, h); agreeContains(V, cap, &c, k, invNew(V, cap, h))) in",
   "rewrite ← absNew(V, cap, h) in",
   "rewrite ← m4(V, k) in",
   "refl"]))
L.append(("H5a", "ContainsInsertSameFrom", "after insert(m, k, v), contains(m′, k) = true",
  "MM ins containsOf inv absOf mget minsert minv invIns agreeContains agreeIns absInv m5".split(),
  M_ARGS + " (k : Word) (v : V) (hm : inv(V, cap, *m))",
  "Eq(Bool, (let c = *m; ins(V, cap, &c, k, v); containsOf(V, cap, c, k)), true)",
  ["rewrite ← " + AT_INS.format(f"agreeContains(V, cap, &c, k, {INV_INS})") + " in",
   "rewrite ← agreeIns(V, cap, m, k, v, hm) in",
   f"rewrite ← m5(V, absOf(V, cap, *m), k, v, {AINV}) in",
   "refl"]))
L.append(("H5b", "GetInsertSameFrom", "... and the value read through get(m′, k) is v",
  "MM ins containsOf get inv absOf mget minsert minv invIns agreeGet agreeIns absInv m5".split(),
  M_ARGS + f" (k : Word) (v : V) (hm : inv(V, cap, *m))\n      (h : IsTrue(containsOf(V, cap, {INS}, k)))",
  "Eq(V, (let c = *m; ins(V, cap, &c, k, v); clone(*get(V, cap, &c, k, h))), v)",
  [f"let e : Eq(Opt(V), mget(V, absOf(V, cap, {INS}), k), Some(v)) = (",
   f"  rewrite ← agreeIns(V, cap, m, k, v, hm) in m5(V, absOf(V, cap, *m), k, v, {AINV}));",
   "trans(" + AT_INS.format(f"agreeGet(V, cap, &c, k, {INV_INS}, h)") + ", e)"]))
L.append(("H6a", "ContainsInsertOtherFrom", "after insert(m, k, v), contains(m′, k′) = contains(m, k′) for k′ ≠ k",
  "MM ins containsOf inv absOf mget minsert minv invIns agreeContains agreeIns absInv m6".split(),
  M_ARGS + " (k : Word) (k2 : Word) (v : V) (hm : inv(V, cap, *m)) (ne : Π(e : Eq(Word, k2, k)). False)",
  "Eq(Bool, (let c = *m; ins(V, cap, &c, k, v); containsOf(V, cap, c, k2)), containsOf(V, cap, *m, k2))",
  ["rewrite ← " + AT_INS.format(f"agreeContains(V, cap, &c, k2, {INV_INS})") + " in",
   "rewrite ← agreeIns(V, cap, m, k, v, hm) in",
   "rewrite ← agreeContains(V, cap, m, k2, hm) in",
   f"rewrite ← m6(V, absOf(V, cap, *m), k, k2, v, {AINV}, ne) in",
   "refl"]))
L.append(("H6b", "GetInsertOtherFrom", "... and the value read through get at k′ is the same, when k′ is present",
  "MM ins containsOf get inv absOf mget minsert minv invIns agreeGet agreeIns absInv m6".split(),
  M_ARGS + f" (k : Word) (k2 : Word) (v : V) (hm : inv(V, cap, *m)) (ne : Π(e : Eq(Word, k2, k)). False)\n      (h : IsTrue(containsOf(V, cap, *m, k2))) (h2 : IsTrue(containsOf(V, cap, {INS}, k2)))",
  "Eq(V, (let c = *m; ins(V, cap, &c, k, v); clone(*get(V, cap, &c, k2, h2))), clone(*get(V, cap, m, k2, h)))",
  [f"let e : Eq(Opt(V), mget(V, absOf(V, cap, {INS}), k2), mget(V, absOf(V, cap, *m), k2)) = (",
   f"  rewrite ← agreeIns(V, cap, m, k, v, hm) in m6(V, absOf(V, cap, *m), k, k2, v, {AINV}, ne));",
   "trans(trans(" + AT_INS.format(f"agreeGet(V, cap, &c, k2, {INV_INS}, h2)") + ", e), symm(agreeGet(V, cap, m, k2, hm, h)))"]))
L.append(("H7a", "InsertReturnsContainsFrom", "insert returns None exactly when k was absent",
  "MM ins containsOf inv absOf mget agreeContains agreeInsRes".split(),
  M_ARGS + " (k : Word) (v : V) (hm : inv(V, cap, *m))",
  "Eq(Bool, (let c = *m; IsSomeB(V, ins(V, cap, &c, k, v))), containsOf(V, cap, *m, k))",
  ["rewrite ← agreeInsRes(V, cap, m, k, v, hm) in",
   "rewrite ← agreeContains(V, cap, m, k, hm) in",
   "refl"]))
L.append(("H7b", "InsertReturnsGetFrom", "when k was present, insert returns Some of the value bound to it",
  "MM ins containsOf get inv absOf mget agreeGet agreeInsRes".split(),
  M_ARGS + " (k : Word) (v : V) (hm : inv(V, cap, *m)) (h : IsTrue(containsOf(V, cap, *m, k)))",
  "Eq(Opt(V), (let c = *m; ins(V, cap, &c, k, v)), Some(clone(*get(V, cap, m, k, h))))",
  ["trans(agreeInsRes(V, cap, m, k, v, hm), symm(agreeGet(V, cap, m, k, hm, h)))"]))
L.append(("H8", "ContainsRemoveSameFrom", "after remove(m, k), contains(m′, k) = false",
  "MM rem containsOf inv absOf mget mremove minv invRem agreeContains agreeRem absInv m8".split(),
  M_ARGS + " (k : Word) (hm : inv(V, cap, *m))",
  "Eq(Bool, (let c = *m; rem(V, cap, &c, k); containsOf(V, cap, c, k)), false)",
  ["rewrite ← " + AT_REM.format(f"agreeContains(V, cap, &c, k, {INV_REM})") + " in",
   "rewrite ← agreeRem(V, cap, m, k, hm) in",
   f"rewrite ← m8(V, absOf(V, cap, *m), k, {AINV}) in",
   "refl"]))
L.append(("H9a", "ContainsRemoveOtherFrom", "after remove(m, k), contains(m′, k′) = contains(m, k′) for k′ ≠ k",
  "MM rem containsOf inv absOf mget mremove minv invRem agreeContains agreeRem absInv m9".split(),
  M_ARGS + " (k : Word) (k2 : Word) (hm : inv(V, cap, *m)) (ne : Π(e : Eq(Word, k2, k)). False)",
  "Eq(Bool, (let c = *m; rem(V, cap, &c, k); containsOf(V, cap, c, k2)), containsOf(V, cap, *m, k2))",
  ["rewrite ← " + AT_REM.format(f"agreeContains(V, cap, &c, k2, {INV_REM})") + " in",
   "rewrite ← agreeRem(V, cap, m, k, hm) in",
   "rewrite ← agreeContains(V, cap, m, k2, hm) in",
   f"rewrite ← m9(V, absOf(V, cap, *m), k, k2, {AINV}, ne) in",
   "refl"]))
L.append(("H9b", "GetRemoveOtherFrom", "... and the value read through get at k′ is the same, when k′ is present",
  "MM rem containsOf get inv absOf mget mremove minv invRem agreeGet agreeRem absInv m9".split(),
  M_ARGS + f" (k : Word) (k2 : Word) (hm : inv(V, cap, *m)) (ne : Π(e : Eq(Word, k2, k)). False)\n      (h : IsTrue(containsOf(V, cap, *m, k2))) (h2 : IsTrue(containsOf(V, cap, {REM}, k2)))",
  "Eq(V, (let c = *m; rem(V, cap, &c, k); clone(*get(V, cap, &c, k2, h2))), clone(*get(V, cap, m, k2, h)))",
  [f"let e : Eq(Opt(V), mget(V, absOf(V, cap, {REM}), k2), mget(V, absOf(V, cap, *m), k2)) = (",
   f"  rewrite ← agreeRem(V, cap, m, k, hm) in m9(V, absOf(V, cap, *m), k, k2, {AINV}, ne));",
   "trans(trans(" + AT_REM.format(f"agreeGet(V, cap, &c, k2, {INV_REM}, h2)") + ", e), symm(agreeGet(V, cap, m, k2, hm, h)))"]))
L.append(("H10a", "RemoveReturnsContainsFrom", "remove returns None exactly when k was absent",
  "MM rem containsOf inv absOf mget agreeContains agreeRemRes".split(),
  M_ARGS + " (k : Word) (hm : inv(V, cap, *m))",
  "Eq(Bool, (let c = *m; IsSomeB(V, rem(V, cap, &c, k))), containsOf(V, cap, *m, k))",
  ["rewrite ← agreeRemRes(V, cap, m, k, hm) in",
   "rewrite ← agreeContains(V, cap, m, k, hm) in",
   "refl"]))
L.append(("H10b", "RemoveReturnsGetFrom", "when k was present, remove returns Some of the value bound to it",
  "MM rem containsOf get inv absOf mget agreeGet agreeRemRes".split(),
  M_ARGS + " (k : Word) (hm : inv(V, cap, *m)) (h : IsTrue(containsOf(V, cap, *m, k)))",
  "Eq(Opt(V), (let c = *m; rem(V, cap, &c, k)), Some(clone(*get(V, cap, m, k, h))))",
  ["trans(agreeRemRes(V, cap, m, k, hm), symm(agreeGet(V, cap, m, k, hm, h)))"]))
L.append(("H11", "LenNewFrom", "len(new(c)) = 0",
  "MM new lenOf inv absOf mnew mlen invNew agreeLen absNew m11".split(),
  "(V : Type) (cap : Word) (h : Lt(Zero, cap))",
  "Eq(Word, lenOf(V, cap, new(V, cap, h)), Zero)",
  ["rewrite ← (let c = new(V, cap, h); agreeLen(V, cap, &c, invNew(V, cap, h))) in",
   "rewrite ← absNew(V, cap, h) in",
   "m11(V)"]))
L.append(("H12", "LenInsertFrom", "insert adds one to len if the key was absent",
  "MM ins containsOf lenOf inv absOf mget mlen minsert minv invIns agreeContains agreeLen agreeIns absInv m12".split(),
  M_ARGS + " (k : Word) (v : V) (hm : inv(V, cap, *m))",
  "Eq(Word, (let c = *m; ins(V, cap, &c, k, v); lenOf(V, cap, c)), Grow(containsOf(V, cap, *m, k), lenOf(V, cap, *m)))",
  ["rewrite ← " + AT_INS.format(f"agreeLen(V, cap, &c, {INV_INS})") + " in",
   "rewrite ← agreeIns(V, cap, m, k, v, hm) in",
   "rewrite ← agreeContains(V, cap, m, k, hm) in",
   "rewrite ← agreeLen(V, cap, m, hm) in",
   f"m12(V, absOf(V, cap, *m), k, v, {AINV})"]))
L.append(("H13", "LenRemoveFrom", "remove takes one from len if the key was present",
  "MM rem containsOf lenOf inv absOf mget mlen mremove minv invRem agreeContains agreeLen agreeRem absInv m13".split(),
  M_ARGS + " (k : Word) (hm : inv(V, cap, *m))",
  "Eq(Word, (let c = *m; rem(V, cap, &c, k); lenOf(V, cap, c)), Shrink(containsOf(V, cap, *m, k), lenOf(V, cap, *m)))",
  ["rewrite ← " + AT_REM.format(f"agreeLen(V, cap, &c, {INV_REM})") + " in",
   "rewrite ← agreeRem(V, cap, m, k, hm) in",
   "rewrite ← agreeContains(V, cap, m, k, hm) in",
   "rewrite ← agreeLen(V, cap, m, hm) in",
   f"m13(V, absOf(V, cap, *m), k, {AINV})"]))
HKM = "(rewrite agreeContains(V, cap, m, k, hm) in hk)"
L.append(("H14a", "GetMutContainsFrom", "writing w through get_mut has the effect of insert on every contains",
  "MM ins containsOf getMut inv absOf mget minsert mwrite minv invIns invWrite agreeContains agreeIns agreeWrite absInv m14".split(),
  M_ARGS + " (k : Word) (w : V) (k2 : Word) (hm : inv(V, cap, *m)) (hk : IsTrue(containsOf(V, cap, *m, k)))",
  "Eq(Bool, (let c = *m; let r = getMut(V, cap, &c, k, hk); *r := w; containsOf(V, cap, c, k2)),\n        (let c = *m; ins(V, cap, &c, k, w); containsOf(V, cap, c, k2)))",
  ["rewrite ← " + AT_WR.format(f"agreeContains(V, cap, &c, k2, {INV_WR})") + " in",
   "rewrite ← agreeWrite(V, cap, m, k, w, hm, hk) in",
   "rewrite ← " + AT_INSW.format(f"agreeContains(V, cap, &c, k2, {INV_INSW})") + " in",
   "rewrite ← agreeIns(V, cap, m, k, w, hm) in",
   f"rewrite ← m14(V, absOf(V, cap, *m), k, w, k2, {AINV}, {HKM}) in",
   "refl"]))
L.append(("H14b", "GetMutGetFrom", "... and on the value read through get",
  "MM ins containsOf get getMut inv absOf mget minsert mwrite minv invIns invWrite agreeContains agreeGet agreeIns agreeWrite absInv m14".split(),
  M_ARGS + f" (k : Word) (w : V) (k2 : Word) (hm : inv(V, cap, *m)) (hk : IsTrue(containsOf(V, cap, *m, k)))\n      (h1 : IsTrue(containsOf(V, cap, {WR}, k2))) (h2 : IsTrue(containsOf(V, cap, {INSW}, k2)))",
  "Eq(V, (let c = *m; let r = getMut(V, cap, &c, k, hk); *r := w; clone(*get(V, cap, &c, k2, h1))),\n        (let c = *m; ins(V, cap, &c, k, w); clone(*get(V, cap, &c, k2, h2))))",
  [f"let e : Eq(Opt(V), mget(V, absOf(V, cap, {WR}), k2), mget(V, absOf(V, cap, {INSW}), k2)) = (",
   f"  rewrite ← agreeWrite(V, cap, m, k, w, hm, hk) in rewrite ← agreeIns(V, cap, m, k, w, hm) in m14(V, absOf(V, cap, *m), k, w, k2, {AINV}, {HKM}));",
   "trans(trans(" + AT_WR.format(f"agreeGet(V, cap, &c, k2, {INV_WR}, h1)") + ", e),",
   "  symm(" + AT_INSW.format(f"agreeGet(V, cap, &c, k2, {INV_INSW}, h2)") + "))"]))
L.append(("H15", "GetMutLenFrom", "... and on len",
  "MM ins containsOf lenOf getMut inv absOf mget mlen minsert mwrite minv invIns invWrite agreeContains agreeLen agreeIns agreeWrite absInv m15".split(),
  M_ARGS + " (k : Word) (w : V) (hm : inv(V, cap, *m)) (hk : IsTrue(containsOf(V, cap, *m, k)))",
  "Eq(Word, (let c = *m; let r = getMut(V, cap, &c, k, hk); *r := w; lenOf(V, cap, c)),\n        (let c = *m; ins(V, cap, &c, k, w); lenOf(V, cap, c)))",
  ["rewrite ← " + AT_WR.format(f"agreeLen(V, cap, &c, {INV_WR})") + " in",
   "rewrite ← agreeWrite(V, cap, m, k, w, hm, hk) in",
   "rewrite ← " + AT_INSW.format(f"agreeLen(V, cap, &c, {INV_INSW})") + " in",
   "rewrite ← agreeIns(V, cap, m, k, w, hm) in",
   f"m15(V, absOf(V, cap, *m), k, w, {AINV}, {HKM})"]))


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


# instantiation: concrete names for each parameter
CONCRETE = {"MM": "MMap", "new": "MapNew", "ins": "MapInsert", "rem": "MapRemove", "containsOf": "ContainsOf",
  "lenOf": "LenOf", "get": "MapGet", "getMut": "MapGetMut", "inv": "Inv", "absOf": "AbsOf", "mnew": "MNew",
  "mget": "MGet", "mlen": "MLen", "minsert": "MInsert", "mremove": "MRemove", "mwrite": "MWrite", "minv": "MInv",
  "invNew": "InvNew", "invIns": "InvInsert", "invRem": "InvRemove", "invWrite": "GetMutInv", "absInv": "AbsInv",
  "absNew": "AbsNew", "agreeContains": "AgreeContains", "agreeGet": "AgreeGet", "agreeLen": "AgreeLen",
  "agreeIns": "AgreeInsert", "agreeInsRes": "AgreeInsertResult", "agreeRem": "AgreeRemove",
  "agreeRemRes": "AgreeRemoveResult", "agreeWrite": "AgreeWrite",
  "m4": "MGetNew", "m5": "MGetInsertSame", "m6": "MGetInsertOther", "m8": "MGetRemoveSame", "m9": "MGetRemoveOther",
  "m11": "MLenNew", "m12": "MLenInsert", "m13": "MLenRemove", "m14": "MWriteGet", "m15": "MWriteLen"}


def instantiation(name, params, argnames):
    return f"{name}({', '.join([CONCRETE[p] for p in params] + argnames)})"


if __name__ == "__main__":
    print(block())
