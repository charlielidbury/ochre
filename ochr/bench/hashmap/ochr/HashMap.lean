-- FIXED-BEGIN header
import Ochr.Examples.«16Arrays»

/-! # Verified in-place hash map (condition `ochr`)

Read `ASSIGNMENT.md` first. Replace every hole `?` with a definition or a proof, and add any
helper definitions and lemmas you need to the block `HashMapSolution`, between its FIXED
regions. Everything inside a FIXED region must stay exactly as it is.

Check your work with `lake exe check` (the checker's verdict on every declaration) and
`./grade.sh` (the grade). -/

/-! ## The representation and what is provided (FIXED, SPEC §1–§2)

The arrays library is `ArrayLemmas` (`checker/Ochr/Examples/16Arrays.lean`). A bucket is
reached in place through the library's element borrow, `GetMut(Bucket(V), cap, s, i, h)`. -/

ochr HashMapSpec uses ArrayLemmas {
  -- Opt(V): what insert and remove return (the value moved out of the map), or nothing.
  inductive Opt (V : Type) := None | Some(val : V)

  -- Whether a result holds a value (H7a, H10a).
  def IsSomeB (V : Type) (o : Opt(V)) : Bool := (
    match o {
      None => false,
      Some(x) => true,
    }
  )

  -- A boolean that is true, as a proposition: the precondition of get and get_mut.
  def IsTrue (b : Bool) : Prop := (
    match b {
      false => False,
      true => ⊤,
    }
  )

  -- len(m) + 1 if the key was absent (`c` = contains(m, k) = false), and len(m) otherwise: H12.
  def Grow (c : Bool) (l : Word) : Word := (
    match c {
      false => Succ(l),
      true => l,
    }
  )

  -- len(m) − 1 if the key was present, and len(m) otherwise: H13.
  def Shrink (c : Bool) (l : Word) : Word := (
    match c {
      false => l,
      true => Sub(l, Succ(Zero)),
    }
  )

  -- A bucket: a singly linked list of entries, each node owning the next.
  inductive Bucket (V : Type) := BNil | BCons(key : Word, value : V, next : Bucket(V))

  -- A map of capacity `cap`: an array of `cap` buckets and the length. The capacity is part
  -- of the type, `Map(V, cap)`, and never changes. (`MapOf` takes the array's model type as a
  -- parameter; `Map(V, cap)` fills it in, so `slots` is an `Array(Bucket(V), cap)`.)
  inductive MapOf (R : Type) := MkMap(slots : ArrayOf(R), len : Word)

  def Map (V : Type) (cap : Word) : Type := MapOf(Cells(Bucket(V), cap))

  -- idx(k) = k mod cap: count up to `k` with a remainder `r` that wraps round at `cap`.
  def IdxGo (cap : Word) (k : Word) (r : Word) : Word by k := (
    match k {
      Zero => r,
      Succ(k') => (
        let d = LtDec(Succ(r), cap);
        match d {
          Yes(h) => IdxGo(cap, k', Succ(r)),
          No(h) => IdxGo(cap, k', Zero),
        }
      ),
    }
  )

  def Idx (cap : Word) (k : Word) : Word := IdxGo(cap, k, Zero)

  -- For example, 13 mod 4 = 1.
  def IdxExample : Eq(Word, Idx(W(4), W(13)), W(1)) := refl

  -- The bucket index is in bounds.
  def IdxGoLt (cap : Word) (k : Word) (r : Word) (hr : Lt(r, cap)) : Lt(IdxGo(cap, k, r), cap) by k := (
    match k {
      Zero => hr,
      Succ(k') => (
        let d = LtDec(Succ(r), cap);
        match d {
          Yes(h) => IdxGoLt(cap, k', Succ(r), h),
          No(h) => IdxGoLt(cap, k', Zero, LeTrans(Succ(Zero), Succ(r), cap, refl, hr)),
        }
      ),
    }
  )

  def IdxLt (cap : Word) (k : Word) (h : Lt(Zero, cap)) : Lt(Idx(cap, k), cap) := IdxGoLt(cap, k, Zero, h)

  -- Key comparison, with the evidence (as the library's `LeDec` for `Le`).
  def EqDec (a : Word) (b : Word) : Dec(Eq(Word, a, b), Π(e : Eq(Word, a, b)). False) by a := (
    match a {
      Zero => match b {
        Zero => Yes(refl),
        Succ(b') => No(λ(e : Eq(Word, Zero, Succ(b'))) : False => match e {}),
      },
      Succ(a') => match b {
        Zero => No(λ(e : Eq(Word, Succ(a'), Zero)) : False => match e {}),
        Succ(b') => EqDec(a', b'),
      },
    }
  )
}

/-! ## Your solution

The operations, your invariant `Inv`, and the proofs of H1–H18. The properties are stated
about the operations themselves, run on a copy of the map: `let c = *m; MapInsert(V, cap, &c,
k, v); ContainsOf(V, cap, c, k)` inserts into a copy `c` of the map `*m` in place, then asks
whether `k` is in `c`. `*m` is still the map before. A property about the value at a key reads
it through `MapGet` inside the statement, given that the key is present. -/

ochr HashMapSolution uses HashMapSpec {
-- FIXED-END header

  -- Your helper definitions and lemmas go here, and anywhere else between the FIXED regions
  -- of this block.

  -- FIXED-BEGIN new
  -- new(c): an empty map, with `cap` empty buckets and length 0. `h` is the precondition c ≥ 1.
  def MapNew (V : Type) (cap : Word) (h : Lt(Zero, cap)) : Map(V, cap) :=
  -- FIXED-END new
    ?

  -- FIXED-BEGIN len
  -- len(m): the number of keys in the map.
  def MapLen (V : Type) (cap : Word) (m : &Map(V, cap)) : Word :=
  -- FIXED-END len
    ?

  -- FIXED-BEGIN contains
  -- contains(m, k): whether `k` is bound.
  def MapContains (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) : Bool :=
  -- FIXED-END contains
    ?

  -- FIXED-BEGIN get
  -- contains(m, k) and len(m) of a map value, run on a copy of it: what the properties observe.
  def ContainsOf (V : Type) (cap : Word) (m : Map(V, cap)) (k : Word) : Bool := MapContains(V, cap, &m, k)

  def LenOf (V : Type) (cap : Word) (m : Map(V, cap)) : Word := MapLen(V, cap, &m)

  -- `k` is bound in the map value `m`: the precondition of get and get_mut.
  def Contains (V : Type) (cap : Word) (m : Map(V, cap)) (k : Word) : Prop := IsTrue(ContainsOf(V, cap, m, k))

  -- get(m, k): a borrow of the value bound to `k`, which must be present; used read-only.
  def MapGet (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (h : Contains(V, cap, *m, k)) : &V :=
  -- FIXED-END get
    ?

  -- FIXED-BEGIN insert
  -- insert(m, k, v): bind `k` to `v`, in place; return the value `k` was bound to before, moved
  -- out of the map, or None.
  def MapInsert (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V) : Opt(V) :=
  -- FIXED-END insert
    ?

  -- FIXED-BEGIN remove
  -- remove(m, k): unbind `k`, in place; return the value it was bound to, moved out, or None.
  def MapRemove (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) : Opt(V) :=
  -- FIXED-END remove
    ?

  -- FIXED-BEGIN get_mut
  -- get_mut(m, k): a borrow of the value bound to `k`, which must be present.
  def MapGetMut (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (h : Contains(V, cap, *m, k)) : &V :=
  -- FIXED-END get_mut
    ?

  -- FIXED-BEGIN inv
  -- Inv(m): your invariant, any predicate that makes H1–H18 provable.
  def Inv (V : Type) (cap : Word) (m : Map(V, cap)) : Prop :=
  -- FIXED-END inv
    ?

  -- FIXED-BEGIN H1
  -- H1: Inv(new(c)).
  def InvNew (V : Type) (cap : Word) (h : Lt(Zero, cap)) : Inv(V, cap, MapNew(V, cap, h)) :=
  -- FIXED-END H1
    ?

  -- FIXED-BEGIN H2
  -- H2: insert preserves Inv.
  def InvInsert (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V) (hm : Inv(V, cap, *m)) :
      (let c = *m; MapInsert(V, cap, &c, k, v); Inv(V, cap, c)) :=
  -- FIXED-END H2
    ?

  -- FIXED-BEGIN H3
  -- H3: remove preserves Inv.
  def InvRemove (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : Inv(V, cap, *m)) :
      (let c = *m; MapRemove(V, cap, &c, k); Inv(V, cap, c)) :=
  -- FIXED-END H3
    ?

  -- FIXED-BEGIN H4
  -- H4: contains(new(c), k) = false.
  def ContainsNew (V : Type) (cap : Word) (h : Lt(Zero, cap)) (k : Word) : Eq(Bool, ContainsOf(V, cap, MapNew(V, cap, h), k), false) :=
  -- FIXED-END H4
    ?

  -- FIXED-BEGIN H5a
  -- H5a: after insert(m, k, v), contains(m′, k) = true.
  def ContainsInsertSame (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V) (hm : Inv(V, cap, *m)) :
      Eq(Bool, (let c = *m; MapInsert(V, cap, &c, k, v); ContainsOf(V, cap, c, k)), true) :=
  -- FIXED-END H5a
    ?

  -- FIXED-BEGIN H5b
  -- H5b: after insert(m, k, v), the value read through get(m′, k) is v.
  def GetInsertSame (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V) (hm : Inv(V, cap, *m))
      (h : Contains(V, cap, (let c = *m; MapInsert(V, cap, &c, k, v); c), k)) :
      Eq(V, (let c = *m; MapInsert(V, cap, &c, k, v); clone(*MapGet(V, cap, &c, k, h))), v) :=
  -- FIXED-END H5b
    ?

  -- FIXED-BEGIN H6a
  -- H6a: after insert(m, k, v), contains(m′, k′) = contains(m, k′) for k′ ≠ k.
  def ContainsInsertOther (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (k2 : Word) (v : V) (hm : Inv(V, cap, *m))
      (ne : Π(e : Eq(Word, k2, k)). False) :
      Eq(Bool, (let c = *m; MapInsert(V, cap, &c, k, v); ContainsOf(V, cap, c, k2)), ContainsOf(V, cap, *m, k2)) :=
  -- FIXED-END H6a
    ?

  -- FIXED-BEGIN H6b
  -- H6b: ... and the value read through get at k′ is the same, when k′ is present.
  def GetInsertOther (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (k2 : Word) (v : V) (hm : Inv(V, cap, *m))
      (ne : Π(e : Eq(Word, k2, k)). False) (h : Contains(V, cap, *m, k2)) (h2 : Contains(V, cap, (let c = *m; MapInsert(V, cap, &c, k, v); c), k2)) :
      Eq(V, (let c = *m; MapInsert(V, cap, &c, k, v); clone(*MapGet(V, cap, &c, k2, h2))), clone(*MapGet(V, cap, m, k2, h))) :=
  -- FIXED-END H6b
    ?

  -- FIXED-BEGIN H7a
  -- H7a: insert returns None exactly when k was absent.
  def InsertReturnsContains (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V) (hm : Inv(V, cap, *m)) :
      Eq(Bool, (let c = *m; IsSomeB(V, MapInsert(V, cap, &c, k, v))), ContainsOf(V, cap, *m, k)) :=
  -- FIXED-END H7a
    ?

  -- FIXED-BEGIN H7b
  -- H7b: when k was present, insert returns Some of the value bound to it.
  def InsertReturnsGet (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V) (hm : Inv(V, cap, *m))
      (h : Contains(V, cap, *m, k)) :
      Eq(Opt(V), (let c = *m; MapInsert(V, cap, &c, k, v)), Some(clone(*MapGet(V, cap, m, k, h)))) :=
  -- FIXED-END H7b
    ?

  -- FIXED-BEGIN H8
  -- H8: after remove(m, k), contains(m′, k) = false.
  def ContainsRemoveSame (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : Inv(V, cap, *m)) :
      Eq(Bool, (let c = *m; MapRemove(V, cap, &c, k); ContainsOf(V, cap, c, k)), false) :=
  -- FIXED-END H8
    ?

  -- FIXED-BEGIN H9a
  -- H9a: after remove(m, k), contains(m′, k′) = contains(m, k′) for k′ ≠ k.
  def ContainsRemoveOther (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (k2 : Word) (hm : Inv(V, cap, *m))
      (ne : Π(e : Eq(Word, k2, k)). False) :
      Eq(Bool, (let c = *m; MapRemove(V, cap, &c, k); ContainsOf(V, cap, c, k2)), ContainsOf(V, cap, *m, k2)) :=
  -- FIXED-END H9a
    ?

  -- FIXED-BEGIN H9b
  -- H9b: ... and the value read through get at k′ is the same, when k′ is present.
  def GetRemoveOther (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (k2 : Word) (hm : Inv(V, cap, *m))
      (ne : Π(e : Eq(Word, k2, k)). False) (h : Contains(V, cap, *m, k2)) (h2 : Contains(V, cap, (let c = *m; MapRemove(V, cap, &c, k); c), k2)) :
      Eq(V, (let c = *m; MapRemove(V, cap, &c, k); clone(*MapGet(V, cap, &c, k2, h2))), clone(*MapGet(V, cap, m, k2, h))) :=
  -- FIXED-END H9b
    ?

  -- FIXED-BEGIN H10a
  -- H10a: remove returns None exactly when k was absent.
  def RemoveReturnsContains (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : Inv(V, cap, *m)) :
      Eq(Bool, (let c = *m; IsSomeB(V, MapRemove(V, cap, &c, k))), ContainsOf(V, cap, *m, k)) :=
  -- FIXED-END H10a
    ?

  -- FIXED-BEGIN H10b
  -- H10b: when k was present, remove returns Some of the value bound to it.
  def RemoveReturnsGet (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : Inv(V, cap, *m))
      (h : Contains(V, cap, *m, k)) :
      Eq(Opt(V), (let c = *m; MapRemove(V, cap, &c, k)), Some(clone(*MapGet(V, cap, m, k, h)))) :=
  -- FIXED-END H10b
    ?

  -- FIXED-BEGIN H11
  -- H11: len(new(c)) = 0.
  def LenNew (V : Type) (cap : Word) (h : Lt(Zero, cap)) : Eq(Word, LenOf(V, cap, MapNew(V, cap, h)), Zero) :=
  -- FIXED-END H11
    ?

  -- FIXED-BEGIN H12
  -- H12: insert adds one to len if k was absent, and leaves it otherwise.
  def LenInsert (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V) (hm : Inv(V, cap, *m)) :
      Eq(Word, (let c = *m; MapInsert(V, cap, &c, k, v); LenOf(V, cap, c)), Grow(ContainsOf(V, cap, *m, k), LenOf(V, cap, *m))) :=
  -- FIXED-END H12
    ?

  -- FIXED-BEGIN H13
  -- H13: remove takes one from len if k was present, and leaves it otherwise.
  def LenRemove (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : Inv(V, cap, *m)) :
      Eq(Word, (let c = *m; MapRemove(V, cap, &c, k); LenOf(V, cap, c)), Shrink(ContainsOf(V, cap, *m, k), LenOf(V, cap, *m))) :=
  -- FIXED-END H13
    ?

  -- FIXED-BEGIN H14a
  -- H14a: writing `w` through get_mut(m, k) has the effect of insert(m, k, w) on every contains ...
  def GetMutContains (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (w : V) (k2 : Word) (hm : Inv(V, cap, *m))
      (hk : Contains(V, cap, *m, k)) :
      Eq(Bool, (let c = *m; let r = MapGetMut(V, cap, &c, k, hk); *r := w; ContainsOf(V, cap, c, k2)),
        (let c = *m; MapInsert(V, cap, &c, k, w); ContainsOf(V, cap, c, k2))) :=
  -- FIXED-END H14a
    ?

  -- FIXED-BEGIN H14b
  -- H14b: ... and on the value read through get.
  def GetMutGet (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (w : V) (k2 : Word) (hm : Inv(V, cap, *m))
      (hk : Contains(V, cap, *m, k)) (h1 : Contains(V, cap, (let c = *m; let r = MapGetMut(V, cap, &c, k, hk); *r := w; c), k2))
      (h2 : Contains(V, cap, (let c = *m; MapInsert(V, cap, &c, k, w); c), k2)) :
      Eq(V, (let c = *m; let r = MapGetMut(V, cap, &c, k, hk); *r := w; clone(*MapGet(V, cap, &c, k2, h1))),
        (let c = *m; MapInsert(V, cap, &c, k, w); clone(*MapGet(V, cap, &c, k2, h2)))) :=
  -- FIXED-END H14b
    ?

  -- FIXED-BEGIN H15
  -- H15: ... and on len.
  def GetMutLen (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (w : V) (hm : Inv(V, cap, *m))
      (hk : Contains(V, cap, *m, k)) :
      Eq(Word, (let c = *m; let r = MapGetMut(V, cap, &c, k, hk); *r := w; LenOf(V, cap, c)),
        (let c = *m; MapInsert(V, cap, &c, k, w); LenOf(V, cap, c))) :=
  -- FIXED-END H15
    ?

  -- FIXED-BEGIN H16
  -- H16: ... and preserves Inv.
  def GetMutInv (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (w : V) (hm : Inv(V, cap, *m))
      (hk : Contains(V, cap, *m, k)) :
      (let c = *m; let r = MapGetMut(V, cap, &c, k, hk); *r := w; Inv(V, cap, c)) :=
  -- FIXED-END H16
    ?

  -- FIXED-BEGIN H17a
  -- H17a: contains leaves the map unchanged (for every map, not only those with Inv).
  def ContainsUnchanged (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) :
      Eq(Map(V, cap), (let c = *m; MapContains(V, cap, &c, k); c), *m) :=
  -- FIXED-END H17a
    ?

  -- FIXED-BEGIN H17b
  -- H17b: get, whose borrow is only read and then ends, leaves the map unchanged.
  def GetUnchanged (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (h : Contains(V, cap, *m, k)) :
      Eq(Map(V, cap), (let c = *m; let r = MapGet(V, cap, &c, k, h); let x = clone(*r); c), *m) :=
  -- FIXED-END H17b
    ?

  -- FIXED-BEGIN H18
  -- H18: len leaves the map unchanged.
  def LenUnchanged (V : Type) (cap : Word) (m : &Map(V, cap)) : Eq(Map(V, cap), (let c = *m; MapLen(V, cap, &c); c), *m) :=
  -- FIXED-END H18
    ?
-- FIXED-BEGIN tests
}

/-! ## The tests (FIXED, SPEC §6)

Each test instantiates the value type as `Word`, starts from `MapNew(Word, cap, refl)`, runs a
sequence of operations on that one map, and records each operation's result and the length
after it in a `Trace`; the test is accepted when the trace is the expected one. An insert or a
remove records what it returned (`TOp`); a get of an absent key records `contains` (`THas`,
false), and a get of a present key the value read through `MapGet` (`TGet`), whose precondition
`refl` proves only if the key is present; a write through get_mut records only the length
(`TWrite`). The last test must be rejected: its expected result is wrong. -/

ochr HashMapTests uses HashMapSolution {
  inductive Trace := TEnd | TOp(res : Opt(Word), len : Word, rest : Trace) | THas(has : Bool, len : Word, rest : Trace)
    | TGet(val : Word, len : Word, rest : Trace) | TWrite(len : Word, rest : Trace)

  -- BEGIN GENERATED TESTS
  -- scripted: 51 ops on new(4)
  def Test_scripted : Id(Trace, (let m = MapNew(Word, W(4), refl); let r0 = MapContains(Word, W(4), &m, W(0)); let l0 = MapLen(Word, W(4), &m); let r1 = MapRemove(Word, W(4), &m, W(3)); let l1 = MapLen(Word, W(4), &m); let r2 = MapInsert(Word, W(4), &m, W(1), W(10)); let l2 = MapLen(Word, W(4), &m); let r3 = MapInsert(Word, W(4), &m, W(5), W(50)); let l3 = MapLen(Word, W(4), &m); let r4 = MapInsert(Word, W(4), &m, W(9), W(90)); let l4 = MapLen(Word, W(4), &m); let r5 = *MapGet(Word, W(4), &m, W(1), refl); let l5 = MapLen(Word, W(4), &m); let r6 = *MapGet(Word, W(4), &m, W(5), refl); let l6 = MapLen(Word, W(4), &m); let r7 = *MapGet(Word, W(4), &m, W(9), refl); let l7 = MapLen(Word, W(4), &m); let r8 = MapContains(Word, W(4), &m, W(13)); let l8 = MapLen(Word, W(4), &m); let r9 = MapContains(Word, W(4), &m, W(2)); let l9 = MapLen(Word, W(4), &m); let r10 = MapInsert(Word, W(4), &m, W(5), W(55)); let l10 = MapLen(Word, W(4), &m); let r11 = *MapGet(Word, W(4), &m, W(5), refl); let l11 = MapLen(Word, W(4), &m); let r12 = *MapGet(Word, W(4), &m, W(1), refl); let l12 = MapLen(Word, W(4), &m); let r13 = *MapGet(Word, W(4), &m, W(9), refl); let l13 = MapLen(Word, W(4), &m); let r14 = MapInsert(Word, W(4), &m, W(0), W(0)); let l14 = MapLen(Word, W(4), &m); let r15 = MapInsert(Word, W(4), &m, W(4), W(40)); let l15 = MapLen(Word, W(4), &m); let r16 = *MapGet(Word, W(4), &m, W(0), refl); let l16 = MapLen(Word, W(4), &m); let r17 = MapRemove(Word, W(4), &m, W(5)); let l17 = MapLen(Word, W(4), &m); let r18 = MapContains(Word, W(4), &m, W(5)); let l18 = MapLen(Word, W(4), &m); let r19 = *MapGet(Word, W(4), &m, W(1), refl); let l19 = MapLen(Word, W(4), &m); let r20 = *MapGet(Word, W(4), &m, W(9), refl); let l20 = MapLen(Word, W(4), &m); let r21 = MapRemove(Word, W(4), &m, W(5)); let l21 = MapLen(Word, W(4), &m); let r22 = MapRemove(Word, W(4), &m, W(13)); let l22 = MapLen(Word, W(4), &m); let r23 = MapRemove(Word, W(4), &m, W(1)); let l23 = MapLen(Word, W(4), &m); let r24 = MapRemove(Word, W(4), &m, W(9)); let l24 = MapLen(Word, W(4), &m); let r25 = MapContains(Word, W(4), &m, W(9)); let l25 = MapLen(Word, W(4), &m); *MapGetMut(Word, W(4), &m, W(4), refl) := W(44); let l26 = MapLen(Word, W(4), &m); let r27 = *MapGet(Word, W(4), &m, W(4), refl); let l27 = MapLen(Word, W(4), &m); let r28 = *MapGet(Word, W(4), &m, W(0), refl); let l28 = MapLen(Word, W(4), &m); *MapGetMut(Word, W(4), &m, W(0), refl) := W(7); let l29 = MapLen(Word, W(4), &m); let r30 = *MapGet(Word, W(4), &m, W(0), refl); let l30 = MapLen(Word, W(4), &m); let r31 = *MapGet(Word, W(4), &m, W(4), refl); let l31 = MapLen(Word, W(4), &m); let r32 = MapInsert(Word, W(4), &m, W(4), W(45)); let l32 = MapLen(Word, W(4), &m); let r33 = MapInsert(Word, W(4), &m, W(1), W(11)); let l33 = MapLen(Word, W(4), &m); let r34 = *MapGet(Word, W(4), &m, W(1), refl); let l34 = MapLen(Word, W(4), &m); let r35 = MapInsert(Word, W(4), &m, W(7), W(70)); let l35 = MapLen(Word, W(4), &m); let r36 = MapInsert(Word, W(4), &m, W(3), W(30)); let l36 = MapLen(Word, W(4), &m); let r37 = MapInsert(Word, W(4), &m, W(11), W(99)); let l37 = MapLen(Word, W(4), &m); *MapGetMut(Word, W(4), &m, W(3), refl) := W(33); let l38 = MapLen(Word, W(4), &m); let r39 = *MapGet(Word, W(4), &m, W(7), refl); let l39 = MapLen(Word, W(4), &m); let r40 = *MapGet(Word, W(4), &m, W(3), refl); let l40 = MapLen(Word, W(4), &m); let r41 = *MapGet(Word, W(4), &m, W(11), refl); let l41 = MapLen(Word, W(4), &m); let r42 = MapRemove(Word, W(4), &m, W(11)); let l42 = MapLen(Word, W(4), &m); let r43 = *MapGet(Word, W(4), &m, W(3), refl); let l43 = MapLen(Word, W(4), &m); let r44 = MapRemove(Word, W(4), &m, W(0)); let l44 = MapLen(Word, W(4), &m); let r45 = *MapGet(Word, W(4), &m, W(4), refl); let l45 = MapLen(Word, W(4), &m); let r46 = MapRemove(Word, W(4), &m, W(4)); let l46 = MapLen(Word, W(4), &m); let r47 = MapContains(Word, W(4), &m, W(0)); let l47 = MapLen(Word, W(4), &m); let r48 = MapContains(Word, W(4), &m, W(4)); let l48 = MapLen(Word, W(4), &m); let r49 = MapInsert(Word, W(4), &m, W(0), W(1)); let l49 = MapLen(Word, W(4), &m); let r50 = *MapGet(Word, W(4), &m, W(0), refl); let l50 = MapLen(Word, W(4), &m); THas(r0, l0, TOp(r1, l1, TOp(r2, l2, TOp(r3, l3, TOp(r4, l4, TGet(r5, l5, TGet(r6, l6, TGet(r7, l7, THas(r8, l8, THas(r9, l9, TOp(r10, l10, TGet(r11, l11, TGet(r12, l12, TGet(r13, l13, TOp(r14, l14, TOp(r15, l15, TGet(r16, l16, TOp(r17, l17, THas(r18, l18, TGet(r19, l19, TGet(r20, l20, TOp(r21, l21, TOp(r22, l22, TOp(r23, l23, TOp(r24, l24, THas(r25, l25, TWrite(l26, TGet(r27, l27, TGet(r28, l28, TWrite(l29, TGet(r30, l30, TGet(r31, l31, TOp(r32, l32, TOp(r33, l33, TGet(r34, l34, TOp(r35, l35, TOp(r36, l36, TOp(r37, l37, TWrite(l38, TGet(r39, l39, TGet(r40, l40, TGet(r41, l41, TOp(r42, l42, TGet(r43, l43, TOp(r44, l44, TGet(r45, l45, TOp(r46, l46, THas(r47, l47, THas(r48, l48, TOp(r49, l49, TGet(r50, l50, TEnd)))))))))))))))))))))))))))))))))))))))))))))))))))), THas(false, W(0), TOp(None[Word], W(0), TOp(None[Word], W(1), TOp(None[Word], W(2), TOp(None[Word], W(3), TGet(W(10), W(3), TGet(W(50), W(3), TGet(W(90), W(3), THas(false, W(3), THas(false, W(3), TOp(Some(W(50)), W(3), TGet(W(55), W(3), TGet(W(10), W(3), TGet(W(90), W(3), TOp(None[Word], W(4), TOp(None[Word], W(5), TGet(W(0), W(5), TOp(Some(W(55)), W(4), THas(false, W(4), TGet(W(10), W(4), TGet(W(90), W(4), TOp(None[Word], W(4), TOp(None[Word], W(4), TOp(Some(W(10)), W(3), TOp(Some(W(90)), W(2), THas(false, W(2), TWrite(W(2), TGet(W(44), W(2), TGet(W(0), W(2), TWrite(W(2), TGet(W(7), W(2), TGet(W(44), W(2), TOp(Some(W(44)), W(2), TOp(None[Word], W(3), TGet(W(11), W(3), TOp(None[Word], W(4), TOp(None[Word], W(5), TOp(None[Word], W(6), TWrite(W(6), TGet(W(70), W(6), TGet(W(33), W(6), TGet(W(99), W(6), TOp(Some(W(99)), W(5), TGet(W(33), W(5), TOp(Some(W(7)), W(4), TGet(W(45), W(4), TOp(Some(W(45)), W(3), THas(false, W(3), THas(false, W(3), TOp(None[Word], W(4), TGet(W(1), W(4), TEnd)))))))))))))))))))))))))))))))))))))))))))))))))))) := refl
  -- random-cap1: 50 ops on new(1)
  def Test_random_cap1 : Id(Trace, (let m = MapNew(Word, W(1), refl); let r0 = MapRemove(Word, W(1), &m, W(2)); let l0 = MapLen(Word, W(1), &m); let r1 = MapInsert(Word, W(1), &m, W(2), W(27)); let l1 = MapLen(Word, W(1), &m); let r2 = MapRemove(Word, W(1), &m, W(2)); let l2 = MapLen(Word, W(1), &m); let r3 = MapContains(Word, W(1), &m, W(1)); let l3 = MapLen(Word, W(1), &m); let r4 = MapContains(Word, W(1), &m, W(3)); let l4 = MapLen(Word, W(1), &m); let r5 = MapInsert(Word, W(1), &m, W(0), W(38)); let l5 = MapLen(Word, W(1), &m); let r6 = MapInsert(Word, W(1), &m, W(7), W(65)); let l6 = MapLen(Word, W(1), &m); let r7 = MapInsert(Word, W(1), &m, W(4), W(20)); let l7 = MapLen(Word, W(1), &m); let r8 = *MapGet(Word, W(1), &m, W(4), refl); let l8 = MapLen(Word, W(1), &m); *MapGetMut(Word, W(1), &m, W(7), refl) := W(79); let l9 = MapLen(Word, W(1), &m); let r10 = MapRemove(Word, W(1), &m, W(2)); let l10 = MapLen(Word, W(1), &m); let r11 = MapInsert(Word, W(1), &m, W(7), W(78)); let l11 = MapLen(Word, W(1), &m); let r12 = MapRemove(Word, W(1), &m, W(1)); let l12 = MapLen(Word, W(1), &m); let r13 = *MapGet(Word, W(1), &m, W(7), refl); let l13 = MapLen(Word, W(1), &m); let r14 = *MapGet(Word, W(1), &m, W(7), refl); let l14 = MapLen(Word, W(1), &m); *MapGetMut(Word, W(1), &m, W(0), refl) := W(41); let l15 = MapLen(Word, W(1), &m); let r16 = MapContains(Word, W(1), &m, W(5)); let l16 = MapLen(Word, W(1), &m); let r17 = MapInsert(Word, W(1), &m, W(0), W(8)); let l17 = MapLen(Word, W(1), &m); let r18 = MapRemove(Word, W(1), &m, W(6)); let l18 = MapLen(Word, W(1), &m); let r19 = MapInsert(Word, W(1), &m, W(2), W(8)); let l19 = MapLen(Word, W(1), &m); let r20 = *MapGet(Word, W(1), &m, W(4), refl); let l20 = MapLen(Word, W(1), &m); let r21 = *MapGet(Word, W(1), &m, W(7), refl); let l21 = MapLen(Word, W(1), &m); let r22 = MapRemove(Word, W(1), &m, W(6)); let l22 = MapLen(Word, W(1), &m); *MapGetMut(Word, W(1), &m, W(4), refl) := W(86); let l23 = MapLen(Word, W(1), &m); let r24 = MapContains(Word, W(1), &m, W(5)); let l24 = MapLen(Word, W(1), &m); let r25 = MapInsert(Word, W(1), &m, W(1), W(19)); let l25 = MapLen(Word, W(1), &m); let r26 = MapInsert(Word, W(1), &m, W(2), W(12)); let l26 = MapLen(Word, W(1), &m); let r27 = MapInsert(Word, W(1), &m, W(7), W(81)); let l27 = MapLen(Word, W(1), &m); let r28 = MapContains(Word, W(1), &m, W(5)); let l28 = MapLen(Word, W(1), &m); let r29 = MapRemove(Word, W(1), &m, W(6)); let l29 = MapLen(Word, W(1), &m); let r30 = *MapGet(Word, W(1), &m, W(2), refl); let l30 = MapLen(Word, W(1), &m); let r31 = *MapGet(Word, W(1), &m, W(0), refl); let l31 = MapLen(Word, W(1), &m); let r32 = MapInsert(Word, W(1), &m, W(4), W(0)); let l32 = MapLen(Word, W(1), &m); let r33 = MapInsert(Word, W(1), &m, W(7), W(77)); let l33 = MapLen(Word, W(1), &m); let r34 = MapInsert(Word, W(1), &m, W(5), W(85)); let l34 = MapLen(Word, W(1), &m); let r35 = MapInsert(Word, W(1), &m, W(0), W(0)); let l35 = MapLen(Word, W(1), &m); let r36 = MapInsert(Word, W(1), &m, W(3), W(71)); let l36 = MapLen(Word, W(1), &m); let r37 = MapInsert(Word, W(1), &m, W(0), W(37)); let l37 = MapLen(Word, W(1), &m); *MapGetMut(Word, W(1), &m, W(4), refl) := W(85); let l38 = MapLen(Word, W(1), &m); *MapGetMut(Word, W(1), &m, W(2), refl) := W(26); let l39 = MapLen(Word, W(1), &m); let r40 = MapInsert(Word, W(1), &m, W(3), W(5)); let l40 = MapLen(Word, W(1), &m); let r41 = MapInsert(Word, W(1), &m, W(0), W(37)); let l41 = MapLen(Word, W(1), &m); let r42 = MapRemove(Word, W(1), &m, W(6)); let l42 = MapLen(Word, W(1), &m); let r43 = MapInsert(Word, W(1), &m, W(0), W(71)); let l43 = MapLen(Word, W(1), &m); let r44 = MapInsert(Word, W(1), &m, W(5), W(9)); let l44 = MapLen(Word, W(1), &m); let r45 = MapInsert(Word, W(1), &m, W(2), W(42)); let l45 = MapLen(Word, W(1), &m); let r46 = MapInsert(Word, W(1), &m, W(0), W(11)); let l46 = MapLen(Word, W(1), &m); let r47 = MapInsert(Word, W(1), &m, W(1), W(25)); let l47 = MapLen(Word, W(1), &m); let r48 = *MapGet(Word, W(1), &m, W(0), refl); let l48 = MapLen(Word, W(1), &m); *MapGetMut(Word, W(1), &m, W(0), refl) := W(84); let l49 = MapLen(Word, W(1), &m); TOp(r0, l0, TOp(r1, l1, TOp(r2, l2, THas(r3, l3, THas(r4, l4, TOp(r5, l5, TOp(r6, l6, TOp(r7, l7, TGet(r8, l8, TWrite(l9, TOp(r10, l10, TOp(r11, l11, TOp(r12, l12, TGet(r13, l13, TGet(r14, l14, TWrite(l15, THas(r16, l16, TOp(r17, l17, TOp(r18, l18, TOp(r19, l19, TGet(r20, l20, TGet(r21, l21, TOp(r22, l22, TWrite(l23, THas(r24, l24, TOp(r25, l25, TOp(r26, l26, TOp(r27, l27, THas(r28, l28, TOp(r29, l29, TGet(r30, l30, TGet(r31, l31, TOp(r32, l32, TOp(r33, l33, TOp(r34, l34, TOp(r35, l35, TOp(r36, l36, TOp(r37, l37, TWrite(l38, TWrite(l39, TOp(r40, l40, TOp(r41, l41, TOp(r42, l42, TOp(r43, l43, TOp(r44, l44, TOp(r45, l45, TOp(r46, l46, TOp(r47, l47, TGet(r48, l48, TWrite(l49, TEnd))))))))))))))))))))))))))))))))))))))))))))))))))), TOp(None[Word], W(0), TOp(None[Word], W(1), TOp(Some(W(27)), W(0), THas(false, W(0), THas(false, W(0), TOp(None[Word], W(1), TOp(None[Word], W(2), TOp(None[Word], W(3), TGet(W(20), W(3), TWrite(W(3), TOp(None[Word], W(3), TOp(Some(W(79)), W(3), TOp(None[Word], W(3), TGet(W(78), W(3), TGet(W(78), W(3), TWrite(W(3), THas(false, W(3), TOp(Some(W(41)), W(3), TOp(None[Word], W(3), TOp(None[Word], W(4), TGet(W(20), W(4), TGet(W(78), W(4), TOp(None[Word], W(4), TWrite(W(4), THas(false, W(4), TOp(None[Word], W(5), TOp(Some(W(8)), W(5), TOp(Some(W(78)), W(5), THas(false, W(5), TOp(None[Word], W(5), TGet(W(12), W(5), TGet(W(8), W(5), TOp(Some(W(86)), W(5), TOp(Some(W(81)), W(5), TOp(None[Word], W(6), TOp(Some(W(8)), W(6), TOp(None[Word], W(7), TOp(Some(W(0)), W(7), TWrite(W(7), TWrite(W(7), TOp(Some(W(71)), W(7), TOp(Some(W(37)), W(7), TOp(None[Word], W(7), TOp(Some(W(37)), W(7), TOp(Some(W(85)), W(7), TOp(Some(W(26)), W(7), TOp(Some(W(71)), W(7), TOp(Some(W(19)), W(7), TGet(W(11), W(7), TWrite(W(7), TEnd))))))))))))))))))))))))))))))))))))))))))))))))))) := refl
  -- random-cap3: 50 ops on new(3)
  def Test_random_cap3 : Id(Trace, (let m = MapNew(Word, W(3), refl); let r0 = MapInsert(Word, W(3), &m, W(6), W(48)); let l0 = MapLen(Word, W(3), &m); let r1 = MapInsert(Word, W(3), &m, W(2), W(20)); let l1 = MapLen(Word, W(3), &m); let r2 = MapInsert(Word, W(3), &m, W(3), W(70)); let l2 = MapLen(Word, W(3), &m); let r3 = MapRemove(Word, W(3), &m, W(11)); let l3 = MapLen(Word, W(3), &m); let r4 = MapInsert(Word, W(3), &m, W(11), W(55)); let l4 = MapLen(Word, W(3), &m); let r5 = MapInsert(Word, W(3), &m, W(5), W(53)); let l5 = MapLen(Word, W(3), &m); *MapGetMut(Word, W(3), &m, W(6), refl) := W(36); let l6 = MapLen(Word, W(3), &m); let r7 = MapInsert(Word, W(3), &m, W(5), W(2)); let l7 = MapLen(Word, W(3), &m); let r8 = MapContains(Word, W(3), &m, W(10)); let l8 = MapLen(Word, W(3), &m); let r9 = MapRemove(Word, W(3), &m, W(5)); let l9 = MapLen(Word, W(3), &m); let r10 = MapInsert(Word, W(3), &m, W(1), W(97)); let l10 = MapLen(Word, W(3), &m); let r11 = MapInsert(Word, W(3), &m, W(0), W(57)); let l11 = MapLen(Word, W(3), &m); let r12 = MapInsert(Word, W(3), &m, W(6), W(18)); let l12 = MapLen(Word, W(3), &m); let r13 = *MapGet(Word, W(3), &m, W(3), refl); let l13 = MapLen(Word, W(3), &m); let r14 = MapInsert(Word, W(3), &m, W(2), W(42)); let l14 = MapLen(Word, W(3), &m); let r15 = MapRemove(Word, W(3), &m, W(0)); let l15 = MapLen(Word, W(3), &m); let r16 = MapRemove(Word, W(3), &m, W(0)); let l16 = MapLen(Word, W(3), &m); let r17 = MapInsert(Word, W(3), &m, W(3), W(18)); let l17 = MapLen(Word, W(3), &m); let r18 = MapInsert(Word, W(3), &m, W(7), W(12)); let l18 = MapLen(Word, W(3), &m); *MapGetMut(Word, W(3), &m, W(6), refl) := W(40); let l19 = MapLen(Word, W(3), &m); *MapGetMut(Word, W(3), &m, W(2), refl) := W(53); let l20 = MapLen(Word, W(3), &m); *MapGetMut(Word, W(3), &m, W(3), refl) := W(31); let l21 = MapLen(Word, W(3), &m); let r22 = *MapGet(Word, W(3), &m, W(7), refl); let l22 = MapLen(Word, W(3), &m); let r23 = MapInsert(Word, W(3), &m, W(9), W(60)); let l23 = MapLen(Word, W(3), &m); let r24 = MapInsert(Word, W(3), &m, W(8), W(83)); let l24 = MapLen(Word, W(3), &m); let r25 = MapInsert(Word, W(3), &m, W(7), W(66)); let l25 = MapLen(Word, W(3), &m); let r26 = *MapGet(Word, W(3), &m, W(11), refl); let l26 = MapLen(Word, W(3), &m); let r27 = MapRemove(Word, W(3), &m, W(8)); let l27 = MapLen(Word, W(3), &m); let r28 = MapInsert(Word, W(3), &m, W(11), W(32)); let l28 = MapLen(Word, W(3), &m); let r29 = MapInsert(Word, W(3), &m, W(8), W(77)); let l29 = MapLen(Word, W(3), &m); let r30 = MapInsert(Word, W(3), &m, W(10), W(73)); let l30 = MapLen(Word, W(3), &m); let r31 = MapRemove(Word, W(3), &m, W(0)); let l31 = MapLen(Word, W(3), &m); let r32 = *MapGet(Word, W(3), &m, W(11), refl); let l32 = MapLen(Word, W(3), &m); let r33 = *MapGet(Word, W(3), &m, W(7), refl); let l33 = MapLen(Word, W(3), &m); let r34 = MapContains(Word, W(3), &m, W(4)); let l34 = MapLen(Word, W(3), &m); let r35 = *MapGet(Word, W(3), &m, W(2), refl); let l35 = MapLen(Word, W(3), &m); let r36 = MapInsert(Word, W(3), &m, W(2), W(53)); let l36 = MapLen(Word, W(3), &m); let r37 = *MapGet(Word, W(3), &m, W(2), refl); let l37 = MapLen(Word, W(3), &m); let r38 = MapInsert(Word, W(3), &m, W(4), W(30)); let l38 = MapLen(Word, W(3), &m); let r39 = MapRemove(Word, W(3), &m, W(11)); let l39 = MapLen(Word, W(3), &m); let r40 = MapRemove(Word, W(3), &m, W(0)); let l40 = MapLen(Word, W(3), &m); let r41 = MapInsert(Word, W(3), &m, W(0), W(15)); let l41 = MapLen(Word, W(3), &m); let r42 = MapInsert(Word, W(3), &m, W(1), W(20)); let l42 = MapLen(Word, W(3), &m); let r43 = MapInsert(Word, W(3), &m, W(10), W(20)); let l43 = MapLen(Word, W(3), &m); let r44 = MapInsert(Word, W(3), &m, W(5), W(90)); let l44 = MapLen(Word, W(3), &m); let r45 = MapRemove(Word, W(3), &m, W(7)); let l45 = MapLen(Word, W(3), &m); *MapGetMut(Word, W(3), &m, W(4), refl) := W(40); let l46 = MapLen(Word, W(3), &m); let r47 = MapContains(Word, W(3), &m, W(11)); let l47 = MapLen(Word, W(3), &m); let r48 = MapInsert(Word, W(3), &m, W(3), W(75)); let l48 = MapLen(Word, W(3), &m); let r49 = MapInsert(Word, W(3), &m, W(0), W(29)); let l49 = MapLen(Word, W(3), &m); TOp(r0, l0, TOp(r1, l1, TOp(r2, l2, TOp(r3, l3, TOp(r4, l4, TOp(r5, l5, TWrite(l6, TOp(r7, l7, THas(r8, l8, TOp(r9, l9, TOp(r10, l10, TOp(r11, l11, TOp(r12, l12, TGet(r13, l13, TOp(r14, l14, TOp(r15, l15, TOp(r16, l16, TOp(r17, l17, TOp(r18, l18, TWrite(l19, TWrite(l20, TWrite(l21, TGet(r22, l22, TOp(r23, l23, TOp(r24, l24, TOp(r25, l25, TGet(r26, l26, TOp(r27, l27, TOp(r28, l28, TOp(r29, l29, TOp(r30, l30, TOp(r31, l31, TGet(r32, l32, TGet(r33, l33, THas(r34, l34, TGet(r35, l35, TOp(r36, l36, TGet(r37, l37, TOp(r38, l38, TOp(r39, l39, TOp(r40, l40, TOp(r41, l41, TOp(r42, l42, TOp(r43, l43, TOp(r44, l44, TOp(r45, l45, TWrite(l46, THas(r47, l47, TOp(r48, l48, TOp(r49, l49, TEnd))))))))))))))))))))))))))))))))))))))))))))))))))), TOp(None[Word], W(1), TOp(None[Word], W(2), TOp(None[Word], W(3), TOp(None[Word], W(3), TOp(None[Word], W(4), TOp(None[Word], W(5), TWrite(W(5), TOp(Some(W(53)), W(5), THas(false, W(5), TOp(Some(W(2)), W(4), TOp(None[Word], W(5), TOp(None[Word], W(6), TOp(Some(W(36)), W(6), TGet(W(70), W(6), TOp(Some(W(20)), W(6), TOp(Some(W(57)), W(5), TOp(None[Word], W(5), TOp(Some(W(70)), W(5), TOp(None[Word], W(6), TWrite(W(6), TWrite(W(6), TWrite(W(6), TGet(W(12), W(6), TOp(None[Word], W(7), TOp(None[Word], W(8), TOp(Some(W(12)), W(8), TGet(W(55), W(8), TOp(Some(W(83)), W(7), TOp(Some(W(55)), W(7), TOp(None[Word], W(8), TOp(None[Word], W(9), TOp(None[Word], W(9), TGet(W(32), W(9), TGet(W(66), W(9), THas(false, W(9), TGet(W(53), W(9), TOp(Some(W(53)), W(9), TGet(W(53), W(9), TOp(None[Word], W(10), TOp(Some(W(32)), W(9), TOp(None[Word], W(9), TOp(None[Word], W(10), TOp(Some(W(97)), W(10), TOp(Some(W(73)), W(10), TOp(None[Word], W(11), TOp(Some(W(66)), W(10), TWrite(W(10), THas(false, W(10), TOp(Some(W(31)), W(10), TOp(Some(W(15)), W(10), TEnd))))))))))))))))))))))))))))))))))))))))))))))))))) := refl
  -- random-cap4: 50 ops on new(4)
  def Test_random_cap4 : Id(Trace, (let m = MapNew(Word, W(4), refl); let r0 = MapInsert(Word, W(4), &m, W(3), W(6)); let l0 = MapLen(Word, W(4), &m); *MapGetMut(Word, W(4), &m, W(3), refl) := W(19); let l1 = MapLen(Word, W(4), &m); let r2 = MapInsert(Word, W(4), &m, W(1), W(39)); let l2 = MapLen(Word, W(4), &m); *MapGetMut(Word, W(4), &m, W(1), refl) := W(3); let l3 = MapLen(Word, W(4), &m); *MapGetMut(Word, W(4), &m, W(3), refl) := W(73); let l4 = MapLen(Word, W(4), &m); let r5 = *MapGet(Word, W(4), &m, W(1), refl); let l5 = MapLen(Word, W(4), &m); let r6 = MapInsert(Word, W(4), &m, W(12), W(39)); let l6 = MapLen(Word, W(4), &m); let r7 = MapInsert(Word, W(4), &m, W(3), W(19)); let l7 = MapLen(Word, W(4), &m); let r8 = MapInsert(Word, W(4), &m, W(7), W(84)); let l8 = MapLen(Word, W(4), &m); let r9 = *MapGet(Word, W(4), &m, W(12), refl); let l9 = MapLen(Word, W(4), &m); let r10 = MapRemove(Word, W(4), &m, W(2)); let l10 = MapLen(Word, W(4), &m); let r11 = MapInsert(Word, W(4), &m, W(0), W(26)); let l11 = MapLen(Word, W(4), &m); let r12 = MapInsert(Word, W(4), &m, W(2), W(10)); let l12 = MapLen(Word, W(4), &m); let r13 = MapInsert(Word, W(4), &m, W(5), W(40)); let l13 = MapLen(Word, W(4), &m); *MapGetMut(Word, W(4), &m, W(5), refl) := W(86); let l14 = MapLen(Word, W(4), &m); let r15 = MapContains(Word, W(4), &m, W(4)); let l15 = MapLen(Word, W(4), &m); let r16 = *MapGet(Word, W(4), &m, W(12), refl); let l16 = MapLen(Word, W(4), &m); let r17 = MapInsert(Word, W(4), &m, W(1), W(59)); let l17 = MapLen(Word, W(4), &m); let r18 = MapContains(Word, W(4), &m, W(4)); let l18 = MapLen(Word, W(4), &m); let r19 = MapContains(Word, W(4), &m, W(8)); let l19 = MapLen(Word, W(4), &m); let r20 = MapRemove(Word, W(4), &m, W(15)); let l20 = MapLen(Word, W(4), &m); let r21 = MapInsert(Word, W(4), &m, W(15), W(68)); let l21 = MapLen(Word, W(4), &m); let r22 = MapInsert(Word, W(4), &m, W(11), W(80)); let l22 = MapLen(Word, W(4), &m); let r23 = MapContains(Word, W(4), &m, W(10)); let l23 = MapLen(Word, W(4), &m); let r24 = MapRemove(Word, W(4), &m, W(4)); let l24 = MapLen(Word, W(4), &m); let r25 = MapInsert(Word, W(4), &m, W(13), W(20)); let l25 = MapLen(Word, W(4), &m); let r26 = MapInsert(Word, W(4), &m, W(9), W(7)); let l26 = MapLen(Word, W(4), &m); *MapGetMut(Word, W(4), &m, W(5), refl) := W(30); let l27 = MapLen(Word, W(4), &m); let r28 = *MapGet(Word, W(4), &m, W(1), refl); let l28 = MapLen(Word, W(4), &m); let r29 = MapRemove(Word, W(4), &m, W(4)); let l29 = MapLen(Word, W(4), &m); let r30 = MapRemove(Word, W(4), &m, W(10)); let l30 = MapLen(Word, W(4), &m); let r31 = *MapGet(Word, W(4), &m, W(13), refl); let l31 = MapLen(Word, W(4), &m); let r32 = MapRemove(Word, W(4), &m, W(9)); let l32 = MapLen(Word, W(4), &m); *MapGetMut(Word, W(4), &m, W(7), refl) := W(75); let l33 = MapLen(Word, W(4), &m); let r34 = MapContains(Word, W(4), &m, W(8)); let l34 = MapLen(Word, W(4), &m); let r35 = MapRemove(Word, W(4), &m, W(11)); let l35 = MapLen(Word, W(4), &m); *MapGetMut(Word, W(4), &m, W(1), refl) := W(32); let l36 = MapLen(Word, W(4), &m); let r37 = MapContains(Word, W(4), &m, W(6)); let l37 = MapLen(Word, W(4), &m); let r38 = MapContains(Word, W(4), &m, W(11)); let l38 = MapLen(Word, W(4), &m); let r39 = MapContains(Word, W(4), &m, W(4)); let l39 = MapLen(Word, W(4), &m); let r40 = MapRemove(Word, W(4), &m, W(6)); let l40 = MapLen(Word, W(4), &m); let r41 = MapInsert(Word, W(4), &m, W(8), W(82)); let l41 = MapLen(Word, W(4), &m); let r42 = MapInsert(Word, W(4), &m, W(3), W(86)); let l42 = MapLen(Word, W(4), &m); let r43 = *MapGet(Word, W(4), &m, W(12), refl); let l43 = MapLen(Word, W(4), &m); *MapGetMut(Word, W(4), &m, W(7), refl) := W(17); let l44 = MapLen(Word, W(4), &m); let r45 = MapContains(Word, W(4), &m, W(10)); let l45 = MapLen(Word, W(4), &m); let r46 = *MapGet(Word, W(4), &m, W(12), refl); let l46 = MapLen(Word, W(4), &m); let r47 = MapRemove(Word, W(4), &m, W(4)); let l47 = MapLen(Word, W(4), &m); let r48 = MapInsert(Word, W(4), &m, W(7), W(79)); let l48 = MapLen(Word, W(4), &m); let r49 = MapRemove(Word, W(4), &m, W(2)); let l49 = MapLen(Word, W(4), &m); TOp(r0, l0, TWrite(l1, TOp(r2, l2, TWrite(l3, TWrite(l4, TGet(r5, l5, TOp(r6, l6, TOp(r7, l7, TOp(r8, l8, TGet(r9, l9, TOp(r10, l10, TOp(r11, l11, TOp(r12, l12, TOp(r13, l13, TWrite(l14, THas(r15, l15, TGet(r16, l16, TOp(r17, l17, THas(r18, l18, THas(r19, l19, TOp(r20, l20, TOp(r21, l21, TOp(r22, l22, THas(r23, l23, TOp(r24, l24, TOp(r25, l25, TOp(r26, l26, TWrite(l27, TGet(r28, l28, TOp(r29, l29, TOp(r30, l30, TGet(r31, l31, TOp(r32, l32, TWrite(l33, THas(r34, l34, TOp(r35, l35, TWrite(l36, THas(r37, l37, THas(r38, l38, THas(r39, l39, TOp(r40, l40, TOp(r41, l41, TOp(r42, l42, TGet(r43, l43, TWrite(l44, THas(r45, l45, TGet(r46, l46, TOp(r47, l47, TOp(r48, l48, TOp(r49, l49, TEnd))))))))))))))))))))))))))))))))))))))))))))))))))), TOp(None[Word], W(1), TWrite(W(1), TOp(None[Word], W(2), TWrite(W(2), TWrite(W(2), TGet(W(3), W(2), TOp(None[Word], W(3), TOp(Some(W(73)), W(3), TOp(None[Word], W(4), TGet(W(39), W(4), TOp(None[Word], W(4), TOp(None[Word], W(5), TOp(None[Word], W(6), TOp(None[Word], W(7), TWrite(W(7), THas(false, W(7), TGet(W(39), W(7), TOp(Some(W(3)), W(7), THas(false, W(7), THas(false, W(7), TOp(None[Word], W(7), TOp(None[Word], W(8), TOp(None[Word], W(9), THas(false, W(9), TOp(None[Word], W(9), TOp(None[Word], W(10), TOp(None[Word], W(11), TWrite(W(11), TGet(W(59), W(11), TOp(None[Word], W(11), TOp(None[Word], W(11), TGet(W(20), W(11), TOp(Some(W(7)), W(10), TWrite(W(10), THas(false, W(10), TOp(Some(W(80)), W(9), TWrite(W(9), THas(false, W(9), THas(false, W(9), THas(false, W(9), TOp(None[Word], W(9), TOp(None[Word], W(10), TOp(Some(W(19)), W(10), TGet(W(39), W(10), TWrite(W(10), THas(false, W(10), TGet(W(39), W(10), TOp(None[Word], W(10), TOp(Some(W(17)), W(10), TOp(Some(W(10)), W(9), TEnd))))))))))))))))))))))))))))))))))))))))))))))))))) := refl
  -- random-cap7: 50 ops on new(7)
  def Test_random_cap7 : Id(Trace, (let m = MapNew(Word, W(7), refl); let r0 = MapInsert(Word, W(7), &m, W(10), W(82)); let l0 = MapLen(Word, W(7), &m); let r1 = MapInsert(Word, W(7), &m, W(15), W(33)); let l1 = MapLen(Word, W(7), &m); let r2 = MapInsert(Word, W(7), &m, W(0), W(14)); let l2 = MapLen(Word, W(7), &m); let r3 = MapInsert(Word, W(7), &m, W(8), W(60)); let l3 = MapLen(Word, W(7), &m); let r4 = MapContains(Word, W(7), &m, W(4)); let l4 = MapLen(Word, W(7), &m); *MapGetMut(Word, W(7), &m, W(0), refl) := W(39); let l5 = MapLen(Word, W(7), &m); let r6 = MapContains(Word, W(7), &m, W(3)); let l6 = MapLen(Word, W(7), &m); let r7 = MapInsert(Word, W(7), &m, W(19), W(57)); let l7 = MapLen(Word, W(7), &m); let r8 = MapRemove(Word, W(7), &m, W(15)); let l8 = MapLen(Word, W(7), &m); let r9 = MapInsert(Word, W(7), &m, W(13), W(82)); let l9 = MapLen(Word, W(7), &m); let r10 = MapRemove(Word, W(7), &m, W(18)); let l10 = MapLen(Word, W(7), &m); let r11 = MapRemove(Word, W(7), &m, W(0)); let l11 = MapLen(Word, W(7), &m); let r12 = *MapGet(Word, W(7), &m, W(13), refl); let l12 = MapLen(Word, W(7), &m); let r13 = MapInsert(Word, W(7), &m, W(5), W(37)); let l13 = MapLen(Word, W(7), &m); let r14 = MapInsert(Word, W(7), &m, W(7), W(48)); let l14 = MapLen(Word, W(7), &m); let r15 = MapRemove(Word, W(7), &m, W(7)); let l15 = MapLen(Word, W(7), &m); let r16 = MapInsert(Word, W(7), &m, W(23), W(31)); let l16 = MapLen(Word, W(7), &m); *MapGetMut(Word, W(7), &m, W(19), refl) := W(27); let l17 = MapLen(Word, W(7), &m); let r18 = MapContains(Word, W(7), &m, W(1)); let l18 = MapLen(Word, W(7), &m); let r19 = MapRemove(Word, W(7), &m, W(3)); let l19 = MapLen(Word, W(7), &m); let r20 = MapInsert(Word, W(7), &m, W(11), W(18)); let l20 = MapLen(Word, W(7), &m); let r21 = MapInsert(Word, W(7), &m, W(5), W(67)); let l21 = MapLen(Word, W(7), &m); let r22 = MapInsert(Word, W(7), &m, W(20), W(96)); let l22 = MapLen(Word, W(7), &m); let r23 = MapContains(Word, W(7), &m, W(12)); let l23 = MapLen(Word, W(7), &m); let r24 = MapContains(Word, W(7), &m, W(15)); let l24 = MapLen(Word, W(7), &m); let r25 = *MapGet(Word, W(7), &m, W(5), refl); let l25 = MapLen(Word, W(7), &m); let r26 = MapRemove(Word, W(7), &m, W(9)); let l26 = MapLen(Word, W(7), &m); let r27 = MapInsert(Word, W(7), &m, W(13), W(87)); let l27 = MapLen(Word, W(7), &m); let r28 = *MapGet(Word, W(7), &m, W(19), refl); let l28 = MapLen(Word, W(7), &m); *MapGetMut(Word, W(7), &m, W(11), refl) := W(84); let l29 = MapLen(Word, W(7), &m); let r30 = MapContains(Word, W(7), &m, W(16)); let l30 = MapLen(Word, W(7), &m); let r31 = MapInsert(Word, W(7), &m, W(3), W(78)); let l31 = MapLen(Word, W(7), &m); let r32 = MapRemove(Word, W(7), &m, W(4)); let l32 = MapLen(Word, W(7), &m); *MapGetMut(Word, W(7), &m, W(20), refl) := W(89); let l33 = MapLen(Word, W(7), &m); let r34 = MapContains(Word, W(7), &m, W(0)); let l34 = MapLen(Word, W(7), &m); let r35 = MapInsert(Word, W(7), &m, W(23), W(28)); let l35 = MapLen(Word, W(7), &m); let r36 = MapInsert(Word, W(7), &m, W(20), W(74)); let l36 = MapLen(Word, W(7), &m); let r37 = MapRemove(Word, W(7), &m, W(5)); let l37 = MapLen(Word, W(7), &m); let r38 = MapInsert(Word, W(7), &m, W(19), W(32)); let l38 = MapLen(Word, W(7), &m); let r39 = MapRemove(Word, W(7), &m, W(9)); let l39 = MapLen(Word, W(7), &m); let r40 = MapInsert(Word, W(7), &m, W(11), W(98)); let l40 = MapLen(Word, W(7), &m); let r41 = MapRemove(Word, W(7), &m, W(13)); let l41 = MapLen(Word, W(7), &m); let r42 = MapRemove(Word, W(7), &m, W(11)); let l42 = MapLen(Word, W(7), &m); let r43 = MapContains(Word, W(7), &m, W(15)); let l43 = MapLen(Word, W(7), &m); let r44 = MapContains(Word, W(7), &m, W(11)); let l44 = MapLen(Word, W(7), &m); *MapGetMut(Word, W(7), &m, W(3), refl) := W(16); let l45 = MapLen(Word, W(7), &m); let r46 = MapContains(Word, W(7), &m, W(13)); let l46 = MapLen(Word, W(7), &m); *MapGetMut(Word, W(7), &m, W(19), refl) := W(17); let l47 = MapLen(Word, W(7), &m); let r48 = MapContains(Word, W(7), &m, W(5)); let l48 = MapLen(Word, W(7), &m); let r49 = MapRemove(Word, W(7), &m, W(14)); let l49 = MapLen(Word, W(7), &m); TOp(r0, l0, TOp(r1, l1, TOp(r2, l2, TOp(r3, l3, THas(r4, l4, TWrite(l5, THas(r6, l6, TOp(r7, l7, TOp(r8, l8, TOp(r9, l9, TOp(r10, l10, TOp(r11, l11, TGet(r12, l12, TOp(r13, l13, TOp(r14, l14, TOp(r15, l15, TOp(r16, l16, TWrite(l17, THas(r18, l18, TOp(r19, l19, TOp(r20, l20, TOp(r21, l21, TOp(r22, l22, THas(r23, l23, THas(r24, l24, TGet(r25, l25, TOp(r26, l26, TOp(r27, l27, TGet(r28, l28, TWrite(l29, THas(r30, l30, TOp(r31, l31, TOp(r32, l32, TWrite(l33, THas(r34, l34, TOp(r35, l35, TOp(r36, l36, TOp(r37, l37, TOp(r38, l38, TOp(r39, l39, TOp(r40, l40, TOp(r41, l41, TOp(r42, l42, THas(r43, l43, THas(r44, l44, TWrite(l45, THas(r46, l46, TWrite(l47, THas(r48, l48, TOp(r49, l49, TEnd))))))))))))))))))))))))))))))))))))))))))))))))))), TOp(None[Word], W(1), TOp(None[Word], W(2), TOp(None[Word], W(3), TOp(None[Word], W(4), THas(false, W(4), TWrite(W(4), THas(false, W(4), TOp(None[Word], W(5), TOp(Some(W(33)), W(4), TOp(None[Word], W(5), TOp(None[Word], W(5), TOp(Some(W(39)), W(4), TGet(W(82), W(4), TOp(None[Word], W(5), TOp(None[Word], W(6), TOp(Some(W(48)), W(5), TOp(None[Word], W(6), TWrite(W(6), THas(false, W(6), TOp(None[Word], W(6), TOp(None[Word], W(7), TOp(Some(W(37)), W(7), TOp(None[Word], W(8), THas(false, W(8), THas(false, W(8), TGet(W(67), W(8), TOp(None[Word], W(8), TOp(Some(W(82)), W(8), TGet(W(27), W(8), TWrite(W(8), THas(false, W(8), TOp(None[Word], W(9), TOp(None[Word], W(9), TWrite(W(9), THas(false, W(9), TOp(Some(W(31)), W(9), TOp(Some(W(89)), W(9), TOp(Some(W(67)), W(8), TOp(Some(W(27)), W(8), TOp(None[Word], W(8), TOp(Some(W(84)), W(8), TOp(Some(W(87)), W(7), TOp(Some(W(98)), W(6), THas(false, W(6), THas(false, W(6), TWrite(W(6), THas(false, W(6), TWrite(W(6), THas(false, W(6), TOp(None[Word], W(6), TEnd))))))))))))))))))))))))))))))))))))))))))))))))))) := refl
  -- must be rejected: a fresh map's first insert returns None, not Some
  reject def TestReject_insert : Id(Trace, (let m = MapNew(Word, W(4), refl); let r0 = MapInsert(Word, W(4), &m, W(1), W(10)); let l0 = MapLen(Word, W(4), &m); TOp(r0, l0, TEnd)), TOp(Some(W(11)), W(1), TEnd)) := refl
  -- END GENERATED TESTS
}
-- FIXED-END tests
