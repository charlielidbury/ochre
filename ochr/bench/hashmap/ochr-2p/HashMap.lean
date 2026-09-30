-- FIXED-BEGIN header
import Ochr.Examples.«16Arrays»

/-! # Verified in-place hash map, two programs (condition `ochr-2p`)

Read `ASSIGNMENT.md` first. Replace every hole `?` with a definition or a proof, and add any
helper definitions and lemmas you need to the blocks `HashMapModel` and
`HashMapSolution`, between their FIXED regions. Everything inside a FIXED region must stay exactly as it is.

Check your work with `lake exe check` (the checker's verdict on every declaration) and
`./grade.sh` (the grade). -/

/-! ## The representation and what is provided (FIXED, SPEC §1–§2)

The arrays library is `ArrayLemmas` (`checker/Ochr/Examples/16Arrays.lean`). -/

ochr HashMapSpec uses ArrayLemmas {
  -- Opt(𝕎): the result of a lookup.
  inductive Opt := None | Some(val : Word)

  -- `IsSome(o)` is o ≠ None.
  def IsSome (o : Opt) : Prop := (
    match o {
      None => False,
      Some(_) => ⊤,
    }
  )

  -- len(m) + 1 if the key was absent (`g` = get(m, k) = None), and len(m) otherwise: H12.
  def Grow (g : Opt) (l : Word) : Word := (
    match g {
      None => Succ(l),
      Some(_) => l,
    }
  )

  -- len(m) − 1 if the key was present, and len(m) otherwise: H13.
  def Shrink (g : Opt) (l : Word) : Word := (
    match g {
      None => l,
      Some(_) => Sub(l, Succ(Zero)),
    }
  )

  -- A bucket: a singly linked list of entries, each node owning the next.
  inductive Bucket := BNil | BCons(key : Word, value : Word, next : Bucket)

  -- A map of capacity `cap`: an array of `cap` buckets and the length. The capacity is part
  -- of the type, `Map(cap)`, and never changes. (`MapOf` takes the array's model type as a
  -- parameter, because a field cannot yet be written `Array(Bucket, cap)`; `Map(cap)` fills
  -- it in, so `slots` is an `Array(Bucket, cap)`.)
  inductive MapOf (R : Type) := MkMap(slots : ArrayOf(R), len : Word)

  def Map (cap : Word) : Type := MapOf(Cells(Bucket, cap))

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
  def IdxExample : Eq Word (Idx(W(4), W(13))) (W(1)) := refl

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
  def EqDec (a : Word) (b : Word) : Dec(Eq Word a b, Π(e : Eq Word a b). False) by a := (
    match a {
      Zero => match b {
        Zero => Yes(refl),
        Succ(b') => No(λ(e : Eq Word Zero (Succ(b'))) : False => match e {}),
      },
      Succ(a') => match b {
        Zero => No(λ(e : Eq Word (Succ(a')) Zero) : False => match e {}),
        Succ(b') => EqDec(a', b'),
      },
    }
  )

  -- [native] A borrow of bucket `i`: the arrays library's `GetMut`, at the element type
  -- `Bucket` (the library's own `GetMut` is written for `Word` elements). It is the only way
  -- to reach a bucket in place.
  def SlotMut (cap : Word) (s : &Slice(Bucket, cap)) (i : Word) (h : Lt(i, cap)) : &Bucket by i := (
    match cap {
      Zero => match h {},
      Succ(m) => match *s {
        MkSlice(c) => match c {
          MkC(x, t) => match i {
            Zero => &x,
            Succ(i') => SlotMut(m, &t, i', h),
          },
        },
      },
    }
  ) implemented by "ochr_arr_get_mut"

  -- The parts of a map value, for the model: its buckets as a view (a model function: it
  -- returns a view by value, so it runs only in statements and other model code), and
  -- its length field.
  def SlotsOf (cap : Word) (m : Map(cap)) : Slice(Bucket, cap) := (
    match m {
      MkMap(slots, len) => match slots {
        MkArray(s) => s,
      },
    }
  )

  def LenField (cap : Word) (m : Map(cap)) : Word := (
    match m {
      MkMap(slots, len) => len,
    }
  )
}

/-! ## From the model to the program (FIXED, provided)

H4–H15 about any in-place map follow from its agreement with a pure model and the model's
own properties. These lemmas are that argument, checked, for any operations, model and
invariants (the parameters); nothing here is for you to do. At the end of `HashMapSolution`
they are applied to your operations, your model and your proofs, which gives H4–H15 about
your operations, stated exactly as in the one-program assignment. -/

ochr HashMapCompose uses HashMapSpec {
  -- H4: get(new(c), k) = None.
  def GetNewFrom
      (MM : Type)
      (new : Π(cap : Word) (h : Lt(Zero, cap)). Map(cap))
      (getOf : Π(cap : Word) (m : Map(cap)) (k : Word). Opt)
      (inv : Π(cap : Word) (m : Map(cap)). Prop)
      (absOf : Π(cap : Word) (m : Map(cap)). MM)
      (mnew : MM)
      (mget : Π(a : MM) (k : Word). Opt)
      (invNew : Π(cap : Word) (h : Lt(Zero, cap)). inv(cap, new(cap, h)))
      (agreeGet : Π(cap : Word) (m : &Map(cap)) (k : Word) (hm : inv(cap, *m)). Eq Opt (getOf(cap, *m, k)) (mget(absOf(cap, *m), k)))
      (absNew : Π(cap : Word) (h : Lt(Zero, cap)). Eq MM (absOf(cap, new(cap, h))) mnew)
      (m4 : Π(k : Word). Eq Opt (mget(mnew, k)) None)
      (cap : Word) (h : Lt(Zero, cap)) (k : Word) :
      Eq Opt (getOf(cap, new(cap, h), k)) None := (
    rewrite ← (let c = new(cap, h); agreeGet(cap, &c, k, invNew(cap, h))) in
    rewrite ← absNew(cap, h) in
    m4(k)
  )

  -- H5: after insert(m, k, v), get(m′, k) = Some(v).
  def GetInsertSameFrom
      (MM : Type)
      (ins : Π(cap : Word) (m : &Map(cap)) (k : Word) (v : Word). Opt)
      (getOf : Π(cap : Word) (m : Map(cap)) (k : Word). Opt)
      (inv : Π(cap : Word) (m : Map(cap)). Prop)
      (absOf : Π(cap : Word) (m : Map(cap)). MM)
      (mget : Π(a : MM) (k : Word). Opt)
      (minsert : Π(a : MM) (k : Word) (v : Word). MM)
      (minv : Π(a : MM). Prop)
      (invIns : Π(cap : Word) (m : &Map(cap)) (k : Word) (v : Word) (hm : inv(cap, *m)). (let c = *m; ins(cap, &c, k, v); inv(cap, c)))
      (agreeGet : Π(cap : Word) (m : &Map(cap)) (k : Word) (hm : inv(cap, *m)). Eq Opt (getOf(cap, *m, k)) (mget(absOf(cap, *m), k)))
      (agreeIns : Π(cap : Word) (m : &Map(cap)) (k : Word) (v : Word) (hm : inv(cap, *m)).
        Eq MM (let c = *m; ins(cap, &c, k, v); absOf(cap, c)) (minsert(absOf(cap, *m), k, v)))
      (absInv : Π(cap : Word) (m : &Map(cap)) (hm : inv(cap, *m)). minv(absOf(cap, *m)))
      (m5 : Π(a : MM) (k : Word) (v : Word) (h : minv(a)). Eq Opt (mget(minsert(a, k, v), k)) (Some(v)))
      (cap : Word) (m : &Map(cap)) (k : Word) (v : Word) (hm : inv(cap, *m)) :
      Eq Opt (let c = *m; ins(cap, &c, k, v); getOf(cap, c, k)) (Some(v)) := (
    rewrite ← (let c = *m; ins(cap, &c, k, v); agreeGet(cap, &c, k, invIns(cap, m, k, v, hm))) in
    rewrite ← agreeIns(cap, m, k, v, hm) in
    m5(absOf(cap, *m), k, v, absInv(cap, m, hm))
  )

  -- H6: after insert(m, k, v), get(m′, k′) = get(m, k′) for k′ ≠ k.
  def GetInsertOtherFrom
      (MM : Type)
      (ins : Π(cap : Word) (m : &Map(cap)) (k : Word) (v : Word). Opt)
      (getOf : Π(cap : Word) (m : Map(cap)) (k : Word). Opt)
      (inv : Π(cap : Word) (m : Map(cap)). Prop)
      (absOf : Π(cap : Word) (m : Map(cap)). MM)
      (mget : Π(a : MM) (k : Word). Opt)
      (minsert : Π(a : MM) (k : Word) (v : Word). MM)
      (minv : Π(a : MM). Prop)
      (invIns : Π(cap : Word) (m : &Map(cap)) (k : Word) (v : Word) (hm : inv(cap, *m)). (let c = *m; ins(cap, &c, k, v); inv(cap, c)))
      (agreeGet : Π(cap : Word) (m : &Map(cap)) (k : Word) (hm : inv(cap, *m)). Eq Opt (getOf(cap, *m, k)) (mget(absOf(cap, *m), k)))
      (agreeIns : Π(cap : Word) (m : &Map(cap)) (k : Word) (v : Word) (hm : inv(cap, *m)).
        Eq MM (let c = *m; ins(cap, &c, k, v); absOf(cap, c)) (minsert(absOf(cap, *m), k, v)))
      (absInv : Π(cap : Word) (m : &Map(cap)) (hm : inv(cap, *m)). minv(absOf(cap, *m)))
      (m6 : Π(a : MM) (k : Word) (k2 : Word) (v : Word) (h : minv(a)) (ne : Π(e : Eq Word k2 k). False).
        Eq Opt (mget(minsert(a, k, v), k2)) (mget(a, k2)))
      (cap : Word) (m : &Map(cap)) (k : Word) (k2 : Word) (v : Word) (hm : inv(cap, *m)) (ne : Π(e : Eq Word k2 k). False) :
      Eq Opt (let c = *m; ins(cap, &c, k, v); getOf(cap, c, k2)) (getOf(cap, *m, k2)) := (
    rewrite ← (let c = *m; ins(cap, &c, k, v); agreeGet(cap, &c, k2, invIns(cap, m, k, v, hm))) in
    rewrite ← agreeIns(cap, m, k, v, hm) in
    rewrite ← agreeGet(cap, m, k2, hm) in
    m6(absOf(cap, *m), k, k2, v, absInv(cap, m, hm), ne)
  )

  -- H7: insert returns get(m, k).
  def InsertReturnsGetFrom
      (MM : Type)
      (ins : Π(cap : Word) (m : &Map(cap)) (k : Word) (v : Word). Opt)
      (getOf : Π(cap : Word) (m : Map(cap)) (k : Word). Opt)
      (inv : Π(cap : Word) (m : Map(cap)). Prop)
      (absOf : Π(cap : Word) (m : Map(cap)). MM)
      (mget : Π(a : MM) (k : Word). Opt)
      (agreeGet : Π(cap : Word) (m : &Map(cap)) (k : Word) (hm : inv(cap, *m)). Eq Opt (getOf(cap, *m, k)) (mget(absOf(cap, *m), k)))
      (agreeInsRes : Π(cap : Word) (m : &Map(cap)) (k : Word) (v : Word) (hm : inv(cap, *m)).
        Eq Opt (let c = *m; ins(cap, &c, k, v)) (mget(absOf(cap, *m), k)))
      (cap : Word) (m : &Map(cap)) (k : Word) (v : Word) (hm : inv(cap, *m)) :
      Eq Opt (let c = *m; ins(cap, &c, k, v)) (getOf(cap, *m, k)) := (
    rewrite ← agreeGet(cap, m, k, hm) in
    agreeInsRes(cap, m, k, v, hm)
  )

  -- H8: after remove(m, k), get(m′, k) = None.
  def GetRemoveSameFrom
      (MM : Type)
      (rem : Π(cap : Word) (m : &Map(cap)) (k : Word). Opt)
      (getOf : Π(cap : Word) (m : Map(cap)) (k : Word). Opt)
      (inv : Π(cap : Word) (m : Map(cap)). Prop)
      (absOf : Π(cap : Word) (m : Map(cap)). MM)
      (mget : Π(a : MM) (k : Word). Opt)
      (mremove : Π(a : MM) (k : Word). MM)
      (minv : Π(a : MM). Prop)
      (invRem : Π(cap : Word) (m : &Map(cap)) (k : Word) (hm : inv(cap, *m)). (let c = *m; rem(cap, &c, k); inv(cap, c)))
      (agreeGet : Π(cap : Word) (m : &Map(cap)) (k : Word) (hm : inv(cap, *m)). Eq Opt (getOf(cap, *m, k)) (mget(absOf(cap, *m), k)))
      (agreeRem : Π(cap : Word) (m : &Map(cap)) (k : Word) (hm : inv(cap, *m)).
        Eq MM (let c = *m; rem(cap, &c, k); absOf(cap, c)) (mremove(absOf(cap, *m), k)))
      (absInv : Π(cap : Word) (m : &Map(cap)) (hm : inv(cap, *m)). minv(absOf(cap, *m)))
      (m8 : Π(a : MM) (k : Word) (h : minv(a)). Eq Opt (mget(mremove(a, k), k)) None)
      (cap : Word) (m : &Map(cap)) (k : Word) (hm : inv(cap, *m)) :
      Eq Opt (let c = *m; rem(cap, &c, k); getOf(cap, c, k)) None := (
    rewrite ← (let c = *m; rem(cap, &c, k); agreeGet(cap, &c, k, invRem(cap, m, k, hm))) in
    rewrite ← agreeRem(cap, m, k, hm) in
    m8(absOf(cap, *m), k, absInv(cap, m, hm))
  )

  -- H9: after remove(m, k), get(m′, k′) = get(m, k′) for k′ ≠ k.
  def GetRemoveOtherFrom
      (MM : Type)
      (rem : Π(cap : Word) (m : &Map(cap)) (k : Word). Opt)
      (getOf : Π(cap : Word) (m : Map(cap)) (k : Word). Opt)
      (inv : Π(cap : Word) (m : Map(cap)). Prop)
      (absOf : Π(cap : Word) (m : Map(cap)). MM)
      (mget : Π(a : MM) (k : Word). Opt)
      (mremove : Π(a : MM) (k : Word). MM)
      (minv : Π(a : MM). Prop)
      (invRem : Π(cap : Word) (m : &Map(cap)) (k : Word) (hm : inv(cap, *m)). (let c = *m; rem(cap, &c, k); inv(cap, c)))
      (agreeGet : Π(cap : Word) (m : &Map(cap)) (k : Word) (hm : inv(cap, *m)). Eq Opt (getOf(cap, *m, k)) (mget(absOf(cap, *m), k)))
      (agreeRem : Π(cap : Word) (m : &Map(cap)) (k : Word) (hm : inv(cap, *m)).
        Eq MM (let c = *m; rem(cap, &c, k); absOf(cap, c)) (mremove(absOf(cap, *m), k)))
      (absInv : Π(cap : Word) (m : &Map(cap)) (hm : inv(cap, *m)). minv(absOf(cap, *m)))
      (m9 : Π(a : MM) (k : Word) (k2 : Word) (h : minv(a)) (ne : Π(e : Eq Word k2 k). False).
        Eq Opt (mget(mremove(a, k), k2)) (mget(a, k2)))
      (cap : Word) (m : &Map(cap)) (k : Word) (k2 : Word) (hm : inv(cap, *m)) (ne : Π(e : Eq Word k2 k). False) :
      Eq Opt (let c = *m; rem(cap, &c, k); getOf(cap, c, k2)) (getOf(cap, *m, k2)) := (
    rewrite ← (let c = *m; rem(cap, &c, k); agreeGet(cap, &c, k2, invRem(cap, m, k, hm))) in
    rewrite ← agreeRem(cap, m, k, hm) in
    rewrite ← agreeGet(cap, m, k2, hm) in
    m9(absOf(cap, *m), k, k2, absInv(cap, m, hm), ne)
  )

  -- H10: remove returns get(m, k).
  def RemoveReturnsGetFrom
      (MM : Type)
      (rem : Π(cap : Word) (m : &Map(cap)) (k : Word). Opt)
      (getOf : Π(cap : Word) (m : Map(cap)) (k : Word). Opt)
      (inv : Π(cap : Word) (m : Map(cap)). Prop)
      (absOf : Π(cap : Word) (m : Map(cap)). MM)
      (mget : Π(a : MM) (k : Word). Opt)
      (agreeGet : Π(cap : Word) (m : &Map(cap)) (k : Word) (hm : inv(cap, *m)). Eq Opt (getOf(cap, *m, k)) (mget(absOf(cap, *m), k)))
      (agreeRemRes : Π(cap : Word) (m : &Map(cap)) (k : Word) (hm : inv(cap, *m)).
        Eq Opt (let c = *m; rem(cap, &c, k)) (mget(absOf(cap, *m), k)))
      (cap : Word) (m : &Map(cap)) (k : Word) (hm : inv(cap, *m)) :
      Eq Opt (let c = *m; rem(cap, &c, k)) (getOf(cap, *m, k)) := (
    rewrite ← agreeGet(cap, m, k, hm) in
    agreeRemRes(cap, m, k, hm)
  )

  -- H11: len(new(c)) = 0.
  def LenNewFrom
      (MM : Type)
      (new : Π(cap : Word) (h : Lt(Zero, cap)). Map(cap))
      (lenOf : Π(cap : Word) (m : Map(cap)). Word)
      (inv : Π(cap : Word) (m : Map(cap)). Prop)
      (absOf : Π(cap : Word) (m : Map(cap)). MM)
      (mnew : MM)
      (mlen : Π(a : MM). Word)
      (invNew : Π(cap : Word) (h : Lt(Zero, cap)). inv(cap, new(cap, h)))
      (agreeLen : Π(cap : Word) (m : &Map(cap)) (hm : inv(cap, *m)). Eq Word (lenOf(cap, *m)) (mlen(absOf(cap, *m))))
      (absNew : Π(cap : Word) (h : Lt(Zero, cap)). Eq MM (absOf(cap, new(cap, h))) mnew)
      (m11 : Eq Word (mlen(mnew)) Zero)
      (cap : Word) (h : Lt(Zero, cap)) :
      Eq Word (lenOf(cap, new(cap, h))) Zero := (
    rewrite ← (let c = new(cap, h); agreeLen(cap, &c, invNew(cap, h))) in
    rewrite ← absNew(cap, h) in
    m11
  )

  -- H12: insert adds one to len if the key was absent.
  def LenInsertFrom
      (MM : Type)
      (ins : Π(cap : Word) (m : &Map(cap)) (k : Word) (v : Word). Opt)
      (getOf : Π(cap : Word) (m : Map(cap)) (k : Word). Opt)
      (lenOf : Π(cap : Word) (m : Map(cap)). Word)
      (inv : Π(cap : Word) (m : Map(cap)). Prop)
      (absOf : Π(cap : Word) (m : Map(cap)). MM)
      (mget : Π(a : MM) (k : Word). Opt)
      (mlen : Π(a : MM). Word)
      (minsert : Π(a : MM) (k : Word) (v : Word). MM)
      (minv : Π(a : MM). Prop)
      (invIns : Π(cap : Word) (m : &Map(cap)) (k : Word) (v : Word) (hm : inv(cap, *m)). (let c = *m; ins(cap, &c, k, v); inv(cap, c)))
      (agreeGet : Π(cap : Word) (m : &Map(cap)) (k : Word) (hm : inv(cap, *m)). Eq Opt (getOf(cap, *m, k)) (mget(absOf(cap, *m), k)))
      (agreeLen : Π(cap : Word) (m : &Map(cap)) (hm : inv(cap, *m)). Eq Word (lenOf(cap, *m)) (mlen(absOf(cap, *m))))
      (agreeIns : Π(cap : Word) (m : &Map(cap)) (k : Word) (v : Word) (hm : inv(cap, *m)).
        Eq MM (let c = *m; ins(cap, &c, k, v); absOf(cap, c)) (minsert(absOf(cap, *m), k, v)))
      (absInv : Π(cap : Word) (m : &Map(cap)) (hm : inv(cap, *m)). minv(absOf(cap, *m)))
      (m12 : Π(a : MM) (k : Word) (v : Word) (h : minv(a)). Eq Word (mlen(minsert(a, k, v))) (Grow(mget(a, k), mlen(a))))
      (cap : Word) (m : &Map(cap)) (k : Word) (v : Word) (hm : inv(cap, *m)) :
      Eq Word (let c = *m; ins(cap, &c, k, v); lenOf(cap, c)) (Grow(getOf(cap, *m, k), lenOf(cap, *m))) := (
    rewrite ← (let c = *m; ins(cap, &c, k, v); agreeLen(cap, &c, invIns(cap, m, k, v, hm))) in
    rewrite ← agreeIns(cap, m, k, v, hm) in
    rewrite ← agreeGet(cap, m, k, hm) in
    rewrite ← agreeLen(cap, m, hm) in
    m12(absOf(cap, *m), k, v, absInv(cap, m, hm))
  )

  -- H13: remove takes one from len if the key was present.
  def LenRemoveFrom
      (MM : Type)
      (rem : Π(cap : Word) (m : &Map(cap)) (k : Word). Opt)
      (getOf : Π(cap : Word) (m : Map(cap)) (k : Word). Opt)
      (lenOf : Π(cap : Word) (m : Map(cap)). Word)
      (inv : Π(cap : Word) (m : Map(cap)). Prop)
      (absOf : Π(cap : Word) (m : Map(cap)). MM)
      (mget : Π(a : MM) (k : Word). Opt)
      (mlen : Π(a : MM). Word)
      (mremove : Π(a : MM) (k : Word). MM)
      (minv : Π(a : MM). Prop)
      (invRem : Π(cap : Word) (m : &Map(cap)) (k : Word) (hm : inv(cap, *m)). (let c = *m; rem(cap, &c, k); inv(cap, c)))
      (agreeGet : Π(cap : Word) (m : &Map(cap)) (k : Word) (hm : inv(cap, *m)). Eq Opt (getOf(cap, *m, k)) (mget(absOf(cap, *m), k)))
      (agreeLen : Π(cap : Word) (m : &Map(cap)) (hm : inv(cap, *m)). Eq Word (lenOf(cap, *m)) (mlen(absOf(cap, *m))))
      (agreeRem : Π(cap : Word) (m : &Map(cap)) (k : Word) (hm : inv(cap, *m)).
        Eq MM (let c = *m; rem(cap, &c, k); absOf(cap, c)) (mremove(absOf(cap, *m), k)))
      (absInv : Π(cap : Word) (m : &Map(cap)) (hm : inv(cap, *m)). minv(absOf(cap, *m)))
      (m13 : Π(a : MM) (k : Word) (h : minv(a)). Eq Word (mlen(mremove(a, k))) (Shrink(mget(a, k), mlen(a))))
      (cap : Word) (m : &Map(cap)) (k : Word) (hm : inv(cap, *m)) :
      Eq Word (let c = *m; rem(cap, &c, k); lenOf(cap, c)) (Shrink(getOf(cap, *m, k), lenOf(cap, *m))) := (
    rewrite ← (let c = *m; rem(cap, &c, k); agreeLen(cap, &c, invRem(cap, m, k, hm))) in
    rewrite ← agreeRem(cap, m, k, hm) in
    rewrite ← agreeGet(cap, m, k, hm) in
    rewrite ← agreeLen(cap, m, hm) in
    m13(absOf(cap, *m), k, absInv(cap, m, hm))
  )

  -- H14: writing through get_mut has the effect of insert on every get.
  def GetMutGetFrom
      (MM : Type)
      (ins : Π(cap : Word) (m : &Map(cap)) (k : Word) (v : Word). Opt)
      (getOf : Π(cap : Word) (m : Map(cap)) (k : Word). Opt)
      (getMut : Π(cap : Word) (m : &Map(cap)) (k : Word) (h : IsSome(getOf(cap, *m, k))). &Word)
      (inv : Π(cap : Word) (m : Map(cap)). Prop)
      (absOf : Π(cap : Word) (m : Map(cap)). MM)
      (mget : Π(a : MM) (k : Word). Opt)
      (minsert : Π(a : MM) (k : Word) (v : Word). MM)
      (mwrite : Π(a : MM) (k : Word) (w : Word). MM)
      (minv : Π(a : MM). Prop)
      (invIns : Π(cap : Word) (m : &Map(cap)) (k : Word) (v : Word) (hm : inv(cap, *m)). (let c = *m; ins(cap, &c, k, v); inv(cap, c)))
      (invWrite : Π(cap : Word) (m : &Map(cap)) (k : Word) (w : Word) (hm : inv(cap, *m)) (hk : IsSome(getOf(cap, *m, k))).
        (let c = *m; let r = getMut(cap, &c, k, hk); *r := w; inv(cap, c)))
      (agreeGet : Π(cap : Word) (m : &Map(cap)) (k : Word) (hm : inv(cap, *m)). Eq Opt (getOf(cap, *m, k)) (mget(absOf(cap, *m), k)))
      (agreeIns : Π(cap : Word) (m : &Map(cap)) (k : Word) (v : Word) (hm : inv(cap, *m)).
        Eq MM (let c = *m; ins(cap, &c, k, v); absOf(cap, c)) (minsert(absOf(cap, *m), k, v)))
      (agreeWrite : Π(cap : Word) (m : &Map(cap)) (k : Word) (w : Word) (hm : inv(cap, *m)) (hk : IsSome(getOf(cap, *m, k))).
        Eq MM (let c = *m; let r = getMut(cap, &c, k, hk); *r := w; absOf(cap, c)) (mwrite(absOf(cap, *m), k, w)))
      (absInv : Π(cap : Word) (m : &Map(cap)) (hm : inv(cap, *m)). minv(absOf(cap, *m)))
      (m14 : Π(a : MM) (k : Word) (w : Word) (k2 : Word) (h : minv(a)) (hk : IsSome(mget(a, k))).
        Eq Opt (mget(mwrite(a, k, w), k2)) (mget(minsert(a, k, w), k2)))
      (cap : Word) (m : &Map(cap)) (k : Word) (w : Word) (k2 : Word) (hm : inv(cap, *m)) (hk : IsSome(getOf(cap, *m, k))) :
      Eq Opt (let c = *m; let r = getMut(cap, &c, k, hk); *r := w; getOf(cap, c, k2))
        (let c = *m; ins(cap, &c, k, w); getOf(cap, c, k2)) := (
    rewrite ← (let c = *m; let r = getMut(cap, &c, k, hk); *r := w; agreeGet(cap, &c, k2, invWrite(cap, m, k, w, hm, hk))) in
    rewrite ← agreeWrite(cap, m, k, w, hm, hk) in
    rewrite ← (let c = *m; ins(cap, &c, k, w); agreeGet(cap, &c, k2, invIns(cap, m, k, w, hm))) in
    rewrite ← agreeIns(cap, m, k, w, hm) in
    m14(absOf(cap, *m), k, w, k2, absInv(cap, m, hm), (rewrite agreeGet(cap, m, k, hm) in hk))
  )

  -- H15: ... and on len.
  def GetMutLenFrom
      (MM : Type)
      (ins : Π(cap : Word) (m : &Map(cap)) (k : Word) (v : Word). Opt)
      (getOf : Π(cap : Word) (m : Map(cap)) (k : Word). Opt)
      (lenOf : Π(cap : Word) (m : Map(cap)). Word)
      (getMut : Π(cap : Word) (m : &Map(cap)) (k : Word) (h : IsSome(getOf(cap, *m, k))). &Word)
      (inv : Π(cap : Word) (m : Map(cap)). Prop)
      (absOf : Π(cap : Word) (m : Map(cap)). MM)
      (mget : Π(a : MM) (k : Word). Opt)
      (mlen : Π(a : MM). Word)
      (minsert : Π(a : MM) (k : Word) (v : Word). MM)
      (mwrite : Π(a : MM) (k : Word) (w : Word). MM)
      (minv : Π(a : MM). Prop)
      (invIns : Π(cap : Word) (m : &Map(cap)) (k : Word) (v : Word) (hm : inv(cap, *m)). (let c = *m; ins(cap, &c, k, v); inv(cap, c)))
      (invWrite : Π(cap : Word) (m : &Map(cap)) (k : Word) (w : Word) (hm : inv(cap, *m)) (hk : IsSome(getOf(cap, *m, k))).
        (let c = *m; let r = getMut(cap, &c, k, hk); *r := w; inv(cap, c)))
      (agreeGet : Π(cap : Word) (m : &Map(cap)) (k : Word) (hm : inv(cap, *m)). Eq Opt (getOf(cap, *m, k)) (mget(absOf(cap, *m), k)))
      (agreeLen : Π(cap : Word) (m : &Map(cap)) (hm : inv(cap, *m)). Eq Word (lenOf(cap, *m)) (mlen(absOf(cap, *m))))
      (agreeIns : Π(cap : Word) (m : &Map(cap)) (k : Word) (v : Word) (hm : inv(cap, *m)).
        Eq MM (let c = *m; ins(cap, &c, k, v); absOf(cap, c)) (minsert(absOf(cap, *m), k, v)))
      (agreeWrite : Π(cap : Word) (m : &Map(cap)) (k : Word) (w : Word) (hm : inv(cap, *m)) (hk : IsSome(getOf(cap, *m, k))).
        Eq MM (let c = *m; let r = getMut(cap, &c, k, hk); *r := w; absOf(cap, c)) (mwrite(absOf(cap, *m), k, w)))
      (absInv : Π(cap : Word) (m : &Map(cap)) (hm : inv(cap, *m)). minv(absOf(cap, *m)))
      (m15 : Π(a : MM) (k : Word) (w : Word) (h : minv(a)) (hk : IsSome(mget(a, k))).
        Eq Word (mlen(mwrite(a, k, w))) (mlen(minsert(a, k, w))))
      (cap : Word) (m : &Map(cap)) (k : Word) (w : Word) (hm : inv(cap, *m)) (hk : IsSome(getOf(cap, *m, k))) :
      Eq Word (let c = *m; let r = getMut(cap, &c, k, hk); *r := w; lenOf(cap, c))
        (let c = *m; ins(cap, &c, k, w); lenOf(cap, c)) := (
    rewrite ← (let c = *m; let r = getMut(cap, &c, k, hk); *r := w; agreeLen(cap, &c, invWrite(cap, m, k, w, hm, hk))) in
    rewrite ← agreeWrite(cap, m, k, w, hm, hk) in
    rewrite ← (let c = *m; ins(cap, &c, k, w); agreeLen(cap, &c, invIns(cap, m, k, w, hm))) in
    rewrite ← agreeIns(cap, m, k, w, hm) in
    m15(absOf(cap, *m), k, w, absInv(cap, m, hm), (rewrite agreeGet(cap, m, k, hm) in hk))
  )
}

/-! ## Your model

A pure functional model of a finite map, and its properties. Pure means: no borrows (`&`)
and no assignment (`p := t`) anywhere in this block; the model computes on values. Declare
the data types the model needs here too (an association list, for example). -/

ochr HashMapModel uses HashMapSpec {
-- FIXED-END header

  -- Your model's data types, pure helper definitions and lemmas go here, and anywhere else
  -- between the FIXED regions of this block.

  -- FIXED-BEGIN model-type
  -- The model's type.
  def MMap : Type :=
  -- FIXED-END model-type
    ?

  -- FIXED-BEGIN model-new
  -- The model of new(c): the empty map.
  def MNew : MMap :=
  -- FIXED-END model-new
    ?

  -- FIXED-BEGIN model-len
  -- The model of len.
  def MLen (a : MMap) : Word :=
  -- FIXED-END model-len
    ?

  -- FIXED-BEGIN model-get
  -- The model of get.
  def MGet (a : MMap) (k : Word) : Opt :=
  -- FIXED-END model-get
    ?

  -- FIXED-BEGIN model-insert
  -- The model of insert: the map afterwards. (The value insert returns is
  -- MGet(a, k), by AgreeInsertResult below.)
  def MInsert (a : MMap) (k : Word) (v : Word) : MMap :=
  -- FIXED-END model-insert
    ?

  -- FIXED-BEGIN model-remove
  -- The model of remove: the map afterwards. (The value remove returns is
  -- MGet(a, k), by AgreeRemoveResult below.)
  def MRemove (a : MMap) (k : Word) : MMap :=
  -- FIXED-END model-remove
    ?

  -- FIXED-BEGIN model-write
  -- The model of writing `w` through get_mut(m, k): the map afterwards.
  def MWrite (a : MMap) (k : Word) (w : Word) : MMap :=
  -- FIXED-END model-write
    ?

  -- FIXED-BEGIN model-inv
  -- The model's invariant: any predicate on models that the properties below need
  -- (it may be ⊤).
  def MInv (a : MMap) : Prop :=
  -- FIXED-END model-inv
    ?

  -- FIXED-BEGIN model-abs
  -- The abstraction: the model of a map, from its buckets (a view, as `SlotsOf` gives
  -- it) and its length field.
  def Abs (cap : Word) (s : Slice(Bucket, cap)) (len : Word) : MMap :=
  -- FIXED-END model-abs
    ?

  -- FIXED-BEGIN M4
  -- M4 (H4 about the model): the model of get on the empty map.
  def MGetNew (k : Word) :
      Eq Opt (MGet(MNew, k)) None :=
  -- FIXED-END M4
    ?

  -- FIXED-BEGIN M5
  -- M5 (H5 about the model): get after insert, at the same key.
  def MGetInsertSame (a : MMap) (k : Word) (v : Word) (h : MInv(a)) :
      Eq Opt (MGet(MInsert(a, k, v), k)) (Some(v)) :=
  -- FIXED-END M5
    ?

  -- FIXED-BEGIN M6
  -- M6 (H6 about the model): get after insert, at another key.
  def MGetInsertOther (a : MMap) (k : Word) (k2 : Word) (v : Word) (h : MInv(a)) (ne : Π(e : Eq Word k2 k). False) :
      Eq Opt (MGet(MInsert(a, k, v), k2)) (MGet(a, k2)) :=
  -- FIXED-END M6
    ?

  -- FIXED-BEGIN M8
  -- M8 (H8 about the model): get after remove, at the same key.
  def MGetRemoveSame (a : MMap) (k : Word) (h : MInv(a)) :
      Eq Opt (MGet(MRemove(a, k), k)) None :=
  -- FIXED-END M8
    ?

  -- FIXED-BEGIN M9
  -- M9 (H9 about the model): get after remove, at another key.
  def MGetRemoveOther (a : MMap) (k : Word) (k2 : Word) (h : MInv(a)) (ne : Π(e : Eq Word k2 k). False) :
      Eq Opt (MGet(MRemove(a, k), k2)) (MGet(a, k2)) :=
  -- FIXED-END M9
    ?

  -- FIXED-BEGIN M11
  -- M11 (H11 about the model): the length of the empty map.
  def MLenNew :
      Eq Word (MLen(MNew)) Zero :=
  -- FIXED-END M11
    ?

  -- FIXED-BEGIN M12
  -- M12 (H12 about the model): the length after insert.
  def MLenInsert (a : MMap) (k : Word) (v : Word) (h : MInv(a)) :
      Eq Word (MLen(MInsert(a, k, v))) (Grow(MGet(a, k), MLen(a))) :=
  -- FIXED-END M12
    ?

  -- FIXED-BEGIN M13
  -- M13 (H13 about the model): the length after remove.
  def MLenRemove (a : MMap) (k : Word) (h : MInv(a)) :
      Eq Word (MLen(MRemove(a, k))) (Shrink(MGet(a, k), MLen(a))) :=
  -- FIXED-END M13
    ?

  -- FIXED-BEGIN M14
  -- M14 (H14 about the model): a write has the effect of insert on every get.
  def MWriteGet (a : MMap) (k : Word) (w : Word) (k2 : Word) (h : MInv(a)) (hk : IsSome(MGet(a, k))) :
      Eq Opt (MGet(MWrite(a, k, w), k2)) (MGet(MInsert(a, k, w), k2)) :=
  -- FIXED-END M14
    ?

  -- FIXED-BEGIN M15
  -- M15 (H15 about the model): ... and on the length.
  def MWriteLen (a : MMap) (k : Word) (w : Word) (h : MInv(a)) (hk : IsSome(MGet(a, k))) :
      Eq Word (MLen(MWrite(a, k, w))) (MLen(MInsert(a, k, w))) :=
  -- FIXED-END M15
    ?

-- FIXED-BEGIN solution-header
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

  -- FIXED-BEGIN new
  -- new(c): an empty map, with `cap` empty buckets and length 0. `h` is the precondition c ≥ 1.
  def MapNew (cap : Word) (h : Lt(Zero, cap)) : Map(cap) :=
  -- FIXED-END new
    ?

  -- FIXED-BEGIN len
  -- len(m): the number of keys in the map.
  def MapLen (cap : Word) (m : &Map(cap)) : Word :=
  -- FIXED-END len
    ?

  -- FIXED-BEGIN get
  -- get(m, k): Some(v) if `k` is bound to `v`, None otherwise.
  def MapGet (cap : Word) (m : &Map(cap)) (k : Word) : Opt :=
  -- FIXED-END get
    ?

  -- FIXED-BEGIN insert
  -- insert(m, k, v): bind `k` to `v`, in place; return what `k` was bound to before.
  def MapInsert (cap : Word) (m : &Map(cap)) (k : Word) (v : Word) : Opt :=
  -- FIXED-END insert
    ?

  -- FIXED-BEGIN remove
  -- remove(m, k): unbind `k`, in place; return what it was bound to.
  def MapRemove (cap : Word) (m : &Map(cap)) (k : Word) : Opt :=
  -- FIXED-END remove
    ?

  -- FIXED-BEGIN get_mut
  -- get(m, k) and len(m) of a map value, run on a copy of it: what the properties observe.
  def GetOf (cap : Word) (m : Map(cap)) (k : Word) : Opt := MapGet(cap, &m, k)

  def LenOf (cap : Word) (m : Map(cap)) : Word := MapLen(cap, &m)

  -- get_mut(m, k): a borrow of the value stored for `k`, which must be present.
  def MapGetMut (cap : Word) (m : &Map(cap)) (k : Word) (h : IsSome(GetOf(cap, *m, k))) : &Word :=
  -- FIXED-END get_mut
    ?

  -- FIXED-BEGIN inv
  -- Inv(m): your invariant, any predicate that makes H1–H18 provable.
  def Inv (cap : Word) (m : Map(cap)) : Prop :=
  -- FIXED-END inv
    ?

  -- FIXED-BEGIN abs-inv
  -- The invariant on maps gives the model's invariant.
  def AbsInv (cap : Word) (m : &Map(cap)) (hm : Inv(cap, *m)) : MInv(AbsOf(cap, *m)) :=
  -- FIXED-END abs-inv
    ?

  -- FIXED-BEGIN H1
  -- H1: Inv(new(c)).
  def InvNew (cap : Word) (h : Lt(Zero, cap)) : Inv(cap, MapNew(cap, h)) :=
  -- FIXED-END H1
    ?

  -- FIXED-BEGIN H2
  -- H2: insert preserves Inv.
  def InvInsert (cap : Word) (m : &Map(cap)) (k : Word) (v : Word) (hm : Inv(cap, *m)) :
      (let c = *m; MapInsert(cap, &c, k, v); Inv(cap, c)) :=
  -- FIXED-END H2
    ?

  -- FIXED-BEGIN H3
  -- H3: remove preserves Inv.
  def InvRemove (cap : Word) (m : &Map(cap)) (k : Word) (hm : Inv(cap, *m)) :
      (let c = *m; MapRemove(cap, &c, k); Inv(cap, c)) :=
  -- FIXED-END H3
    ?

  -- FIXED-BEGIN agree-new
  -- Agreement: new(c) is the empty model.
  def AbsNew (cap : Word) (h : Lt(Zero, cap)) :
      Eq MMap (AbsOf(cap, MapNew(cap, h))) MNew :=
  -- FIXED-END agree-new
    ?

  -- FIXED-BEGIN agree-len
  -- Agreement: len agrees with the model.
  def AgreeLen (cap : Word) (m : &Map(cap)) (hm : Inv(cap, *m)) :
      Eq Word (LenOf(cap, *m)) (MLen(AbsOf(cap, *m))) :=
  -- FIXED-END agree-len
    ?

  -- FIXED-BEGIN agree-get
  -- Agreement: get agrees with the model.
  def AgreeGet (cap : Word) (m : &Map(cap)) (k : Word) (hm : Inv(cap, *m)) :
      Eq Opt (GetOf(cap, *m, k)) (MGet(AbsOf(cap, *m), k)) :=
  -- FIXED-END agree-get
    ?

  -- FIXED-BEGIN agree-insert
  -- Agreement: insert agrees with the model: the map afterwards.
  def AgreeInsert (cap : Word) (m : &Map(cap)) (k : Word) (v : Word) (hm : Inv(cap, *m)) :
      Eq MMap (let c = *m; MapInsert(cap, &c, k, v); AbsOf(cap, c)) (MInsert(AbsOf(cap, *m), k, v)) :=
  -- FIXED-END agree-insert
    ?

  -- FIXED-BEGIN agree-insert-result
  -- Agreement: ... and the value it returns.
  def AgreeInsertResult (cap : Word) (m : &Map(cap)) (k : Word) (v : Word) (hm : Inv(cap, *m)) :
      Eq Opt (let c = *m; MapInsert(cap, &c, k, v)) (MGet(AbsOf(cap, *m), k)) :=
  -- FIXED-END agree-insert-result
    ?

  -- FIXED-BEGIN agree-remove
  -- Agreement: remove agrees with the model: the map afterwards.
  def AgreeRemove (cap : Word) (m : &Map(cap)) (k : Word) (hm : Inv(cap, *m)) :
      Eq MMap (let c = *m; MapRemove(cap, &c, k); AbsOf(cap, c)) (MRemove(AbsOf(cap, *m), k)) :=
  -- FIXED-END agree-remove
    ?

  -- FIXED-BEGIN agree-remove-result
  -- Agreement: ... and the value it returns.
  def AgreeRemoveResult (cap : Word) (m : &Map(cap)) (k : Word) (hm : Inv(cap, *m)) :
      Eq Opt (let c = *m; MapRemove(cap, &c, k)) (MGet(AbsOf(cap, *m), k)) :=
  -- FIXED-END agree-remove-result
    ?

  -- FIXED-BEGIN agree-write
  -- Agreement: a write through get_mut agrees with the model.
  def AgreeWrite (cap : Word) (m : &Map(cap)) (k : Word) (w : Word) (hm : Inv(cap, *m))
      (hk : IsSome(GetOf(cap, *m, k))) :
      Eq MMap (let c = *m; let r = MapGetMut(cap, &c, k, hk); *r := w; AbsOf(cap, c)) (MWrite(AbsOf(cap, *m), k, w)) :=
  -- FIXED-END agree-write
    ?

  -- FIXED-BEGIN H16
  -- H16: ... and preserves Inv.
  def GetMutInv (cap : Word) (m : &Map(cap)) (k : Word) (w : Word) (hm : Inv(cap, *m))
      (hk : IsSome(GetOf(cap, *m, k))) :
      (let c = *m; let r = MapGetMut(cap, &c, k, hk); *r := w; Inv(cap, c)) :=
  -- FIXED-END H16
    ?

  -- FIXED-BEGIN H17
  -- H17: get leaves the map unchanged (for every map, not only those with Inv).
  def GetUnchanged (cap : Word) (m : &Map(cap)) (k : Word) : Eq (Map(cap)) (let c = *m; MapGet(cap, &c, k); c) (*m) :=
  -- FIXED-END H17
    ?

  -- FIXED-BEGIN H18
  -- H18: len leaves the map unchanged.
  def LenUnchanged (cap : Word) (m : &Map(cap)) : Eq (Map(cap)) (let c = *m; MapLen(cap, &c); c) (*m) :=
  -- FIXED-END H18
    ?

  -- FIXED-BEGIN H4
  -- H4: get(new(c), k) = None.
  def GetNew (cap : Word) (h : Lt(Zero, cap)) (k : Word) : Eq Opt (GetOf(cap, MapNew(cap, h), k)) None :=
    -- provided: from the model, by GetNewFrom (HashMapCompose)
    GetNewFrom(MMap, MapNew, GetOf, Inv, AbsOf, MNew, MGet, InvNew, AgreeGet, AbsNew, MGetNew, cap, h, k)
  -- FIXED-END H4

  -- FIXED-BEGIN H5
  -- H5: after insert(m, k, v), get(m′, k) = Some(v).
  def GetInsertSame (cap : Word) (m : &Map(cap)) (k : Word) (v : Word) (hm : Inv(cap, *m)) :
      Eq Opt (let c = *m; MapInsert(cap, &c, k, v); GetOf(cap, c, k)) (Some(v)) :=
    -- provided: from the model, by GetInsertSameFrom (HashMapCompose)
    GetInsertSameFrom(MMap, MapInsert, GetOf, Inv, AbsOf, MGet, MInsert, MInv, InvInsert, AgreeGet, AgreeInsert, AbsInv, MGetInsertSame, cap, m, k, v, hm)
  -- FIXED-END H5

  -- FIXED-BEGIN H6
  -- H6: after insert(m, k, v), get(m′, k′) = get(m, k′) for k′ ≠ k.
  def GetInsertOther (cap : Word) (m : &Map(cap)) (k : Word) (k2 : Word) (v : Word) (hm : Inv(cap, *m))
      (ne : Π(e : Eq Word k2 k). False) :
      Eq Opt (let c = *m; MapInsert(cap, &c, k, v); GetOf(cap, c, k2)) (GetOf(cap, *m, k2)) :=
    -- provided: from the model, by GetInsertOtherFrom (HashMapCompose)
    GetInsertOtherFrom(MMap, MapInsert, GetOf, Inv, AbsOf, MGet, MInsert, MInv, InvInsert, AgreeGet, AgreeInsert, AbsInv, MGetInsertOther, cap, m, k, k2, v, hm, ne)
  -- FIXED-END H6

  -- FIXED-BEGIN H7
  -- H7: insert returns get(m, k).
  def InsertReturnsGet (cap : Word) (m : &Map(cap)) (k : Word) (v : Word) (hm : Inv(cap, *m)) :
      Eq Opt (let c = *m; MapInsert(cap, &c, k, v)) (GetOf(cap, *m, k)) :=
    -- provided: from the model, by InsertReturnsGetFrom (HashMapCompose)
    InsertReturnsGetFrom(MMap, MapInsert, GetOf, Inv, AbsOf, MGet, AgreeGet, AgreeInsertResult, cap, m, k, v, hm)
  -- FIXED-END H7

  -- FIXED-BEGIN H8
  -- H8: after remove(m, k), get(m′, k) = None.
  def GetRemoveSame (cap : Word) (m : &Map(cap)) (k : Word) (hm : Inv(cap, *m)) :
      Eq Opt (let c = *m; MapRemove(cap, &c, k); GetOf(cap, c, k)) None :=
    -- provided: from the model, by GetRemoveSameFrom (HashMapCompose)
    GetRemoveSameFrom(MMap, MapRemove, GetOf, Inv, AbsOf, MGet, MRemove, MInv, InvRemove, AgreeGet, AgreeRemove, AbsInv, MGetRemoveSame, cap, m, k, hm)
  -- FIXED-END H8

  -- FIXED-BEGIN H9
  -- H9: after remove(m, k), get(m′, k′) = get(m, k′) for k′ ≠ k.
  def GetRemoveOther (cap : Word) (m : &Map(cap)) (k : Word) (k2 : Word) (hm : Inv(cap, *m))
      (ne : Π(e : Eq Word k2 k). False) :
      Eq Opt (let c = *m; MapRemove(cap, &c, k); GetOf(cap, c, k2)) (GetOf(cap, *m, k2)) :=
    -- provided: from the model, by GetRemoveOtherFrom (HashMapCompose)
    GetRemoveOtherFrom(MMap, MapRemove, GetOf, Inv, AbsOf, MGet, MRemove, MInv, InvRemove, AgreeGet, AgreeRemove, AbsInv, MGetRemoveOther, cap, m, k, k2, hm, ne)
  -- FIXED-END H9

  -- FIXED-BEGIN H10
  -- H10: remove returns get(m, k).
  def RemoveReturnsGet (cap : Word) (m : &Map(cap)) (k : Word) (hm : Inv(cap, *m)) :
      Eq Opt (let c = *m; MapRemove(cap, &c, k)) (GetOf(cap, *m, k)) :=
    -- provided: from the model, by RemoveReturnsGetFrom (HashMapCompose)
    RemoveReturnsGetFrom(MMap, MapRemove, GetOf, Inv, AbsOf, MGet, AgreeGet, AgreeRemoveResult, cap, m, k, hm)
  -- FIXED-END H10

  -- FIXED-BEGIN H11
  -- H11: len(new(c)) = 0.
  def LenNew (cap : Word) (h : Lt(Zero, cap)) : Eq Word (LenOf(cap, MapNew(cap, h))) Zero :=
    -- provided: from the model, by LenNewFrom (HashMapCompose)
    LenNewFrom(MMap, MapNew, LenOf, Inv, AbsOf, MNew, MLen, InvNew, AgreeLen, AbsNew, MLenNew, cap, h)
  -- FIXED-END H11

  -- FIXED-BEGIN H12
  -- H12: insert adds one to len if get(m, k) = None, and leaves it otherwise.
  def LenInsert (cap : Word) (m : &Map(cap)) (k : Word) (v : Word) (hm : Inv(cap, *m)) :
      Eq Word (let c = *m; MapInsert(cap, &c, k, v); LenOf(cap, c)) (Grow(GetOf(cap, *m, k), LenOf(cap, *m))) :=
    -- provided: from the model, by LenInsertFrom (HashMapCompose)
    LenInsertFrom(MMap, MapInsert, GetOf, LenOf, Inv, AbsOf, MGet, MLen, MInsert, MInv, InvInsert, AgreeGet, AgreeLen, AgreeInsert, AbsInv, MLenInsert, cap, m, k, v, hm)
  -- FIXED-END H12

  -- FIXED-BEGIN H13
  -- H13: remove takes one from len if get(m, k) ≠ None, and leaves it otherwise.
  def LenRemove (cap : Word) (m : &Map(cap)) (k : Word) (hm : Inv(cap, *m)) :
      Eq Word (let c = *m; MapRemove(cap, &c, k); LenOf(cap, c)) (Shrink(GetOf(cap, *m, k), LenOf(cap, *m))) :=
    -- provided: from the model, by LenRemoveFrom (HashMapCompose)
    LenRemoveFrom(MMap, MapRemove, GetOf, LenOf, Inv, AbsOf, MGet, MLen, MRemove, MInv, InvRemove, AgreeGet, AgreeLen, AgreeRemove, AbsInv, MLenRemove, cap, m, k, hm)
  -- FIXED-END H13

  -- FIXED-BEGIN H14
  -- H14: writing `w` through get_mut(m, k) has the effect of insert(m, k, w) on every get.
  def GetMutGet (cap : Word) (m : &Map(cap)) (k : Word) (w : Word) (k2 : Word) (hm : Inv(cap, *m))
      (hk : IsSome(GetOf(cap, *m, k))) :
      Eq Opt (let c = *m; let r = MapGetMut(cap, &c, k, hk); *r := w; GetOf(cap, c, k2))
        (let c = *m; MapInsert(cap, &c, k, w); GetOf(cap, c, k2)) :=
    -- provided: from the model, by GetMutGetFrom (HashMapCompose)
    GetMutGetFrom(MMap, MapInsert, GetOf, MapGetMut, Inv, AbsOf, MGet, MInsert, MWrite, MInv, InvInsert, GetMutInv, AgreeGet, AgreeInsert, AgreeWrite, AbsInv, MWriteGet, cap, m, k, w, k2, hm, hk)
  -- FIXED-END H14

  -- FIXED-BEGIN H15
  -- H15: ... and on len.
  def GetMutLen (cap : Word) (m : &Map(cap)) (k : Word) (w : Word) (hm : Inv(cap, *m))
      (hk : IsSome(GetOf(cap, *m, k))) :
      Eq Word (let c = *m; let r = MapGetMut(cap, &c, k, hk); *r := w; LenOf(cap, c))
        (let c = *m; MapInsert(cap, &c, k, w); LenOf(cap, c)) :=
    -- provided: from the model, by GetMutLenFrom (HashMapCompose)
    GetMutLenFrom(MMap, MapInsert, GetOf, LenOf, MapGetMut, Inv, AbsOf, MGet, MLen, MInsert, MWrite, MInv, InvInsert, GetMutInv, AgreeGet, AgreeLen, AgreeInsert, AgreeWrite, AbsInv, MWriteLen, cap, m, k, w, hm, hk)
  -- FIXED-END H15

-- FIXED-BEGIN tests
}

/-! ## The tests (FIXED, SPEC §6)

Each test starts from `MapNew(cap, refl)`, runs a sequence of operations on that one map, and
records each operation's result and the length after it in a `Trace`; the test is accepted
when the trace is the expected one. A write through get_mut records only the length. The
last test must be rejected: its expected result is wrong. -/

ochr HashMapTests uses HashMapSolution {
  inductive Trace := TEnd | TOp(res : Opt, len : Word, rest : Trace) | TWrite(len : Word, rest : Trace)

  -- BEGIN GENERATED TESTS
  -- scripted: 51 ops on new(4)
  def Test_scripted : Id Trace (let m = MapNew(W(4), refl); let r0 = MapGet(W(4), &m, W(0)); let l0 = MapLen(W(4), &m); let r1 = MapRemove(W(4), &m, W(3)); let l1 = MapLen(W(4), &m); let r2 = MapInsert(W(4), &m, W(1), W(10)); let l2 = MapLen(W(4), &m); let r3 = MapInsert(W(4), &m, W(5), W(50)); let l3 = MapLen(W(4), &m); let r4 = MapInsert(W(4), &m, W(9), W(90)); let l4 = MapLen(W(4), &m); let r5 = MapGet(W(4), &m, W(1)); let l5 = MapLen(W(4), &m); let r6 = MapGet(W(4), &m, W(5)); let l6 = MapLen(W(4), &m); let r7 = MapGet(W(4), &m, W(9)); let l7 = MapLen(W(4), &m); let r8 = MapGet(W(4), &m, W(13)); let l8 = MapLen(W(4), &m); let r9 = MapGet(W(4), &m, W(2)); let l9 = MapLen(W(4), &m); let r10 = MapInsert(W(4), &m, W(5), W(55)); let l10 = MapLen(W(4), &m); let r11 = MapGet(W(4), &m, W(5)); let l11 = MapLen(W(4), &m); let r12 = MapGet(W(4), &m, W(1)); let l12 = MapLen(W(4), &m); let r13 = MapGet(W(4), &m, W(9)); let l13 = MapLen(W(4), &m); let r14 = MapInsert(W(4), &m, W(0), W(0)); let l14 = MapLen(W(4), &m); let r15 = MapInsert(W(4), &m, W(4), W(40)); let l15 = MapLen(W(4), &m); let r16 = MapGet(W(4), &m, W(0)); let l16 = MapLen(W(4), &m); let r17 = MapRemove(W(4), &m, W(5)); let l17 = MapLen(W(4), &m); let r18 = MapGet(W(4), &m, W(5)); let l18 = MapLen(W(4), &m); let r19 = MapGet(W(4), &m, W(1)); let l19 = MapLen(W(4), &m); let r20 = MapGet(W(4), &m, W(9)); let l20 = MapLen(W(4), &m); let r21 = MapRemove(W(4), &m, W(5)); let l21 = MapLen(W(4), &m); let r22 = MapRemove(W(4), &m, W(13)); let l22 = MapLen(W(4), &m); let r23 = MapRemove(W(4), &m, W(1)); let l23 = MapLen(W(4), &m); let r24 = MapRemove(W(4), &m, W(9)); let l24 = MapLen(W(4), &m); let r25 = MapGet(W(4), &m, W(9)); let l25 = MapLen(W(4), &m); let p26 = MapGetMut(W(4), &m, W(4), refl); *p26 := W(44); let l26 = MapLen(W(4), &m); let r27 = MapGet(W(4), &m, W(4)); let l27 = MapLen(W(4), &m); let r28 = MapGet(W(4), &m, W(0)); let l28 = MapLen(W(4), &m); let p29 = MapGetMut(W(4), &m, W(0), refl); *p29 := W(7); let l29 = MapLen(W(4), &m); let r30 = MapGet(W(4), &m, W(0)); let l30 = MapLen(W(4), &m); let r31 = MapGet(W(4), &m, W(4)); let l31 = MapLen(W(4), &m); let r32 = MapInsert(W(4), &m, W(4), W(45)); let l32 = MapLen(W(4), &m); let r33 = MapInsert(W(4), &m, W(1), W(11)); let l33 = MapLen(W(4), &m); let r34 = MapGet(W(4), &m, W(1)); let l34 = MapLen(W(4), &m); let r35 = MapInsert(W(4), &m, W(7), W(70)); let l35 = MapLen(W(4), &m); let r36 = MapInsert(W(4), &m, W(3), W(30)); let l36 = MapLen(W(4), &m); let r37 = MapInsert(W(4), &m, W(11), W(99)); let l37 = MapLen(W(4), &m); let p38 = MapGetMut(W(4), &m, W(3), refl); *p38 := W(33); let l38 = MapLen(W(4), &m); let r39 = MapGet(W(4), &m, W(7)); let l39 = MapLen(W(4), &m); let r40 = MapGet(W(4), &m, W(3)); let l40 = MapLen(W(4), &m); let r41 = MapGet(W(4), &m, W(11)); let l41 = MapLen(W(4), &m); let r42 = MapRemove(W(4), &m, W(11)); let l42 = MapLen(W(4), &m); let r43 = MapGet(W(4), &m, W(3)); let l43 = MapLen(W(4), &m); let r44 = MapRemove(W(4), &m, W(0)); let l44 = MapLen(W(4), &m); let r45 = MapGet(W(4), &m, W(4)); let l45 = MapLen(W(4), &m); let r46 = MapRemove(W(4), &m, W(4)); let l46 = MapLen(W(4), &m); let r47 = MapGet(W(4), &m, W(0)); let l47 = MapLen(W(4), &m); let r48 = MapGet(W(4), &m, W(4)); let l48 = MapLen(W(4), &m); let r49 = MapInsert(W(4), &m, W(0), W(1)); let l49 = MapLen(W(4), &m); let r50 = MapGet(W(4), &m, W(0)); let l50 = MapLen(W(4), &m); TOp(r0, l0, TOp(r1, l1, TOp(r2, l2, TOp(r3, l3, TOp(r4, l4, TOp(r5, l5, TOp(r6, l6, TOp(r7, l7, TOp(r8, l8, TOp(r9, l9, TOp(r10, l10, TOp(r11, l11, TOp(r12, l12, TOp(r13, l13, TOp(r14, l14, TOp(r15, l15, TOp(r16, l16, TOp(r17, l17, TOp(r18, l18, TOp(r19, l19, TOp(r20, l20, TOp(r21, l21, TOp(r22, l22, TOp(r23, l23, TOp(r24, l24, TOp(r25, l25, TWrite(l26, TOp(r27, l27, TOp(r28, l28, TWrite(l29, TOp(r30, l30, TOp(r31, l31, TOp(r32, l32, TOp(r33, l33, TOp(r34, l34, TOp(r35, l35, TOp(r36, l36, TOp(r37, l37, TWrite(l38, TOp(r39, l39, TOp(r40, l40, TOp(r41, l41, TOp(r42, l42, TOp(r43, l43, TOp(r44, l44, TOp(r45, l45, TOp(r46, l46, TOp(r47, l47, TOp(r48, l48, TOp(r49, l49, TOp(r50, l50, TEnd)))))))))))))))))))))))))))))))))))))))))))))))))))) (TOp(None, W(0), TOp(None, W(0), TOp(None, W(1), TOp(None, W(2), TOp(None, W(3), TOp(Some(W(10)), W(3), TOp(Some(W(50)), W(3), TOp(Some(W(90)), W(3), TOp(None, W(3), TOp(None, W(3), TOp(Some(W(50)), W(3), TOp(Some(W(55)), W(3), TOp(Some(W(10)), W(3), TOp(Some(W(90)), W(3), TOp(None, W(4), TOp(None, W(5), TOp(Some(W(0)), W(5), TOp(Some(W(55)), W(4), TOp(None, W(4), TOp(Some(W(10)), W(4), TOp(Some(W(90)), W(4), TOp(None, W(4), TOp(None, W(4), TOp(Some(W(10)), W(3), TOp(Some(W(90)), W(2), TOp(None, W(2), TWrite(W(2), TOp(Some(W(44)), W(2), TOp(Some(W(0)), W(2), TWrite(W(2), TOp(Some(W(7)), W(2), TOp(Some(W(44)), W(2), TOp(Some(W(44)), W(2), TOp(None, W(3), TOp(Some(W(11)), W(3), TOp(None, W(4), TOp(None, W(5), TOp(None, W(6), TWrite(W(6), TOp(Some(W(70)), W(6), TOp(Some(W(33)), W(6), TOp(Some(W(99)), W(6), TOp(Some(W(99)), W(5), TOp(Some(W(33)), W(5), TOp(Some(W(7)), W(4), TOp(Some(W(45)), W(4), TOp(Some(W(45)), W(3), TOp(None, W(3), TOp(None, W(3), TOp(None, W(4), TOp(Some(W(1)), W(4), TEnd)))))))))))))))))))))))))))))))))))))))))))))))))))) := refl
  -- random-cap1: 50 ops on new(1)
  def Test_random_cap1 : Id Trace (let m = MapNew(W(1), refl); let r0 = MapRemove(W(1), &m, W(2)); let l0 = MapLen(W(1), &m); let r1 = MapInsert(W(1), &m, W(2), W(27)); let l1 = MapLen(W(1), &m); let r2 = MapRemove(W(1), &m, W(2)); let l2 = MapLen(W(1), &m); let r3 = MapGet(W(1), &m, W(1)); let l3 = MapLen(W(1), &m); let r4 = MapGet(W(1), &m, W(3)); let l4 = MapLen(W(1), &m); let r5 = MapInsert(W(1), &m, W(0), W(38)); let l5 = MapLen(W(1), &m); let r6 = MapInsert(W(1), &m, W(7), W(65)); let l6 = MapLen(W(1), &m); let r7 = MapInsert(W(1), &m, W(4), W(20)); let l7 = MapLen(W(1), &m); let r8 = MapGet(W(1), &m, W(4)); let l8 = MapLen(W(1), &m); let p9 = MapGetMut(W(1), &m, W(7), refl); *p9 := W(79); let l9 = MapLen(W(1), &m); let r10 = MapRemove(W(1), &m, W(2)); let l10 = MapLen(W(1), &m); let r11 = MapInsert(W(1), &m, W(7), W(78)); let l11 = MapLen(W(1), &m); let r12 = MapRemove(W(1), &m, W(1)); let l12 = MapLen(W(1), &m); let r13 = MapGet(W(1), &m, W(7)); let l13 = MapLen(W(1), &m); let r14 = MapGet(W(1), &m, W(7)); let l14 = MapLen(W(1), &m); let p15 = MapGetMut(W(1), &m, W(0), refl); *p15 := W(41); let l15 = MapLen(W(1), &m); let r16 = MapGet(W(1), &m, W(5)); let l16 = MapLen(W(1), &m); let r17 = MapInsert(W(1), &m, W(0), W(8)); let l17 = MapLen(W(1), &m); let r18 = MapRemove(W(1), &m, W(6)); let l18 = MapLen(W(1), &m); let r19 = MapInsert(W(1), &m, W(2), W(8)); let l19 = MapLen(W(1), &m); let r20 = MapGet(W(1), &m, W(4)); let l20 = MapLen(W(1), &m); let r21 = MapGet(W(1), &m, W(7)); let l21 = MapLen(W(1), &m); let r22 = MapRemove(W(1), &m, W(6)); let l22 = MapLen(W(1), &m); let p23 = MapGetMut(W(1), &m, W(4), refl); *p23 := W(86); let l23 = MapLen(W(1), &m); let r24 = MapGet(W(1), &m, W(5)); let l24 = MapLen(W(1), &m); let r25 = MapInsert(W(1), &m, W(1), W(19)); let l25 = MapLen(W(1), &m); let r26 = MapInsert(W(1), &m, W(2), W(12)); let l26 = MapLen(W(1), &m); let r27 = MapInsert(W(1), &m, W(7), W(81)); let l27 = MapLen(W(1), &m); let r28 = MapGet(W(1), &m, W(5)); let l28 = MapLen(W(1), &m); let r29 = MapRemove(W(1), &m, W(6)); let l29 = MapLen(W(1), &m); let r30 = MapGet(W(1), &m, W(2)); let l30 = MapLen(W(1), &m); let r31 = MapGet(W(1), &m, W(0)); let l31 = MapLen(W(1), &m); let r32 = MapInsert(W(1), &m, W(4), W(0)); let l32 = MapLen(W(1), &m); let r33 = MapInsert(W(1), &m, W(7), W(77)); let l33 = MapLen(W(1), &m); let r34 = MapInsert(W(1), &m, W(5), W(85)); let l34 = MapLen(W(1), &m); let r35 = MapInsert(W(1), &m, W(0), W(0)); let l35 = MapLen(W(1), &m); let r36 = MapInsert(W(1), &m, W(3), W(71)); let l36 = MapLen(W(1), &m); let r37 = MapInsert(W(1), &m, W(0), W(37)); let l37 = MapLen(W(1), &m); let p38 = MapGetMut(W(1), &m, W(4), refl); *p38 := W(85); let l38 = MapLen(W(1), &m); let p39 = MapGetMut(W(1), &m, W(2), refl); *p39 := W(26); let l39 = MapLen(W(1), &m); let r40 = MapInsert(W(1), &m, W(3), W(5)); let l40 = MapLen(W(1), &m); let r41 = MapInsert(W(1), &m, W(0), W(37)); let l41 = MapLen(W(1), &m); let r42 = MapRemove(W(1), &m, W(6)); let l42 = MapLen(W(1), &m); let r43 = MapInsert(W(1), &m, W(0), W(71)); let l43 = MapLen(W(1), &m); let r44 = MapInsert(W(1), &m, W(5), W(9)); let l44 = MapLen(W(1), &m); let r45 = MapInsert(W(1), &m, W(2), W(42)); let l45 = MapLen(W(1), &m); let r46 = MapInsert(W(1), &m, W(0), W(11)); let l46 = MapLen(W(1), &m); let r47 = MapInsert(W(1), &m, W(1), W(25)); let l47 = MapLen(W(1), &m); let r48 = MapGet(W(1), &m, W(0)); let l48 = MapLen(W(1), &m); let p49 = MapGetMut(W(1), &m, W(0), refl); *p49 := W(84); let l49 = MapLen(W(1), &m); TOp(r0, l0, TOp(r1, l1, TOp(r2, l2, TOp(r3, l3, TOp(r4, l4, TOp(r5, l5, TOp(r6, l6, TOp(r7, l7, TOp(r8, l8, TWrite(l9, TOp(r10, l10, TOp(r11, l11, TOp(r12, l12, TOp(r13, l13, TOp(r14, l14, TWrite(l15, TOp(r16, l16, TOp(r17, l17, TOp(r18, l18, TOp(r19, l19, TOp(r20, l20, TOp(r21, l21, TOp(r22, l22, TWrite(l23, TOp(r24, l24, TOp(r25, l25, TOp(r26, l26, TOp(r27, l27, TOp(r28, l28, TOp(r29, l29, TOp(r30, l30, TOp(r31, l31, TOp(r32, l32, TOp(r33, l33, TOp(r34, l34, TOp(r35, l35, TOp(r36, l36, TOp(r37, l37, TWrite(l38, TWrite(l39, TOp(r40, l40, TOp(r41, l41, TOp(r42, l42, TOp(r43, l43, TOp(r44, l44, TOp(r45, l45, TOp(r46, l46, TOp(r47, l47, TOp(r48, l48, TWrite(l49, TEnd))))))))))))))))))))))))))))))))))))))))))))))))))) (TOp(None, W(0), TOp(None, W(1), TOp(Some(W(27)), W(0), TOp(None, W(0), TOp(None, W(0), TOp(None, W(1), TOp(None, W(2), TOp(None, W(3), TOp(Some(W(20)), W(3), TWrite(W(3), TOp(None, W(3), TOp(Some(W(79)), W(3), TOp(None, W(3), TOp(Some(W(78)), W(3), TOp(Some(W(78)), W(3), TWrite(W(3), TOp(None, W(3), TOp(Some(W(41)), W(3), TOp(None, W(3), TOp(None, W(4), TOp(Some(W(20)), W(4), TOp(Some(W(78)), W(4), TOp(None, W(4), TWrite(W(4), TOp(None, W(4), TOp(None, W(5), TOp(Some(W(8)), W(5), TOp(Some(W(78)), W(5), TOp(None, W(5), TOp(None, W(5), TOp(Some(W(12)), W(5), TOp(Some(W(8)), W(5), TOp(Some(W(86)), W(5), TOp(Some(W(81)), W(5), TOp(None, W(6), TOp(Some(W(8)), W(6), TOp(None, W(7), TOp(Some(W(0)), W(7), TWrite(W(7), TWrite(W(7), TOp(Some(W(71)), W(7), TOp(Some(W(37)), W(7), TOp(None, W(7), TOp(Some(W(37)), W(7), TOp(Some(W(85)), W(7), TOp(Some(W(26)), W(7), TOp(Some(W(71)), W(7), TOp(Some(W(19)), W(7), TOp(Some(W(11)), W(7), TWrite(W(7), TEnd))))))))))))))))))))))))))))))))))))))))))))))))))) := refl
  -- random-cap3: 50 ops on new(3)
  def Test_random_cap3 : Id Trace (let m = MapNew(W(3), refl); let r0 = MapInsert(W(3), &m, W(6), W(48)); let l0 = MapLen(W(3), &m); let r1 = MapInsert(W(3), &m, W(2), W(20)); let l1 = MapLen(W(3), &m); let r2 = MapInsert(W(3), &m, W(3), W(70)); let l2 = MapLen(W(3), &m); let r3 = MapRemove(W(3), &m, W(11)); let l3 = MapLen(W(3), &m); let r4 = MapInsert(W(3), &m, W(11), W(55)); let l4 = MapLen(W(3), &m); let r5 = MapInsert(W(3), &m, W(5), W(53)); let l5 = MapLen(W(3), &m); let p6 = MapGetMut(W(3), &m, W(6), refl); *p6 := W(36); let l6 = MapLen(W(3), &m); let r7 = MapInsert(W(3), &m, W(5), W(2)); let l7 = MapLen(W(3), &m); let r8 = MapGet(W(3), &m, W(10)); let l8 = MapLen(W(3), &m); let r9 = MapRemove(W(3), &m, W(5)); let l9 = MapLen(W(3), &m); let r10 = MapInsert(W(3), &m, W(1), W(97)); let l10 = MapLen(W(3), &m); let r11 = MapInsert(W(3), &m, W(0), W(57)); let l11 = MapLen(W(3), &m); let r12 = MapInsert(W(3), &m, W(6), W(18)); let l12 = MapLen(W(3), &m); let r13 = MapGet(W(3), &m, W(3)); let l13 = MapLen(W(3), &m); let r14 = MapInsert(W(3), &m, W(2), W(42)); let l14 = MapLen(W(3), &m); let r15 = MapRemove(W(3), &m, W(0)); let l15 = MapLen(W(3), &m); let r16 = MapRemove(W(3), &m, W(0)); let l16 = MapLen(W(3), &m); let r17 = MapInsert(W(3), &m, W(3), W(18)); let l17 = MapLen(W(3), &m); let r18 = MapInsert(W(3), &m, W(7), W(12)); let l18 = MapLen(W(3), &m); let p19 = MapGetMut(W(3), &m, W(6), refl); *p19 := W(40); let l19 = MapLen(W(3), &m); let p20 = MapGetMut(W(3), &m, W(2), refl); *p20 := W(53); let l20 = MapLen(W(3), &m); let p21 = MapGetMut(W(3), &m, W(3), refl); *p21 := W(31); let l21 = MapLen(W(3), &m); let r22 = MapGet(W(3), &m, W(7)); let l22 = MapLen(W(3), &m); let r23 = MapInsert(W(3), &m, W(9), W(60)); let l23 = MapLen(W(3), &m); let r24 = MapInsert(W(3), &m, W(8), W(83)); let l24 = MapLen(W(3), &m); let r25 = MapInsert(W(3), &m, W(7), W(66)); let l25 = MapLen(W(3), &m); let r26 = MapGet(W(3), &m, W(11)); let l26 = MapLen(W(3), &m); let r27 = MapRemove(W(3), &m, W(8)); let l27 = MapLen(W(3), &m); let r28 = MapInsert(W(3), &m, W(11), W(32)); let l28 = MapLen(W(3), &m); let r29 = MapInsert(W(3), &m, W(8), W(77)); let l29 = MapLen(W(3), &m); let r30 = MapInsert(W(3), &m, W(10), W(73)); let l30 = MapLen(W(3), &m); let r31 = MapRemove(W(3), &m, W(0)); let l31 = MapLen(W(3), &m); let r32 = MapGet(W(3), &m, W(11)); let l32 = MapLen(W(3), &m); let r33 = MapGet(W(3), &m, W(7)); let l33 = MapLen(W(3), &m); let r34 = MapGet(W(3), &m, W(4)); let l34 = MapLen(W(3), &m); let r35 = MapGet(W(3), &m, W(2)); let l35 = MapLen(W(3), &m); let r36 = MapInsert(W(3), &m, W(2), W(53)); let l36 = MapLen(W(3), &m); let r37 = MapGet(W(3), &m, W(2)); let l37 = MapLen(W(3), &m); let r38 = MapInsert(W(3), &m, W(4), W(30)); let l38 = MapLen(W(3), &m); let r39 = MapRemove(W(3), &m, W(11)); let l39 = MapLen(W(3), &m); let r40 = MapRemove(W(3), &m, W(0)); let l40 = MapLen(W(3), &m); let r41 = MapInsert(W(3), &m, W(0), W(15)); let l41 = MapLen(W(3), &m); let r42 = MapInsert(W(3), &m, W(1), W(20)); let l42 = MapLen(W(3), &m); let r43 = MapInsert(W(3), &m, W(10), W(20)); let l43 = MapLen(W(3), &m); let r44 = MapInsert(W(3), &m, W(5), W(90)); let l44 = MapLen(W(3), &m); let r45 = MapRemove(W(3), &m, W(7)); let l45 = MapLen(W(3), &m); let p46 = MapGetMut(W(3), &m, W(4), refl); *p46 := W(40); let l46 = MapLen(W(3), &m); let r47 = MapGet(W(3), &m, W(11)); let l47 = MapLen(W(3), &m); let r48 = MapInsert(W(3), &m, W(3), W(75)); let l48 = MapLen(W(3), &m); let r49 = MapInsert(W(3), &m, W(0), W(29)); let l49 = MapLen(W(3), &m); TOp(r0, l0, TOp(r1, l1, TOp(r2, l2, TOp(r3, l3, TOp(r4, l4, TOp(r5, l5, TWrite(l6, TOp(r7, l7, TOp(r8, l8, TOp(r9, l9, TOp(r10, l10, TOp(r11, l11, TOp(r12, l12, TOp(r13, l13, TOp(r14, l14, TOp(r15, l15, TOp(r16, l16, TOp(r17, l17, TOp(r18, l18, TWrite(l19, TWrite(l20, TWrite(l21, TOp(r22, l22, TOp(r23, l23, TOp(r24, l24, TOp(r25, l25, TOp(r26, l26, TOp(r27, l27, TOp(r28, l28, TOp(r29, l29, TOp(r30, l30, TOp(r31, l31, TOp(r32, l32, TOp(r33, l33, TOp(r34, l34, TOp(r35, l35, TOp(r36, l36, TOp(r37, l37, TOp(r38, l38, TOp(r39, l39, TOp(r40, l40, TOp(r41, l41, TOp(r42, l42, TOp(r43, l43, TOp(r44, l44, TOp(r45, l45, TWrite(l46, TOp(r47, l47, TOp(r48, l48, TOp(r49, l49, TEnd))))))))))))))))))))))))))))))))))))))))))))))))))) (TOp(None, W(1), TOp(None, W(2), TOp(None, W(3), TOp(None, W(3), TOp(None, W(4), TOp(None, W(5), TWrite(W(5), TOp(Some(W(53)), W(5), TOp(None, W(5), TOp(Some(W(2)), W(4), TOp(None, W(5), TOp(None, W(6), TOp(Some(W(36)), W(6), TOp(Some(W(70)), W(6), TOp(Some(W(20)), W(6), TOp(Some(W(57)), W(5), TOp(None, W(5), TOp(Some(W(70)), W(5), TOp(None, W(6), TWrite(W(6), TWrite(W(6), TWrite(W(6), TOp(Some(W(12)), W(6), TOp(None, W(7), TOp(None, W(8), TOp(Some(W(12)), W(8), TOp(Some(W(55)), W(8), TOp(Some(W(83)), W(7), TOp(Some(W(55)), W(7), TOp(None, W(8), TOp(None, W(9), TOp(None, W(9), TOp(Some(W(32)), W(9), TOp(Some(W(66)), W(9), TOp(None, W(9), TOp(Some(W(53)), W(9), TOp(Some(W(53)), W(9), TOp(Some(W(53)), W(9), TOp(None, W(10), TOp(Some(W(32)), W(9), TOp(None, W(9), TOp(None, W(10), TOp(Some(W(97)), W(10), TOp(Some(W(73)), W(10), TOp(None, W(11), TOp(Some(W(66)), W(10), TWrite(W(10), TOp(None, W(10), TOp(Some(W(31)), W(10), TOp(Some(W(15)), W(10), TEnd))))))))))))))))))))))))))))))))))))))))))))))))))) := refl
  -- random-cap4: 50 ops on new(4)
  def Test_random_cap4 : Id Trace (let m = MapNew(W(4), refl); let r0 = MapInsert(W(4), &m, W(3), W(6)); let l0 = MapLen(W(4), &m); let p1 = MapGetMut(W(4), &m, W(3), refl); *p1 := W(19); let l1 = MapLen(W(4), &m); let r2 = MapInsert(W(4), &m, W(1), W(39)); let l2 = MapLen(W(4), &m); let p3 = MapGetMut(W(4), &m, W(1), refl); *p3 := W(3); let l3 = MapLen(W(4), &m); let p4 = MapGetMut(W(4), &m, W(3), refl); *p4 := W(73); let l4 = MapLen(W(4), &m); let r5 = MapGet(W(4), &m, W(1)); let l5 = MapLen(W(4), &m); let r6 = MapInsert(W(4), &m, W(12), W(39)); let l6 = MapLen(W(4), &m); let r7 = MapInsert(W(4), &m, W(3), W(19)); let l7 = MapLen(W(4), &m); let r8 = MapInsert(W(4), &m, W(7), W(84)); let l8 = MapLen(W(4), &m); let r9 = MapGet(W(4), &m, W(12)); let l9 = MapLen(W(4), &m); let r10 = MapRemove(W(4), &m, W(2)); let l10 = MapLen(W(4), &m); let r11 = MapInsert(W(4), &m, W(0), W(26)); let l11 = MapLen(W(4), &m); let r12 = MapInsert(W(4), &m, W(2), W(10)); let l12 = MapLen(W(4), &m); let r13 = MapInsert(W(4), &m, W(5), W(40)); let l13 = MapLen(W(4), &m); let p14 = MapGetMut(W(4), &m, W(5), refl); *p14 := W(86); let l14 = MapLen(W(4), &m); let r15 = MapGet(W(4), &m, W(4)); let l15 = MapLen(W(4), &m); let r16 = MapGet(W(4), &m, W(12)); let l16 = MapLen(W(4), &m); let r17 = MapInsert(W(4), &m, W(1), W(59)); let l17 = MapLen(W(4), &m); let r18 = MapGet(W(4), &m, W(4)); let l18 = MapLen(W(4), &m); let r19 = MapGet(W(4), &m, W(8)); let l19 = MapLen(W(4), &m); let r20 = MapRemove(W(4), &m, W(15)); let l20 = MapLen(W(4), &m); let r21 = MapInsert(W(4), &m, W(15), W(68)); let l21 = MapLen(W(4), &m); let r22 = MapInsert(W(4), &m, W(11), W(80)); let l22 = MapLen(W(4), &m); let r23 = MapGet(W(4), &m, W(10)); let l23 = MapLen(W(4), &m); let r24 = MapRemove(W(4), &m, W(4)); let l24 = MapLen(W(4), &m); let r25 = MapInsert(W(4), &m, W(13), W(20)); let l25 = MapLen(W(4), &m); let r26 = MapInsert(W(4), &m, W(9), W(7)); let l26 = MapLen(W(4), &m); let p27 = MapGetMut(W(4), &m, W(5), refl); *p27 := W(30); let l27 = MapLen(W(4), &m); let r28 = MapGet(W(4), &m, W(1)); let l28 = MapLen(W(4), &m); let r29 = MapRemove(W(4), &m, W(4)); let l29 = MapLen(W(4), &m); let r30 = MapRemove(W(4), &m, W(10)); let l30 = MapLen(W(4), &m); let r31 = MapGet(W(4), &m, W(13)); let l31 = MapLen(W(4), &m); let r32 = MapRemove(W(4), &m, W(9)); let l32 = MapLen(W(4), &m); let p33 = MapGetMut(W(4), &m, W(7), refl); *p33 := W(75); let l33 = MapLen(W(4), &m); let r34 = MapGet(W(4), &m, W(8)); let l34 = MapLen(W(4), &m); let r35 = MapRemove(W(4), &m, W(11)); let l35 = MapLen(W(4), &m); let p36 = MapGetMut(W(4), &m, W(1), refl); *p36 := W(32); let l36 = MapLen(W(4), &m); let r37 = MapGet(W(4), &m, W(6)); let l37 = MapLen(W(4), &m); let r38 = MapGet(W(4), &m, W(11)); let l38 = MapLen(W(4), &m); let r39 = MapGet(W(4), &m, W(4)); let l39 = MapLen(W(4), &m); let r40 = MapRemove(W(4), &m, W(6)); let l40 = MapLen(W(4), &m); let r41 = MapInsert(W(4), &m, W(8), W(82)); let l41 = MapLen(W(4), &m); let r42 = MapInsert(W(4), &m, W(3), W(86)); let l42 = MapLen(W(4), &m); let r43 = MapGet(W(4), &m, W(12)); let l43 = MapLen(W(4), &m); let p44 = MapGetMut(W(4), &m, W(7), refl); *p44 := W(17); let l44 = MapLen(W(4), &m); let r45 = MapGet(W(4), &m, W(10)); let l45 = MapLen(W(4), &m); let r46 = MapGet(W(4), &m, W(12)); let l46 = MapLen(W(4), &m); let r47 = MapRemove(W(4), &m, W(4)); let l47 = MapLen(W(4), &m); let r48 = MapInsert(W(4), &m, W(7), W(79)); let l48 = MapLen(W(4), &m); let r49 = MapRemove(W(4), &m, W(2)); let l49 = MapLen(W(4), &m); TOp(r0, l0, TWrite(l1, TOp(r2, l2, TWrite(l3, TWrite(l4, TOp(r5, l5, TOp(r6, l6, TOp(r7, l7, TOp(r8, l8, TOp(r9, l9, TOp(r10, l10, TOp(r11, l11, TOp(r12, l12, TOp(r13, l13, TWrite(l14, TOp(r15, l15, TOp(r16, l16, TOp(r17, l17, TOp(r18, l18, TOp(r19, l19, TOp(r20, l20, TOp(r21, l21, TOp(r22, l22, TOp(r23, l23, TOp(r24, l24, TOp(r25, l25, TOp(r26, l26, TWrite(l27, TOp(r28, l28, TOp(r29, l29, TOp(r30, l30, TOp(r31, l31, TOp(r32, l32, TWrite(l33, TOp(r34, l34, TOp(r35, l35, TWrite(l36, TOp(r37, l37, TOp(r38, l38, TOp(r39, l39, TOp(r40, l40, TOp(r41, l41, TOp(r42, l42, TOp(r43, l43, TWrite(l44, TOp(r45, l45, TOp(r46, l46, TOp(r47, l47, TOp(r48, l48, TOp(r49, l49, TEnd))))))))))))))))))))))))))))))))))))))))))))))))))) (TOp(None, W(1), TWrite(W(1), TOp(None, W(2), TWrite(W(2), TWrite(W(2), TOp(Some(W(3)), W(2), TOp(None, W(3), TOp(Some(W(73)), W(3), TOp(None, W(4), TOp(Some(W(39)), W(4), TOp(None, W(4), TOp(None, W(5), TOp(None, W(6), TOp(None, W(7), TWrite(W(7), TOp(None, W(7), TOp(Some(W(39)), W(7), TOp(Some(W(3)), W(7), TOp(None, W(7), TOp(None, W(7), TOp(None, W(7), TOp(None, W(8), TOp(None, W(9), TOp(None, W(9), TOp(None, W(9), TOp(None, W(10), TOp(None, W(11), TWrite(W(11), TOp(Some(W(59)), W(11), TOp(None, W(11), TOp(None, W(11), TOp(Some(W(20)), W(11), TOp(Some(W(7)), W(10), TWrite(W(10), TOp(None, W(10), TOp(Some(W(80)), W(9), TWrite(W(9), TOp(None, W(9), TOp(None, W(9), TOp(None, W(9), TOp(None, W(9), TOp(None, W(10), TOp(Some(W(19)), W(10), TOp(Some(W(39)), W(10), TWrite(W(10), TOp(None, W(10), TOp(Some(W(39)), W(10), TOp(None, W(10), TOp(Some(W(17)), W(10), TOp(Some(W(10)), W(9), TEnd))))))))))))))))))))))))))))))))))))))))))))))))))) := refl
  -- random-cap7: 50 ops on new(7)
  def Test_random_cap7 : Id Trace (let m = MapNew(W(7), refl); let r0 = MapInsert(W(7), &m, W(10), W(82)); let l0 = MapLen(W(7), &m); let r1 = MapInsert(W(7), &m, W(15), W(33)); let l1 = MapLen(W(7), &m); let r2 = MapInsert(W(7), &m, W(0), W(14)); let l2 = MapLen(W(7), &m); let r3 = MapInsert(W(7), &m, W(8), W(60)); let l3 = MapLen(W(7), &m); let r4 = MapGet(W(7), &m, W(4)); let l4 = MapLen(W(7), &m); let p5 = MapGetMut(W(7), &m, W(0), refl); *p5 := W(39); let l5 = MapLen(W(7), &m); let r6 = MapGet(W(7), &m, W(3)); let l6 = MapLen(W(7), &m); let r7 = MapInsert(W(7), &m, W(19), W(57)); let l7 = MapLen(W(7), &m); let r8 = MapRemove(W(7), &m, W(15)); let l8 = MapLen(W(7), &m); let r9 = MapInsert(W(7), &m, W(13), W(82)); let l9 = MapLen(W(7), &m); let r10 = MapRemove(W(7), &m, W(18)); let l10 = MapLen(W(7), &m); let r11 = MapRemove(W(7), &m, W(0)); let l11 = MapLen(W(7), &m); let r12 = MapGet(W(7), &m, W(13)); let l12 = MapLen(W(7), &m); let r13 = MapInsert(W(7), &m, W(5), W(37)); let l13 = MapLen(W(7), &m); let r14 = MapInsert(W(7), &m, W(7), W(48)); let l14 = MapLen(W(7), &m); let r15 = MapRemove(W(7), &m, W(7)); let l15 = MapLen(W(7), &m); let r16 = MapInsert(W(7), &m, W(23), W(31)); let l16 = MapLen(W(7), &m); let p17 = MapGetMut(W(7), &m, W(19), refl); *p17 := W(27); let l17 = MapLen(W(7), &m); let r18 = MapGet(W(7), &m, W(1)); let l18 = MapLen(W(7), &m); let r19 = MapRemove(W(7), &m, W(3)); let l19 = MapLen(W(7), &m); let r20 = MapInsert(W(7), &m, W(11), W(18)); let l20 = MapLen(W(7), &m); let r21 = MapInsert(W(7), &m, W(5), W(67)); let l21 = MapLen(W(7), &m); let r22 = MapInsert(W(7), &m, W(20), W(96)); let l22 = MapLen(W(7), &m); let r23 = MapGet(W(7), &m, W(12)); let l23 = MapLen(W(7), &m); let r24 = MapGet(W(7), &m, W(15)); let l24 = MapLen(W(7), &m); let r25 = MapGet(W(7), &m, W(5)); let l25 = MapLen(W(7), &m); let r26 = MapRemove(W(7), &m, W(9)); let l26 = MapLen(W(7), &m); let r27 = MapInsert(W(7), &m, W(13), W(87)); let l27 = MapLen(W(7), &m); let r28 = MapGet(W(7), &m, W(19)); let l28 = MapLen(W(7), &m); let p29 = MapGetMut(W(7), &m, W(11), refl); *p29 := W(84); let l29 = MapLen(W(7), &m); let r30 = MapGet(W(7), &m, W(16)); let l30 = MapLen(W(7), &m); let r31 = MapInsert(W(7), &m, W(3), W(78)); let l31 = MapLen(W(7), &m); let r32 = MapRemove(W(7), &m, W(4)); let l32 = MapLen(W(7), &m); let p33 = MapGetMut(W(7), &m, W(20), refl); *p33 := W(89); let l33 = MapLen(W(7), &m); let r34 = MapGet(W(7), &m, W(0)); let l34 = MapLen(W(7), &m); let r35 = MapInsert(W(7), &m, W(23), W(28)); let l35 = MapLen(W(7), &m); let r36 = MapInsert(W(7), &m, W(20), W(74)); let l36 = MapLen(W(7), &m); let r37 = MapRemove(W(7), &m, W(5)); let l37 = MapLen(W(7), &m); let r38 = MapInsert(W(7), &m, W(19), W(32)); let l38 = MapLen(W(7), &m); let r39 = MapRemove(W(7), &m, W(9)); let l39 = MapLen(W(7), &m); let r40 = MapInsert(W(7), &m, W(11), W(98)); let l40 = MapLen(W(7), &m); let r41 = MapRemove(W(7), &m, W(13)); let l41 = MapLen(W(7), &m); let r42 = MapRemove(W(7), &m, W(11)); let l42 = MapLen(W(7), &m); let r43 = MapGet(W(7), &m, W(15)); let l43 = MapLen(W(7), &m); let r44 = MapGet(W(7), &m, W(11)); let l44 = MapLen(W(7), &m); let p45 = MapGetMut(W(7), &m, W(3), refl); *p45 := W(16); let l45 = MapLen(W(7), &m); let r46 = MapGet(W(7), &m, W(13)); let l46 = MapLen(W(7), &m); let p47 = MapGetMut(W(7), &m, W(19), refl); *p47 := W(17); let l47 = MapLen(W(7), &m); let r48 = MapGet(W(7), &m, W(5)); let l48 = MapLen(W(7), &m); let r49 = MapRemove(W(7), &m, W(14)); let l49 = MapLen(W(7), &m); TOp(r0, l0, TOp(r1, l1, TOp(r2, l2, TOp(r3, l3, TOp(r4, l4, TWrite(l5, TOp(r6, l6, TOp(r7, l7, TOp(r8, l8, TOp(r9, l9, TOp(r10, l10, TOp(r11, l11, TOp(r12, l12, TOp(r13, l13, TOp(r14, l14, TOp(r15, l15, TOp(r16, l16, TWrite(l17, TOp(r18, l18, TOp(r19, l19, TOp(r20, l20, TOp(r21, l21, TOp(r22, l22, TOp(r23, l23, TOp(r24, l24, TOp(r25, l25, TOp(r26, l26, TOp(r27, l27, TOp(r28, l28, TWrite(l29, TOp(r30, l30, TOp(r31, l31, TOp(r32, l32, TWrite(l33, TOp(r34, l34, TOp(r35, l35, TOp(r36, l36, TOp(r37, l37, TOp(r38, l38, TOp(r39, l39, TOp(r40, l40, TOp(r41, l41, TOp(r42, l42, TOp(r43, l43, TOp(r44, l44, TWrite(l45, TOp(r46, l46, TWrite(l47, TOp(r48, l48, TOp(r49, l49, TEnd))))))))))))))))))))))))))))))))))))))))))))))))))) (TOp(None, W(1), TOp(None, W(2), TOp(None, W(3), TOp(None, W(4), TOp(None, W(4), TWrite(W(4), TOp(None, W(4), TOp(None, W(5), TOp(Some(W(33)), W(4), TOp(None, W(5), TOp(None, W(5), TOp(Some(W(39)), W(4), TOp(Some(W(82)), W(4), TOp(None, W(5), TOp(None, W(6), TOp(Some(W(48)), W(5), TOp(None, W(6), TWrite(W(6), TOp(None, W(6), TOp(None, W(6), TOp(None, W(7), TOp(Some(W(37)), W(7), TOp(None, W(8), TOp(None, W(8), TOp(None, W(8), TOp(Some(W(67)), W(8), TOp(None, W(8), TOp(Some(W(82)), W(8), TOp(Some(W(27)), W(8), TWrite(W(8), TOp(None, W(8), TOp(None, W(9), TOp(None, W(9), TWrite(W(9), TOp(None, W(9), TOp(Some(W(31)), W(9), TOp(Some(W(89)), W(9), TOp(Some(W(67)), W(8), TOp(Some(W(27)), W(8), TOp(None, W(8), TOp(Some(W(84)), W(8), TOp(Some(W(87)), W(7), TOp(Some(W(98)), W(6), TOp(None, W(6), TOp(None, W(6), TWrite(W(6), TOp(None, W(6), TWrite(W(6), TOp(None, W(6), TOp(None, W(6), TEnd))))))))))))))))))))))))))))))))))))))))))))))))))) := refl
  -- must be rejected: a fresh map's first insert returns None, not Some
  reject def TestReject_insert : Id Trace (let m = MapNew(W(4), refl); let r0 = MapInsert(W(4), &m, W(1), W(10)); let l0 = MapLen(W(4), &m); TOp(r0, l0, TEnd)) (TOp(Some(W(11)), W(1), TEnd)) := refl
  -- END GENERATED TESTS
}
-- FIXED-END tests
