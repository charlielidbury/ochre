-- FIXED-BEGIN header
import Ochr.Examples.«16Arrays»

/-! # Verified in-place hash map, two programs (condition `ochr-2p`)

Read `ASSIGNMENT.md` first. Replace every hole `?` with a definition or a proof, and add any
helper definitions and lemmas you need to the blocks `HashMapModel` and
`HashMapSolution`, between their FIXED regions. Everything inside a FIXED region must stay exactly as it is.

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

  -- The parts of a map value, for the model: its buckets as a view (a model function: it
  -- returns a view by value, so it runs only in statements and other model code), and
  -- its length field.
  def SlotsOf (V : Type) (cap : Word) (m : Map(V, cap)) : Slice(Bucket(V), cap) := (
    match m {
      MkMap(slots, len) => match slots {
        MkArray(s) => s,
      },
    }
  )

  def LenField (V : Type) (cap : Word) (m : Map(V, cap)) : Word := (
    match m {
      MkMap(slots, len) => len,
    }
  )
}

/-! ## From the model to the program (FIXED, provided)

H4–H15 about any in-place map follow from its agreement with a pure model and the model's
own properties. These lemmas are that argument, checked, for any operations, model and
invariants (the parameters, each generic in the value type); nothing here is for you to do.
At the end of `HashMapSolution` they are applied to your operations, your model and your
proofs, which gives H4–H15 about your operations, stated exactly as in the one-program
assignment. -/

ochr HashMapCompose uses HashMapSpec {
  -- H4: contains(new(c), k) = false.
  def ContainsNewFrom
      (MM : Π(V : Type). Type)
      (new : Π(V : Type) (cap : Word) (h : Lt(Zero, cap)). Map(V, cap))
      (containsOf : Π(V : Type) (cap : Word) (m : Map(V, cap)) (k : Word). Bool)
      (inv : Π(V : Type) (cap : Word) (m : Map(V, cap)). Prop)
      (absOf : Π(V : Type) (cap : Word) (m : Map(V, cap)). MM(V))
      (mnew : Π(V : Type). MM(V))
      (mget : Π(V : Type) (a : MM(V)) (k : Word). Opt(V))
      (invNew : Π(V : Type) (cap : Word) (h : Lt(Zero, cap)). inv(V, cap, new(V, cap, h)))
      (agreeContains : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : inv(V, cap, *m)).
        Eq(Bool, containsOf(V, cap, *m, k), IsSomeB(V, mget(V, absOf(V, cap, *m), k))))
      (absNew : Π(V : Type) (cap : Word) (h : Lt(Zero, cap)). Eq(MM(V), absOf(V, cap, new(V, cap, h)), mnew(V)))
      (m4 : Π(V : Type) (k : Word). Eq(Opt(V), mget(V, mnew(V), k), None[V]))
      (V : Type) (cap : Word) (h : Lt(Zero, cap)) (k : Word) :
      Eq(Bool, containsOf(V, cap, new(V, cap, h), k), false) := (
    rewrite ← (let c = new(V, cap, h); agreeContains(V, cap, &c, k, invNew(V, cap, h))) in
    rewrite ← absNew(V, cap, h) in
    rewrite ← m4(V, k) in
    refl
  )

  -- H5a: after insert(m, k, v), contains(m′, k) = true.
  def ContainsInsertSameFrom
      (MM : Π(V : Type). Type)
      (ins : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V). Opt(V))
      (containsOf : Π(V : Type) (cap : Word) (m : Map(V, cap)) (k : Word). Bool)
      (inv : Π(V : Type) (cap : Word) (m : Map(V, cap)). Prop)
      (absOf : Π(V : Type) (cap : Word) (m : Map(V, cap)). MM(V))
      (mget : Π(V : Type) (a : MM(V)) (k : Word). Opt(V))
      (minsert : Π(V : Type) (a : MM(V)) (k : Word) (v : V). MM(V))
      (minv : Π(V : Type) (a : MM(V)). Prop)
      (invIns : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V) (hm : inv(V, cap, *m)).
        (let c = *m; ins(V, cap, &c, k, v); inv(V, cap, c)))
      (agreeContains : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : inv(V, cap, *m)).
        Eq(Bool, containsOf(V, cap, *m, k), IsSomeB(V, mget(V, absOf(V, cap, *m), k))))
      (agreeIns : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V) (hm : inv(V, cap, *m)).
        Eq(MM(V), (let c = *m; ins(V, cap, &c, k, v); absOf(V, cap, c)), minsert(V, absOf(V, cap, *m), k, v)))
      (absInv : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (hm : inv(V, cap, *m)). minv(V, absOf(V, cap, *m)))
      (m5 : Π(V : Type) (a : MM(V)) (k : Word) (v : V) (h : minv(V, a)). Eq(Opt(V), mget(V, minsert(V, a, k, v), k), Some(v)))
      (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V) (hm : inv(V, cap, *m)) :
      Eq(Bool, (let c = *m; ins(V, cap, &c, k, v); containsOf(V, cap, c, k)), true) := (
    rewrite ← (let c = *m; ins(V, cap, &c, k, v); agreeContains(V, cap, &c, k, invIns(V, cap, m, k, v, hm))) in
    rewrite ← agreeIns(V, cap, m, k, v, hm) in
    rewrite ← m5(V, absOf(V, cap, *m), k, v, absInv(V, cap, m, hm)) in
    refl
  )

  -- H5b: ... and the value read through get(m′, k) is v.
  def GetInsertSameFrom
      (MM : Π(V : Type). Type)
      (ins : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V). Opt(V))
      (containsOf : Π(V : Type) (cap : Word) (m : Map(V, cap)) (k : Word). Bool)
      (get : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (h : IsTrue(containsOf(V, cap, *m, k))). &V)
      (inv : Π(V : Type) (cap : Word) (m : Map(V, cap)). Prop)
      (absOf : Π(V : Type) (cap : Word) (m : Map(V, cap)). MM(V))
      (mget : Π(V : Type) (a : MM(V)) (k : Word). Opt(V))
      (minsert : Π(V : Type) (a : MM(V)) (k : Word) (v : V). MM(V))
      (minv : Π(V : Type) (a : MM(V)). Prop)
      (invIns : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V) (hm : inv(V, cap, *m)).
        (let c = *m; ins(V, cap, &c, k, v); inv(V, cap, c)))
      (agreeGet : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : inv(V, cap, *m)) (h : IsTrue(containsOf(V, cap, *m, k))).
        Eq(Opt(V), Some(clone(*get(V, cap, m, k, h))), mget(V, absOf(V, cap, *m), k)))
      (agreeIns : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V) (hm : inv(V, cap, *m)).
        Eq(MM(V), (let c = *m; ins(V, cap, &c, k, v); absOf(V, cap, c)), minsert(V, absOf(V, cap, *m), k, v)))
      (absInv : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (hm : inv(V, cap, *m)). minv(V, absOf(V, cap, *m)))
      (m5 : Π(V : Type) (a : MM(V)) (k : Word) (v : V) (h : minv(V, a)). Eq(Opt(V), mget(V, minsert(V, a, k, v), k), Some(v)))
      (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V) (hm : inv(V, cap, *m))
      (h : IsTrue(containsOf(V, cap, (let c = *m; ins(V, cap, &c, k, v); c), k))) :
      Eq(V, (let c = *m; ins(V, cap, &c, k, v); clone(*get(V, cap, &c, k, h))), v) := (
    let e : Eq(Opt(V), mget(V, absOf(V, cap, (let c = *m; ins(V, cap, &c, k, v); c)), k), Some(v)) = (
      rewrite ← agreeIns(V, cap, m, k, v, hm) in m5(V, absOf(V, cap, *m), k, v, absInv(V, cap, m, hm)));
    trans((let c = *m; ins(V, cap, &c, k, v); agreeGet(V, cap, &c, k, invIns(V, cap, m, k, v, hm), h)), e)
  )

  -- H6a: after insert(m, k, v), contains(m′, k′) = contains(m, k′) for k′ ≠ k.
  def ContainsInsertOtherFrom
      (MM : Π(V : Type). Type)
      (ins : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V). Opt(V))
      (containsOf : Π(V : Type) (cap : Word) (m : Map(V, cap)) (k : Word). Bool)
      (inv : Π(V : Type) (cap : Word) (m : Map(V, cap)). Prop)
      (absOf : Π(V : Type) (cap : Word) (m : Map(V, cap)). MM(V))
      (mget : Π(V : Type) (a : MM(V)) (k : Word). Opt(V))
      (minsert : Π(V : Type) (a : MM(V)) (k : Word) (v : V). MM(V))
      (minv : Π(V : Type) (a : MM(V)). Prop)
      (invIns : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V) (hm : inv(V, cap, *m)).
        (let c = *m; ins(V, cap, &c, k, v); inv(V, cap, c)))
      (agreeContains : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : inv(V, cap, *m)).
        Eq(Bool, containsOf(V, cap, *m, k), IsSomeB(V, mget(V, absOf(V, cap, *m), k))))
      (agreeIns : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V) (hm : inv(V, cap, *m)).
        Eq(MM(V), (let c = *m; ins(V, cap, &c, k, v); absOf(V, cap, c)), minsert(V, absOf(V, cap, *m), k, v)))
      (absInv : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (hm : inv(V, cap, *m)). minv(V, absOf(V, cap, *m)))
      (m6 : Π(V : Type) (a : MM(V)) (k : Word) (k2 : Word) (v : V) (h : minv(V, a)) (ne : Π(e : Eq(Word, k2, k)). False).
        Eq(Opt(V), mget(V, minsert(V, a, k, v), k2), mget(V, a, k2)))
      (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (k2 : Word) (v : V) (hm : inv(V, cap, *m)) (ne : Π(e : Eq(Word, k2, k)). False) :
      Eq(Bool, (let c = *m; ins(V, cap, &c, k, v); containsOf(V, cap, c, k2)), containsOf(V, cap, *m, k2)) := (
    rewrite ← (let c = *m; ins(V, cap, &c, k, v); agreeContains(V, cap, &c, k2, invIns(V, cap, m, k, v, hm))) in
    rewrite ← agreeIns(V, cap, m, k, v, hm) in
    rewrite ← agreeContains(V, cap, m, k2, hm) in
    rewrite ← m6(V, absOf(V, cap, *m), k, k2, v, absInv(V, cap, m, hm), ne) in
    refl
  )

  -- H6b: ... and the value read through get at k′ is the same, when k′ is present.
  def GetInsertOtherFrom
      (MM : Π(V : Type). Type)
      (ins : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V). Opt(V))
      (containsOf : Π(V : Type) (cap : Word) (m : Map(V, cap)) (k : Word). Bool)
      (get : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (h : IsTrue(containsOf(V, cap, *m, k))). &V)
      (inv : Π(V : Type) (cap : Word) (m : Map(V, cap)). Prop)
      (absOf : Π(V : Type) (cap : Word) (m : Map(V, cap)). MM(V))
      (mget : Π(V : Type) (a : MM(V)) (k : Word). Opt(V))
      (minsert : Π(V : Type) (a : MM(V)) (k : Word) (v : V). MM(V))
      (minv : Π(V : Type) (a : MM(V)). Prop)
      (invIns : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V) (hm : inv(V, cap, *m)).
        (let c = *m; ins(V, cap, &c, k, v); inv(V, cap, c)))
      (agreeGet : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : inv(V, cap, *m)) (h : IsTrue(containsOf(V, cap, *m, k))).
        Eq(Opt(V), Some(clone(*get(V, cap, m, k, h))), mget(V, absOf(V, cap, *m), k)))
      (agreeIns : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V) (hm : inv(V, cap, *m)).
        Eq(MM(V), (let c = *m; ins(V, cap, &c, k, v); absOf(V, cap, c)), minsert(V, absOf(V, cap, *m), k, v)))
      (absInv : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (hm : inv(V, cap, *m)). minv(V, absOf(V, cap, *m)))
      (m6 : Π(V : Type) (a : MM(V)) (k : Word) (k2 : Word) (v : V) (h : minv(V, a)) (ne : Π(e : Eq(Word, k2, k)). False).
        Eq(Opt(V), mget(V, minsert(V, a, k, v), k2), mget(V, a, k2)))
      (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (k2 : Word) (v : V) (hm : inv(V, cap, *m)) (ne : Π(e : Eq(Word, k2, k)). False)
      (h : IsTrue(containsOf(V, cap, *m, k2))) (h2 : IsTrue(containsOf(V, cap, (let c = *m; ins(V, cap, &c, k, v); c), k2))) :
      Eq(V, (let c = *m; ins(V, cap, &c, k, v); clone(*get(V, cap, &c, k2, h2))), clone(*get(V, cap, m, k2, h))) := (
    let e : Eq(Opt(V), mget(V, absOf(V, cap, (let c = *m; ins(V, cap, &c, k, v); c)), k2), mget(V, absOf(V, cap, *m), k2)) = (
      rewrite ← agreeIns(V, cap, m, k, v, hm) in m6(V, absOf(V, cap, *m), k, k2, v, absInv(V, cap, m, hm), ne));
    trans(trans((let c = *m; ins(V, cap, &c, k, v); agreeGet(V, cap, &c, k2, invIns(V, cap, m, k, v, hm), h2)), e), symm(agreeGet(V, cap, m, k2, hm, h)))
  )

  -- H7a: insert returns None exactly when k was absent.
  def InsertReturnsContainsFrom
      (MM : Π(V : Type). Type)
      (ins : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V). Opt(V))
      (containsOf : Π(V : Type) (cap : Word) (m : Map(V, cap)) (k : Word). Bool)
      (inv : Π(V : Type) (cap : Word) (m : Map(V, cap)). Prop)
      (absOf : Π(V : Type) (cap : Word) (m : Map(V, cap)). MM(V))
      (mget : Π(V : Type) (a : MM(V)) (k : Word). Opt(V))
      (agreeContains : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : inv(V, cap, *m)).
        Eq(Bool, containsOf(V, cap, *m, k), IsSomeB(V, mget(V, absOf(V, cap, *m), k))))
      (agreeInsRes : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V) (hm : inv(V, cap, *m)).
        Eq(Opt(V), (let c = *m; ins(V, cap, &c, k, v)), mget(V, absOf(V, cap, *m), k)))
      (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V) (hm : inv(V, cap, *m)) :
      Eq(Bool, (let c = *m; IsSomeB(V, ins(V, cap, &c, k, v))), containsOf(V, cap, *m, k)) := (
    rewrite ← agreeInsRes(V, cap, m, k, v, hm) in
    rewrite ← agreeContains(V, cap, m, k, hm) in
    refl
  )

  -- H7b: when k was present, insert returns Some of the value bound to it.
  def InsertReturnsGetFrom
      (MM : Π(V : Type). Type)
      (ins : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V). Opt(V))
      (containsOf : Π(V : Type) (cap : Word) (m : Map(V, cap)) (k : Word). Bool)
      (get : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (h : IsTrue(containsOf(V, cap, *m, k))). &V)
      (inv : Π(V : Type) (cap : Word) (m : Map(V, cap)). Prop)
      (absOf : Π(V : Type) (cap : Word) (m : Map(V, cap)). MM(V))
      (mget : Π(V : Type) (a : MM(V)) (k : Word). Opt(V))
      (agreeGet : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : inv(V, cap, *m)) (h : IsTrue(containsOf(V, cap, *m, k))).
        Eq(Opt(V), Some(clone(*get(V, cap, m, k, h))), mget(V, absOf(V, cap, *m), k)))
      (agreeInsRes : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V) (hm : inv(V, cap, *m)).
        Eq(Opt(V), (let c = *m; ins(V, cap, &c, k, v)), mget(V, absOf(V, cap, *m), k)))
      (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V) (hm : inv(V, cap, *m)) (h : IsTrue(containsOf(V, cap, *m, k))) :
      Eq(Opt(V), (let c = *m; ins(V, cap, &c, k, v)), Some(clone(*get(V, cap, m, k, h)))) := (
    trans(agreeInsRes(V, cap, m, k, v, hm), symm(agreeGet(V, cap, m, k, hm, h)))
  )

  -- H8: after remove(m, k), contains(m′, k) = false.
  def ContainsRemoveSameFrom
      (MM : Π(V : Type). Type)
      (rem : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word). Opt(V))
      (containsOf : Π(V : Type) (cap : Word) (m : Map(V, cap)) (k : Word). Bool)
      (inv : Π(V : Type) (cap : Word) (m : Map(V, cap)). Prop)
      (absOf : Π(V : Type) (cap : Word) (m : Map(V, cap)). MM(V))
      (mget : Π(V : Type) (a : MM(V)) (k : Word). Opt(V))
      (mremove : Π(V : Type) (a : MM(V)) (k : Word). MM(V))
      (minv : Π(V : Type) (a : MM(V)). Prop)
      (invRem : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : inv(V, cap, *m)).
        (let c = *m; rem(V, cap, &c, k); inv(V, cap, c)))
      (agreeContains : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : inv(V, cap, *m)).
        Eq(Bool, containsOf(V, cap, *m, k), IsSomeB(V, mget(V, absOf(V, cap, *m), k))))
      (agreeRem : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : inv(V, cap, *m)).
        Eq(MM(V), (let c = *m; rem(V, cap, &c, k); absOf(V, cap, c)), mremove(V, absOf(V, cap, *m), k)))
      (absInv : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (hm : inv(V, cap, *m)). minv(V, absOf(V, cap, *m)))
      (m8 : Π(V : Type) (a : MM(V)) (k : Word) (h : minv(V, a)). Eq(Opt(V), mget(V, mremove(V, a, k), k), None[V]))
      (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : inv(V, cap, *m)) :
      Eq(Bool, (let c = *m; rem(V, cap, &c, k); containsOf(V, cap, c, k)), false) := (
    rewrite ← (let c = *m; rem(V, cap, &c, k); agreeContains(V, cap, &c, k, invRem(V, cap, m, k, hm))) in
    rewrite ← agreeRem(V, cap, m, k, hm) in
    rewrite ← m8(V, absOf(V, cap, *m), k, absInv(V, cap, m, hm)) in
    refl
  )

  -- H9a: after remove(m, k), contains(m′, k′) = contains(m, k′) for k′ ≠ k.
  def ContainsRemoveOtherFrom
      (MM : Π(V : Type). Type)
      (rem : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word). Opt(V))
      (containsOf : Π(V : Type) (cap : Word) (m : Map(V, cap)) (k : Word). Bool)
      (inv : Π(V : Type) (cap : Word) (m : Map(V, cap)). Prop)
      (absOf : Π(V : Type) (cap : Word) (m : Map(V, cap)). MM(V))
      (mget : Π(V : Type) (a : MM(V)) (k : Word). Opt(V))
      (mremove : Π(V : Type) (a : MM(V)) (k : Word). MM(V))
      (minv : Π(V : Type) (a : MM(V)). Prop)
      (invRem : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : inv(V, cap, *m)).
        (let c = *m; rem(V, cap, &c, k); inv(V, cap, c)))
      (agreeContains : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : inv(V, cap, *m)).
        Eq(Bool, containsOf(V, cap, *m, k), IsSomeB(V, mget(V, absOf(V, cap, *m), k))))
      (agreeRem : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : inv(V, cap, *m)).
        Eq(MM(V), (let c = *m; rem(V, cap, &c, k); absOf(V, cap, c)), mremove(V, absOf(V, cap, *m), k)))
      (absInv : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (hm : inv(V, cap, *m)). minv(V, absOf(V, cap, *m)))
      (m9 : Π(V : Type) (a : MM(V)) (k : Word) (k2 : Word) (h : minv(V, a)) (ne : Π(e : Eq(Word, k2, k)). False).
        Eq(Opt(V), mget(V, mremove(V, a, k), k2), mget(V, a, k2)))
      (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (k2 : Word) (hm : inv(V, cap, *m)) (ne : Π(e : Eq(Word, k2, k)). False) :
      Eq(Bool, (let c = *m; rem(V, cap, &c, k); containsOf(V, cap, c, k2)), containsOf(V, cap, *m, k2)) := (
    rewrite ← (let c = *m; rem(V, cap, &c, k); agreeContains(V, cap, &c, k2, invRem(V, cap, m, k, hm))) in
    rewrite ← agreeRem(V, cap, m, k, hm) in
    rewrite ← agreeContains(V, cap, m, k2, hm) in
    rewrite ← m9(V, absOf(V, cap, *m), k, k2, absInv(V, cap, m, hm), ne) in
    refl
  )

  -- H9b: ... and the value read through get at k′ is the same, when k′ is present.
  def GetRemoveOtherFrom
      (MM : Π(V : Type). Type)
      (rem : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word). Opt(V))
      (containsOf : Π(V : Type) (cap : Word) (m : Map(V, cap)) (k : Word). Bool)
      (get : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (h : IsTrue(containsOf(V, cap, *m, k))). &V)
      (inv : Π(V : Type) (cap : Word) (m : Map(V, cap)). Prop)
      (absOf : Π(V : Type) (cap : Word) (m : Map(V, cap)). MM(V))
      (mget : Π(V : Type) (a : MM(V)) (k : Word). Opt(V))
      (mremove : Π(V : Type) (a : MM(V)) (k : Word). MM(V))
      (minv : Π(V : Type) (a : MM(V)). Prop)
      (invRem : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : inv(V, cap, *m)).
        (let c = *m; rem(V, cap, &c, k); inv(V, cap, c)))
      (agreeGet : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : inv(V, cap, *m)) (h : IsTrue(containsOf(V, cap, *m, k))).
        Eq(Opt(V), Some(clone(*get(V, cap, m, k, h))), mget(V, absOf(V, cap, *m), k)))
      (agreeRem : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : inv(V, cap, *m)).
        Eq(MM(V), (let c = *m; rem(V, cap, &c, k); absOf(V, cap, c)), mremove(V, absOf(V, cap, *m), k)))
      (absInv : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (hm : inv(V, cap, *m)). minv(V, absOf(V, cap, *m)))
      (m9 : Π(V : Type) (a : MM(V)) (k : Word) (k2 : Word) (h : minv(V, a)) (ne : Π(e : Eq(Word, k2, k)). False).
        Eq(Opt(V), mget(V, mremove(V, a, k), k2), mget(V, a, k2)))
      (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (k2 : Word) (hm : inv(V, cap, *m)) (ne : Π(e : Eq(Word, k2, k)). False)
      (h : IsTrue(containsOf(V, cap, *m, k2))) (h2 : IsTrue(containsOf(V, cap, (let c = *m; rem(V, cap, &c, k); c), k2))) :
      Eq(V, (let c = *m; rem(V, cap, &c, k); clone(*get(V, cap, &c, k2, h2))), clone(*get(V, cap, m, k2, h))) := (
    let e : Eq(Opt(V), mget(V, absOf(V, cap, (let c = *m; rem(V, cap, &c, k); c)), k2), mget(V, absOf(V, cap, *m), k2)) = (
      rewrite ← agreeRem(V, cap, m, k, hm) in m9(V, absOf(V, cap, *m), k, k2, absInv(V, cap, m, hm), ne));
    trans(trans((let c = *m; rem(V, cap, &c, k); agreeGet(V, cap, &c, k2, invRem(V, cap, m, k, hm), h2)), e), symm(agreeGet(V, cap, m, k2, hm, h)))
  )

  -- H10a: remove returns None exactly when k was absent.
  def RemoveReturnsContainsFrom
      (MM : Π(V : Type). Type)
      (rem : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word). Opt(V))
      (containsOf : Π(V : Type) (cap : Word) (m : Map(V, cap)) (k : Word). Bool)
      (inv : Π(V : Type) (cap : Word) (m : Map(V, cap)). Prop)
      (absOf : Π(V : Type) (cap : Word) (m : Map(V, cap)). MM(V))
      (mget : Π(V : Type) (a : MM(V)) (k : Word). Opt(V))
      (agreeContains : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : inv(V, cap, *m)).
        Eq(Bool, containsOf(V, cap, *m, k), IsSomeB(V, mget(V, absOf(V, cap, *m), k))))
      (agreeRemRes : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : inv(V, cap, *m)).
        Eq(Opt(V), (let c = *m; rem(V, cap, &c, k)), mget(V, absOf(V, cap, *m), k)))
      (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : inv(V, cap, *m)) :
      Eq(Bool, (let c = *m; IsSomeB(V, rem(V, cap, &c, k))), containsOf(V, cap, *m, k)) := (
    rewrite ← agreeRemRes(V, cap, m, k, hm) in
    rewrite ← agreeContains(V, cap, m, k, hm) in
    refl
  )

  -- H10b: when k was present, remove returns Some of the value bound to it.
  def RemoveReturnsGetFrom
      (MM : Π(V : Type). Type)
      (rem : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word). Opt(V))
      (containsOf : Π(V : Type) (cap : Word) (m : Map(V, cap)) (k : Word). Bool)
      (get : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (h : IsTrue(containsOf(V, cap, *m, k))). &V)
      (inv : Π(V : Type) (cap : Word) (m : Map(V, cap)). Prop)
      (absOf : Π(V : Type) (cap : Word) (m : Map(V, cap)). MM(V))
      (mget : Π(V : Type) (a : MM(V)) (k : Word). Opt(V))
      (agreeGet : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : inv(V, cap, *m)) (h : IsTrue(containsOf(V, cap, *m, k))).
        Eq(Opt(V), Some(clone(*get(V, cap, m, k, h))), mget(V, absOf(V, cap, *m), k)))
      (agreeRemRes : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : inv(V, cap, *m)).
        Eq(Opt(V), (let c = *m; rem(V, cap, &c, k)), mget(V, absOf(V, cap, *m), k)))
      (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : inv(V, cap, *m)) (h : IsTrue(containsOf(V, cap, *m, k))) :
      Eq(Opt(V), (let c = *m; rem(V, cap, &c, k)), Some(clone(*get(V, cap, m, k, h)))) := (
    trans(agreeRemRes(V, cap, m, k, hm), symm(agreeGet(V, cap, m, k, hm, h)))
  )

  -- H11: len(new(c)) = 0.
  def LenNewFrom
      (MM : Π(V : Type). Type)
      (new : Π(V : Type) (cap : Word) (h : Lt(Zero, cap)). Map(V, cap))
      (lenOf : Π(V : Type) (cap : Word) (m : Map(V, cap)). Word)
      (inv : Π(V : Type) (cap : Word) (m : Map(V, cap)). Prop)
      (absOf : Π(V : Type) (cap : Word) (m : Map(V, cap)). MM(V))
      (mnew : Π(V : Type). MM(V))
      (mlen : Π(V : Type) (a : MM(V)). Word)
      (invNew : Π(V : Type) (cap : Word) (h : Lt(Zero, cap)). inv(V, cap, new(V, cap, h)))
      (agreeLen : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (hm : inv(V, cap, *m)). Eq(Word, lenOf(V, cap, *m), mlen(V, absOf(V, cap, *m))))
      (absNew : Π(V : Type) (cap : Word) (h : Lt(Zero, cap)). Eq(MM(V), absOf(V, cap, new(V, cap, h)), mnew(V)))
      (m11 : Π(V : Type). Eq(Word, mlen(V, mnew(V)), Zero))
      (V : Type) (cap : Word) (h : Lt(Zero, cap)) :
      Eq(Word, lenOf(V, cap, new(V, cap, h)), Zero) := (
    rewrite ← (let c = new(V, cap, h); agreeLen(V, cap, &c, invNew(V, cap, h))) in
    rewrite ← absNew(V, cap, h) in
    m11(V)
  )

  -- H12: insert adds one to len if the key was absent.
  def LenInsertFrom
      (MM : Π(V : Type). Type)
      (ins : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V). Opt(V))
      (containsOf : Π(V : Type) (cap : Word) (m : Map(V, cap)) (k : Word). Bool)
      (lenOf : Π(V : Type) (cap : Word) (m : Map(V, cap)). Word)
      (inv : Π(V : Type) (cap : Word) (m : Map(V, cap)). Prop)
      (absOf : Π(V : Type) (cap : Word) (m : Map(V, cap)). MM(V))
      (mget : Π(V : Type) (a : MM(V)) (k : Word). Opt(V))
      (mlen : Π(V : Type) (a : MM(V)). Word)
      (minsert : Π(V : Type) (a : MM(V)) (k : Word) (v : V). MM(V))
      (minv : Π(V : Type) (a : MM(V)). Prop)
      (invIns : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V) (hm : inv(V, cap, *m)).
        (let c = *m; ins(V, cap, &c, k, v); inv(V, cap, c)))
      (agreeContains : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : inv(V, cap, *m)).
        Eq(Bool, containsOf(V, cap, *m, k), IsSomeB(V, mget(V, absOf(V, cap, *m), k))))
      (agreeLen : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (hm : inv(V, cap, *m)). Eq(Word, lenOf(V, cap, *m), mlen(V, absOf(V, cap, *m))))
      (agreeIns : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V) (hm : inv(V, cap, *m)).
        Eq(MM(V), (let c = *m; ins(V, cap, &c, k, v); absOf(V, cap, c)), minsert(V, absOf(V, cap, *m), k, v)))
      (absInv : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (hm : inv(V, cap, *m)). minv(V, absOf(V, cap, *m)))
      (m12 : Π(V : Type) (a : MM(V)) (k : Word) (v : V) (h : minv(V, a)). Eq(Word, mlen(V, minsert(V, a, k, v)), Grow(IsSomeB(V, mget(V, a, k)), mlen(V, a))))
      (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V) (hm : inv(V, cap, *m)) :
      Eq(Word, (let c = *m; ins(V, cap, &c, k, v); lenOf(V, cap, c)), Grow(containsOf(V, cap, *m, k), lenOf(V, cap, *m))) := (
    rewrite ← (let c = *m; ins(V, cap, &c, k, v); agreeLen(V, cap, &c, invIns(V, cap, m, k, v, hm))) in
    rewrite ← agreeIns(V, cap, m, k, v, hm) in
    rewrite ← agreeContains(V, cap, m, k, hm) in
    rewrite ← agreeLen(V, cap, m, hm) in
    m12(V, absOf(V, cap, *m), k, v, absInv(V, cap, m, hm))
  )

  -- H13: remove takes one from len if the key was present.
  def LenRemoveFrom
      (MM : Π(V : Type). Type)
      (rem : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word). Opt(V))
      (containsOf : Π(V : Type) (cap : Word) (m : Map(V, cap)) (k : Word). Bool)
      (lenOf : Π(V : Type) (cap : Word) (m : Map(V, cap)). Word)
      (inv : Π(V : Type) (cap : Word) (m : Map(V, cap)). Prop)
      (absOf : Π(V : Type) (cap : Word) (m : Map(V, cap)). MM(V))
      (mget : Π(V : Type) (a : MM(V)) (k : Word). Opt(V))
      (mlen : Π(V : Type) (a : MM(V)). Word)
      (mremove : Π(V : Type) (a : MM(V)) (k : Word). MM(V))
      (minv : Π(V : Type) (a : MM(V)). Prop)
      (invRem : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : inv(V, cap, *m)).
        (let c = *m; rem(V, cap, &c, k); inv(V, cap, c)))
      (agreeContains : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : inv(V, cap, *m)).
        Eq(Bool, containsOf(V, cap, *m, k), IsSomeB(V, mget(V, absOf(V, cap, *m), k))))
      (agreeLen : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (hm : inv(V, cap, *m)). Eq(Word, lenOf(V, cap, *m), mlen(V, absOf(V, cap, *m))))
      (agreeRem : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : inv(V, cap, *m)).
        Eq(MM(V), (let c = *m; rem(V, cap, &c, k); absOf(V, cap, c)), mremove(V, absOf(V, cap, *m), k)))
      (absInv : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (hm : inv(V, cap, *m)). minv(V, absOf(V, cap, *m)))
      (m13 : Π(V : Type) (a : MM(V)) (k : Word) (h : minv(V, a)). Eq(Word, mlen(V, mremove(V, a, k)), Shrink(IsSomeB(V, mget(V, a, k)), mlen(V, a))))
      (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : inv(V, cap, *m)) :
      Eq(Word, (let c = *m; rem(V, cap, &c, k); lenOf(V, cap, c)), Shrink(containsOf(V, cap, *m, k), lenOf(V, cap, *m))) := (
    rewrite ← (let c = *m; rem(V, cap, &c, k); agreeLen(V, cap, &c, invRem(V, cap, m, k, hm))) in
    rewrite ← agreeRem(V, cap, m, k, hm) in
    rewrite ← agreeContains(V, cap, m, k, hm) in
    rewrite ← agreeLen(V, cap, m, hm) in
    m13(V, absOf(V, cap, *m), k, absInv(V, cap, m, hm))
  )

  -- H14a: writing w through get_mut has the effect of insert on every contains.
  def GetMutContainsFrom
      (MM : Π(V : Type). Type)
      (ins : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V). Opt(V))
      (containsOf : Π(V : Type) (cap : Word) (m : Map(V, cap)) (k : Word). Bool)
      (getMut : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (h : IsTrue(containsOf(V, cap, *m, k))). &V)
      (inv : Π(V : Type) (cap : Word) (m : Map(V, cap)). Prop)
      (absOf : Π(V : Type) (cap : Word) (m : Map(V, cap)). MM(V))
      (mget : Π(V : Type) (a : MM(V)) (k : Word). Opt(V))
      (minsert : Π(V : Type) (a : MM(V)) (k : Word) (v : V). MM(V))
      (mwrite : Π(V : Type) (a : MM(V)) (k : Word) (w : V). MM(V))
      (minv : Π(V : Type) (a : MM(V)). Prop)
      (invIns : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V) (hm : inv(V, cap, *m)).
        (let c = *m; ins(V, cap, &c, k, v); inv(V, cap, c)))
      (invWrite : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (w : V) (hm : inv(V, cap, *m)) (hk : IsTrue(containsOf(V, cap, *m, k))).
        (let c = *m; let r = getMut(V, cap, &c, k, hk); *r := w; inv(V, cap, c)))
      (agreeContains : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : inv(V, cap, *m)).
        Eq(Bool, containsOf(V, cap, *m, k), IsSomeB(V, mget(V, absOf(V, cap, *m), k))))
      (agreeIns : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V) (hm : inv(V, cap, *m)).
        Eq(MM(V), (let c = *m; ins(V, cap, &c, k, v); absOf(V, cap, c)), minsert(V, absOf(V, cap, *m), k, v)))
      (agreeWrite : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (w : V) (hm : inv(V, cap, *m)) (hk : IsTrue(containsOf(V, cap, *m, k))).
        Eq(MM(V), (let c = *m; let r = getMut(V, cap, &c, k, hk); *r := w; absOf(V, cap, c)), mwrite(V, absOf(V, cap, *m), k, w)))
      (absInv : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (hm : inv(V, cap, *m)). minv(V, absOf(V, cap, *m)))
      (m14 : Π(V : Type) (a : MM(V)) (k : Word) (w : V) (k2 : Word) (h : minv(V, a)) (hk : IsTrue(IsSomeB(V, mget(V, a, k)))).
        Eq(Opt(V), mget(V, mwrite(V, a, k, w), k2), mget(V, minsert(V, a, k, w), k2)))
      (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (w : V) (k2 : Word) (hm : inv(V, cap, *m)) (hk : IsTrue(containsOf(V, cap, *m, k))) :
      Eq(Bool, (let c = *m; let r = getMut(V, cap, &c, k, hk); *r := w; containsOf(V, cap, c, k2)),
        (let c = *m; ins(V, cap, &c, k, w); containsOf(V, cap, c, k2))) := (
    rewrite ← (let c = *m; let r = getMut(V, cap, &c, k, hk); *r := w; agreeContains(V, cap, &c, k2, invWrite(V, cap, m, k, w, hm, hk))) in
    rewrite ← agreeWrite(V, cap, m, k, w, hm, hk) in
    rewrite ← (let c = *m; ins(V, cap, &c, k, w); agreeContains(V, cap, &c, k2, invIns(V, cap, m, k, w, hm))) in
    rewrite ← agreeIns(V, cap, m, k, w, hm) in
    rewrite ← m14(V, absOf(V, cap, *m), k, w, k2, absInv(V, cap, m, hm), (rewrite agreeContains(V, cap, m, k, hm) in hk)) in
    refl
  )

  -- H14b: ... and on the value read through get.
  def GetMutGetFrom
      (MM : Π(V : Type). Type)
      (ins : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V). Opt(V))
      (containsOf : Π(V : Type) (cap : Word) (m : Map(V, cap)) (k : Word). Bool)
      (get : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (h : IsTrue(containsOf(V, cap, *m, k))). &V)
      (getMut : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (h : IsTrue(containsOf(V, cap, *m, k))). &V)
      (inv : Π(V : Type) (cap : Word) (m : Map(V, cap)). Prop)
      (absOf : Π(V : Type) (cap : Word) (m : Map(V, cap)). MM(V))
      (mget : Π(V : Type) (a : MM(V)) (k : Word). Opt(V))
      (minsert : Π(V : Type) (a : MM(V)) (k : Word) (v : V). MM(V))
      (mwrite : Π(V : Type) (a : MM(V)) (k : Word) (w : V). MM(V))
      (minv : Π(V : Type) (a : MM(V)). Prop)
      (invIns : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V) (hm : inv(V, cap, *m)).
        (let c = *m; ins(V, cap, &c, k, v); inv(V, cap, c)))
      (invWrite : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (w : V) (hm : inv(V, cap, *m)) (hk : IsTrue(containsOf(V, cap, *m, k))).
        (let c = *m; let r = getMut(V, cap, &c, k, hk); *r := w; inv(V, cap, c)))
      (agreeContains : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : inv(V, cap, *m)).
        Eq(Bool, containsOf(V, cap, *m, k), IsSomeB(V, mget(V, absOf(V, cap, *m), k))))
      (agreeGet : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : inv(V, cap, *m)) (h : IsTrue(containsOf(V, cap, *m, k))).
        Eq(Opt(V), Some(clone(*get(V, cap, m, k, h))), mget(V, absOf(V, cap, *m), k)))
      (agreeIns : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V) (hm : inv(V, cap, *m)).
        Eq(MM(V), (let c = *m; ins(V, cap, &c, k, v); absOf(V, cap, c)), minsert(V, absOf(V, cap, *m), k, v)))
      (agreeWrite : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (w : V) (hm : inv(V, cap, *m)) (hk : IsTrue(containsOf(V, cap, *m, k))).
        Eq(MM(V), (let c = *m; let r = getMut(V, cap, &c, k, hk); *r := w; absOf(V, cap, c)), mwrite(V, absOf(V, cap, *m), k, w)))
      (absInv : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (hm : inv(V, cap, *m)). minv(V, absOf(V, cap, *m)))
      (m14 : Π(V : Type) (a : MM(V)) (k : Word) (w : V) (k2 : Word) (h : minv(V, a)) (hk : IsTrue(IsSomeB(V, mget(V, a, k)))).
        Eq(Opt(V), mget(V, mwrite(V, a, k, w), k2), mget(V, minsert(V, a, k, w), k2)))
      (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (w : V) (k2 : Word) (hm : inv(V, cap, *m)) (hk : IsTrue(containsOf(V, cap, *m, k)))
      (h1 : IsTrue(containsOf(V, cap, (let c = *m; let r = getMut(V, cap, &c, k, hk); *r := w; c), k2))) (h2 : IsTrue(containsOf(V, cap, (let c = *m; ins(V, cap, &c, k, w); c), k2))) :
      Eq(V, (let c = *m; let r = getMut(V, cap, &c, k, hk); *r := w; clone(*get(V, cap, &c, k2, h1))),
        (let c = *m; ins(V, cap, &c, k, w); clone(*get(V, cap, &c, k2, h2)))) := (
    let e : Eq(Opt(V), mget(V, absOf(V, cap, (let c = *m; let r = getMut(V, cap, &c, k, hk); *r := w; c)), k2), mget(V, absOf(V, cap, (let c = *m; ins(V, cap, &c, k, w); c)), k2)) = (
      rewrite ← agreeWrite(V, cap, m, k, w, hm, hk) in rewrite ← agreeIns(V, cap, m, k, w, hm) in m14(V, absOf(V, cap, *m), k, w, k2, absInv(V, cap, m, hm), (rewrite agreeContains(V, cap, m, k, hm) in hk)));
    trans(trans((let c = *m; let r = getMut(V, cap, &c, k, hk); *r := w; agreeGet(V, cap, &c, k2, invWrite(V, cap, m, k, w, hm, hk), h1)), e),
      symm((let c = *m; ins(V, cap, &c, k, w); agreeGet(V, cap, &c, k2, invIns(V, cap, m, k, w, hm), h2))))
  )

  -- H15: ... and on len.
  def GetMutLenFrom
      (MM : Π(V : Type). Type)
      (ins : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V). Opt(V))
      (containsOf : Π(V : Type) (cap : Word) (m : Map(V, cap)) (k : Word). Bool)
      (lenOf : Π(V : Type) (cap : Word) (m : Map(V, cap)). Word)
      (getMut : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (h : IsTrue(containsOf(V, cap, *m, k))). &V)
      (inv : Π(V : Type) (cap : Word) (m : Map(V, cap)). Prop)
      (absOf : Π(V : Type) (cap : Word) (m : Map(V, cap)). MM(V))
      (mget : Π(V : Type) (a : MM(V)) (k : Word). Opt(V))
      (mlen : Π(V : Type) (a : MM(V)). Word)
      (minsert : Π(V : Type) (a : MM(V)) (k : Word) (v : V). MM(V))
      (mwrite : Π(V : Type) (a : MM(V)) (k : Word) (w : V). MM(V))
      (minv : Π(V : Type) (a : MM(V)). Prop)
      (invIns : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V) (hm : inv(V, cap, *m)).
        (let c = *m; ins(V, cap, &c, k, v); inv(V, cap, c)))
      (invWrite : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (w : V) (hm : inv(V, cap, *m)) (hk : IsTrue(containsOf(V, cap, *m, k))).
        (let c = *m; let r = getMut(V, cap, &c, k, hk); *r := w; inv(V, cap, c)))
      (agreeContains : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : inv(V, cap, *m)).
        Eq(Bool, containsOf(V, cap, *m, k), IsSomeB(V, mget(V, absOf(V, cap, *m), k))))
      (agreeLen : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (hm : inv(V, cap, *m)). Eq(Word, lenOf(V, cap, *m), mlen(V, absOf(V, cap, *m))))
      (agreeIns : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V) (hm : inv(V, cap, *m)).
        Eq(MM(V), (let c = *m; ins(V, cap, &c, k, v); absOf(V, cap, c)), minsert(V, absOf(V, cap, *m), k, v)))
      (agreeWrite : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (w : V) (hm : inv(V, cap, *m)) (hk : IsTrue(containsOf(V, cap, *m, k))).
        Eq(MM(V), (let c = *m; let r = getMut(V, cap, &c, k, hk); *r := w; absOf(V, cap, c)), mwrite(V, absOf(V, cap, *m), k, w)))
      (absInv : Π(V : Type) (cap : Word) (m : &Map(V, cap)) (hm : inv(V, cap, *m)). minv(V, absOf(V, cap, *m)))
      (m15 : Π(V : Type) (a : MM(V)) (k : Word) (w : V) (h : minv(V, a)) (hk : IsTrue(IsSomeB(V, mget(V, a, k)))).
        Eq(Word, mlen(V, mwrite(V, a, k, w)), mlen(V, minsert(V, a, k, w))))
      (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (w : V) (hm : inv(V, cap, *m)) (hk : IsTrue(containsOf(V, cap, *m, k))) :
      Eq(Word, (let c = *m; let r = getMut(V, cap, &c, k, hk); *r := w; lenOf(V, cap, c)),
        (let c = *m; ins(V, cap, &c, k, w); lenOf(V, cap, c))) := (
    rewrite ← (let c = *m; let r = getMut(V, cap, &c, k, hk); *r := w; agreeLen(V, cap, &c, invWrite(V, cap, m, k, w, hm, hk))) in
    rewrite ← agreeWrite(V, cap, m, k, w, hm, hk) in
    rewrite ← (let c = *m; ins(V, cap, &c, k, w); agreeLen(V, cap, &c, invIns(V, cap, m, k, w, hm))) in
    rewrite ← agreeIns(V, cap, m, k, w, hm) in
    m15(V, absOf(V, cap, *m), k, w, absInv(V, cap, m, hm), (rewrite agreeContains(V, cap, m, k, hm) in hk))
  )
}

/-! ## Your model

A pure functional model of a finite map from words to values of type `V`, and its properties.
Pure means: no borrows (`&`) and no assignment (`p := t`) anywhere in this block; the model
computes on values. Declare the data types the model needs here too (an association list, for
example). -/

ochr HashMapModel uses HashMapSpec {
-- FIXED-END header

  -- Your model's data types, pure helper definitions and lemmas go here, and anywhere else
  -- between the FIXED regions of this block.

  -- FIXED-BEGIN model-type
  -- The model's type.
  def MMap (V : Type) : Type :=
  -- FIXED-END model-type
    ?

  -- FIXED-BEGIN model-new
  -- The model of new(c): the empty map.
  def MNew (V : Type) : MMap(V) :=
  -- FIXED-END model-new
    ?

  -- FIXED-BEGIN model-len
  -- The model of len.
  def MLen (V : Type) (a : MMap(V)) : Word :=
  -- FIXED-END model-len
    ?

  -- FIXED-BEGIN model-get
  -- The model of a lookup: Some of the value bound to `k`, or None. (contains is whether
  -- it is Some, and get the value in it, by AgreeContains and AgreeGet below.)
  def MGet (V : Type) (a : MMap(V)) (k : Word) : Opt(V) :=
  -- FIXED-END model-get
    ?

  -- FIXED-BEGIN model-insert
  -- The model of insert: the map afterwards. (The value insert returns is
  -- MGet(V, a, k), by AgreeInsertResult below.)
  def MInsert (V : Type) (a : MMap(V)) (k : Word) (v : V) : MMap(V) :=
  -- FIXED-END model-insert
    ?

  -- FIXED-BEGIN model-remove
  -- The model of remove: the map afterwards. (The value remove returns is
  -- MGet(V, a, k), by AgreeRemoveResult below.)
  def MRemove (V : Type) (a : MMap(V)) (k : Word) : MMap(V) :=
  -- FIXED-END model-remove
    ?

  -- FIXED-BEGIN model-write
  -- The model of writing `w` through get_mut(m, k): the map afterwards.
  def MWrite (V : Type) (a : MMap(V)) (k : Word) (w : V) : MMap(V) :=
  -- FIXED-END model-write
    ?

  -- FIXED-BEGIN model-inv
  -- The model's invariant: any predicate on models that the properties below need
  -- (it may be ⊤).
  def MInv (V : Type) (a : MMap(V)) : Prop :=
  -- FIXED-END model-inv
    ?

  -- FIXED-BEGIN model-abs
  -- The abstraction: the model of a map, from its buckets (a view, as `SlotsOf` gives
  -- it) and its length field.
  def Abs (V : Type) (cap : Word) (s : Slice(Bucket(V), cap)) (len : Word) : MMap(V) :=
  -- FIXED-END model-abs
    ?

  -- FIXED-BEGIN M4
  -- M4 (H4 about the model): the model of a lookup in the empty map.
  def MGetNew (V : Type) (k : Word) :
      Eq(Opt(V), MGet(V, MNew(V), k), None[V]) :=
  -- FIXED-END M4
    ?

  -- FIXED-BEGIN M5
  -- M5 (H5 about the model): a lookup after insert, at the same key.
  def MGetInsertSame (V : Type) (a : MMap(V)) (k : Word) (v : V) (h : MInv(V, a)) :
      Eq(Opt(V), MGet(V, MInsert(V, a, k, v), k), Some(v)) :=
  -- FIXED-END M5
    ?

  -- FIXED-BEGIN M6
  -- M6 (H6 about the model): a lookup after insert, at another key.
  def MGetInsertOther (V : Type) (a : MMap(V)) (k : Word) (k2 : Word) (v : V) (h : MInv(V, a)) (ne : Π(e : Eq(Word, k2, k)). False) :
      Eq(Opt(V), MGet(V, MInsert(V, a, k, v), k2), MGet(V, a, k2)) :=
  -- FIXED-END M6
    ?

  -- FIXED-BEGIN M8
  -- M8 (H8 about the model): a lookup after remove, at the same key.
  def MGetRemoveSame (V : Type) (a : MMap(V)) (k : Word) (h : MInv(V, a)) :
      Eq(Opt(V), MGet(V, MRemove(V, a, k), k), None[V]) :=
  -- FIXED-END M8
    ?

  -- FIXED-BEGIN M9
  -- M9 (H9 about the model): a lookup after remove, at another key.
  def MGetRemoveOther (V : Type) (a : MMap(V)) (k : Word) (k2 : Word) (h : MInv(V, a)) (ne : Π(e : Eq(Word, k2, k)). False) :
      Eq(Opt(V), MGet(V, MRemove(V, a, k), k2), MGet(V, a, k2)) :=
  -- FIXED-END M9
    ?

  -- FIXED-BEGIN M11
  -- M11 (H11 about the model): the length of the empty map.
  def MLenNew (V : Type) :
      Eq(Word, MLen(V, MNew(V)), Zero) :=
  -- FIXED-END M11
    ?

  -- FIXED-BEGIN M12
  -- M12 (H12 about the model): the length after insert.
  def MLenInsert (V : Type) (a : MMap(V)) (k : Word) (v : V) (h : MInv(V, a)) :
      Eq(Word, MLen(V, MInsert(V, a, k, v)), Grow(IsSomeB(V, MGet(V, a, k)), MLen(V, a))) :=
  -- FIXED-END M12
    ?

  -- FIXED-BEGIN M13
  -- M13 (H13 about the model): the length after remove.
  def MLenRemove (V : Type) (a : MMap(V)) (k : Word) (h : MInv(V, a)) :
      Eq(Word, MLen(V, MRemove(V, a, k)), Shrink(IsSomeB(V, MGet(V, a, k)), MLen(V, a))) :=
  -- FIXED-END M13
    ?

  -- FIXED-BEGIN M14
  -- M14 (H14 about the model): a write has the effect of insert on every lookup.
  def MWriteGet (V : Type) (a : MMap(V)) (k : Word) (w : V) (k2 : Word) (h : MInv(V, a)) (hk : IsTrue(IsSomeB(V, MGet(V, a, k)))) :
      Eq(Opt(V), MGet(V, MWrite(V, a, k, w), k2), MGet(V, MInsert(V, a, k, w), k2)) :=
  -- FIXED-END M14
    ?

  -- FIXED-BEGIN M15
  -- M15 (H15 about the model): ... and on the length.
  def MWriteLen (V : Type) (a : MMap(V)) (k : Word) (w : V) (h : MInv(V, a)) (hk : IsTrue(IsSomeB(V, MGet(V, a, k)))) :
      Eq(Word, MLen(V, MWrite(V, a, k, w)), MLen(V, MInsert(V, a, k, w))) :=
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
  def AbsOf (V : Type) (cap : Word) (m : Map(V, cap)) : MMap(V) := Abs(V, cap, SlotsOf(V, cap, clone(m)), LenField(V, cap, m))
-- FIXED-END solution-header

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

  -- FIXED-BEGIN abs-inv
  -- The invariant on maps gives the model's invariant.
  def AbsInv (V : Type) (cap : Word) (m : &Map(V, cap)) (hm : Inv(V, cap, *m)) : MInv(V, AbsOf(V, cap, *m)) :=
  -- FIXED-END abs-inv
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

  -- FIXED-BEGIN agree-new
  -- Agreement: new(c) is the empty model.
  def AbsNew (V : Type) (cap : Word) (h : Lt(Zero, cap)) :
      Eq(MMap(V), AbsOf(V, cap, MapNew(V, cap, h)), MNew(V)) :=
  -- FIXED-END agree-new
    ?

  -- FIXED-BEGIN agree-len
  -- Agreement: len agrees with the model.
  def AgreeLen (V : Type) (cap : Word) (m : &Map(V, cap)) (hm : Inv(V, cap, *m)) :
      Eq(Word, LenOf(V, cap, *m), MLen(V, AbsOf(V, cap, *m))) :=
  -- FIXED-END agree-len
    ?

  -- FIXED-BEGIN agree-contains
  -- Agreement: contains agrees with the model.
  def AgreeContains (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : Inv(V, cap, *m)) :
      Eq(Bool, ContainsOf(V, cap, *m, k), IsSomeB(V, MGet(V, AbsOf(V, cap, *m), k))) :=
  -- FIXED-END agree-contains
    ?

  -- FIXED-BEGIN agree-get
  -- Agreement: the value read through get agrees with the model.
  def AgreeGet (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : Inv(V, cap, *m))
      (h : Contains(V, cap, *m, k)) :
      Eq(Opt(V), Some(clone(*MapGet(V, cap, m, k, h))), MGet(V, AbsOf(V, cap, *m), k)) :=
  -- FIXED-END agree-get
    ?

  -- FIXED-BEGIN agree-insert
  -- Agreement: insert agrees with the model: the map afterwards.
  def AgreeInsert (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V) (hm : Inv(V, cap, *m)) :
      Eq(MMap(V), (let c = *m; MapInsert(V, cap, &c, k, v); AbsOf(V, cap, c)), MInsert(V, AbsOf(V, cap, *m), k, v)) :=
  -- FIXED-END agree-insert
    ?

  -- FIXED-BEGIN agree-insert-result
  -- Agreement: ... and the value it returns.
  def AgreeInsertResult (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V) (hm : Inv(V, cap, *m)) :
      Eq(Opt(V), (let c = *m; MapInsert(V, cap, &c, k, v)), MGet(V, AbsOf(V, cap, *m), k)) :=
  -- FIXED-END agree-insert-result
    ?

  -- FIXED-BEGIN agree-remove
  -- Agreement: remove agrees with the model: the map afterwards.
  def AgreeRemove (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : Inv(V, cap, *m)) :
      Eq(MMap(V), (let c = *m; MapRemove(V, cap, &c, k); AbsOf(V, cap, c)), MRemove(V, AbsOf(V, cap, *m), k)) :=
  -- FIXED-END agree-remove
    ?

  -- FIXED-BEGIN agree-remove-result
  -- Agreement: ... and the value it returns.
  def AgreeRemoveResult (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : Inv(V, cap, *m)) :
      Eq(Opt(V), (let c = *m; MapRemove(V, cap, &c, k)), MGet(V, AbsOf(V, cap, *m), k)) :=
  -- FIXED-END agree-remove-result
    ?

  -- FIXED-BEGIN agree-write
  -- Agreement: a write through get_mut agrees with the model.
  def AgreeWrite (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (w : V) (hm : Inv(V, cap, *m))
      (hk : Contains(V, cap, *m, k)) :
      Eq(MMap(V), (let c = *m; let r = MapGetMut(V, cap, &c, k, hk); *r := w; AbsOf(V, cap, c)), MWrite(V, AbsOf(V, cap, *m), k, w)) :=
  -- FIXED-END agree-write
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

  -- FIXED-BEGIN H4
  -- H4: contains(new(c), k) = false.
  def ContainsNew (V : Type) (cap : Word) (h : Lt(Zero, cap)) (k : Word) : Eq(Bool, ContainsOf(V, cap, MapNew(V, cap, h), k), false) :=
    -- provided: from the model, by ContainsNewFrom (HashMapCompose)
    ContainsNewFrom(MMap, MapNew, ContainsOf, Inv, AbsOf, MNew, MGet, InvNew, AgreeContains, AbsNew, MGetNew, V, cap, h, k)
  -- FIXED-END H4

  -- FIXED-BEGIN H5a
  -- H5a: after insert(m, k, v), contains(m′, k) = true.
  def ContainsInsertSame (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V) (hm : Inv(V, cap, *m)) :
      Eq(Bool, (let c = *m; MapInsert(V, cap, &c, k, v); ContainsOf(V, cap, c, k)), true) :=
    -- provided: from the model, by ContainsInsertSameFrom (HashMapCompose)
    ContainsInsertSameFrom(MMap, MapInsert, ContainsOf, Inv, AbsOf, MGet, MInsert, MInv, InvInsert, AgreeContains, AgreeInsert, AbsInv, MGetInsertSame, V, cap, m, k, v, hm)
  -- FIXED-END H5a

  -- FIXED-BEGIN H5b
  -- H5b: after insert(m, k, v), the value read through get(m′, k) is v.
  def GetInsertSame (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V) (hm : Inv(V, cap, *m))
      (h : Contains(V, cap, (let c = *m; MapInsert(V, cap, &c, k, v); c), k)) :
      Eq(V, (let c = *m; MapInsert(V, cap, &c, k, v); clone(*MapGet(V, cap, &c, k, h))), v) :=
    -- provided: from the model, by GetInsertSameFrom (HashMapCompose)
    GetInsertSameFrom(MMap, MapInsert, ContainsOf, MapGet, Inv, AbsOf, MGet, MInsert, MInv, InvInsert, AgreeGet, AgreeInsert, AbsInv, MGetInsertSame, V, cap, m, k, v, hm, h)
  -- FIXED-END H5b

  -- FIXED-BEGIN H6a
  -- H6a: after insert(m, k, v), contains(m′, k′) = contains(m, k′) for k′ ≠ k.
  def ContainsInsertOther (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (k2 : Word) (v : V) (hm : Inv(V, cap, *m))
      (ne : Π(e : Eq(Word, k2, k)). False) :
      Eq(Bool, (let c = *m; MapInsert(V, cap, &c, k, v); ContainsOf(V, cap, c, k2)), ContainsOf(V, cap, *m, k2)) :=
    -- provided: from the model, by ContainsInsertOtherFrom (HashMapCompose)
    ContainsInsertOtherFrom(MMap, MapInsert, ContainsOf, Inv, AbsOf, MGet, MInsert, MInv, InvInsert, AgreeContains, AgreeInsert, AbsInv, MGetInsertOther, V, cap, m, k, k2, v, hm, ne)
  -- FIXED-END H6a

  -- FIXED-BEGIN H6b
  -- H6b: ... and the value read through get at k′ is the same, when k′ is present.
  def GetInsertOther (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (k2 : Word) (v : V) (hm : Inv(V, cap, *m))
      (ne : Π(e : Eq(Word, k2, k)). False) (h : Contains(V, cap, *m, k2)) (h2 : Contains(V, cap, (let c = *m; MapInsert(V, cap, &c, k, v); c), k2)) :
      Eq(V, (let c = *m; MapInsert(V, cap, &c, k, v); clone(*MapGet(V, cap, &c, k2, h2))), clone(*MapGet(V, cap, m, k2, h))) :=
    -- provided: from the model, by GetInsertOtherFrom (HashMapCompose)
    GetInsertOtherFrom(MMap, MapInsert, ContainsOf, MapGet, Inv, AbsOf, MGet, MInsert, MInv, InvInsert, AgreeGet, AgreeInsert, AbsInv, MGetInsertOther, V, cap, m, k, k2, v, hm, ne, h, h2)
  -- FIXED-END H6b

  -- FIXED-BEGIN H7a
  -- H7a: insert returns None exactly when k was absent.
  def InsertReturnsContains (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V) (hm : Inv(V, cap, *m)) :
      Eq(Bool, (let c = *m; IsSomeB(V, MapInsert(V, cap, &c, k, v))), ContainsOf(V, cap, *m, k)) :=
    -- provided: from the model, by InsertReturnsContainsFrom (HashMapCompose)
    InsertReturnsContainsFrom(MMap, MapInsert, ContainsOf, Inv, AbsOf, MGet, AgreeContains, AgreeInsertResult, V, cap, m, k, v, hm)
  -- FIXED-END H7a

  -- FIXED-BEGIN H7b
  -- H7b: when k was present, insert returns Some of the value bound to it.
  def InsertReturnsGet (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V) (hm : Inv(V, cap, *m))
      (h : Contains(V, cap, *m, k)) :
      Eq(Opt(V), (let c = *m; MapInsert(V, cap, &c, k, v)), Some(clone(*MapGet(V, cap, m, k, h)))) :=
    -- provided: from the model, by InsertReturnsGetFrom (HashMapCompose)
    InsertReturnsGetFrom(MMap, MapInsert, ContainsOf, MapGet, Inv, AbsOf, MGet, AgreeGet, AgreeInsertResult, V, cap, m, k, v, hm, h)
  -- FIXED-END H7b

  -- FIXED-BEGIN H8
  -- H8: after remove(m, k), contains(m′, k) = false.
  def ContainsRemoveSame (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : Inv(V, cap, *m)) :
      Eq(Bool, (let c = *m; MapRemove(V, cap, &c, k); ContainsOf(V, cap, c, k)), false) :=
    -- provided: from the model, by ContainsRemoveSameFrom (HashMapCompose)
    ContainsRemoveSameFrom(MMap, MapRemove, ContainsOf, Inv, AbsOf, MGet, MRemove, MInv, InvRemove, AgreeContains, AgreeRemove, AbsInv, MGetRemoveSame, V, cap, m, k, hm)
  -- FIXED-END H8

  -- FIXED-BEGIN H9a
  -- H9a: after remove(m, k), contains(m′, k′) = contains(m, k′) for k′ ≠ k.
  def ContainsRemoveOther (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (k2 : Word) (hm : Inv(V, cap, *m))
      (ne : Π(e : Eq(Word, k2, k)). False) :
      Eq(Bool, (let c = *m; MapRemove(V, cap, &c, k); ContainsOf(V, cap, c, k2)), ContainsOf(V, cap, *m, k2)) :=
    -- provided: from the model, by ContainsRemoveOtherFrom (HashMapCompose)
    ContainsRemoveOtherFrom(MMap, MapRemove, ContainsOf, Inv, AbsOf, MGet, MRemove, MInv, InvRemove, AgreeContains, AgreeRemove, AbsInv, MGetRemoveOther, V, cap, m, k, k2, hm, ne)
  -- FIXED-END H9a

  -- FIXED-BEGIN H9b
  -- H9b: ... and the value read through get at k′ is the same, when k′ is present.
  def GetRemoveOther (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (k2 : Word) (hm : Inv(V, cap, *m))
      (ne : Π(e : Eq(Word, k2, k)). False) (h : Contains(V, cap, *m, k2)) (h2 : Contains(V, cap, (let c = *m; MapRemove(V, cap, &c, k); c), k2)) :
      Eq(V, (let c = *m; MapRemove(V, cap, &c, k); clone(*MapGet(V, cap, &c, k2, h2))), clone(*MapGet(V, cap, m, k2, h))) :=
    -- provided: from the model, by GetRemoveOtherFrom (HashMapCompose)
    GetRemoveOtherFrom(MMap, MapRemove, ContainsOf, MapGet, Inv, AbsOf, MGet, MRemove, MInv, InvRemove, AgreeGet, AgreeRemove, AbsInv, MGetRemoveOther, V, cap, m, k, k2, hm, ne, h, h2)
  -- FIXED-END H9b

  -- FIXED-BEGIN H10a
  -- H10a: remove returns None exactly when k was absent.
  def RemoveReturnsContains (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : Inv(V, cap, *m)) :
      Eq(Bool, (let c = *m; IsSomeB(V, MapRemove(V, cap, &c, k))), ContainsOf(V, cap, *m, k)) :=
    -- provided: from the model, by RemoveReturnsContainsFrom (HashMapCompose)
    RemoveReturnsContainsFrom(MMap, MapRemove, ContainsOf, Inv, AbsOf, MGet, AgreeContains, AgreeRemoveResult, V, cap, m, k, hm)
  -- FIXED-END H10a

  -- FIXED-BEGIN H10b
  -- H10b: when k was present, remove returns Some of the value bound to it.
  def RemoveReturnsGet (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : Inv(V, cap, *m))
      (h : Contains(V, cap, *m, k)) :
      Eq(Opt(V), (let c = *m; MapRemove(V, cap, &c, k)), Some(clone(*MapGet(V, cap, m, k, h)))) :=
    -- provided: from the model, by RemoveReturnsGetFrom (HashMapCompose)
    RemoveReturnsGetFrom(MMap, MapRemove, ContainsOf, MapGet, Inv, AbsOf, MGet, AgreeGet, AgreeRemoveResult, V, cap, m, k, hm, h)
  -- FIXED-END H10b

  -- FIXED-BEGIN H11
  -- H11: len(new(c)) = 0.
  def LenNew (V : Type) (cap : Word) (h : Lt(Zero, cap)) : Eq(Word, LenOf(V, cap, MapNew(V, cap, h)), Zero) :=
    -- provided: from the model, by LenNewFrom (HashMapCompose)
    LenNewFrom(MMap, MapNew, LenOf, Inv, AbsOf, MNew, MLen, InvNew, AgreeLen, AbsNew, MLenNew, V, cap, h)
  -- FIXED-END H11

  -- FIXED-BEGIN H12
  -- H12: insert adds one to len if k was absent, and leaves it otherwise.
  def LenInsert (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (v : V) (hm : Inv(V, cap, *m)) :
      Eq(Word, (let c = *m; MapInsert(V, cap, &c, k, v); LenOf(V, cap, c)), Grow(ContainsOf(V, cap, *m, k), LenOf(V, cap, *m))) :=
    -- provided: from the model, by LenInsertFrom (HashMapCompose)
    LenInsertFrom(MMap, MapInsert, ContainsOf, LenOf, Inv, AbsOf, MGet, MLen, MInsert, MInv, InvInsert, AgreeContains, AgreeLen, AgreeInsert, AbsInv, MLenInsert, V, cap, m, k, v, hm)
  -- FIXED-END H12

  -- FIXED-BEGIN H13
  -- H13: remove takes one from len if k was present, and leaves it otherwise.
  def LenRemove (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (hm : Inv(V, cap, *m)) :
      Eq(Word, (let c = *m; MapRemove(V, cap, &c, k); LenOf(V, cap, c)), Shrink(ContainsOf(V, cap, *m, k), LenOf(V, cap, *m))) :=
    -- provided: from the model, by LenRemoveFrom (HashMapCompose)
    LenRemoveFrom(MMap, MapRemove, ContainsOf, LenOf, Inv, AbsOf, MGet, MLen, MRemove, MInv, InvRemove, AgreeContains, AgreeLen, AgreeRemove, AbsInv, MLenRemove, V, cap, m, k, hm)
  -- FIXED-END H13

  -- FIXED-BEGIN H14a
  -- H14a: writing `w` through get_mut(m, k) has the effect of insert(m, k, w) on every contains ...
  def GetMutContains (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (w : V) (k2 : Word) (hm : Inv(V, cap, *m))
      (hk : Contains(V, cap, *m, k)) :
      Eq(Bool, (let c = *m; let r = MapGetMut(V, cap, &c, k, hk); *r := w; ContainsOf(V, cap, c, k2)),
        (let c = *m; MapInsert(V, cap, &c, k, w); ContainsOf(V, cap, c, k2))) :=
    -- provided: from the model, by GetMutContainsFrom (HashMapCompose)
    GetMutContainsFrom(MMap, MapInsert, ContainsOf, MapGetMut, Inv, AbsOf, MGet, MInsert, MWrite, MInv, InvInsert, GetMutInv, AgreeContains, AgreeInsert, AgreeWrite, AbsInv, MWriteGet, V, cap, m, k, w, k2, hm, hk)
  -- FIXED-END H14a

  -- FIXED-BEGIN H14b
  -- H14b: ... and on the value read through get.
  def GetMutGet (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (w : V) (k2 : Word) (hm : Inv(V, cap, *m))
      (hk : Contains(V, cap, *m, k)) (h1 : Contains(V, cap, (let c = *m; let r = MapGetMut(V, cap, &c, k, hk); *r := w; c), k2))
      (h2 : Contains(V, cap, (let c = *m; MapInsert(V, cap, &c, k, w); c), k2)) :
      Eq(V, (let c = *m; let r = MapGetMut(V, cap, &c, k, hk); *r := w; clone(*MapGet(V, cap, &c, k2, h1))),
        (let c = *m; MapInsert(V, cap, &c, k, w); clone(*MapGet(V, cap, &c, k2, h2)))) :=
    -- provided: from the model, by GetMutGetFrom (HashMapCompose)
    GetMutGetFrom(MMap, MapInsert, ContainsOf, MapGet, MapGetMut, Inv, AbsOf, MGet, MInsert, MWrite, MInv, InvInsert, GetMutInv, AgreeContains, AgreeGet, AgreeInsert, AgreeWrite, AbsInv, MWriteGet, V, cap, m, k, w, k2, hm, hk, h1, h2)
  -- FIXED-END H14b

  -- FIXED-BEGIN H15
  -- H15: ... and on len.
  def GetMutLen (V : Type) (cap : Word) (m : &Map(V, cap)) (k : Word) (w : V) (hm : Inv(V, cap, *m))
      (hk : Contains(V, cap, *m, k)) :
      Eq(Word, (let c = *m; let r = MapGetMut(V, cap, &c, k, hk); *r := w; LenOf(V, cap, c)),
        (let c = *m; MapInsert(V, cap, &c, k, w); LenOf(V, cap, c))) :=
    -- provided: from the model, by GetMutLenFrom (HashMapCompose)
    GetMutLenFrom(MMap, MapInsert, ContainsOf, LenOf, MapGetMut, Inv, AbsOf, MGet, MLen, MInsert, MWrite, MInv, InvInsert, GetMutInv, AgreeContains, AgreeLen, AgreeInsert, AgreeWrite, AbsInv, MWriteLen, V, cap, m, k, w, hm, hk)
  -- FIXED-END H15

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
