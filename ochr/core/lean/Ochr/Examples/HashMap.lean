import Ochr.Examples.Array
import Ochr.Examples.Option

/-! # HashMap: a verified hash map

The case study of `notes/hashmap-case-study.md`: the resizing hash map that Aeneas verifies
(ICFP 2022, §6), written once, in place, with its theorems stated and proved about that
program. There is no pure model and no refinement proof: where Aeneas states "after
`insert`, `find_s` of the key is the value" about a hand-written model `find_s`, here the
statement uses the map's own lookup, run on a copy of the map (`Find`, as `Add` runs `AddM`
on a copy).

Values have any type `V`, keys are `Word`s. The table is an array of `n + 1` buckets
(`Array.lean`), each bucket a list of key–value pairs. A map holds its size `n` next to an
array of that many buckets plus one, so the array's type depends on `n` (a dependent field,
`DependentFields.lean`), and resizing replaces both. `Slot` borrows the bucket of a key through
the array's element borrow, as Rust's `&mut slots[i]`; the hash is the identity, as in
Aeneas, and `k mod (n + 1)` picks the bucket, whose bound is a lemma. Keys, sizes and the
length are `Word`s, which reading copies; values move, as in Rust. `Insert` and `Remove`
return the value they move out; `Get` and `MapGetMut` return a borrow of a present key's value
(Ochr has no shared borrows and no borrows inside data, so both take a proof that the key is
present).

The file has four programs: `HashMap`, the implementation; `HashMapLookup`, lookups after each
operation; `HashMapLength`, the length field and the count of entries; `HashMapResize`, the
invariant, resizing, `Insert` with its resize, and the load factor. Each holds only what a later
block uses (the definitions, and the lemmas later proofs call), and is followed by a companion
`…Tests` block, which no block uses, with the rest: the concrete runs, the theorems, and the
negative tests. -/

open Ochr.Test

ochr HashMap uses Bools, Words, Options, Lists, Arrays, ArrayLemmas {
  -- ## The bucket index
  -- `k mod (n + 1)`, `Words`' `ModS`, and its bound: the index is in an array of `n + 1`
  -- buckets. Key comparison (`EqB`), `LtB`, `Pred` and the arithmetic are `Words`'; `Opt` is
  -- `Options`'.
  def Idx (k : Word) (n : Word) : Word := ModS(k, Succ(n))

  def IdxLt (k : Word) (n : Word) : Lt(Idx(k, n), Succ(n)) := ModLt(k, Succ(n), refl)

  -- ## The data
  -- A bucket is a list of key–value pairs. A map of size `n` has `n + 1` buckets (`Slots`
  -- names the array's type, so that the field's type depends on `n` through a type function)
  -- and `len` entries.
  def Bucket (V : Type) : Type := List(Pair(Word, V))
  def Slots (V : Type) (n : Word) : Type := Array(Bucket(V), Succ(n))
  inductive HashMap (V : Type) := HM(n : Word, len : Word, slots : Slots(V, n))

  -- ## Buckets
  -- Test for a key, insert or overwrite it (returning the value it held), remove it
  -- (returning the removed value), and borrow its value. Each returns a value moved out of
  -- the bucket or a borrow into it; none copies one.
  def BContains (V : Type) (b : &Bucket(V)) (k : Word) : Bool by b := (
    match *b {
      Nil => false,
      Cons(e, t) => (
        let (k', _) = e;
        if EqB(k', k) { true } else { BContains(V, &t, k) }
      ),
    }
  )

  def BInsert (V : Type) (b : &Bucket(V)) (k : Word) (v : V) : Opt(V) by b := (
    match *b {
      Nil => (
        *b := Cons((k, v), Nil[Pair(Word, V)]);
        None[V]
      ),
      Cons(e, t) => (
        let (k', v') = e;
        if EqB(k', k) {
          let old = v';
          v' := v;
          Some(old)
        } else {
          BInsert(V, &t, k, v)
        }
      ),
    }
  )

  def BRemove (V : Type) (b : &Bucket(V)) (k : Word) : Opt(V) by b := (
    match *b {
      Nil => None[V],
      Cons(e, t) => (
        let (k', v') = e;
        if EqB(k', k) {
          let x = v';
          *b := t;
          Some(x)
        } else {
          BRemove(V, &t, k)
        }
      ),
    }
  )

  -- The lookup that statements use: the value a key holds, copied (`clone`), or `None`. It
  -- runs on a copy of the bucket, as `Add` runs `AddM` on a copy, so it leaves the bucket as
  -- it was; in a statement the copy is free.
  def BLookup (V : Type) (b : &Bucket(V)) (k : Word) : Opt(V) by b := (
    match *b {
      Nil => None[V],
      Cons(e, t) => (
        let (k', v') = e;
        if EqB(k', k) { Some(clone(v')) } else { BLookup(V, &t, k) }
      ),
    }
  )

  def BFind (V : Type) (b : Bucket(V)) (k : Word) : Opt(V) := BLookup(V, &b, k)

  -- The borrow of a present key's value. The key is present, so the `Nil` arm cannot
  -- happen: there `h` is a proof of `IsSome(V, None)`, which is `False`.
  def BGet (V : Type) (b : &Bucket(V)) (k : Word) (h : IsSome(V, BFind(V, *b, k))) : &V by b := (
    match *b {
      Nil => match h {},
      Cons(e, t) => (
        let (k', v') = e;
        if EqB(k', k) { &v' } else { BGet(V, &t, k, h) }
      ),
    }
  )

  -- ## The slots
  -- The index borrow (Rust's `&mut slots[i]`): the array's element borrow of the key's
  -- bucket, whose bound is `IdxLt`. A fresh table's buckets are all empty.
  def Slot (V : Type) (n : Word) (slots : &Slots(V, n)) (k : Word) : &Bucket(V) :=
    GetMut(Bucket(V), Succ(n), AsSlice(Bucket(V), Succ(n), slots), Idx(k, n), IdxLt(k, n))

  def EmptySlots (V : Type) (n : Word) : Slots(V, n) := ArrFromFn(Bucket(V), Succ(n), λ(i : Word) : Bucket(V) => Nil[Pair(Word, V)])

  -- ## The map
  -- Every operation finds the key's bucket through `Slot` and works on it in place.
  def New (V : Type) (n : Word) : HashMap(V) := HM[V](n, Zero, EmptySlots(V, n))

  -- The lookup on a copy, for statements, and the length field.
  def Lookup (V : Type) (hm : &HashMap(V)) (k : Word) : Opt(V) := (
    let HM(n, _, slots) = *hm;
    let b = Slot(V, n, &slots, k);
    BLookup(V, b, k)
  )

  def Find (V : Type) (m : HashMap(V)) (k : Word) : Opt(V) := Lookup(V, &m, k)

  def Len (V : Type) (m : HashMap(V)) : Word := (
    let HM(_, len, _) = m;
    len
  )

  def ContainsKey (V : Type) (hm : &HashMap(V)) (k : Word) : Bool := (
    let HM(n, _, slots) = *hm;
    let b = Slot(V, n, &slots, k);
    BContains(V, b, k)
  )

  -- `Get` and `MapGetMut` borrow a present key's value: `Get`'s borrow is only read (Ochr has
  -- no shared borrows), `MapGetMut`'s may be written through.
  def Get (V : Type) (hm : &HashMap(V)) (k : Word) (h : IsSome(V, Find(V, *hm, k))) : &V := (
    let HM(n, _, slots) = *hm;
    let b = Slot(V, n, &slots, k);
    BGet(V, b, k, h)
  )

  def MapGetMut (V : Type) (hm : &HashMap(V)) (k : Word) (h : IsSome(V, Find(V, *hm, k))) : &V := (
    let HM(n, _, slots) = *hm;
    let b = Slot(V, n, &slots, k);
    BGet(V, b, k, h)
  )

  -- Insert or overwrite, and remove, each returning the value moved out; the length grows
  -- when the bucket insert found nothing to overwrite, and shrinks when the remove found
  -- something.
  def InsertNoResize (V : Type) (hm : &HashMap(V)) (k : Word) (v : V) : Opt(V) := (
    let HM(n, len, slots) = *hm;
    let b = Slot(V, n, &slots, k);
    let r = BInsert(V, b, k, v);
    match r {
      None => len := Succ(len),
      Some(_) => (),
    };
    r
  )

  def Remove (V : Type) (hm : &HashMap(V)) (k : Word) : Opt(V) := (
    let HM(n, len, slots) = *hm;
    let b = Slot(V, n, &slots, k);
    let x = BRemove(V, b, k);
    match x {
      None => (),
      Some(_) => len := Pred(len),
    };
    x
  )

  def Clear (V : Type) (hm : &HashMap(V)) : Unit := (
    let HM(n, len, slots) = *hm;
    len := Zero;
    slots := EmptySlots(V, n)
  )

  -- ## Resizing
  -- Move every entry into a map with `2n + 2` buckets, by inserting it again. Resizing
  -- happens when the entries outnumber the buckets (load factor 1). The old buckets are
  -- visited by index, each taken out of the old array and replaced by an empty one (Rust's
  -- `mem::take`), so nothing is copied.
  def MoveBucket (V : Type) (b : Bucket(V)) (hm : &HashMap(V)) : Unit by b := (
    match b {
      Nil => (),
      Cons(e, t) => (
        let (k, v) = e;
        InsertNoResize(V, &*hm, k, v);
        MoveBucket(V, t, hm)
      ),
    }
  )

  def Take (V : Type) (n : Word) (s : &Slice(Bucket(V), n)) (i : Word) (h : Lt(i, n)) : Bucket(V) := (
    let r = GetMut(Bucket(V), n, s, i, h);
    let b = *r;
    *r := Nil[Pair(Word, V)];
    b
  )

  -- Buckets `i, …, n - 1`, by recursion on the count `rem` still to go (`rem + i = n`).
  def MoveFrom (V : Type) (n : Word) (s : &Slice(Bucket(V), n)) (i : Word) (rem : Word)
      (hr : Eq(Word, WAdd(rem, i), n)) (hm : &HashMap(V)) : Unit by rem := (
    match rem {
      Zero => (),
      Succ(r) => (
        let hi : Lt(i, n) = (rewrite hr in LeAddL(r, i));
        let hr2 : Eq(Word, WAdd(r, Succ(i)), n) = (rewrite AddRS(r, i) in hr);
        let b = Take(V, n, &*s, i, hi);
        MoveBucket(V, b, &*hm);
        MoveFrom(V, n, s, Succ(i), r, hr2, hm)
      ),
    }
  )

  def Resize (V : Type) (hm : &HashMap(V)) : Unit := (
    let HM(n, _, slots) = *hm;
    let n0 = n;
    let old = slots;
    *hm := New(V, Succ(WAdd(n0, n0)));
    MoveFrom(V, Succ(n0), AsSlice(Bucket(V), Succ(n0), &old), Zero, Succ(n0), AddZeroR(Succ(n0)), hm)
  )

  def Insert (V : Type) (hm : &HashMap(V)) (k : Word) (v : V) : Opt(V) := (
    let r = InsertNoResize(V, &*hm, k, v);
    let HM(n, len, _) = *hm;
    if LtB(n, len) { Resize(V, &*hm) };
    r
  )
}

/-! The concrete runs, at `V := Word`, and the lookup without its `clone`. -/

ochr HashMapTests uses Bools, Words, Options, Lists, Arrays, ArrayLemmas, HashMap {
  -- ## Runs
  -- At `V := Word`. Three inserts into a map with two buckets: the second reaches the load
  -- factor and resizes to four. Every key is found again, an absent one is not.
  def RunLayout : Id(HashMap(Word),
    let m = New(Word, W(1));
    Insert(Word, &m, W(1), W(10));
    Insert(Word, &m, W(2), W(20));
    Insert(Word, &m, W(3), W(30));
    m
  , HM(W(3), W(3), ([Nil, Cons((W(1), W(10)), Nil), Cons((W(2), W(20)), Nil), Cons((W(3), W(30)), Nil)] : Array(Bucket(Word), W(4))))) := refl

  def RunGet : Id(Word × Opt(Word),
    let m = New(Word, W(1));
    Insert(Word, &m, W(1), W(10));
    Insert(Word, &m, W(2), W(20));
    Insert(Word, &m, W(3), W(30));
    let x = *Get(Word, &m, W(2), refl);
    (x, Find(Word, m, W(5)))
  , (W(20), None)) := refl

  reject def RunGetWrong : Id(Word,
    let m = New(Word, W(1));
    Insert(Word, &m, W(1), W(10));
    Insert(Word, &m, W(2), W(20));
    *Get(Word, &m, W(1), refl)
  , W(20)) := refl

  def RunContains : Id(Bool × Bool,
    let m = New(Word, W(1));
    Insert(Word, &m, W(1), W(10));
    Insert(Word, &m, W(2), W(20));
    let a = ContainsKey(Word, &m, W(2));
    (a, ContainsKey(Word, &m, W(3)))
  , (true, false)) := refl

  -- Overwriting returns the old value and keeps the length.
  def RunOverwrite : Id(Opt(Word) × (Word × Word),
    let m = New(Word, W(1));
    Insert(Word, &m, W(1), W(10));
    Insert(Word, &m, W(2), W(20));
    let r = Insert(Word, &m, W(2), W(25));
    let l = Len(Word, clone(m));
    (r, (l, *Get(Word, &m, W(2), refl)))
  , (Some(W(20)), (W(2), W(25)))) := refl

  -- `5` collides with `1` in a map with four buckets.
  def RunCollide : Id(HashMap(Word),
    let m = New(Word, W(3));
    Insert(Word, &m, W(1), W(10));
    Insert(Word, &m, W(5), W(50));
    m
  , HM(W(3), W(2), ([Nil, Cons((W(1), W(10)), Cons((W(5), W(50)), Nil)), Nil, Nil] : Array(Bucket(Word), W(4))))) := refl

  -- Remove returns the value it removed; removing an absent key does nothing.
  def RunRemove : Id(Opt(Word) × HashMap(Word),
    let m = New(Word, W(3));
    Insert(Word, &m, W(1), W(10));
    Insert(Word, &m, W(5), W(50));
    let x = Remove(Word, &m, W(1));
    Remove(Word, &m, W(7));
    (x, m)
  , (Some(W(10)), HM(W(3), W(1), ([Nil, Cons((W(5), W(50)), Nil), Nil, Nil] : Array(Bucket(Word), W(4)))))) := refl

  -- Write through the borrow of a present key. For an absent key the proof `refl` of
  -- `IsSome(Word, Find(Word, m, 5))` does not exist: the precondition computes to `False`.
  def RunGetMut : Id(Word,
    let m = New(Word, W(3));
    Insert(Word, &m, W(1), W(10));
    Insert(Word, &m, W(5), W(50));
    let q = MapGetMut(Word, &m, W(5), refl);
    *q := W(55);
    *Get(Word, &m, W(5), refl)
  , W(55)) := refl

  reject def RunGetMutAbsent : Id(Word,
    let m = New(Word, W(3));
    Insert(Word, &m, W(1), W(10));
    let q = MapGetMut(Word, &m, W(5), refl);
    *q := W(55);
    *Get(Word, &m, W(5), refl)
  , W(55)) := refl

  -- Clear empties the map and keeps the number of buckets.
  def RunClear : Id(HashMap(Word),
    let m = New(Word, W(1));
    Insert(Word, &m, W(1), W(10));
    Clear(Word, &m);
    m
  , New(Word, W(1))) := refl

  -- Without its `clone`, the lookup would move the value out of a bucket it only borrows,
  -- and the borrow would end with the bucket partly moved out.
  reject def BLookupMoves (V : Type) (b : &Bucket(V)) (k : Word) : Opt(V) by b := (
    match *b {
      Nil => None,
      Cons(e, t) => (
        let (k', v') = e;
        if EqB(k', k) { Some(v') } else { BLookupMoves(V, &t, k) }
      ),
    }
  )
}

/-! ## Lookups after each operation

Each theorem says what `Find` returns after an operation, for the key it touched and for
any other key. The statements use the operations themselves: "after `InsertNoResize(hm, k,
v)`, `Find(*hm, k)` is `Some(v)`" is `Id(Opt(V), (InsertNoResize(V, &*hm, k, v); Find(V,
clone(*hm), k)), (InsertNoResize(V, &*hm, k, clone(v)); Some(v)))`. Each is proved first for
one bucket, by recursion on the bucket, then lifted through the array's element borrow by
recursion on the index, following `GetMut`'s own recursion, then stated for the map. -/

ochr HashMapLookup uses Bools, Words, Options, Lists, Arrays, ArrayLemmas, HashMap {
  -- ## Key comparison
  -- Where the comparison says the keys are equal, they are. `Succ(a) = Succ(b)` is
  -- `a = b` (injectivity), so the recursive call proves the `Succ` case as it stands.
  def EqBSound (a : Word) (b : Word) (h : Eq(Bool, EqB(a, b), true)) : Eq(Word, a, b) by a := (
    match a {
      Zero => match b {
        Zero => refl,
        Succ(_) => match h {},
      },
      Succ(a') => match b {
        Zero => match h {},
        Succ(b') => EqBSound(a', b', h),
      },
    }
  )

  def EqBTrans (a : Word) (b : Word) (c : Word) (h1 : Eq(Bool, EqB(a, b), true)) (h2 : Eq(Bool, EqB(a, c), true)) :
      Eq(Bool, EqB(b, c), true) := rewrite EqBSound(a, b, h1) in h2

  -- A bucket key equal to both `k` and `k2` contradicts `k ≠ k2`.
  def EqBContra (a : Word) (b : Word) (c : Word) (h1 : Eq(Bool, EqB(a, b), true)) (h2 : Eq(Bool, EqB(a, c), true))
      (h : Eq(Bool, EqB(b, c), false)) : False := (
    if EqB(b, c) { match h {} } else { match EqBTrans(a, b, c, h1, h2) {} }
  )

  -- ## Insert, in one bucket
  -- After inserting `k`, looking `k` up gives the inserted value. In the `Nil` arm the
  -- lookup compares `k` with itself, which the checker cannot compute for an abstract `k`:
  -- split on it, and the `false` arm contradicts `EqBRefl`.
  def BInsertFind (V : Type) (b : &Bucket(V)) (k : Word) (v : V) :
      Id(Opt(V), (BInsert(V, &*b, k, v); BFind(V, clone(*b), k)), (BInsert(V, &*b, k, clone(v)); Some(v))) by b := (
    match *b {
      Nil => if EqB(k, k) { refl } else { match EqBRefl(k) {} },
      Cons(e, t) => (
        let (k', _) = e;
        if EqB(k', k) { refl } else { BInsertFind(V, &t, k, v) }
      ),
    }
  )

  -- Inserting `k` does not change the lookup of another key `k2`.
  def BInsertFindOther (V : Type) (b : &Bucket(V)) (k : Word) (v : V) (k2 : Word) (h : Eq(Bool, EqB(k, k2), false)) :
      Id(Opt(V), (BInsert(V, &*b, k, v); BFind(V, clone(*b), k2)), (let r = BFind(V, clone(*b), k2); BInsert(V, &*b, k, v); r)) by b := (
    match *b {
      Nil => if EqB(k, k2) { match h {} } else { refl },
      Cons(e, t) => (
        let (k', _) = e;
        if EqB(k', k) {
          if EqB(k', k2) { match EqBContra(k', k, k2, refl, refl, h) {} } else { refl }
        } else if EqB(k', k2) {
          refl
        } else {
          BInsertFindOther(V, &t, k, v, k2, h)
        }
      ),
    }
  )

  -- The insert returns what the lookup would have returned: the old value, or `None`.
  def BInsertResult (V : Type) (b : &Bucket(V)) (k : Word) (v : V) :
      Id(Opt(V), BInsert(V, &*b, k, v), (let r = BFind(V, clone(*b), k); BInsert(V, &*b, k, v); r)) by b := (
    match *b {
      Nil => refl,
      Cons(e, t) => (
        let (k', _) = e;
        if EqB(k', k) { refl } else { BInsertResult(V, &t, k, v) }
      ),
    }
  )

  -- ## Insert, through the element borrow
  -- `NthS(V, n, s, i, h)` takes bucket `i` out of a copy of the view `s` through the
  -- element borrow (leaving an empty one, as Rust's `mem::take`): at an unknown index its
  -- normal form is the same sealed program as the bucket the closed-off lookup reads. Each
  -- bucket theorem is lifted by recursion on the index, following `GetMut`'s own recursion:
  -- the recursive call borrows the rest of the view, so the untouched buckets stay where
  -- they are and need no argument.
  def NthS (V : Type) (n : Word) (s : Slice(Bucket(V), n)) (i : Word) (h : Lt(i, n)) : Bucket(V) := (
    let c = s;
    let r = GetMut(Bucket(V), n, &c, i, h);
    let b = *r;
    *r := Nil[Pair(Word, V)];
    b
  )

  def SlotInsertFind (V : Type) (n : Word) (s : &Slice(Bucket(V), n)) (i : Word) (hi : Lt(i, n)) (k : Word) (v : V) :
      Id(Opt(V), (let b = GetMut(Bucket(V), n, &*s, i, hi); BInsert(V, b, k, v); BFind(V, NthS(V, n, clone(*s), i, hi), k)),
        (let b = GetMut(Bucket(V), n, &*s, i, hi); BInsert(V, b, k, clone(v)); Some(v))) by i := (
    match n {
      Zero => match hi {},
      Succ(m) => (
        let MkSlice(MkC(x, t)) = *s;
        match i {
          Zero => BInsertFind(V, &x, k, v),
          Succ(i') => SlotInsertFind(V, m, &t, i', hi, k, v),
        }
      ),
    }
  )

  -- Writing bucket `i` and reading bucket `j`: the same bucket is the bucket theorem,
  -- different buckets do not interact.
  def SlotInsertFindOther (V : Type) (n : Word) (s : &Slice(Bucket(V), n)) (i : Word) (hi : Lt(i, n)) (j : Word) (hj : Lt(j, n))
      (k : Word) (v : V) (k2 : Word) (h : Eq(Bool, EqB(k, k2), false)) :
      Id(Opt(V), (let b = GetMut(Bucket(V), n, &*s, i, hi); BInsert(V, b, k, v); BFind(V, NthS(V, n, clone(*s), j, hj), k2)),
        (let r = BFind(V, NthS(V, n, clone(*s), j, hj), k2); let b = GetMut(Bucket(V), n, &*s, i, hi); BInsert(V, b, k, v); r)) by i := (
    match n {
      Zero => match hi {},
      Succ(m) => (
        let MkSlice(MkC(x, t)) = *s;
        match i {
          Zero => match j {
            Zero => BInsertFindOther(V, &x, k, v, k2, h),
            Succ(_) => refl,
          },
          Succ(i') => match j {
            Zero => refl,
            Succ(j') => SlotInsertFindOther(V, m, &t, i', hi, j', hj, k, v, k2, h),
          },
        }
      ),
    }
  )

  def SlotInsertResult (V : Type) (n : Word) (s : &Slice(Bucket(V), n)) (i : Word) (hi : Lt(i, n)) (k : Word) (v : V) :
      Id(Opt(V), (let b = GetMut(Bucket(V), n, &*s, i, hi); BInsert(V, b, k, v)),
        (let r = BFind(V, NthS(V, n, clone(*s), i, hi), k); let b = GetMut(Bucket(V), n, &*s, i, hi); BInsert(V, b, k, v); r)) by i := (
    match n {
      Zero => match hi {},
      Succ(m) => (
        let MkSlice(MkC(x, t)) = *s;
        match i {
          Zero => BInsertResult(V, &x, k, v),
          Succ(i') => SlotInsertResult(V, m, &t, i', hi, k, v),
        }
      ),
    }
  )

  -- ## Insert, in the map
  -- `InsertNoResize` updates the length according to what the bucket insert returned. That
  -- result is a sealed program; `split BInsert` splits on it, in each arm the map computes,
  -- and the slot theorem applies. The view is reached by taking the array apart, which a
  -- proof may do (the representation is abstract only at runtime).
  def InsertFind (V : Type) (hm : &HashMap(V)) (k : Word) (v : V) :
      Id(Opt(V), (InsertNoResize(V, &*hm, k, v); Find(V, clone(*hm), k)), (InsertNoResize(V, &*hm, k, clone(v)); Some(v))) := (
    let HM(n, _, MkArray(s)) = *hm;
    split BInsert in SlotInsertFind(V, Succ(n), &s, Idx(k, n), IdxLt(k, n), k, v)
  )

  def InsertFindOther (V : Type) (hm : &HashMap(V)) (k : Word) (v : V) (k2 : Word) (h : Eq(Bool, EqB(k, k2), false)) :
      Id(Opt(V), (InsertNoResize(V, &*hm, k, v); Find(V, clone(*hm), k2)), (let r = Find(V, clone(*hm), k2); InsertNoResize(V, &*hm, k, v); r)) := (
    let HM(n, _, MkArray(s)) = *hm;
    split BInsert in
      SlotInsertFindOther(V, Succ(n), &s, Idx(k, n), IdxLt(k, n), Idx(k2, n), IdxLt(k2, n), k, v, k2, h)
  )

  -- Insert returns what `Find` returned before it: the old value, or `None`.
  def InsertResult (V : Type) (hm : &HashMap(V)) (k : Word) (v : V) :
      Id(Opt(V), InsertNoResize(V, &*hm, k, v), (let r = Find(V, clone(*hm), k); InsertNoResize(V, &*hm, k, v); r)) := (
    let HM(n, _, MkArray(s)) = *hm;
    split BInsert in SlotInsertResult(V, Succ(n), &s, Idx(k, n), IdxLt(k, n), k, v)
  )

  -- ## Remove
  -- A bucket's keys are distinct (part of the invariant): each key is absent from the rest
  -- of the bucket, stated with the lookup itself. Across the table, every bucket; of a map,
  -- its table (a proposition may take the array apart).
  def Unique (V : Type) (b : Bucket(V)) : Prop by b := (
    match b {
      Nil => ⊤,
      Cons(e, t) => (
        let (k, _) = e;
        Eq(Opt(V), BFind(V, t, k), None[V]) ∧ Unique(V, t)
      ),
    }
  )

  def AllUnique (V : Type) (n : Word) (s : Slice(Bucket(V), n)) : Prop by n := (
    match n {
      Zero => ⊤,
      Succ(m) => (
        let MkSlice(MkC(b, t)) = s;
        Unique(V, b) ∧ AllUnique(V, m, t)
      ),
    }
  )

  def KeysUnique (V : Type) (m : HashMap(V)) : Prop := (
    let HM(n, _, MkArray(s)) = m;
    AllUnique(V, Succ(n), s)
  )

  -- Remove returns what a lookup would have returned.
  def BRemoveResult (V : Type) (b : &Bucket(V)) (k : Word) :
      Id(Opt(V), BRemove(V, &*b, k), (let r = BFind(V, clone(*b), k); BRemove(V, &*b, k); r)) by b := (
    match *b {
      Nil => refl,
      Cons(e, t) => (
        let (k', _) = e;
        if EqB(k', k) { refl } else { BRemoveResult(V, &t, k) }
      ),
    }
  )

  def BRemoveFindOther (V : Type) (b : &Bucket(V)) (k : Word) (k2 : Word) (h : Eq(Bool, EqB(k, k2), false)) :
      Id(Opt(V), (BRemove(V, &*b, k); BFind(V, clone(*b), k2)), (let r = BFind(V, clone(*b), k2); BRemove(V, &*b, k); r)) by b := (
    match *b {
      Nil => refl,
      Cons(e, t) => (
        let (k', _) = e;
        if EqB(k', k) {
          if EqB(k', k2) { match EqBContra(k', k, k2, refl, refl, h) {} } else { refl }
        } else if EqB(k', k2) {
          refl
        } else {
          BRemoveFindOther(V, &t, k, k2, h)
        }
      ),
    }
  )

  -- Lifted through the element borrow, and stated for the map. The precondition of
  -- `RemoveFind` is the part of the invariant it needs: the keys of each bucket are
  -- distinct.
  def SlotRemoveResult (V : Type) (n : Word) (s : &Slice(Bucket(V), n)) (i : Word) (hi : Lt(i, n)) (k : Word) :
      Id(Opt(V), (let b = GetMut(Bucket(V), n, &*s, i, hi); BRemove(V, b, k)),
        (let r = BFind(V, NthS(V, n, clone(*s), i, hi), k); let b = GetMut(Bucket(V), n, &*s, i, hi); BRemove(V, b, k); r)) by i := (
    match n {
      Zero => match hi {},
      Succ(m) => (
        let MkSlice(MkC(x, t)) = *s;
        match i {
          Zero => BRemoveResult(V, &x, k),
          Succ(i') => SlotRemoveResult(V, m, &t, i', hi, k),
        }
      ),
    }
  )

  -- ## MapGetMut is an insert
  -- Writing `w` through the borrow is inserting `k ↦ w`: the key is present, so the
  -- insert overwrites and adds nothing (and returns the old value, which the write drops).
  -- Every other theorem about `MapGetMut` follows from the insert's.
  def BGetMutIsInsert (V : Type) (b : &Bucket(V)) (k : Word) (w : V) (h : IsSome(V, BFind(V, *b, k))) :
      Id(Unit, (let q = BGet(V, &*b, k, h); *q := w), (BInsert(V, &*b, k, w); ())) by b := (
    match *b {
      Nil => match h {},
      Cons(e, t) => (
        let (k', _) = e;
        if EqB(k', k) { refl } else { BGetMutIsInsert(V, &t, k, w, h) }
      ),
    }
  )

  def SlotGetMutIsInsert (V : Type) (n : Word) (s : &Slice(Bucket(V), n)) (i : Word) (hi : Lt(i, n)) (k : Word) (w : V)
      (h : IsSome(V, BFind(V, NthS(V, n, *s, i, hi), k))) :
      Id(Unit, (let b = GetMut(Bucket(V), n, &*s, i, hi); let q = BGet(V, b, k, h); *q := w),
        (let b = GetMut(Bucket(V), n, &*s, i, hi); BInsert(V, b, k, w); ())) by i := (
    match n {
      Zero => match hi {},
      Succ(m) => (
        let MkSlice(MkC(x, t)) = *s;
        match i {
          Zero => BGetMutIsInsert(V, &x, k, w, h),
          Succ(i') => SlotGetMutIsInsert(V, m, &t, i', hi, k, w, h),
        }
      ),
    }
  )

  -- The map inserts through the same borrow; where the insert would have added an entry,
  -- `SlotInsertResult` says the key was absent, against the precondition.
  def GetMutIsInsert (V : Type) (hm : &HashMap(V)) (k : Word) (w : V) (h : IsSome(V, Find(V, *hm, k))) :
      Id(Unit, (let q = MapGetMut(V, &*hm, k, h); *q := w), (InsertNoResize(V, &*hm, k, w); ())) := (
    let HM(n, _, MkArray(s)) = *hm;
    let p = SlotInsertResult(V, Succ(n), &s, Idx(k, n), IdxLt(k, n), k, w);
    let r = BFind(V, NthS(V, Succ(n), clone(s), Idx(k, n), IdxLt(k, n)), k);
    split BInsert {
      None => match r {
        None => match h {},
        Some(_) => match p {},
      },
      Some(_) => SlotGetMutIsInsert(V, Succ(n), &s, Idx(k, n), IdxLt(k, n), k, w, h),
    }
  )

  -- ## New and Clear
  -- Every bucket of a fresh table is empty, so no key is found. `EmptyFrom(V, n, j)` is the
  -- view `ArrFromFn` builds for `EmptySlots`, from element `j` on (the model `FromFnS`).
  def EmptyFrom (V : Type) (n : Word) (j : Word) : Slice(Bucket(V), n) := FromFnS(Bucket(V), n, λ(i : Word) : Bucket(V) => Nil[Pair(Word, V)], j)

  def EmptyLookup (V : Type) (n : Word) (j : Word) (i : Word) (h : Lt(i, n)) (k : Word) :
      Id(Opt(V), (let c = EmptyFrom(V, n, j); BLookup(V, GetMut(Bucket(V), n, &c, i, h), k)), None[V]) by n := (
    match n {
      Zero => match h {},
      Succ(m) => match i {
        Zero => refl,
        Succ(i') => EmptyLookup(V, m, Succ(j), i', h, k),
      },
    }
  )

  def NewFind (V : Type) (n : Word) (k : Word) : Id(Opt(V), Find(V, New(V, n), k), None[V]) := (
    EmptyLookup(V, Succ(n), Zero, Idx(k, n), IdxLt(k, n), k)
  )
}

/-! The lookup theorems that no later block uses: after remove, get_mut, clear; `Get` and
`ContainsKey` agree with `Find`; and the negative tests. -/

ochr HashMapLookupTests uses Bools, Words, Options, Lists, Arrays, ArrayLemmas, HashMap, HashMapLookup {
  -- Without the split the goal is stuck on the sealed `InsertNoResize` and does not meet
  -- the slot theorem's statement.
  reject def InsertFindNoSplit (V : Type) (hm : &HashMap(V)) (k : Word) (v : V) :
      Id(Opt(V), (InsertNoResize(V, &*hm, k, v); Find(V, clone(*hm), k)), (InsertNoResize(V, &*hm, k, clone(v)); Some(v))) := (
    let HM(n, _, MkArray(s)) = *hm;
    SlotInsertFind(V, Succ(n), &s, Idx(k, n), IdxLt(k, n), k, v)
  )

  -- After removing `k`, looking `k` up gives `None`, if the keys are distinct. Where the
  -- first `k` is removed, the rest of the bucket does not hold `k'`, which is `k`: rewrite
  -- along `k' = k`.
  def BRemoveFind (V : Type) (b : &Bucket(V)) (k : Word) (h : Unique(V, clone(*b))) :
      Id(Opt(V), (BRemove(V, &*b, k); BFind(V, clone(*b), k)), (BRemove(V, &*b, k); None[V])) by b := (
    match *b {
      Nil => refl,
      Cons(e, t) => (
        let (k', _) = e;
        let ⟨absent, rest⟩ = h;
        if EqB(k', k) { rewrite EqBSound(k', k, refl) in absent } else { BRemoveFind(V, &t, k, rest) }
      ),
    }
  )

  reject def BRemoveFindDup (V : Type) (b : &Bucket(V)) (k : Word) :
      Id(Opt(V), (BRemove(V, &*b, k); BFind(V, clone(*b), k)), (BRemove(V, &*b, k); None[V])) by b := (
    match *b {
      Nil => refl,
      Cons(e, t) => (
        let (k', _) = e;
        if EqB(k', k) { refl } else { BRemoveFindDup(V, &t, k) }
      ),
    }
  )

  def SlotRemoveFind (V : Type) (n : Word) (s : &Slice(Bucket(V), n)) (i : Word) (hi : Lt(i, n)) (k : Word)
      (h : AllUnique(V, n, clone(*s))) :
      Id(Opt(V), (let b = GetMut(Bucket(V), n, &*s, i, hi); BRemove(V, b, k); BFind(V, NthS(V, n, clone(*s), i, hi), k)),
        (let b = GetMut(Bucket(V), n, &*s, i, hi); BRemove(V, b, k); None[V])) by i := (
    match n {
      Zero => match hi {},
      Succ(m) => (
        let MkSlice(MkC(x, t)) = *s;
        let ⟨hb, ht⟩ = h;
        match i {
          Zero => BRemoveFind(V, &x, k, hb),
          Succ(i') => SlotRemoveFind(V, m, &t, i', hi, k, ht),
        }
      ),
    }
  )

  def SlotRemoveFindOther (V : Type) (n : Word) (s : &Slice(Bucket(V), n)) (i : Word) (hi : Lt(i, n)) (j : Word) (hj : Lt(j, n))
      (k : Word) (k2 : Word) (h : Eq(Bool, EqB(k, k2), false)) :
      Id(Opt(V), (let b = GetMut(Bucket(V), n, &*s, i, hi); BRemove(V, b, k); BFind(V, NthS(V, n, clone(*s), j, hj), k2)),
        (let r = BFind(V, NthS(V, n, clone(*s), j, hj), k2); let b = GetMut(Bucket(V), n, &*s, i, hi); BRemove(V, b, k); r)) by i := (
    match n {
      Zero => match hi {},
      Succ(m) => (
        let MkSlice(MkC(x, t)) = *s;
        match i {
          Zero => match j {
            Zero => BRemoveFindOther(V, &x, k, k2, h),
            Succ(_) => refl,
          },
          Succ(i') => match j {
            Zero => refl,
            Succ(j') => SlotRemoveFindOther(V, m, &t, i', hi, j', hj, k, k2, h),
          },
        }
      ),
    }
  )

  def RemoveResult (V : Type) (hm : &HashMap(V)) (k : Word) :
      Id(Opt(V), Remove(V, &*hm, k), (let r = Find(V, clone(*hm), k); Remove(V, &*hm, k); r)) := (
    let HM(n, _, MkArray(s)) = *hm;
    split BRemove in SlotRemoveResult(V, Succ(n), &s, Idx(k, n), IdxLt(k, n), k)
  )

  def RemoveFind (V : Type) (hm : &HashMap(V)) (k : Word) (h : KeysUnique(V, clone(*hm))) :
      Id(Opt(V), (Remove(V, &*hm, k); Find(V, clone(*hm), k)), (Remove(V, &*hm, k); None[V])) := (
    let HM(n, _, MkArray(s)) = *hm;
    split BRemove in SlotRemoveFind(V, Succ(n), &s, Idx(k, n), IdxLt(k, n), k, h)
  )

  def RemoveFindOther (V : Type) (hm : &HashMap(V)) (k : Word) (k2 : Word) (h : Eq(Bool, EqB(k, k2), false)) :
      Id(Opt(V), (Remove(V, &*hm, k); Find(V, clone(*hm), k2)), (let r = Find(V, clone(*hm), k2); Remove(V, &*hm, k); r)) := (
    let HM(n, _, MkArray(s)) = *hm;
    split BRemove in
      SlotRemoveFindOther(V, Succ(n), &s, Idx(k, n), IdxLt(k, n), Idx(k2, n), IdxLt(k2, n), k, k2, h)
  )

  -- ## MapGetMut
  -- The borrow points at the value a lookup returns. In the `Nil` arm the precondition is
  -- `IsSome(V, None)`, which is `False`.
  def BGetMutRead (V : Type) (b : &Bucket(V)) (k : Word) (w : V) (h : IsSome(V, BFind(V, clone(*b), k))) :
      Id(Opt(V), (let q = BGet(V, &*b, k, h); let x = clone(*q); *q := w; Some(x)),
        (let r = BFind(V, clone(*b), k); let q = BGet(V, &*b, k, h); *q := w; r)) by b := (
    match *b {
      Nil => match h {},
      Cons(e, t) => (
        let (k', _) = e;
        if EqB(k', k) { refl } else { BGetMutRead(V, &t, k, w, h) }
      ),
    }
  )

  -- Lifted through the element borrow, and stated for the map. `MapGetMut` branches on no
  -- sealed result, so the map theorem is the slot theorem at the key's index.
  def SlotGetMutRead (V : Type) (n : Word) (s : &Slice(Bucket(V), n)) (i : Word) (hi : Lt(i, n)) (k : Word) (w : V)
      (h : IsSome(V, BFind(V, NthS(V, n, clone(*s), i, hi), k))) :
      Id(Opt(V), (let b = GetMut(Bucket(V), n, &*s, i, hi); let q = BGet(V, b, k, h); let x = clone(*q); *q := w; Some(x)),
        (let r = BFind(V, NthS(V, n, clone(*s), i, hi), k); let b = GetMut(Bucket(V), n, &*s, i, hi); let q = BGet(V, b, k, h); *q := w; r)) by i := (
    match n {
      Zero => match hi {},
      Succ(m) => (
        let MkSlice(MkC(x, t)) = *s;
        match i {
          Zero => BGetMutRead(V, &x, k, w, h),
          Succ(i') => SlotGetMutRead(V, m, &t, i', hi, k, w, h),
        }
      ),
    }
  )

  def MapGetMutRead (V : Type) (hm : &HashMap(V)) (k : Word) (w : V) (h : IsSome(V, Find(V, clone(*hm), k))) :
      Id(Opt(V), (let q = MapGetMut(V, &*hm, k, h); let x = clone(*q); *q := w; Some(x)),
        (let r = Find(V, clone(*hm), k); let q = MapGetMut(V, &*hm, k, h); *q := w; r)) := (
    let HM(n, _, MkArray(s)) = *hm;
    SlotGetMutRead(V, Succ(n), &s, Idx(k, n), IdxLt(k, n), k, w, h)
  )

  def GetMutFind (V : Type) (hm : &HashMap(V)) (k : Word) (w : V) (h : IsSome(V, Find(V, clone(*hm), k))) :
      Id(Opt(V), (let q = MapGetMut(V, &*hm, k, h); *q := w; Find(V, clone(*hm), k)),
        (let q = MapGetMut(V, &*hm, k, h); *q := clone(w); Some(w))) := (
    rewrite ← GetMutIsInsert(V, &*hm, k, w, h) in InsertFind(V, &*hm, k, w)
  )

  def GetMutFindOther (V : Type) (hm : &HashMap(V)) (k : Word) (w : V) (h : IsSome(V, Find(V, clone(*hm), k))) (k2 : Word)
      (ne : Eq(Bool, EqB(k, k2), false)) :
      Id(Opt(V), (let q = MapGetMut(V, &*hm, k, h); *q := w; Find(V, clone(*hm), k2)),
        (let r = Find(V, clone(*hm), k2); let q = MapGetMut(V, &*hm, k, h); *q := w; r)) := (
    rewrite ← GetMutIsInsert(V, &*hm, k, w, h) in InsertFindOther(V, &*hm, k, w, k2, ne)
  )

  -- ## Get, through the borrow
  -- `Get` returns a mutable borrow (Ochr has no shared borrows), only read. When the
  -- lookup is stuck on an abstract bucket, closing it off leaves a sealed program in the
  -- bucket ("borrow `k`'s value in `u`, then give `u` back"), which is `u` only by a proof.
  -- These three lemmas are that proof: reading through `Get`'s borrow gives what `Find`
  -- returns, and leaves the map as it was.
  def BGetFind (V : Type) (b : &Bucket(V)) (k : Word) (h : IsSome(V, BFind(V, clone(*b), k))) :
      Id(Opt(V), Some(clone(*BGet(V, &*b, k, h))), BFind(V, clone(*b), k)) by b := (
    match *b {
      Nil => match h {},
      Cons(e, t) => (
        let (k', _) = e;
        if EqB(k', k) { refl } else { BGetFind(V, &t, k, h) }
      ),
    }
  )

  def SlotGetFind (V : Type) (n : Word) (s : &Slice(Bucket(V), n)) (i : Word) (hi : Lt(i, n)) (k : Word)
      (h : IsSome(V, BFind(V, NthS(V, n, clone(*s), i, hi), k))) :
      Id(Opt(V), (let b = GetMut(Bucket(V), n, &*s, i, hi); Some(clone(*BGet(V, b, k, h)))), BFind(V, NthS(V, n, clone(*s), i, hi), k)) by i := (
    match n {
      Zero => match hi {},
      Succ(m) => (
        let MkSlice(MkC(x, t)) = *s;
        match i {
          Zero => BGetFind(V, &x, k, h),
          Succ(i') => SlotGetFind(V, m, &t, i', hi, k, h),
        }
      ),
    }
  )

  def GetFind (V : Type) (hm : &HashMap(V)) (k : Word) (h : IsSome(V, Find(V, clone(*hm), k))) :
      Id(Opt(V), Some(clone(*Get(V, &*hm, k, h))), Find(V, clone(*hm), k)) := (
    let HM(n, _, MkArray(s)) = *hm;
    SlotGetFind(V, Succ(n), &s, Idx(k, n), IdxLt(k, n), k, h)
  )

  -- `ContainsKey` also reads through the borrow: it says whether `Find` finds the key.
  def Has (V : Type) (o : Opt(V)) : Bool := (
    match o {
      None => false,
      Some(_) => true,
    }
  )

  def BContainsFind (V : Type) (b : &Bucket(V)) (k : Word) : Id(Bool, BContains(V, &*b, k), Has(V, BFind(V, clone(*b), k))) by b := (
    match *b {
      Nil => refl,
      Cons(e, t) => (
        let (k', _) = e;
        if EqB(k', k) { refl } else { BContainsFind(V, &t, k) }
      ),
    }
  )

  def SlotContainsFind (V : Type) (n : Word) (s : &Slice(Bucket(V), n)) (i : Word) (hi : Lt(i, n)) (k : Word) :
      Id(Bool, (let b = GetMut(Bucket(V), n, &*s, i, hi); BContains(V, b, k)), Has(V, BFind(V, NthS(V, n, clone(*s), i, hi), k))) by i := (
    match n {
      Zero => match hi {},
      Succ(m) => (
        let MkSlice(MkC(x, t)) = *s;
        match i {
          Zero => BContainsFind(V, &x, k),
          Succ(i') => SlotContainsFind(V, m, &t, i', hi, k),
        }
      ),
    }
  )

  def ContainsFind (V : Type) (hm : &HashMap(V)) (k : Word) : Id(Bool, ContainsKey(V, &*hm, k), Has(V, Find(V, clone(*hm), k))) := (
    let HM(n, _, MkArray(s)) = *hm;
    SlotContainsFind(V, Succ(n), &s, Idx(k, n), IdxLt(k, n), k)
  )

  def ClearFind (V : Type) (hm : &HashMap(V)) (k : Word) : Id(Opt(V), (Clear(V, &*hm); Find(V, clone(*hm), k)), (Clear(V, &*hm); None[V])) := (
    let HM(n, _, _) = *hm;
    NewFind(V, n, k)
  )
}

/-! ## The length

`Len` is the map's `len` field. After an insert it grows by one exactly when the key was
absent, and after a remove it shrinks by one exactly when the key was present; with the
invariant `len = Entries(slots)` (the number of entries, `Counted`), each operation keeps
it. The number of entries reads every bucket, so it is a model function of the array's view
(it takes the view by value), and `Counted` is a proposition, which may take the array apart:
the invariant is stated on a copy of the map. -/

ochr HashMapLength uses Bools, Words, Options, Lists, Arrays, ArrayLemmas, HashMap, HashMapLookup {
  -- Sizes, and the ways a length changes.
  def BLen (V : Type) (b : Bucket(V)) : Word by b := (
    match b {
      Nil => Zero,
      Cons(e, t) => Succ(BLen(V, t)),
    }
  )

  def Entries (V : Type) (n : Word) (s : Slice(Bucket(V), n)) : Word by n := (
    match n {
      Zero => Zero,
      Succ(m) => (
        let MkSlice(MkC(b, t)) = s;
        WAdd(BLen(V, b), Entries(V, m, t))
      ),
    }
  )

  def Counted (V : Type) (m : HashMap(V)) : Prop := (
    let HM(n, len, MkArray(s)) = m;
    Eq(Word, len, Entries(V, Succ(n), s))
  )

  def IfNew (V : Type) (r : Opt(V)) (l : Word) : Word := (
    match r {
      None => Succ(l),
      Some(_) => l,
    }
  )

  def IfFound (V : Type) (r : Opt(V)) (l : Word) : Word := (
    match r {
      None => l,
      Some(_) => Succ(l),
    }
  )

  -- ## The len field
  -- Split on what the bucket insert returned and on the earlier lookup; where they
  -- disagree, `SlotInsertResult`'s type is `None = Some(…)` or `Some(…) = None`, which is
  -- `False`.
  def InsertLen (V : Type) (hm : &HashMap(V)) (k : Word) (v : V) :
      Id(Word, (InsertNoResize(V, &*hm, k, v); Len(V, clone(*hm))),
        (let l = Len(V, clone(*hm)); let r = Find(V, clone(*hm), k); InsertNoResize(V, &*hm, k, v); IfNew(V, r, l))) := (
    let HM(n, _, MkArray(s)) = *hm;
    let p = SlotInsertResult(V, Succ(n), &s, Idx(k, n), IdxLt(k, n), k, v);
    split BInsert {
      None => split BLookup {
        None => refl,
        Some(_) => match p {},
      },
      Some(_) => split BLookup {
        None => match p {},
        Some(_) => refl,
      },
    }
  )

  -- ## The invariant len = Entries(slots), for insert
  -- A bucket grows by one exactly when the key was absent. `Succ(a) = Succ(b)` is
  -- `a = b`, so each arm is the induction hypothesis as it stands.
  def BInsertCount (V : Type) (b : &Bucket(V)) (k : Word) (v : V) :
      Id(Word, (let r = BFind(V, clone(*b), k); let l = BLen(V, clone(*b)); BInsert(V, &*b, k, v); IfNew(V, r, l)),
        (BInsert(V, &*b, k, v); BLen(V, clone(*b)))) by b := (
    match *b {
      Nil => refl,
      Cons(e, t) => (
        let (k', _) = e;
        if EqB(k', k) { refl } else { split BLookup in BInsertCount(V, &t, k, v) }
      ),
    }
  )

  -- Lifted to the view, where `Entries` adds the bucket lengths: each arm rewrites once
  -- under the addition.
  def SlotInsertCount (V : Type) (n : Word) (s : &Slice(Bucket(V), n)) (i : Word) (hi : Lt(i, n)) (k : Word) (v : V) :
      Id(Word, (let r = BFind(V, NthS(V, n, clone(*s), i, hi), k); let c = Entries(V, n, clone(*s)); let b = GetMut(Bucket(V), n, &*s, i, hi); BInsert(V, b, k, v); IfNew(V, r, c)),
        (let b = GetMut(Bucket(V), n, &*s, i, hi); BInsert(V, b, k, v); Entries(V, n, clone(*s)))) by i := (
    match n {
      Zero => match hi {},
      Succ(m) => (
        let MkSlice(MkC(x, t)) = *s;
        match i {
          Zero => split BLookup in rewrite BInsertCount(V, &x, k, v) in refl,
          Succ(i') => split BLookup {
            None => rewrite SlotInsertCount(V, m, &t, i', hi, k, v) in rewrite ← AddRS(BLen(V, x), Entries(V, m, t)) in refl,
            Some(_) => rewrite SlotInsertCount(V, m, &t, i', hi, k, v) in refl,
          },
        }
      ),
    }
  )

  -- The map: split on what the bucket insert returned and on the earlier lookup (the
  -- mixed arms contradict `SlotInsertResult`), then one rewrite against the hypothesis.
  def InsertCount (V : Type) (m : HashMap(V)) (k : Word) (v : V) (h : Counted(V, m)) :
      (let c = m; InsertNoResize(V, &c, k, v); Counted(V, c)) := (
    let HM(n, _, MkArray(s)) = m;
    let p = SlotInsertResult(V, Succ(n), &s, Idx(k, n), IdxLt(k, n), k, v);
    let r = BFind(V, NthS(V, Succ(n), clone(s), Idx(k, n), IdxLt(k, n)), k);
    split BInsert {
      None => match r {
        None => rewrite SlotInsertCount(V, Succ(n), &s, Idx(k, n), IdxLt(k, n), k, v) in h,
        Some(_) => match p {},
      },
      Some(_) => match r {
        None => match p {},
        Some(_) => rewrite SlotInsertCount(V, Succ(n), &s, Idx(k, n), IdxLt(k, n), k, v) in h,
      },
    }
  )

  -- ## Remove
  -- The len field shrinks by one exactly when the key was found (the code's `Pred`).
  def Shrink (V : Type) (r : Opt(V)) (l : Word) : Word := (
    match r {
      None => l,
      Some(_) => Pred(l),
    }
  )

  -- The count before a remove is the count after, plus one if the key was found.
  def BRemoveCount (V : Type) (b : &Bucket(V)) (k : Word) :
      Id(Word, (let l = BLen(V, clone(*b)); BRemove(V, &*b, k); l),
        (let r = BFind(V, clone(*b), k); BRemove(V, &*b, k); IfFound(V, r, BLen(V, clone(*b))))) by b := (
    match *b {
      Nil => refl,
      Cons(e, t) => (
        let (k', _) = e;
        if EqB(k', k) { refl } else { split BLookup in BRemoveCount(V, &t, k) }
      ),
    }
  )

  def SlotRemoveCount (V : Type) (n : Word) (s : &Slice(Bucket(V), n)) (i : Word) (hi : Lt(i, n)) (k : Word) :
      Id(Word, (let c = Entries(V, n, clone(*s)); let b = GetMut(Bucket(V), n, &*s, i, hi); BRemove(V, b, k); c),
        (let r = BFind(V, NthS(V, n, clone(*s), i, hi), k); let b = GetMut(Bucket(V), n, &*s, i, hi); BRemove(V, b, k); IfFound(V, r, Entries(V, n, clone(*s))))) by i := (
    match n {
      Zero => match hi {},
      Succ(m) => (
        let MkSlice(MkC(x, t)) = *s;
        match i {
          Zero => split BLookup {
            None => rewrite BRemoveCount(V, &x, k) in refl,
            Some(_) => rewrite ← BRemoveCount(V, &x, k) in refl,
          },
          Succ(i') => split BLookup {
            None => rewrite SlotRemoveCount(V, m, &t, i', hi, k) in refl,
            Some(_) => (
              let ct = clone(t);
              let rb = GetMut(Bucket(V), m, &ct, i', hi);
              BRemove(V, rb, k);
              rewrite ← SlotRemoveCount(V, m, &t, i', hi, k) in symm(AddRS(BLen(V, x), Entries(V, m, ct)))
            ),
          },
        }
      ),
    }
  )

  def RemoveCount (V : Type) (m : HashMap(V)) (k : Word) (h : Counted(V, m)) :
      (let c = m; Remove(V, &c, k); Counted(V, c)) := (
    let HM(n, _, MkArray(s)) = m;
    let p = SlotRemoveResult(V, Succ(n), &s, Idx(k, n), IdxLt(k, n), k);
    let r = BFind(V, NthS(V, Succ(n), clone(s), Idx(k, n), IdxLt(k, n)), k);
    split BRemove {
      None => match r {
        None => rewrite SlotRemoveCount(V, Succ(n), &s, Idx(k, n), IdxLt(k, n), k) in h,
        Some(_) => match p {},
      },
      Some(_) => match r {
        None => match p {},
        Some(_) => rewrite ← h in rewrite ← SlotRemoveCount(V, Succ(n), &s, Idx(k, n), IdxLt(k, n), k) in refl,
      },
    }
  )

  -- ## New and Clear
  def EmptyCount (V : Type) (n : Word) (j : Word) :
      Eq(Word, Entries(V, n, EmptyFrom(V, n, j)), Zero) by n := (
    match n {
      Zero => refl,
      Succ(m) => EmptyCount(V, m, Succ(j)),
    }
  )

  def NewCount (V : Type) (n : Word) : Counted(V, New(V, n)) := rewrite ← EmptyCount(V, Succ(n), Zero) in refl
}

/-! The length theorems that no later block uses, and the negative test. -/

ochr HashMapLengthTests uses Bools, Words, Options, Lists, Arrays, ArrayLemmas, HashMap, HashMapLookup, HashMapLength {
  -- The hypothesis is needed.
  reject def InsertCountNoHyp (V : Type) (m : HashMap(V)) (k : Word) (v : V) :
      (let c = m; InsertNoResize(V, &c, k, v); Counted(V, c)) := (
    let HM(n, _, MkArray(s)) = m;
    SlotInsertCount(V, Succ(n), &s, Idx(k, n), IdxLt(k, n), k, v)
  )

  def RemoveLen (V : Type) (hm : &HashMap(V)) (k : Word) :
      Id(Word, (Remove(V, &*hm, k); Len(V, clone(*hm))),
        (let l = Len(V, clone(*hm)); let r = Find(V, clone(*hm), k); Remove(V, &*hm, k); Shrink(V, r, l))) := (
    let HM(n, _, MkArray(s)) = *hm;
    let p = SlotRemoveResult(V, Succ(n), &s, Idx(k, n), IdxLt(k, n), k);
    split BRemove {
      None => split BLookup {
        None => refl,
        Some(_) => match p {},
      },
      Some(_) => split BLookup {
        None => match p {},
        Some(_) => refl,
      },
    }
  )

  def ClearCount (V : Type) (m : HashMap(V)) : (let c = m; Clear(V, &c); Counted(V, c)) := (
    let HM(n, _, _) = m;
    NewCount(V, n)
  )

  -- ## MapGetMut
  -- Writing through the borrow leaves the length as it was.
  def GetMutLen (V : Type) (hm : &HashMap(V)) (k : Word) (w : V) (h : IsSome(V, Find(V, clone(*hm), k))) :
      Id(Word, (let q = MapGetMut(V, &*hm, k, h); *q := w; Len(V, clone(*hm))),
        (let l = Len(V, clone(*hm)); let q = MapGetMut(V, &*hm, k, h); *q := w; l)) := (
    let HM(_, _, _) = *hm;
    refl
  )
}

/-! ## The invariant, and resizing

The invariant (Aeneas's `hash_map_t_inv`, less its load-factor and overflow clauses): the
length counts the entries, the keys of each bucket are distinct, and every key lies only in
its own bucket. The last is a statement about every key, `Π(k : Word). OnlyIn(…)`, proved
for each key by a function of `k`. Every operation keeps the invariant, stated as "run the
operation on a copy, then the invariant holds of the copy". Resizing moves every entry with
`InsertNoResize`, so it keeps every lookup; with the invariant, the insert with resizing
behaves like the insert without. Resizing visits the old buckets by index, so what it has
still to move is stated as a list, `Rest`: the old buckets from an index on. -/

ochr HashMapResize uses Bools, Words, Options, Lists, Arrays, ArrayLemmas, HashMap, HashMapLookup, HashMapLength {

  -- ## Keys stay in their bucket
  -- `k` is in no bucket of the view; in none but bucket `d`; and every key is only in the
  -- bucket the index gives it.
  def Nowhere (V : Type) (n : Word) (s : Slice(Bucket(V), n)) (k : Word) : Prop by n := (
    match n {
      Zero => ⊤,
      Succ(m) => (
        let MkSlice(MkC(b, t)) = s;
        Eq(Opt(V), BFind(V, b, k), None[V]) ∧ Nowhere(V, m, t, k)
      ),
    }
  )

  def OnlyIn (V : Type) (n : Word) (s : Slice(Bucket(V), n)) (d : Word) (k : Word) : Prop by n := (
    match n {
      Zero => ⊤,
      Succ(m) => (
        let MkSlice(MkC(b, t)) = s;
        match d {
          Zero => Nowhere(V, m, t, k),
          Succ(d') => Eq(Opt(V), BFind(V, b, k), None[V]) ∧ OnlyIn(V, m, t, d', k),
        }
      ),
    }
  )

  def Placed (V : Type) (n : Word) (s : Slice(Bucket(V), Succ(n))) : Prop := Π(k : Word). OnlyIn(V, Succ(n), s, Idx(k, n), k)

  -- ## The invariant
  -- The length counts the entries, the keys of each bucket are distinct, and every key
  -- lies only in its own bucket (all three are Aeneas's `hash_map_t_inv`, less its load
  -- factor and overflow clauses).
  def Inv (V : Type) (m : HashMap(V)) : Prop := (
    let HM(n, len, MkArray(s)) = m;
    Eq(Word, len, Entries(V, Succ(n), s)) ∧ (AllUnique(V, Succ(n), s) ∧ Placed(V, n, s))
  )

  -- ## Resizing keeps every lookup
  -- Re-inserting overwrites, so after moving a bucket (or the buckets still to move) into a
  -- map, a key's lookup is its last occurrence in what was moved, or else what it was before.
  -- That needs no hypothesis. The invariant then says the last occurrence of `k` in the old
  -- buckets is the one `Find` sees: `k` is only in its own bucket, and at most once.
  def OrElse (V : Type) (a : Opt(V)) (b : Opt(V)) : Opt(V) := (
    match a {
      None => b,
      Some(x) => Some(x),
    }
  )

  def BFindLast (V : Type) (b : Bucket(V)) (k : Word) : Opt(V) by b := (
    match b {
      Nil => None[V],
      Cons(e, t) => (
        let (k', v') = e;
        if EqB(k', k) { OrElse(V, BFindLast(V, t, k), Some(v')) } else { BFindLast(V, t, k) }
      ),
    }
  )

  -- The old buckets still to move: `Rest` lists the buckets of the view from `i` on, and the
  -- lookup of a list of buckets is the last occurrence. Taking bucket `i` out gives it and
  -- leaves an empty bucket in its place (`TakeV`), which `Rest` from `i + 1` on does not see.
  def Rest (V : Type) (n : Word) (s : Slice(Bucket(V), n)) (i : Word) (rem : Word) (hr : Eq(Word, WAdd(rem, i), n)) :
      List(Bucket(V)) by rem := (
    match rem {
      Zero => Nil[Bucket(V)],
      Succ(r) => (
        let hi : Lt(i, n) = (rewrite hr in LeAddL(r, i));
        let hr2 : Eq(Word, WAdd(r, Succ(i)), n) = (rewrite AddRS(r, i) in hr);
        Cons(Nth(Bucket(V), n, clone(s), i, hi), Rest(V, n, s, Succ(i), r, hr2))
      ),
    }
  )

  def FindLast (V : Type) (l : List(Bucket(V))) (k : Word) : Opt(V) by l := (
    match l {
      Nil => None[V],
      Cons(b, t) => OrElse(V, FindLast(V, t, k), BFindLast(V, b, k)),
    }
  )

  -- `k` is in no bucket of a list; a view's `Nowhere` is its buckets'.
  def NowhereL (V : Type) (l : List(Bucket(V))) (k : Word) : Prop by l := (
    match l {
      Nil => ⊤,
      Cons(b, t) => Eq(Opt(V), BFind(V, b, k), None[V]) ∧ NowhereL(V, t, k),
    }
  )

  -- The keys of `b` are absent from the map `m`.
  def Fresh (V : Type) (b : Bucket(V)) (m : HashMap(V)) : Prop by b := (
    match b {
      Nil => ⊤,
      Cons(e, t) => (
        let (k, _) = e;
        Eq(Opt(V), Find(V, m, k), None[V]) ∧ Fresh(V, t, m)
      ),
    }
  )

  -- Over a list of buckets: the entries, the keys absent from `m`, the keys of `b'` not in
  -- `b`, every bucket apart from `b`, and the keys distinct within and across buckets.
  def CountL (V : Type) (l : List(Bucket(V))) : Word by l := (
    match l {
      Nil => Zero,
      Cons(b, t) => WAdd(BLen(V, b), CountL(V, t)),
    }
  )

  def FreshL (V : Type) (l : List(Bucket(V))) (m : HashMap(V)) : Prop by l := (
    match l {
      Nil => ⊤,
      Cons(b, t) => Fresh(V, b, m) ∧ FreshL(V, t, m),
    }
  )

  def AbsentFrom (V : Type) (b' : Bucket(V)) (b : Bucket(V)) : Prop by b' := (
    match b' {
      Nil => ⊤,
      Cons(e, r) => (
        let (k, _) = e;
        Eq(Opt(V), BFind(V, b, k), None[V]) ∧ AbsentFrom(V, r, b)
      ),
    }
  )

  def ApartL (V : Type) (l : List(Bucket(V))) (b : Bucket(V)) : Prop by l := (
    match l {
      Nil => ⊤,
      Cons(b', t) => AbsentFrom(V, b', b) ∧ ApartL(V, t, b),
    }
  )

  def GUniqueL (V : Type) (l : List(Bucket(V))) : Prop by l := (
    match l {
      Nil => ⊤,
      Cons(b, t) => Unique(V, b) ∧ (ApartL(V, t, b) ∧ GUniqueL(V, t)),
    }
  )

  -- ## The load factor
  -- The entries do not outnumber the buckets: `len ≤ n`, with `n + 1` buckets. `Insert`
  -- keeps it by resizing (as Aeneas's `hash_map_not_overloaded_lem`, with a load factor
  -- of 1 rather than a configurable fraction).
  def NOf (V : Type) (m : HashMap(V)) : Word := (
    let HM(n, _, _) = m;
    n
  )

  def NotOver (V : Type) (m : HashMap(V)) : Prop := Eq(Bool, LtB(NOf(V, clone(m)), Len(V, m)), false)
}

/-! The theorems: the invariant and its preservation, resizing, insert with its resize,
and the load factor. -/

ochr HashMapResizeTests uses Bools, Words, Options, Lists, Arrays, ArrayLemmas, HashMap, HashMapLookup, HashMapLength, HashMapResize {
  -- ## Helpers
  def EqBSymm (a : Word) (b : Word) (h : Eq(Bool, EqB(a, b), true)) : Eq(Bool, EqB(b, a), true) := (
    rewrite EqBSound(a, b, h) in EqBRefl(a)
  )

  def NeqFlip (a : Word) (b : Word) (h : Eq(Bool, EqB(a, b), false)) : Eq(Bool, EqB(b, a), false) := (
    if EqB(b, a) {
      let p = EqBSymm(b, a, refl);
      if EqB(a, b) { match h {} } else { match p {} }
    } else {
      refl
    }
  )

  -- ## Keys stay distinct
  def BInsertUnique (V : Type) (b : Bucket(V)) (k : Word) (v : V) (h : Unique(V, b)) :
      (let c = b; BInsert(V, &c, k, v); Unique(V, c)) by b := (
    match b {
      Nil => ⟨refl, refl⟩,
      Cons(e, t) => (
        let (k', _) = e;
        let ⟨absent, rest⟩ = h;
        if EqB(k', k) {
          ⟨absent, rest⟩
        } else {
          ⟨rewrite ← BInsertFindOther(V, &t, k, v, k', NeqFlip(k', k, refl)) in absent, BInsertUnique(V, t, k, v, rest)⟩
        }
      ),
    }
  )

  def SlotInsertUnique (V : Type) (n : Word) (s : Slice(Bucket(V), n)) (i : Word) (hi : Lt(i, n)) (k : Word) (v : V)
      (h : AllUnique(V, n, s)) : (let c = s; let b = GetMut(Bucket(V), n, &c, i, hi); BInsert(V, b, k, v); AllUnique(V, n, c)) by n := (
    match n {
      Zero => match hi {},
      Succ(m) => (
        let MkSlice(MkC(x, t)) = s;
        let ⟨hb, ht⟩ = h;
        match i {
          Zero => ⟨BInsertUnique(V, x, k, v, hb), ht⟩,
          Succ(i') => ⟨hb, SlotInsertUnique(V, m, t, i', hi, k, v, ht)⟩,
        }
      ),
    }
  )

  def BRemoveUnique (V : Type) (b : Bucket(V)) (k : Word) (h : Unique(V, b)) : (let c = b; BRemove(V, &c, k); Unique(V, c)) by b := (
    match b {
      Nil => refl,
      Cons(e, t) => (
        let (k', _) = e;
        let ⟨absent, rest⟩ = h;
        if EqB(k', k) {
          rest
        } else {
          ⟨rewrite ← BRemoveFindOther(V, &t, k, k', NeqFlip(k', k, refl)) in absent, BRemoveUnique(V, t, k, rest)⟩
        }
      ),
    }
  )

  def SlotRemoveUnique (V : Type) (n : Word) (s : Slice(Bucket(V), n)) (i : Word) (hi : Lt(i, n)) (k : Word)
      (h : AllUnique(V, n, s)) : (let c = s; let b = GetMut(Bucket(V), n, &c, i, hi); BRemove(V, b, k); AllUnique(V, n, c)) by n := (
    match n {
      Zero => match hi {},
      Succ(m) => (
        let MkSlice(MkC(x, t)) = s;
        let ⟨hb, ht⟩ = h;
        match i {
          Zero => ⟨BRemoveUnique(V, x, k, hb), ht⟩,
          Succ(i') => ⟨hb, SlotRemoveUnique(V, m, t, i', hi, k, ht)⟩,
        }
      ),
    }
  )

  -- ## Keys stay in their bucket
  -- Inserting `k` keeps another key absent where it was absent.
  def BInsertAbsent (V : Type) (b : Bucket(V)) (k : Word) (v : V) (k2 : Word) (ne : Eq(Bool, EqB(k, k2), false))
      (h : Eq(Opt(V), BFind(V, b, k2), None[V])) : (let c = b; BInsert(V, &c, k, v); Eq(Opt(V), BFind(V, c, k2), None[V])) := (
    rewrite ← BInsertFindOther(V, &b, k, v, k2, ne) in h
  )

  def NowhereInsert (V : Type) (n : Word) (s : Slice(Bucket(V), n)) (i : Word) (hi : Lt(i, n)) (k : Word) (v : V) (k2 : Word)
      (ne : Eq(Bool, EqB(k, k2), false)) (h : Nowhere(V, n, s, k2)) :
      (let c = s; let b = GetMut(Bucket(V), n, &c, i, hi); BInsert(V, b, k, v); Nowhere(V, n, c, k2)) by n := (
    match n {
      Zero => match hi {},
      Succ(m) => (
        let MkSlice(MkC(x, t)) = s;
        let ⟨hb, ht⟩ = h;
        match i {
          Zero => ⟨BInsertAbsent(V, x, k, v, k2, ne, hb), ht⟩,
          Succ(i') => ⟨hb, NowhereInsert(V, m, t, i', hi, k, v, k2, ne, ht)⟩,
        }
      ),
    }
  )

  def OnlyInOther (V : Type) (n : Word) (s : Slice(Bucket(V), n)) (i : Word) (hi : Lt(i, n)) (d : Word) (k : Word) (v : V)
      (k2 : Word) (ne : Eq(Bool, EqB(k, k2), false)) (h : OnlyIn(V, n, s, d, k2)) :
      (let c = s; let b = GetMut(Bucket(V), n, &c, i, hi); BInsert(V, b, k, v); OnlyIn(V, n, c, d, k2)) by n := (
    match n {
      Zero => match hi {},
      Succ(m) => (
        let MkSlice(MkC(x, t)) = s;
        match d {
          Zero => match i {
            Zero => h,
            Succ(i') => NowhereInsert(V, m, t, i', hi, k, v, k2, ne, h),
          },
          Succ(d') => (
            let ⟨hb, ht⟩ = h;
            match i {
              Zero => ⟨BInsertAbsent(V, x, k, v, k2, ne, hb), ht⟩,
              Succ(i') => ⟨hb, OnlyInOther(V, m, t, i', hi, d', k, v, k2, ne, ht)⟩,
            }
          ),
        }
      ),
    }
  )

  def OnlyInSame (V : Type) (n : Word) (s : Slice(Bucket(V), n)) (i : Word) (hi : Lt(i, n)) (k : Word) (v : V)
      (h : OnlyIn(V, n, s, i, k)) : (let c = s; let b = GetMut(Bucket(V), n, &c, i, hi); BInsert(V, b, k, v); OnlyIn(V, n, c, i, k)) by n := (
    match n {
      Zero => match hi {},
      Succ(m) => (
        let MkSlice(MkC(_, t)) = s;
        match i {
          Zero => h,
          Succ(i') => (
            let ⟨hb, ht⟩ = h;
            ⟨hb, OnlyInSame(V, m, t, i', hi, k, v, ht)⟩
          ),
        }
      ),
    }
  )

  -- For every key `k2`: if it is `k`, it went into its own bucket; if not, it did not move.
  def SlotInsertPlaced (V : Type) (n : Word) (s : Slice(Bucket(V), Succ(n))) (k : Word) (v : V) (h : Placed(V, n, s)) :
      (let c = s; let b = GetMut(Bucket(V), Succ(n), &c, Idx(k, n), IdxLt(k, n)); BInsert(V, b, k, v); Placed(V, n, c)) := (
    let c = clone(s);
    let b = GetMut(Bucket(V), Succ(n), &c, Idx(k, n), IdxLt(k, n));
    BInsert(V, b, k, clone(v));
    λ(k2 : Word) : OnlyIn(V, Succ(n), c, Idx(k2, n), k2) => (
      if EqB(k, k2) {
        rewrite EqBSound(k, k2, refl) in OnlyInSame(V, Succ(n), s, Idx(k, n), IdxLt(k, n), k, v, h(k))
      } else {
        OnlyInOther(V, Succ(n), s, Idx(k, n), IdxLt(k, n), Idx(k2, n), k, v, k2, refl, h(k2))
      }
    )
  )

  -- Removing never makes a key present.
  def BRemoveAbsent (V : Type) (b : Bucket(V)) (k : Word) (k2 : Word) (h : Eq(Opt(V), BFind(V, b, k2), None[V])) :
      (let c = b; BRemove(V, &c, k); Eq(Opt(V), BFind(V, c, k2), None[V])) by b := (
    match b {
      Nil => refl,
      Cons(e, t) => (
        let (k', _) = e;
        if EqB(k', k2) { match h {} } else { if EqB(k', k) { h } else { BRemoveAbsent(V, t, k, k2, h) } }
      ),
    }
  )

  def NowhereRemove (V : Type) (n : Word) (s : Slice(Bucket(V), n)) (i : Word) (hi : Lt(i, n)) (k : Word) (k2 : Word)
      (h : Nowhere(V, n, s, k2)) : (let c = s; let b = GetMut(Bucket(V), n, &c, i, hi); BRemove(V, b, k); Nowhere(V, n, c, k2)) by n := (
    match n {
      Zero => match hi {},
      Succ(m) => (
        let MkSlice(MkC(x, t)) = s;
        let ⟨hb, ht⟩ = h;
        match i {
          Zero => ⟨BRemoveAbsent(V, x, k, k2, hb), ht⟩,
          Succ(i') => ⟨hb, NowhereRemove(V, m, t, i', hi, k, k2, ht)⟩,
        }
      ),
    }
  )

  def OnlyInRemove (V : Type) (n : Word) (s : Slice(Bucket(V), n)) (i : Word) (hi : Lt(i, n)) (d : Word) (k : Word) (k2 : Word)
      (h : OnlyIn(V, n, s, d, k2)) : (let c = s; let b = GetMut(Bucket(V), n, &c, i, hi); BRemove(V, b, k); OnlyIn(V, n, c, d, k2)) by n := (
    match n {
      Zero => match hi {},
      Succ(m) => (
        let MkSlice(MkC(x, t)) = s;
        match d {
          Zero => match i {
            Zero => h,
            Succ(i') => NowhereRemove(V, m, t, i', hi, k, k2, h),
          },
          Succ(d') => (
            let ⟨hb, ht⟩ = h;
            match i {
              Zero => ⟨BRemoveAbsent(V, x, k, k2, hb), ht⟩,
              Succ(i') => ⟨hb, OnlyInRemove(V, m, t, i', hi, d', k, k2, ht)⟩,
            }
          ),
        }
      ),
    }
  )

  def SlotRemovePlaced (V : Type) (n : Word) (s : Slice(Bucket(V), Succ(n))) (k : Word) (h : Placed(V, n, s)) :
      (let c = s; let b = GetMut(Bucket(V), Succ(n), &c, Idx(k, n), IdxLt(k, n)); BRemove(V, b, k); Placed(V, n, c)) := (
    let c = clone(s);
    let b = GetMut(Bucket(V), Succ(n), &c, Idx(k, n), IdxLt(k, n));
    BRemove(V, b, k);
    λ(k2 : Word) : OnlyIn(V, Succ(n), c, Idx(k2, n), k2) => OnlyInRemove(V, Succ(n), s, Idx(k, n), IdxLt(k, n), Idx(k2, n), k, k2, h(k2))
  )

  -- ## The invariant
  -- A new map has it, and each operation keeps it.
  def NowhereEmpty (V : Type) (n : Word) (j : Word) (k : Word) :
      Nowhere(V, n, EmptyFrom(V, n, j), k) by n := (
    match n {
      Zero => refl,
      Succ(m) => ⟨refl, NowhereEmpty(V, m, Succ(j), k)⟩,
    }
  )

  def OnlyInEmpty (V : Type) (n : Word) (j : Word) (d : Word) (k : Word) :
      OnlyIn(V, n, EmptyFrom(V, n, j), d, k) by n := (
    match n {
      Zero => refl,
      Succ(m) => match d {
        Zero => NowhereEmpty(V, m, Succ(j), k),
        Succ(d') => ⟨refl, OnlyInEmpty(V, m, Succ(j), d', k)⟩,
      },
    }
  )

  def UniqueEmpty (V : Type) (n : Word) (j : Word) : AllUnique(V, n, EmptyFrom(V, n, j)) by n := (
    match n {
      Zero => refl,
      Succ(m) => ⟨refl, UniqueEmpty(V, m, Succ(j))⟩,
    }
  )

  def NewInv (V : Type) (n : Word) : Inv(V, New(V, n)) := (
    let hu : AllUnique(V, Succ(n), EmptyFrom(V, Succ(n), Zero)) = UniqueEmpty(V, Succ(n), Zero);
    let hp : Placed(V, n, EmptyFrom(V, Succ(n), Zero)) = (
      λ(k : Word) : OnlyIn(V, Succ(n), EmptyFrom(V, Succ(n), Zero), Idx(k, n), k) =>
        OnlyInEmpty(V, Succ(n), Zero, Idx(k, n), k));
    ⟨NewCount(V, n), ⟨hu, hp⟩⟩
  )

  -- Each operation keeps it. Split on what the bucket operation returned, as for the
  -- length theorems; the three parts are the lemmas above.
  def InsertInv (V : Type) (m : HashMap(V)) (k : Word) (v : V) (h : Inv(V, m)) : (let c = m; InsertNoResize(V, &c, k, v); Inv(V, c)) := (
    let HM(n, _, MkArray(s)) = m;
    let ⟨hl, hu, hp⟩ = h;
    split BInsert in ⟨InsertCount(V, clone(m), k, v, hl), ⟨SlotInsertUnique(V, Succ(n), s, Idx(k, n), IdxLt(k, n), k, v, hu), SlotInsertPlaced(V, n, s, k, v, hp)⟩⟩
  )

  def RemoveInv (V : Type) (m : HashMap(V)) (k : Word) (h : Inv(V, m)) : (let c = m; Remove(V, &c, k); Inv(V, c)) := (
    let HM(n, _, MkArray(s)) = m;
    let ⟨hl, hu, hp⟩ = h;
    split BRemove in ⟨RemoveCount(V, clone(m), k, hl), ⟨SlotRemoveUnique(V, Succ(n), s, Idx(k, n), IdxLt(k, n), k, hu), SlotRemovePlaced(V, n, s, k, hp)⟩⟩
  )

  def ClearInv (V : Type) (m : HashMap(V)) : (let c = m; Clear(V, &c); Inv(V, c)) := (
    let HM(n, _, _) = m;
    NewInv(V, n)
  )

  -- `MapGetMut` keeps the invariant, because writing through it is an insert (`GetMutIsInsert`).
  def GetMutInv (V : Type) (m : HashMap(V)) (k : Word) (w : V) (h : IsSome(V, Find(V, m, k))) (hi : Inv(V, m)) :
      (let c = m; let q = MapGetMut(V, &c, k, h); *q := w; Inv(V, c)) := (
    rewrite ← GetMutIsInsert(V, &m, k, w, h) in InsertInv(V, m, k, w, hi)
  )

  -- ## Resizing keeps the invariant
  -- Every entry is moved by `InsertNoResize`, which keeps the invariant, into a fresh
  -- table, which has it: so the result has it, whatever the old map was. Each step's
  -- induction hypothesis is about the old view as the step leaves it, and the map after the
  -- bucket it moved, both sealed programs: no lemma about the take is needed.
  def MoveBucketInv (V : Type) (b : Bucket(V)) (m : HashMap(V)) (h : Inv(V, m)) : (let c = m; MoveBucket(V, b, &c); Inv(V, c)) by b := (
    match b {
      Nil => h,
      Cons(e, t) => (
        let (k, v) = e;
        let m2 = clone(m);
        InsertNoResize(V, &m2, k, clone(v));
        MoveBucketInv(V, t, m2, InsertInv(V, m, k, v, h))
      ),
    }
  )

  def MoveFromInv (V : Type) (n : Word) (s : Slice(Bucket(V), n)) (i : Word) (rem : Word) (hr : Eq(Word, WAdd(rem, i), n))
      (m : HashMap(V)) (h : Inv(V, m)) : (let c = m; let o = s; MoveFrom(V, n, &o, i, rem, hr, &c); Inv(V, c)) by rem := (
    match rem {
      Zero => h,
      Succ(r) => (
        let hi : Lt(i, n) = (rewrite hr in LeAddL(r, i));
        let hr2 : Eq(Word, WAdd(r, Succ(i)), n) = (rewrite AddRS(r, i) in hr);
        let o = clone(s);
        let b = Take(V, n, &o, i, hi);
        let m2 = clone(m);
        MoveBucket(V, clone(b), &m2);
        MoveFromInv(V, n, o, Succ(i), r, hr2, m2, MoveBucketInv(V, b, m, h))
      ),
    }
  )

  def ResizeInv (V : Type) (m : HashMap(V)) : (let c = m; Resize(V, &c); Inv(V, c)) := (
    let HM(n, _, MkArray(s)) = m;
    MoveFromInv(V, Succ(n), s, Zero, Succ(n), AddZeroR(Succ(n)), New(V, Succ(WAdd(n, n))), NewInv(V, Succ(WAdd(n, n))))
  )

  -- ## Resizing keeps every lookup
  def MoveBucketFind (V : Type) (b : Bucket(V)) (m : HashMap(V)) (k : Word) :
      Id(Opt(V), (let c = m; MoveBucket(V, b, &c); Find(V, c, k)), OrElse(V, BFindLast(V, b, k), Find(V, m, k))) by b := (
    match b {
      Nil => refl,
      Cons(e, t) => (
        let (k', v') = e;
        let mc = clone(m);
        let m2 = clone(m);
        InsertNoResize(V, &m2, k', clone(v'));
        if EqB(k', k) {
          let found : Eq(Opt(V), Find(V, m2, k), Some(v')) = (rewrite EqBSound(k', k, refl) in InsertFind(V, &mc, k', v'));
          split BFindLast {
            None => rewrite found in MoveBucketFind(V, t, m2, k),
            Some(_) => MoveBucketFind(V, t, m2, k),
          }
        } else {
          rewrite InsertFindOther(V, &mc, k', v', k, refl) in MoveBucketFind(V, t, m2, k)
        }
      ),
    }
  )

  def TakeV (V : Type) (n : Word) (v : Slice(Bucket(V), n)) (i : Word) (h : Lt(i, n)) :
      Eq(Bucket(V), (let c = v; Take(V, n, &c, i, h)), Nth(Bucket(V), n, v, i, h)) ∧
        Eq(Slice(Bucket(V), n), (let c = v; let b = Take(V, n, &c, i, h); c), SetS(Bucket(V), n, v, i, Nil)) by i := (
    match n {
      Zero => match h {},
      Succ(m) => (
        let MkSlice(MkC(_, t)) = v;
        match i {
          Zero => refl,
          Succ(i') => TakeV(V, m, t, i', h),
        }
      ),
    }
  )

  def RestSet (V : Type) (n : Word) (s : Slice(Bucket(V), n)) (i : Word) (x : Bucket(V)) (hi : Lt(i, n)) (j : Word)
      (rem : Word) (hr : Eq(Word, WAdd(rem, j), n)) (hij : Lt(i, j)) :
      Eq(List(Bucket(V)), Rest(V, n, SetS(Bucket(V), n, clone(s), i, x), j, rem, hr), Rest(V, n, s, j, rem, hr)) by rem := (
    match rem {
      Zero => refl,
      Succ(r) => (
        let hj : Lt(j, n) = (rewrite hr in LeAddL(r, j));
        let hr2 : Eq(Word, WAdd(r, Succ(j)), n) = (rewrite AddRS(r, j) in hr);
        rewrite NthSetOther(Bucket(V), n, clone(s), i, j, clone(x), hi, hj, λ(e : Eq(Word, i, j)) : False => LtNe(i, j, hij, e)) in
        rewrite RestSet(V, n, clone(s), i, clone(x), hi, Succ(j), r, hr2, LeStep(Succ(i), j, hij)) in
        refl
      ),
    }
  )

  -- Moving the buckets from `i` on. The step takes bucket `i`; the induction hypothesis is
  -- about the view the take leaves and the map after the moved bucket, and the rest of the
  -- goal is rewritten onto them.
  def MoveFromFind (V : Type) (n : Word) (s : Slice(Bucket(V), n)) (i : Word) (rem : Word) (hr : Eq(Word, WAdd(rem, i), n))
      (m : HashMap(V)) (k : Word) :
      Id(Opt(V), (let c = m; let o = s; MoveFrom(V, n, &o, i, rem, hr, &c); Find(V, c, k)),
        OrElse(V, FindLast(V, Rest(V, n, s, i, rem, hr), k), Find(V, m, k))) by rem := (
    match rem {
      Zero => refl,
      Succ(r) => (
        let hi : Lt(i, n) = (rewrite hr in LeAddL(r, i));
        let hr2 : Eq(Word, WAdd(r, Succ(i)), n) = (rewrite AddRS(r, i) in hr);
        let ⟨hb, ho⟩ = TakeV(V, n, clone(s), i, hi);
        let o = clone(s);
        let b = Take(V, n, &o, i, hi);
        let m2 = clone(m);
        MoveBucket(V, clone(b), &m2);
        rewrite hb in
        rewrite RestSet(V, n, clone(s), i, Nil, hi, Succ(i), r, hr2, LeRefl(Succ(i))) in
        rewrite ho in
        split FindLast {
          None => rewrite MoveBucketFind(V, b, m, k) in MoveFromFind(V, n, o, Succ(i), r, hr2, m2, k),
          Some(_) => MoveFromFind(V, n, o, Succ(i), r, hr2, m2, k),
        }
      ),
    }
  )

  -- `Rest` of a view whose first cell is known, from `j + 1` on, is `Rest` of its tail from `j`.
  def RestShift (V : Type) (m : Word) (b : Bucket(V)) (t : Slice(Bucket(V), m)) (j : Word) (rem : Word)
      (hr : Eq(Word, WAdd(rem, Succ(j)), Succ(m))) (hr' : Eq(Word, WAdd(rem, j), m)) :
      Eq(List(Bucket(V)), Rest(V, Succ(m), MkSlice(MkC(b, t)), Succ(j), rem, hr), Rest(V, m, t, j, rem, hr')) by rem := (
    match rem {
      Zero => refl,
      Succ(r) => (
        let hr2 : Eq(Word, WAdd(r, Succ(Succ(j))), Succ(m)) = (rewrite AddRS(r, Succ(j)) in hr);
        let hr2' : Eq(Word, WAdd(r, Succ(j)), m) = (rewrite AddRS(r, j) in hr');
        RestShift(V, m, b, t, Succ(j), r, hr2, hr2')
      ),
    }
  )

  def BFindLastNone (V : Type) (b : Bucket(V)) (k : Word) (h : Eq(Opt(V), BFind(V, b, k), None[V])) :
      Eq(Opt(V), BFindLast(V, b, k), None[V]) by b := (
    match b {
      Nil => refl,
      Cons(e, t) => (
        let (k', _) = e;
        if EqB(k', k) { match h {} } else { BFindLastNone(V, t, k, h) }
      ),
    }
  )

  def BFindLastUnique (V : Type) (b : Bucket(V)) (k : Word) (h : Unique(V, b)) : Eq(Opt(V), BFindLast(V, b, k), BFind(V, b, k)) by b := (
    match b {
      Nil => refl,
      Cons(e, t) => (
        let (k', _) = e;
        let ⟨absent, rest⟩ = h;
        if EqB(k', k) {
          let none = BFindLastNone(V, t, k, rewrite EqBSound(k', k, refl) in absent);
          split BFindLast {
            None => refl,
            Some(_) => match none {},
          }
        } else {
          BFindLastUnique(V, t, k, rest)
        }
      ),
    }
  )

  def NowhereRest (V : Type) (n : Word) (s : Slice(Bucket(V), n)) (k : Word) (h : Nowhere(V, n, s, k)) :
      NowhereL(V, Rest(V, n, s, Zero, n, AddZeroR(n)), k) by n := (
    match n {
      Zero => refl,
      Succ(m) => (
        let MkSlice(MkC(b, t)) = s;
        let ⟨hb, ht⟩ = h;
        rewrite ← RestShift(V, m, b, t, Zero, m, AddOneR(m), AddZeroR(m)) in ⟨hb, NowhereRest(V, m, t, k, ht)⟩
      ),
    }
  )

  def NowhereLLast (V : Type) (l : List(Bucket(V))) (k : Word) (h : NowhereL(V, l, k)) : Eq(Opt(V), FindLast(V, l, k), None[V]) by l := (
    match l {
      Nil => refl,
      Cons(b, t) => (
        let ⟨hb, ht⟩ = h;
        let none = NowhereLLast(V, t, k, ht);
        split FindLast {
          None => BFindLastNone(V, b, k, hb),
          Some(_) => match none {},
        }
      ),
    }
  )

  -- The key's last occurrence in the old buckets is its lookup in its own bucket.
  def OnlyInLast (V : Type) (n : Word) (s : Slice(Bucket(V), n)) (d : Word) (hd : Lt(d, n)) (k : Word)
      (h : OnlyIn(V, n, s, d, k)) (hu : AllUnique(V, n, s)) :
      Eq(Opt(V), FindLast(V, Rest(V, n, s, Zero, n, AddZeroR(n)), k), BFind(V, NthS(V, n, s, d, hd), k)) by n := (
    match n {
      Zero => match hd {},
      Succ(m) => (
        let MkSlice(MkC(b, t)) = s;
        let ⟨ub, ut⟩ = hu;
        rewrite ← RestShift(V, m, b, t, Zero, m, AddOneR(m), AddZeroR(m)) in
        match d {
          Zero => (
            let none = NowhereLLast(V, Rest(V, m, t, Zero, m, AddZeroR(m)), k, NowhereRest(V, m, t, k, h));
            split FindLast {
              None => BFindLastUnique(V, b, k, ub),
              Some(_) => match none {},
            }
          ),
          Succ(d') => (
            let ⟨hb, ht⟩ = h;
            split FindLast {
              None => rewrite ← BFindLastNone(V, b, k, hb) in OnlyInLast(V, m, t, d', hd, k, ht, ut),
              Some(_) => OnlyInLast(V, m, t, d', hd, k, ht, ut),
            }
          ),
        }
      ),
    }
  )

  -- Resizing keeps every lookup, given the invariant.
  def ResizeFind (V : Type) (m : HashMap(V)) (k : Word) (h : Inv(V, m)) : Id(Opt(V), (let c = m; Resize(V, &c); Find(V, c, k)), Find(V, m, k)) := (
    let HM(n, _, MkArray(s)) = m;
    let ⟨hl, hu, hp⟩ = h;
    match FindLast(V, Rest(V, Succ(n), clone(s), Zero, Succ(n), AddZeroR(Succ(n))), k) {
      None => (
        rewrite OnlyInLast(V, Succ(n), s, Idx(k, n), IdxLt(k, n), k, hp(k), hu) in
        rewrite NewFind(V, Succ(WAdd(n, n)), k) in
        MoveFromFind(V, Succ(n), s, Zero, Succ(n), AddZeroR(Succ(n)), New(V, Succ(WAdd(n, n))), k)
      ),
      Some(_) => rewrite OnlyInLast(V, Succ(n), s, Idx(k, n), IdxLt(k, n), k, hp(k), hu) in
        MoveFromFind(V, Succ(n), s, Zero, Succ(n), AddZeroR(Succ(n)), New(V, Succ(WAdd(n, n))), k),
    }
  )

  -- ## Resizing keeps the length
  -- Each entry moved is new to the target, so each insert adds one. That needs the keys
  -- of the old table to be distinct across buckets, which follows from placement.
  def WAddAssoc (x : Word) (y : Word) (z : Word) : Eq(Word, WAdd(WAdd(x, y), z), WAdd(x, WAdd(y, z))) by x := (
    match x {
      Zero => refl,
      Succ(x') => WAddAssoc(x', y, z),
    }
  )

  def FreshInsert (V : Type) (t : Bucket(V)) (m : HashMap(V)) (k : Word) (v : V) (h : Fresh(V, t, m))
      (a : Eq(Opt(V), BFind(V, t, k), None[V])) : (let c = m; InsertNoResize(V, &c, k, v); Fresh(V, t, c)) by t := (
    match t {
      Nil => refl,
      Cons(e, t2) => (
        let (k2, _) = e;
        let ⟨f, ft⟩ = h;
        if EqB(k2, k) {
          match a {}
        } else {
          let mc = clone(m);
          ⟨rewrite ← InsertFindOther(V, &mc, k, v, k2, NeqFlip(k2, k, refl)) in f, FreshInsert(V, t2, m, k, v, ft, a)⟩
        }
      ),
    }
  )

  -- Moving a bucket of fresh, distinct keys adds its length.
  def MoveBucketLen (V : Type) (b : Bucket(V)) (m : HashMap(V)) (hf : Fresh(V, b, m)) (hu : Unique(V, b)) :
      Id(Word, (let c = m; MoveBucket(V, b, &c); Len(V, c)), WAdd(Len(V, clone(m)), BLen(V, b))) by b := (
    match b {
      Nil => rewrite ← AddZeroR(Len(V, m)) in refl,
      Cons(e, t) => (
        let (k, v) = e;
        let ⟨f, ft⟩ = hf;
        let ⟨a, ut⟩ = hu;
        let mc = clone(m);
        let m2 = clone(m);
        InsertNoResize(V, &m2, k, clone(v));
        rewrite AddRS(Len(V, m), BLen(V, t)) in
        rewrite ← MoveBucketLen(V, t, m2, FreshInsert(V, t, m, k, v, ft, a), ut) in
        rewrite ← InsertLen(V, &mc, k, v) in
        rewrite ← f in refl
      ),
    }
  )

  -- After moving `b`, keys that are not in `b` are still absent.
  def FreshMove (V : Type) (b' : Bucket(V)) (b : Bucket(V)) (m : HashMap(V)) (hf : Fresh(V, b', m)) (ha : AbsentFrom(V, b', b)) :
      (let c = m; MoveBucket(V, b, &c); Fresh(V, b', c)) by b' := (
    match b' {
      Nil => refl,
      Cons(e, r) => (
        let (k, _) = e;
        let ⟨f, fr⟩ = hf;
        let ⟨a, ar⟩ = ha;
        let none = BFindLastNone(V, b, k, a);
        match BFindLast(V, clone(b), k) {
          None => ⟨rewrite ← MoveBucketFind(V, b, m, k) in f, FreshMove(V, r, b, m, fr, ar)⟩,
          Some(_) => match none {},
        }
      ),
    }
  )

  def FreshLMove (V : Type) (l : List(Bucket(V))) (b : Bucket(V)) (m : HashMap(V)) (hf : FreshL(V, l, m)) (ha : ApartL(V, l, b)) :
      (let c = m; MoveBucket(V, b, &c); FreshL(V, l, c)) by l := (
    match l {
      Nil => refl,
      Cons(b', t) => (
        let ⟨fb, ft⟩ = hf;
        let ⟨ab, ap⟩ = ha;
        ⟨FreshMove(V, b', b, m, fb, ab), FreshLMove(V, t, b, m, ft, ap)⟩
      ),
    }
  )

  -- Moving the buckets from `i` on adds their entries, if their keys are fresh and distinct.
  def MoveFromLen (V : Type) (n : Word) (s : Slice(Bucket(V), n)) (i : Word) (rem : Word) (hr : Eq(Word, WAdd(rem, i), n))
      (m : HashMap(V)) (hf : FreshL(V, Rest(V, n, s, i, rem, hr), m)) (hg : GUniqueL(V, Rest(V, n, s, i, rem, hr))) :
      Id(Word, (let c = m; let o = s; MoveFrom(V, n, &o, i, rem, hr, &c); Len(V, c)),
        WAdd(Len(V, clone(m)), CountL(V, Rest(V, n, s, i, rem, hr)))) by rem := (
    match rem {
      Zero => rewrite ← AddZeroR(Len(V, m)) in refl,
      Succ(r) => (
        let hi : Lt(i, n) = (rewrite hr in LeAddL(r, i));
        let hr2 : Eq(Word, WAdd(r, Succ(i)), n) = (rewrite AddRS(r, i) in hr);
        let ⟨hb, ho⟩ = TakeV(V, n, clone(s), i, hi);
        let ⟨fb, ft⟩ = hf;
        let ⟨ub, ap, gt⟩ = hg;
        let o = clone(s);
        let b = Take(V, n, &o, i, hi);
        let m2 = clone(m);
        MoveBucket(V, clone(b), &m2);
        let fb2 : Fresh(V, b, m) = (rewrite ← hb in fb);
        let ub2 : Unique(V, b) = (rewrite ← hb in ub);
        let hf2 : FreshL(V, Rest(V, n, o, Succ(i), r, hr2), m2) = (
          rewrite ← ho in rewrite ← RestSet(V, n, clone(s), i, Nil, hi, Succ(i), r, hr2, LeRefl(Succ(i))) in
          FreshLMove(V, Rest(V, n, clone(s), Succ(i), r, hr2), b, m, ft, (rewrite ← hb in ap)));
        let hg2 : GUniqueL(V, Rest(V, n, o, Succ(i), r, hr2)) = (
          rewrite ← ho in rewrite ← RestSet(V, n, clone(s), i, Nil, hi, Succ(i), r, hr2, LeRefl(Succ(i))) in gt);
        rewrite hb in
        rewrite RestSet(V, n, clone(s), i, Nil, hi, Succ(i), r, hr2, LeRefl(Succ(i))) in
        rewrite ho in
        rewrite WAddAssoc(Len(V, m), BLen(V, b), CountL(V, Rest(V, n, o, Succ(i), r, hr2))) in
        rewrite MoveBucketLen(V, b, m, fb2, ub2) in
        MoveFromLen(V, n, o, Succ(i), r, hr2, m2, hf2, hg2)
      ),
    }
  )

  -- A new map has no keys, and the old view's entries are its buckets' lengths.
  def FreshNew (V : Type) (b : Bucket(V)) (n : Word) : Fresh(V, b, New(V, n)) by b := (
    match b {
      Nil => refl,
      Cons(e, t) => (
        let (k, _) = e;
        ⟨NewFind(V, n, k), FreshNew(V, t, n)⟩
      ),
    }
  )

  def FreshLNew (V : Type) (l : List(Bucket(V))) (n : Word) : FreshL(V, l, New(V, n)) by l := (
    match l {
      Nil => refl,
      Cons(b, t) => ⟨FreshNew(V, b, n), FreshLNew(V, t, n)⟩,
    }
  )

  def CountRest (V : Type) (n : Word) (s : Slice(Bucket(V), n)) :
      Eq(Word, CountL(V, Rest(V, n, s, Zero, n, AddZeroR(n))), Entries(V, n, s)) by n := (
    match n {
      Zero => refl,
      Succ(m) => (
        let MkSlice(MkC(b, t)) = s;
        rewrite ← RestShift(V, m, b, t, Zero, m, AddOneR(m), AddZeroR(m)) in rewrite CountRest(V, m, t) in refl
      ),
    }
  )

  -- Placement gives distinct keys across buckets.
  -- If every key lies only in its own bucket (`D(k)` says which, relative to `s`), keys in
  -- different buckets differ. For a key `k` of a later bucket: if `D(k)` points at the first
  -- bucket, `k` would be nowhere in the rest, where it is; otherwise the first bucket lacks
  -- it. The rest's own `D` is one less.
  def NowhereOnlyIn (V : Type) (n : Word) (s : Slice(Bucket(V), n)) (d : Word) (k : Word) (h : Nowhere(V, n, s, k)) :
      OnlyIn(V, n, s, d, k) by n := (
    match n {
      Zero => refl,
      Succ(m) => (
        let MkSlice(MkC(_, t)) = s;
        let ⟨hb, ht⟩ = h;
        match d {
          Zero => ht,
          Succ(d') => ⟨hb, NowhereOnlyIn(V, m, t, d', k, ht)⟩,
        }
      ),
    }
  )

  -- The first key `k` of a bucket of `t` is not in `b`.
  def HeadApart (V : Type) (k : Word) (v : V) (r : Bucket(V)) (b : Bucket(V)) (m : Word) (t : Slice(Bucket(V), m))
      (D : Π(k : Word). Word) (hp : Π(k : Word). OnlyIn(V, Succ(m), MkSlice(MkC(b, t)), D(k), k))
      (hin : Π(k2 : Word) (nw : Nowhere(V, m, t, k2)). Eq(Opt(V), BFind(V, Cons((k, v), r), k2), None[V])) :
      Eq(Opt(V), BFind(V, b, k), None[V]) := (
    let dk = D(k);
    let p = hp(k);
    match dk {
      Zero => (
        let f = hin(k, p);
        if EqB(k, k) { match f {} } else { match EqBRefl(k) {} }
      ),
      Succ(_) => (
        let ⟨a, rest⟩ = p;
        a
      ),
    }
  )

  -- `cur` is (a suffix of) a bucket of `t`: a key nowhere in `t` is not in `cur`.
  def AbsentFromOf (V : Type) (cur : Bucket(V)) (b : Bucket(V)) (m : Word) (t : Slice(Bucket(V), m)) (D : Π(k : Word). Word)
      (hp : Π(k : Word). OnlyIn(V, Succ(m), MkSlice(MkC(b, t)), D(k), k))
      (hin : Π(k : Word) (nw : Nowhere(V, m, t, k)). Eq(Opt(V), BFind(V, cur, k), None[V])) : AbsentFrom(V, cur, b) by cur := (
    match cur {
      Nil => refl,
      Cons(e, r) => (
        let (k, v) = e;
        ⟨HeadApart(V, k, v, r, b, m, t, D, hp, hin),
          AbsentFromOf(V, r, b, m, t, D, hp, λ(k2 : Word) (nw : Nowhere(V, m, t, k2)) : Eq(Opt(V), BFind(V, r, k2), None[V]) => (
            let f = hin(k2, nw);
            if EqB(k, k2) { match f {} } else { f }
          ))⟩
      ),
    }
  )

  -- `u` lists buckets of `t`: every bucket of it is apart from `b`.
  def ApartOfGoL (V : Type) (u : List(Bucket(V))) (b : Bucket(V)) (m : Word) (t : Slice(Bucket(V), m)) (D : Π(k : Word). Word)
      (hp : Π(k : Word). OnlyIn(V, Succ(m), MkSlice(MkC(b, t)), D(k), k))
      (hu : Π(k : Word) (nw : Nowhere(V, m, t, k)). NowhereL(V, u, k)) : ApartL(V, u, b) by u := (
    match u {
      Nil => refl,
      Cons(b', u') => ⟨
        AbsentFromOf(V, b', b, m, t, D, hp, λ(k : Word) (nw : Nowhere(V, m, t, k)) : Eq(Opt(V), BFind(V, b', k), None[V]) => (
          let ⟨x, y⟩ = hu(k, nw);
          x
        )),
        ApartOfGoL(V, u', b, m, t, D, hp, λ(k : Word) (nw : Nowhere(V, m, t, k)) : NowhereL(V, u', k) => (
          let ⟨x, y⟩ = hu(k, nw);
          y
        ))⟩,
    }
  )

  def TailOnlyIn (V : Type) (b : Bucket(V)) (m : Word) (t : Slice(Bucket(V), m)) (d : Word) (k : Word)
      (h : OnlyIn(V, Succ(m), MkSlice(MkC(b, t)), d, k)) : OnlyIn(V, m, t, Pred(d), k) := (
    match d {
      Zero => NowhereOnlyIn(V, m, t, Zero, k, h),
      Succ(_) => (
        let ⟨x, y⟩ = h;
        y
      ),
    }
  )

  def GUniqueOf (V : Type) (n : Word) (s : Slice(Bucket(V), n)) (D : Π(k : Word). Word) (hp : Π(k : Word). OnlyIn(V, n, s, D(k), k))
      (hu : AllUnique(V, n, s)) : GUniqueL(V, Rest(V, n, s, Zero, n, AddZeroR(n))) by n := (
    match n {
      Zero => refl,
      Succ(m) => (
        let MkSlice(MkC(b, t)) = s;
        let ⟨ub, ut⟩ = hu;
        rewrite ← RestShift(V, m, b, t, Zero, m, AddOneR(m), AddZeroR(m)) in
        ⟨ub, ⟨
          ApartOfGoL(V, Rest(V, m, t, Zero, m, AddZeroR(m)), b, m, t, D, hp,
            λ(k : Word) (nw : Nowhere(V, m, t, k)) : NowhereL(V, Rest(V, m, t, Zero, m, AddZeroR(m)), k) => NowhereRest(V, m, t, k, nw)),
          GUniqueOf(V, m, t, λ(k : Word) : Word => Pred(D(k)),
            λ(k : Word) : OnlyIn(V, m, t, Pred(D(k)), k) => TailOnlyIn(V, b, m, t, D(k), k, hp(k)), ut)⟩⟩
      ),
    }
  )

  -- Resizing keeps the length, given the invariant.
  def ResizeLen (V : Type) (m : HashMap(V)) (h : Inv(V, m)) : Id(Word, (let c = m; Resize(V, &c); Len(V, c)), Len(V, m)) := (
    let HM(n, _, MkArray(s)) = m;
    let ⟨hl, hu, hp⟩ = h;
    rewrite ← hl in
    rewrite CountRest(V, Succ(n), s) in
    MoveFromLen(V, Succ(n), s, Zero, Succ(n), AddZeroR(Succ(n)), New(V, Succ(WAdd(n, n))),
      FreshLNew(V, Rest(V, Succ(n), s, Zero, Succ(n), AddZeroR(Succ(n))), Succ(WAdd(n, n))),
      GUniqueOf(V, Succ(n), s, λ(k : Word) : Word => Idx(k, n), hp, hu))
  )

  -- ## Insert, with the resize
  -- Split on what the bucket insert returned and on whether the table is then full. When it
  -- is, the resize keeps the invariant, every lookup and the length, the last two under the
  -- invariant, which `InsertInv` gives for the map before the resize. The load factor is
  -- last.
  def InsertFindR (V : Type) (m : HashMap(V)) (k : Word) (v : V) (h : Inv(V, m)) :
      Id(Opt(V), (let c = m; Insert(V, &c, k, v); Find(V, c, k)), Some(v)) := (
    let HM(_, _, MkArray(_)) = m;
    let mc = clone(m);
    let m2 = clone(m);
    InsertNoResize(V, &m2, k, clone(v));
    split BInsert in split LtB {
      false => InsertFind(V, &mc, k, v),
      true => rewrite ← ResizeFind(V, m2, k, InsertInv(V, m, k, v, h)) in InsertFind(V, &mc, k, v),
    }
  )

  def InsertFindOtherR (V : Type) (m : HashMap(V)) (k : Word) (v : V) (k2 : Word) (ne : Eq(Bool, EqB(k, k2), false)) (h : Inv(V, m)) :
      Id(Opt(V), (let c = m; Insert(V, &c, k, v); Find(V, c, k2)), Find(V, m, k2)) := (
    let HM(_, _, MkArray(_)) = m;
    let mc = clone(m);
    let m2 = clone(m);
    InsertNoResize(V, &m2, k, clone(v));
    split BInsert in split LtB {
      false => InsertFindOther(V, &mc, k, v, k2, ne),
      true => rewrite ← ResizeFind(V, m2, k2, InsertInv(V, m, k, v, h)) in InsertFindOther(V, &mc, k, v, k2, ne),
    }
  )

  -- The value returned: the resize happens after the bucket insert, so it changes nothing.
  def InsertResultR (V : Type) (m : HashMap(V)) (k : Word) (v : V) :
      Id(Opt(V), (let c = m; Insert(V, &c, k, v)), Find(V, m, k)) := (
    let HM(_, _, MkArray(_)) = m;
    let mc = clone(m);
    split BInsert in split LtB {
      false => InsertResult(V, &mc, k, v),
      true => InsertResult(V, &mc, k, v),
    }
  )

  -- The invariant.
  def InsertInvR (V : Type) (m : HashMap(V)) (k : Word) (v : V) (h : Inv(V, m)) : (let c = m; Insert(V, &c, k, v); Inv(V, c)) := (
    let HM(_, _, MkArray(_)) = m;
    let m2 = clone(m);
    InsertNoResize(V, &m2, k, clone(v));
    split BInsert in split LtB {
      false => InsertInv(V, m, k, v, h),
      true => ResizeInv(V, m2),
    }
  )

  -- The length grows by one exactly when the key was absent.
  def InsertLenR (V : Type) (m : HashMap(V)) (k : Word) (v : V) (h : Inv(V, m)) :
      Id(Word, (let c = m; Insert(V, &c, k, v); Len(V, c)), IfNew(V, Find(V, clone(m), k), Len(V, m))) := (
    let HM(_, _, MkArray(_)) = m;
    let mc = clone(m);
    let m2 = clone(m);
    InsertNoResize(V, &m2, k, clone(v));
    split BInsert in split LtB {
      false => InsertLen(V, &mc, k, v),
      true => rewrite ← ResizeLen(V, m2, InsertInv(V, m, k, v, h)) in InsertLen(V, &mc, k, v),
    }
  )

  -- ## The load factor
  -- `a ≥ y` gives `a + 1 ≥ y`, `a + z ≥ y`, and `a ≥ y - 1`.
  def LtBS (a : Word) (y : Word) (h : Eq(Bool, LtB(a, y), false)) : Eq(Bool, LtB(Succ(a), y), false) by a := (
    match a {
      Zero => match y {
        Zero => refl,
        Succ(_) => match h {},
      },
      Succ(a') => match y {
        Zero => refl,
        Succ(y') => LtBS(a', y', h),
      },
    }
  )

  def LtBAdd (x : Word) (y : Word) (z : Word) (h : Eq(Bool, LtB(x, y), false)) : Eq(Bool, LtB(WAdd(x, z), y), false) by x := (
    match x {
      Zero => match y {
        Zero => match z {
          Zero => refl,
          Succ(_) => refl,
        },
        Succ(_) => match h {},
      },
      Succ(x') => match y {
        Zero => refl,
        Succ(y') => LtBAdd(x', y', z, h),
      },
    }
  )

  def LtBPred (a : Word) (y : Word) (h : Eq(Bool, LtB(a, y), false)) : Eq(Bool, LtB(a, Pred(y)), false) := (
    match y {
      Zero => h,
      Succ(y') => match a {
        Zero => match h {},
        Succ(a') => LtBS(a', y', h),
      },
    }
  )

  -- Inserting and moving entries does not change the number of buckets; resizing sets it.
  def InsertN (V : Type) (m : HashMap(V)) (k : Word) (v : V) : Id(Word, (let c = m; InsertNoResize(V, &c, k, v); NOf(V, c)), NOf(V, m)) := (
    let HM(_, _, _) = m;
    split BInsert in refl
  )

  def MoveBucketN (V : Type) (b : Bucket(V)) (m : HashMap(V)) : Id(Word, (let c = m; MoveBucket(V, b, &c); NOf(V, c)), NOf(V, m)) by b := (
    match b {
      Nil => refl,
      Cons(e, t) => (
        let (k, v) = e;
        let m2 = clone(m);
        InsertNoResize(V, &m2, k, clone(v));
        rewrite ← MoveBucketN(V, t, m2) in InsertN(V, m, k, v)
      ),
    }
  )

  def MoveFromN (V : Type) (n : Word) (s : Slice(Bucket(V), n)) (i : Word) (rem : Word) (hr : Eq(Word, WAdd(rem, i), n))
      (m : HashMap(V)) : Id(Word, (let c = m; let o = s; MoveFrom(V, n, &o, i, rem, hr, &c); NOf(V, c)), NOf(V, m)) by rem := (
    match rem {
      Zero => refl,
      Succ(r) => (
        let hi : Lt(i, n) = (rewrite hr in LeAddL(r, i));
        let hr2 : Eq(Word, WAdd(r, Succ(i)), n) = (rewrite AddRS(r, i) in hr);
        let o = clone(s);
        let b = Take(V, n, &o, i, hi);
        let m2 = clone(m);
        MoveBucket(V, clone(b), &m2);
        rewrite ← MoveFromN(V, n, o, Succ(i), r, hr2, m2) in MoveBucketN(V, b, m)
      ),
    }
  )

  def ResizeN (V : Type) (m : HashMap(V)) : Id(Word, (let c = m; Resize(V, &c); NOf(V, c)), Succ(WAdd(NOf(V, clone(m)), NOf(V, m)))) := (
    let HM(n, _, MkArray(s)) = m;
    MoveFromN(V, Succ(n), s, Zero, Succ(n), AddZeroR(Succ(n)), New(V, Succ(WAdd(n, n))))
  )

  -- After a resize the bucket count is `2n + 2` and the length is unchanged, so the
  -- entries (at most `n + 1`) do not outnumber the buckets.
  def InsertNotOver (V : Type) (m : HashMap(V)) (k : Word) (v : V) (h : Inv(V, m)) (ho : NotOver(V, m)) :
      (let c = m; Insert(V, &c, k, v); NotOver(V, c)) := (
    let HM(n, len, MkArray(_)) = m;
    let m2 = clone(m);
    InsertNoResize(V, &m2, k, clone(v));
    split BInsert {
      None => split LtB {
        false => refl,
        true => rewrite ← ResizeN(V, m2) in rewrite ← ResizeLen(V, m2, InsertInv(V, m, k, v, h)) in LtBAdd(n, len, n, ho),
      },
      Some(_) => split LtB {
        false => refl,
        true => match ho {},
      },
    }
  )

  def NewNotOver (V : Type) (n : Word) : NotOver(V, New(V, n)) := (
    match n {
      Zero => refl,
      Succ(_) => refl,
    }
  )

  def RemoveNotOver (V : Type) (m : HashMap(V)) (k : Word) (ho : NotOver(V, m)) : (let c = m; Remove(V, &c, k); NotOver(V, c)) := (
    let HM(n, len, MkArray(_)) = m;
    split BRemove {
      None => ho,
      Some(_) => LtBPred(n, len, ho),
    }
  )

  def GetMutNotOver (V : Type) (m : HashMap(V)) (k : Word) (w : V) (h : IsSome(V, Find(V, m, k))) (ho : NotOver(V, m)) :
      (let c = m; let q = MapGetMut(V, &c, k, h); *q := w; NotOver(V, c)) := (
    let HM(_, _, _) = m;
    ho
  )

  def ClearNotOver (V : Type) (m : HashMap(V)) : (let c = m; Clear(V, &c); NotOver(V, c)) := (
    let HM(n, _, _) = m;
    NewNotOver(V, n)
  )
}
