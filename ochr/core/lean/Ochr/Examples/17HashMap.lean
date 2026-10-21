import Ochr.Examples.«16Arrays»

/-! # 17. A verified hash map

The case study of `notes/hashmap-case-study.md`: the resizing hash map that Aeneas verifies
(ICFP 2022, §6), written once, in place, with its theorems stated and proved about that
program. There is no pure model and no refinement proof: where Aeneas states "after
`insert`, `find_s` of the key is the value" about a hand-written model `find_s`, here the
statement uses the map's own lookup, run on a copy of the map (`Find`, as `Add` runs `AddM`
on a copy).

Values have any type `V`, keys are `Word`s. The table is an array of `n + 1` buckets
(`16Arrays`), each bucket a list of key–value pairs. A map holds its size `n` next to an
array of that many buckets plus one, so the array's type depends on `n` (a dependent field,
`18DependentFields`), and resizing replaces both. `Slot` borrows the bucket of a key through
the array's element borrow, as Rust's `&mut slots[i]`; the hash is the identity, as in
Aeneas, and `k mod (n + 1)` picks the bucket, whose bound is a lemma. Keys, sizes and the
length are `Word`s, which reading copies; values move, as in Rust. `Insert` and `Remove`
return the value they move out; `Get` and `GetMutM` return a borrow of a present key's value
(Ochr has no shared borrows and no borrows inside data, so both take a proof that the key is
present).

The file has four programs: `HashMap`, the implementation with concrete runs; `HashMapLookup`,
lookups after each operation; `HashMapLength`, the length field and the count of entries;
`HashMapResize`, the invariant, resizing, `Insert` with its resize, and the load factor. -/

open Ochr.Test

ochr HashMap uses Index, Arrays, ArrayLemmas {
  -- ## Helpers: the case study's copies of the central library's definitions
  -- An optional value and whether it holds one, boolean comparisons of `Word`s, the
  -- predecessor, and that a key equals itself. Named as in the central library (`Std`,
  -- `Words`), so that they are deleted, not renamed, when it lands.
  inductive Opt (A : Type) := None | Some(v : A)

  def IsSome (A : Type) (o : Opt(A)) : Prop := (
    match o {
      None => False,
      Some(_) => ⊤,
    }
  )

  def EqB (a : Word) (b : Word) : Bool by a := (
    match a {
      Zero => match b {
        Zero => true,
        Succ(_) => false,
      },
      Succ(a') => match b {
        Zero => false,
        Succ(b') => EqB(a', b'),
      },
    }
  )

  def LtB (a : Word) (b : Word) : Bool by a := (
    match a {
      Zero => match b {
        Zero => false,
        Succ(_) => true,
      },
      Succ(a') => match b {
        Zero => false,
        Succ(b') => LtB(a', b'),
      },
    }
  )

  def Pred (n : Word) : Word := (
    match n {
      Zero => Zero,
      Succ(m) => m,
    }
  )

  def EqBRefl (k : Word) : Eq(Bool, EqB(k, k), true) by k := (
    match k {
      Zero => refl,
      Succ(k') => EqBRefl(k'),
    }
  )

  -- ## The bucket index
  -- `k mod (n + 1)`, by recursion on `k` with a running remainder, and its bound: the
  -- remainder never passes `n`, so the index is in an array of `n + 1` buckets.
  def ModGo (k : Word) (n : Word) (r : Word) : Word by k := (
    match k {
      Zero => r,
      Succ(k') => (
        let e = EqB(r, n);
        match e {
          false => ModGo(k', n, Succ(r)),
          true => ModGo(k', n, Zero),
        }
      ),
    }
  )

  def Idx (k : Word) (n : Word) : Word := ModGo(k, n, Zero)

  def LeNextB (a : Word) (c : Word) (h : Le(a, c)) (e : Eq(Bool, EqB(a, c), false)) : Le(Succ(a), c) by a := (
    match a {
      Zero => match c {
        Zero => match e {},
        Succ(_) => refl,
      },
      Succ(a') => match c {
        Zero => match h {},
        Succ(c') => LeNextB(a', c', h, e),
      },
    }
  )

  def ModGoLe (k : Word) (n : Word) (r : Word) (h : Le(r, n)) : Le(ModGo(k, n, r), n) by k := (
    match k {
      Zero => h,
      Succ(k') => (
        let e = EqB(r, n);
        match e {
          false => ModGoLe(k', n, Succ(r), LeNextB(r, n, h, refl)),
          true => ModGoLe(k', n, Zero, refl),
        }
      ),
    }
  )

  def IdxLt (k : Word) (n : Word) : Lt(Idx(k, n), Succ(n)) := ModGoLe(k, n, Zero, refl)

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
      Cons(e, t) => match e {
        Mk(k', v') => (
          let eq = EqB(k', k);
          match eq {
            false => BContains(V, &t, k),
            true => true,
          }
        ),
      },
    }
  )

  def BInsert (V : Type) (b : &Bucket(V)) (k : Word) (v : V) : Opt(V) by b := (
    match *b {
      Nil => (
        *b := Cons((k, v), Nil);
        None
      ),
      Cons(e, t) => match e {
        Mk(k', v') => (
          let eq = EqB(k', k);
          match eq {
            false => BInsert(V, &t, k, v),
            true => (
              let old = v';
              v' := v;
              Some(old)
            ),
          }
        ),
      },
    }
  )

  def BRemove (V : Type) (b : &Bucket(V)) (k : Word) : Opt(V) by b := (
    match *b {
      Nil => None,
      Cons(e, t) => match e {
        Mk(k', v') => (
          let eq = EqB(k', k);
          match eq {
            false => BRemove(V, &t, k),
            true => (
              let x = v';
              *b := t;
              Some(x)
            ),
          }
        ),
      },
    }
  )

  -- The lookup that statements use: the value a key holds, copied (`clone`), or `None`. It
  -- runs on a copy of the bucket, as `Add` runs `AddM` on a copy, so it leaves the bucket as
  -- it was; in a statement the copy is free.
  def BLookup (V : Type) (b : &Bucket(V)) (k : Word) : Opt(V) by b := (
    match *b {
      Nil => None,
      Cons(e, t) => match e {
        Mk(k', v') => (
          let eq = EqB(k', k);
          match eq {
            false => BLookup(V, &t, k),
            true => Some(clone(v')),
          }
        ),
      },
    }
  )

  def BFind (V : Type) (b : Bucket(V)) (k : Word) : Opt(V) := BLookup(V, &b, k)

  -- The borrow of a present key's value. The key is present, so the `Nil` arm cannot
  -- happen: there `h` is a proof of `IsSome(V, None)`, which is `False`.
  def BGet (V : Type) (b : &Bucket(V)) (k : Word) (h : IsSome(V, BFind(V, *b, k))) : &V by b := (
    match *b {
      Nil => match h {},
      Cons(e, t) => match e {
        Mk(k', v') => (
          let eq = EqB(k', k);
          match eq {
            false => BGet(V, &t, k, h),
            true => &v',
          }
        ),
      },
    }
  )

  -- ## The slots
  -- The index borrow (Rust's `&mut slots[i]`): the array's element borrow of the key's
  -- bucket, whose bound is `IdxLt`. A fresh table's buckets are all empty.
  def Slot (V : Type) (n : Word) (slots : &Slots(V, n)) (k : Word) : &Bucket(V) :=
    GetMut(Bucket(V), Succ(n), AsSlice(Bucket(V), Succ(n), slots), Idx(k, n), IdxLt(k, n))

  def EmptySlots (V : Type) (n : Word) : Slots(V, n) := ArrFromFn(Bucket(V), Succ(n), λ(i : Word) : Bucket(V) => Nil)

  -- ## The map
  -- Every operation finds the key's bucket through `Slot` and works on it in place.
  def New (V : Type) (n : Word) : HashMap(V) := HM(n, Zero, EmptySlots(V, n))

  -- The lookup on a copy, for statements, and the length field.
  def Lookup (V : Type) (hm : &HashMap(V)) (k : Word) : Opt(V) := (
    match *hm {
      HM(n, len, slots) => (
        let b = Slot(V, n, &slots, k);
        BLookup(V, b, k)
      ),
    }
  )

  def Find (V : Type) (m : HashMap(V)) (k : Word) : Opt(V) := Lookup(V, &m, k)

  def Len (V : Type) (m : HashMap(V)) : Word := (
    match m {
      HM(n, len, s) => len,
    }
  )

  def ContainsKey (V : Type) (hm : &HashMap(V)) (k : Word) : Bool := (
    match *hm {
      HM(n, len, slots) => (
        let b = Slot(V, n, &slots, k);
        BContains(V, b, k)
      ),
    }
  )

  -- `Get` and `MapGetMut` borrow a present key's value: `Get`'s borrow is only read (Ochr has
  -- no shared borrows), `MapGetMut`'s may be written through.
  def Get (V : Type) (hm : &HashMap(V)) (k : Word) (h : IsSome(V, Find(V, *hm, k))) : &V := (
    match *hm {
      HM(n, len, slots) => (
        let b = Slot(V, n, &slots, k);
        BGet(V, b, k, h)
      ),
    }
  )

  def MapGetMut (V : Type) (hm : &HashMap(V)) (k : Word) (h : IsSome(V, Find(V, *hm, k))) : &V := (
    match *hm {
      HM(n, len, slots) => (
        let b = Slot(V, n, &slots, k);
        BGet(V, b, k, h)
      ),
    }
  )

  -- Insert or overwrite, and remove, each returning the value moved out; the length grows
  -- when the bucket insert found nothing to overwrite, and shrinks when the remove found
  -- something.
  def InsertNoResize (V : Type) (hm : &HashMap(V)) (k : Word) (v : V) : Opt(V) := (
    match *hm {
      HM(n, len, slots) => (
        let b = Slot(V, n, &slots, k);
        let r = BInsert(V, b, k, v);
        match r {
          None => len := Succ(len),
          Some(_) => (),
        };
        r
      ),
    }
  )

  def Remove (V : Type) (hm : &HashMap(V)) (k : Word) : Opt(V) := (
    match *hm {
      HM(n, len, slots) => (
        let b = Slot(V, n, &slots, k);
        let x = BRemove(V, b, k);
        match x {
          None => (),
          Some(_) => len := Pred(len),
        };
        x
      ),
    }
  )

  def Clear (V : Type) (hm : &HashMap(V)) : Unit := (
    match *hm {
      HM(n, len, slots) => (
        len := Zero;
        slots := EmptySlots(V, n)
      ),
    }
  )

  -- ## Resizing
  -- Move every entry into a map with `2n + 2` buckets, by inserting it again. Resizing
  -- happens when the entries outnumber the buckets (load factor 1). The old buckets are
  -- visited by index, each taken out of the old array and replaced by an empty one (Rust's
  -- `mem::take`), so nothing is copied.
  def MoveBucket (V : Type) (b : Bucket(V)) (hm : &HashMap(V)) : Unit by b := (
    match b {
      Nil => (),
      Cons(e, t) => match e {
        Mk(k, v) => (
          InsertNoResize(V, &*hm, k, v);
          MoveBucket(V, t, hm)
        ),
      },
    }
  )

  def Take (V : Type) (n : Word) (s : &Slice(Bucket(V), n)) (i : Word) (h : Lt(i, n)) : Bucket(V) := (
    let r = GetMut(Bucket(V), n, s, i, h);
    let b = *r;
    *r := Nil;
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
    match *hm {
      HM(n, len, slots) => (
        let n0 = n;
        let old = slots;
        *hm := New(V, Succ(WAdd(n0, n0)));
        MoveFrom(V, Succ(n0), AsSlice(Bucket(V), Succ(n0), &old), Zero, Succ(n0), AddZeroR(Succ(n0)), hm)
      ),
    }
  )

  def Insert (V : Type) (hm : &HashMap(V)) (k : Word) (v : V) : Opt(V) := (
    let r = InsertNoResize(V, &*hm, k, v);
    match *hm {
      HM(n, len, slots) => (
        let full = LtB(n, len);
        match full {
          false => (),
          true => Resize(V, &*hm),
        }
      ),
    };
    r
  )

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
      Cons(e, t) => match e {
        Mk(k', v') => (
          let eq = EqB(k', k);
          match eq {
            false => BLookupMoves(V, &t, k),
            true => Some(v'),
          }
        ),
      },
    }
  )
}

-- the exact number of declarations (a truncated file changes it)
#guard HashMap.decls.length == 48

/-! ## Lookups after each operation

Each theorem says what `Find` returns after an operation, for the key it touched and for
any other key. The statements use the operations themselves: "after `InsertNoResize(hm, k,
v)`, `Find(*hm, k)` is `Some(v)`" is `Id(Opt(V), (InsertNoResize(V, &*hm, k, v); Find(V,
clone(*hm), k)), (InsertNoResize(V, &*hm, k, clone(v)); Some(v)))`. Each is proved first for
one bucket, by recursion on the bucket, then lifted through the array's element borrow by
recursion on the index, following `GetMut`'s own recursion, then stated for the map. -/

ochr HashMapLookup uses Index, Arrays, ArrayLemmas, HashMap {
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
    let e = EqB(b, c);
    match e {
      false => (
        let p = EqBTrans(a, b, c, h1, h2);
        match p {}
      ),
      true => match h {},
    }
  )

  -- ## Insert, in one bucket
  -- After inserting `k`, looking `k` up gives the inserted value. In the `Nil` arm the
  -- lookup compares `k` with itself, which the checker cannot compute for an abstract `k`:
  -- split on it, and the `false` arm contradicts `EqBRefl`.
  def BInsertFind (V : Type) (b : &Bucket(V)) (k : Word) (v : V) :
      Id(Opt(V), (BInsert(V, &*b, k, v); BFind(V, clone(*b), k)), (BInsert(V, &*b, k, clone(v)); Some(v))) by b := (
    match *b {
      Nil => (
        let e = EqB(k, k);
        match e {
          false => (
            let p = EqBRefl(k);
            match p {}
          ),
          true => refl,
        }
      ),
      Cons(e, t) => match e {
        Mk(k', v') => (
          let eq = EqB(k', k);
          match eq {
            false => BInsertFind(V, &t, k, v),
            true => refl,
          }
        ),
      },
    }
  )

  -- Inserting `k` does not change the lookup of another key `k2`.
  def BInsertFindOther (V : Type) (b : &Bucket(V)) (k : Word) (v : V) (k2 : Word) (h : Eq(Bool, EqB(k, k2), false)) :
      Id(Opt(V), (BInsert(V, &*b, k, v); BFind(V, clone(*b), k2)), (let r = BFind(V, clone(*b), k2); BInsert(V, &*b, k, v); r)) by b := (
    match *b {
      Nil => (
        let e = EqB(k, k2);
        match e {
          false => refl,
          true => match h {},
        }
      ),
      Cons(e, t) => match e {
        Mk(k', v') => (
          let eq = EqB(k', k);
          let eq2 = EqB(k', k2);
          match eq {
            false => match eq2 {
              false => BInsertFindOther(V, &t, k, v, k2, h),
              true => refl,
            },
            true => match eq2 {
              false => refl,
              true => (
                let f = EqBContra(k', k, k2, refl, refl, h);
                match f {}
              ),
            },
          }
        ),
      },
    }
  )

  -- The insert returns what the lookup would have returned: the old value, or `None`.
  def BInsertResult (V : Type) (b : &Bucket(V)) (k : Word) (v : V) :
      Id(Opt(V), BInsert(V, &*b, k, v), (let r = BFind(V, clone(*b), k); BInsert(V, &*b, k, v); r)) by b := (
    match *b {
      Nil => refl,
      Cons(e, t) => match e {
        Mk(k', v') => (
          let eq = EqB(k', k);
          match eq {
            false => BInsertResult(V, &t, k, v),
            true => refl,
          }
        ),
      },
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
    *r := Nil;
    b
  )

  def SlotInsertFind (V : Type) (n : Word) (s : &Slice(Bucket(V), n)) (i : Word) (hi : Lt(i, n)) (k : Word) (v : V) :
      Id(Opt(V), (let b = GetMut(Bucket(V), n, &*s, i, hi); BInsert(V, b, k, v); BFind(V, NthS(V, n, clone(*s), i, hi), k)),
        (let b = GetMut(Bucket(V), n, &*s, i, hi); BInsert(V, b, k, clone(v)); Some(v))) by i := (
    match n {
      Zero => match hi {},
      Succ(m) => match *s {
        MkSlice(c) => match c {
          MkC(x, t) => match i {
            Zero => BInsertFind(V, &x, k, v),
            Succ(i') => SlotInsertFind(V, m, &t, i', hi, k, v),
          },
        },
      },
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
      Succ(m) => match *s {
        MkSlice(c) => match c {
          MkC(x, t) => match i {
            Zero => match j {
              Zero => BInsertFindOther(V, &x, k, v, k2, h),
              Succ(_) => refl,
            },
            Succ(i') => match j {
              Zero => refl,
              Succ(j') => SlotInsertFindOther(V, m, &t, i', hi, j', hj, k, v, k2, h),
            },
          },
        },
      },
    }
  )

  def SlotInsertResult (V : Type) (n : Word) (s : &Slice(Bucket(V), n)) (i : Word) (hi : Lt(i, n)) (k : Word) (v : V) :
      Id(Opt(V), (let b = GetMut(Bucket(V), n, &*s, i, hi); BInsert(V, b, k, v)),
        (let r = BFind(V, NthS(V, n, clone(*s), i, hi), k); let b = GetMut(Bucket(V), n, &*s, i, hi); BInsert(V, b, k, v); r)) by i := (
    match n {
      Zero => match hi {},
      Succ(m) => match *s {
        MkSlice(c) => match c {
          MkC(x, t) => match i {
            Zero => BInsertResult(V, &x, k, v),
            Succ(i') => SlotInsertResult(V, m, &t, i', hi, k, v),
          },
        },
      },
    }
  )

  -- ## Insert, in the map
  -- `InsertNoResize` updates the length according to what the bucket insert returned. That
  -- result is a sealed program; `split BInsert` splits on it, in each arm the map computes,
  -- and the slot theorem applies. The view is reached by taking the array apart, which a
  -- proof may do (the representation is abstract only at runtime).
  def InsertFind (V : Type) (hm : &HashMap(V)) (k : Word) (v : V) :
      Id(Opt(V), (InsertNoResize(V, &*hm, k, v); Find(V, clone(*hm), k)), (InsertNoResize(V, &*hm, k, clone(v)); Some(v))) := (
    match *hm {
      HM(n, len, slots) => match slots {
        MkArray(s) => split BInsert in SlotInsertFind(V, Succ(n), &s, Idx(k, n), IdxLt(k, n), k, v),
      },
    }
  )

  def InsertFindOther (V : Type) (hm : &HashMap(V)) (k : Word) (v : V) (k2 : Word) (h : Eq(Bool, EqB(k, k2), false)) :
      Id(Opt(V), (InsertNoResize(V, &*hm, k, v); Find(V, clone(*hm), k2)), (let r = Find(V, clone(*hm), k2); InsertNoResize(V, &*hm, k, v); r)) := (
    match *hm {
      HM(n, len, slots) => match slots {
        MkArray(s) => split BInsert in
          SlotInsertFindOther(V, Succ(n), &s, Idx(k, n), IdxLt(k, n), Idx(k2, n), IdxLt(k2, n), k, v, k2, h),
      },
    }
  )

  -- Without the split the goal is stuck on the sealed `InsertNoResize` and does not meet
  -- the slot theorem's statement.
  reject def InsertFindNoSplit (V : Type) (hm : &HashMap(V)) (k : Word) (v : V) :
      Id(Opt(V), (InsertNoResize(V, &*hm, k, v); Find(V, clone(*hm), k)), (InsertNoResize(V, &*hm, k, clone(v)); Some(v))) := (
    match *hm {
      HM(n, len, slots) => match slots {
        MkArray(s) => SlotInsertFind(V, Succ(n), &s, Idx(k, n), IdxLt(k, n), k, v),
      },
    }
  )

  -- Insert returns what `Find` returned before it: the old value, or `None`.
  def InsertResult (V : Type) (hm : &HashMap(V)) (k : Word) (v : V) :
      Id(Opt(V), InsertNoResize(V, &*hm, k, v), (let r = Find(V, clone(*hm), k); InsertNoResize(V, &*hm, k, v); r)) := (
    match *hm {
      HM(n, len, slots) => match slots {
        MkArray(s) => split BInsert in SlotInsertResult(V, Succ(n), &s, Idx(k, n), IdxLt(k, n), k, v),
      },
    }
  )

  -- ## Remove
  -- A bucket's keys are distinct (part of the invariant): each key is absent from the rest
  -- of the bucket, stated with the lookup itself. Across the table, every bucket; of a map,
  -- its table (a proposition may take the array apart).
  def Unique (V : Type) (b : Bucket(V)) : Prop by b := (
    match b {
      Nil => ⊤,
      Cons(e, t) => match e {
        Mk(k, v) => Eq(Opt(V), BFind(V, t, k), None[V]) ∧ Unique(V, t),
      },
    }
  )

  def AllUnique (V : Type) (n : Word) (s : Slice(Bucket(V), n)) : Prop by n := (
    match n {
      Zero => ⊤,
      Succ(m) => match s {
        MkSlice(c) => match c {
          MkC(b, t) => Unique(V, b) ∧ AllUnique(V, m, t),
        },
      },
    }
  )

  def KeysUnique (V : Type) (m : HashMap(V)) : Prop := (
    match m {
      HM(n, len, a) => match a {
        MkArray(s) => AllUnique(V, Succ(n), s),
      },
    }
  )

  -- Remove returns what a lookup would have returned.
  def BRemoveResult (V : Type) (b : &Bucket(V)) (k : Word) :
      Id(Opt(V), BRemove(V, &*b, k), (let r = BFind(V, clone(*b), k); BRemove(V, &*b, k); r)) by b := (
    match *b {
      Nil => refl,
      Cons(e, t) => match e {
        Mk(k', v') => (
          let eq = EqB(k', k);
          match eq {
            false => BRemoveResult(V, &t, k),
            true => refl,
          }
        ),
      },
    }
  )

  -- After removing `k`, looking `k` up gives `None`, if the keys are distinct. Where the
  -- first `k` is removed, the rest of the bucket does not hold `k'`, which is `k`: rewrite
  -- along `k' = k`.
  def BRemoveFind (V : Type) (b : &Bucket(V)) (k : Word) (h : Unique(V, clone(*b))) :
      Id(Opt(V), (BRemove(V, &*b, k); BFind(V, clone(*b), k)), (BRemove(V, &*b, k); None[V])) by b := (
    match *b {
      Nil => refl,
      Cons(e, t) => match e {
        Mk(k', v') => (
          let ⟨absent, rest⟩ = h;
          let eq = EqB(k', k);
          match eq {
            false => BRemoveFind(V, &t, k, rest),
            true => rewrite EqBSound(k', k, refl) in absent,
          }
        ),
      },
    }
  )

  reject def BRemoveFindDup (V : Type) (b : &Bucket(V)) (k : Word) :
      Id(Opt(V), (BRemove(V, &*b, k); BFind(V, clone(*b), k)), (BRemove(V, &*b, k); None[V])) by b := (
    match *b {
      Nil => refl,
      Cons(e, t) => match e {
        Mk(k', v') => (
          let eq = EqB(k', k);
          match eq {
            false => BRemoveFindDup(V, &t, k),
            true => refl,
          }
        ),
      },
    }
  )

  def BRemoveFindOther (V : Type) (b : &Bucket(V)) (k : Word) (k2 : Word) (h : Eq(Bool, EqB(k, k2), false)) :
      Id(Opt(V), (BRemove(V, &*b, k); BFind(V, clone(*b), k2)), (let r = BFind(V, clone(*b), k2); BRemove(V, &*b, k); r)) by b := (
    match *b {
      Nil => refl,
      Cons(e, t) => match e {
        Mk(k', v') => (
          let eq = EqB(k', k);
          let eq2 = EqB(k', k2);
          match eq {
            false => match eq2 {
              false => BRemoveFindOther(V, &t, k, k2, h),
              true => refl,
            },
            true => match eq2 {
              false => refl,
              true => (
                let f = EqBContra(k', k, k2, refl, refl, h);
                match f {}
              ),
            },
          }
        ),
      },
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
      Succ(m) => match *s {
        MkSlice(c) => match c {
          MkC(x, t) => match i {
            Zero => BRemoveResult(V, &x, k),
            Succ(i') => SlotRemoveResult(V, m, &t, i', hi, k),
          },
        },
      },
    }
  )

  def SlotRemoveFind (V : Type) (n : Word) (s : &Slice(Bucket(V), n)) (i : Word) (hi : Lt(i, n)) (k : Word)
      (h : AllUnique(V, n, clone(*s))) :
      Id(Opt(V), (let b = GetMut(Bucket(V), n, &*s, i, hi); BRemove(V, b, k); BFind(V, NthS(V, n, clone(*s), i, hi), k)),
        (let b = GetMut(Bucket(V), n, &*s, i, hi); BRemove(V, b, k); None[V])) by i := (
    match n {
      Zero => match hi {},
      Succ(m) => match *s {
        MkSlice(c) => match c {
          MkC(x, t) => (
            let ⟨hb, ht⟩ = h;
            match i {
              Zero => BRemoveFind(V, &x, k, hb),
              Succ(i') => SlotRemoveFind(V, m, &t, i', hi, k, ht),
            }
          ),
        },
      },
    }
  )

  def SlotRemoveFindOther (V : Type) (n : Word) (s : &Slice(Bucket(V), n)) (i : Word) (hi : Lt(i, n)) (j : Word) (hj : Lt(j, n))
      (k : Word) (k2 : Word) (h : Eq(Bool, EqB(k, k2), false)) :
      Id(Opt(V), (let b = GetMut(Bucket(V), n, &*s, i, hi); BRemove(V, b, k); BFind(V, NthS(V, n, clone(*s), j, hj), k2)),
        (let r = BFind(V, NthS(V, n, clone(*s), j, hj), k2); let b = GetMut(Bucket(V), n, &*s, i, hi); BRemove(V, b, k); r)) by i := (
    match n {
      Zero => match hi {},
      Succ(m) => match *s {
        MkSlice(c) => match c {
          MkC(x, t) => match i {
            Zero => match j {
              Zero => BRemoveFindOther(V, &x, k, k2, h),
              Succ(_) => refl,
            },
            Succ(i') => match j {
              Zero => refl,
              Succ(j') => SlotRemoveFindOther(V, m, &t, i', hi, j', hj, k, k2, h),
            },
          },
        },
      },
    }
  )

  def RemoveResult (V : Type) (hm : &HashMap(V)) (k : Word) :
      Id(Opt(V), Remove(V, &*hm, k), (let r = Find(V, clone(*hm), k); Remove(V, &*hm, k); r)) := (
    match *hm {
      HM(n, len, slots) => match slots {
        MkArray(s) => split BRemove in SlotRemoveResult(V, Succ(n), &s, Idx(k, n), IdxLt(k, n), k),
      },
    }
  )

  def RemoveFind (V : Type) (hm : &HashMap(V)) (k : Word) (h : KeysUnique(V, clone(*hm))) :
      Id(Opt(V), (Remove(V, &*hm, k); Find(V, clone(*hm), k)), (Remove(V, &*hm, k); None[V])) := (
    match *hm {
      HM(n, len, slots) => match slots {
        MkArray(s) => split BRemove in SlotRemoveFind(V, Succ(n), &s, Idx(k, n), IdxLt(k, n), k, h),
      },
    }
  )

  def RemoveFindOther (V : Type) (hm : &HashMap(V)) (k : Word) (k2 : Word) (h : Eq(Bool, EqB(k, k2), false)) :
      Id(Opt(V), (Remove(V, &*hm, k); Find(V, clone(*hm), k2)), (let r = Find(V, clone(*hm), k2); Remove(V, &*hm, k); r)) := (
    match *hm {
      HM(n, len, slots) => match slots {
        MkArray(s) => split BRemove in
          SlotRemoveFindOther(V, Succ(n), &s, Idx(k, n), IdxLt(k, n), Idx(k2, n), IdxLt(k2, n), k, k2, h),
      },
    }
  )

  -- ## MapGetMut
  -- The borrow points at the value a lookup returns. In the `Nil` arm the precondition is
  -- `IsSome(V, None)`, which is `False`.
  def BGetMutRead (V : Type) (b : &Bucket(V)) (k : Word) (w : V) (h : IsSome(V, BFind(V, clone(*b), k))) :
      Id(Opt(V), (let q = BGet(V, &*b, k, h); let x = clone(*q); *q := w; Some(x)),
        (let r = BFind(V, clone(*b), k); let q = BGet(V, &*b, k, h); *q := w; r)) by b := (
    match *b {
      Nil => match h {},
      Cons(e, t) => match e {
        Mk(k', v') => (
          let eq = EqB(k', k);
          match eq {
            false => BGetMutRead(V, &t, k, w, h),
            true => refl,
          }
        ),
      },
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
      Succ(m) => match *s {
        MkSlice(c) => match c {
          MkC(x, t) => match i {
            Zero => BGetMutRead(V, &x, k, w, h),
            Succ(i') => SlotGetMutRead(V, m, &t, i', hi, k, w, h),
          },
        },
      },
    }
  )

  def MapGetMutRead (V : Type) (hm : &HashMap(V)) (k : Word) (w : V) (h : IsSome(V, Find(V, clone(*hm), k))) :
      Id(Opt(V), (let q = MapGetMut(V, &*hm, k, h); let x = clone(*q); *q := w; Some(x)),
        (let r = Find(V, clone(*hm), k); let q = MapGetMut(V, &*hm, k, h); *q := w; r)) := (
    match *hm {
      HM(n, len, slots) => match slots {
        MkArray(s) => SlotGetMutRead(V, Succ(n), &s, Idx(k, n), IdxLt(k, n), k, w, h),
      },
    }
  )

  -- Writing `w` through the borrow is inserting `k ↦ w`: the key is present, so the
  -- insert overwrites and adds nothing (and returns the old value, which the write drops).
  -- Every other theorem about `MapGetMut` follows from the insert's.
  def BGetMutIsInsert (V : Type) (b : &Bucket(V)) (k : Word) (w : V) (h : IsSome(V, BFind(V, *b, k))) :
      Id(Unit, (let q = BGet(V, &*b, k, h); *q := w), (BInsert(V, &*b, k, w); ())) by b := (
    match *b {
      Nil => match h {},
      Cons(e, t) => match e {
        Mk(k', v') => (
          let eq = EqB(k', k);
          match eq {
            false => BGetMutIsInsert(V, &t, k, w, h),
            true => refl,
          }
        ),
      },
    }
  )

  def SlotGetMutIsInsert (V : Type) (n : Word) (s : &Slice(Bucket(V), n)) (i : Word) (hi : Lt(i, n)) (k : Word) (w : V)
      (h : IsSome(V, BFind(V, NthS(V, n, *s, i, hi), k))) :
      Id(Unit, (let b = GetMut(Bucket(V), n, &*s, i, hi); let q = BGet(V, b, k, h); *q := w),
        (let b = GetMut(Bucket(V), n, &*s, i, hi); BInsert(V, b, k, w); ())) by i := (
    match n {
      Zero => match hi {},
      Succ(m) => match *s {
        MkSlice(c) => match c {
          MkC(x, t) => match i {
            Zero => BGetMutIsInsert(V, &x, k, w, h),
            Succ(i') => SlotGetMutIsInsert(V, m, &t, i', hi, k, w, h),
          },
        },
      },
    }
  )

  -- The map inserts through the same borrow; where the insert would have added an entry,
  -- `SlotInsertResult` says the key was absent, against the precondition.
  def GetMutIsInsert (V : Type) (hm : &HashMap(V)) (k : Word) (w : V) (h : IsSome(V, Find(V, *hm, k))) :
      Id(Unit, (let q = MapGetMut(V, &*hm, k, h); *q := w), (InsertNoResize(V, &*hm, k, w); ())) := (
    match *hm {
      HM(n, len, slots) => match slots {
        MkArray(s) => (
          let p = SlotInsertResult(V, Succ(n), &s, Idx(k, n), IdxLt(k, n), k, w);
          let r = BFind(V, NthS(V, Succ(n), clone(s), Idx(k, n), IdxLt(k, n)), k);
          split BInsert {
            None => match r {
              None => match h {},
              Some(_) => match p {},
            },
            Some(_) => SlotGetMutIsInsert(V, Succ(n), &s, Idx(k, n), IdxLt(k, n), k, w, h),
          }
        ),
      },
    }
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
      Cons(e, t) => match e {
        Mk(k', v') => (
          let eq = EqB(k', k);
          match eq {
            false => BGetFind(V, &t, k, h),
            true => refl,
          }
        ),
      },
    }
  )

  def SlotGetFind (V : Type) (n : Word) (s : &Slice(Bucket(V), n)) (i : Word) (hi : Lt(i, n)) (k : Word)
      (h : IsSome(V, BFind(V, NthS(V, n, clone(*s), i, hi), k))) :
      Id(Opt(V), (let b = GetMut(Bucket(V), n, &*s, i, hi); Some(clone(*BGet(V, b, k, h)))), BFind(V, NthS(V, n, clone(*s), i, hi), k)) by i := (
    match n {
      Zero => match hi {},
      Succ(m) => match *s {
        MkSlice(c) => match c {
          MkC(x, t) => match i {
            Zero => BGetFind(V, &x, k, h),
            Succ(i') => SlotGetFind(V, m, &t, i', hi, k, h),
          },
        },
      },
    }
  )

  def GetFind (V : Type) (hm : &HashMap(V)) (k : Word) (h : IsSome(V, Find(V, clone(*hm), k))) :
      Id(Opt(V), Some(clone(*Get(V, &*hm, k, h))), Find(V, clone(*hm), k)) := (
    match *hm {
      HM(n, len, slots) => match slots {
        MkArray(s) => SlotGetFind(V, Succ(n), &s, Idx(k, n), IdxLt(k, n), k, h),
      },
    }
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
      Cons(e, t) => match e {
        Mk(k', v') => (
          let eq = EqB(k', k);
          match eq {
            false => BContainsFind(V, &t, k),
            true => refl,
          }
        ),
      },
    }
  )

  def SlotContainsFind (V : Type) (n : Word) (s : &Slice(Bucket(V), n)) (i : Word) (hi : Lt(i, n)) (k : Word) :
      Id(Bool, (let b = GetMut(Bucket(V), n, &*s, i, hi); BContains(V, b, k)), Has(V, BFind(V, NthS(V, n, clone(*s), i, hi), k))) by i := (
    match n {
      Zero => match hi {},
      Succ(m) => match *s {
        MkSlice(c) => match c {
          MkC(x, t) => match i {
            Zero => BContainsFind(V, &x, k),
            Succ(i') => SlotContainsFind(V, m, &t, i', hi, k),
          },
        },
      },
    }
  )

  def ContainsFind (V : Type) (hm : &HashMap(V)) (k : Word) : Id(Bool, ContainsKey(V, &*hm, k), Has(V, Find(V, clone(*hm), k))) := (
    match *hm {
      HM(n, len, slots) => match slots {
        MkArray(s) => SlotContainsFind(V, Succ(n), &s, Idx(k, n), IdxLt(k, n), k),
      },
    }
  )

  -- ## New and Clear
  -- Every bucket of a fresh table is empty, so no key is found.
  def EmptyLookup (V : Type) (n : Word) (j : Word) (i : Word) (h : Lt(i, n)) (k : Word) :
      Id(Opt(V), (let c = FromFnS(Bucket(V), n, λ(x : Word) : Bucket(V) => Nil, j); BLookup(V, GetMut(Bucket(V), n, &c, i, h), k)), None[V]) by n := (
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

  def ClearFind (V : Type) (hm : &HashMap(V)) (k : Word) : Id(Opt(V), (Clear(V, &*hm); Find(V, clone(*hm), k)), (Clear(V, &*hm); None[V])) := (
    match *hm {
      HM(n, len, slots) => NewFind(V, n, k),
    }
  )
}

-- the exact number of declarations (a truncated file changes it)
#guard HashMapLookup.decls.length == 45
