import Ochr.Examples.«00Std»

/-! # 17. A verified hash map

The case study of `notes/hashmap-case-study.md`: the resizing hash map that Aeneas verifies
(ICFP 2022, §6), written once, in place, with its theorems stated and proved about that
program. There is no pure model and no refinement proof: where Aeneas states "after
`insert`, `find_s` of the key is the value" about a hand-written model `find_s`, here the
statement uses `Get` itself, run on a copy of the map (`Find`, as `Add` runs `AddM` on a
copy).

The table is a non-empty list of buckets (Ochr has no arrays yet), each bucket an
association list. `Slot(s, i)` returns a borrow of bucket `i`, as Rust's `&mut slots[i]`,
and saturates at the last bucket, so it needs no bounds proof. Keys, the table size and the
length are `Word`s, which reading copies, and values are `Nat`s, which reading moves (D53),
as Rust's `usize` keys and non-`Copy` values; the hash is the identity, as in Aeneas, and
`k mod (n + 1)` picks the bucket.

The file has four programs: `HashMap`, the implementation with concrete runs; `HashMapLookup`,
lookups after each operation; `HashMapLength`, the length field and the count of entries;
`HashMapResize`, the invariant, resizing, `Insert` with its resize, and the load factor. -/

open Ochr.Test

ochr HashMap uses Std {
  -- ## The data
  -- `n + 1` buckets, `len` entries; `Opt` is the result of a lookup.
  inductive Opt := None | Some(v : Nat)
  inductive Bucket := BNil | BCons(k : Word, v : Nat, t : Bucket)
  inductive Slots := SOne(b : Bucket) | SCons(b : Bucket, t : Slots)
  inductive HashMap := HM(n : Word, len : Word, slots : Slots)

  -- ## Arithmetic
  -- Keys, sizes and indices are `Word`s, which reading copies; values are `Nat`s, which
  -- reading moves (D53). Key comparison, the bucket index `k mod (n + 1)` by recursion on
  -- `k` with a running remainder, and addition.
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

  def Lt (a : Word) (b : Word) : Bool by a := (
    match a {
      Zero => match b {
        Zero => false,
        Succ(_) => true,
      },
      Succ(a') => match b {
        Zero => false,
        Succ(b') => Lt(a', b'),
      },
    }
  )

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

  def Pred (n : Word) : Word := (
    match n {
      Zero => Zero,
      Succ(m) => m,
    }
  )

  def WAdd (a : Word) (b : Word) : Word by a := (
    match a {
      Zero => b,
      Succ(a') => Succ(WAdd(a', b)),
    }
  )

  -- ## Buckets
  -- Look a key up, test for it, insert or overwrite it (`true` if a new entry was added),
  -- remove it (returning the removed value), and borrow its value. The lookup returns a
  -- copy of the value, which stays in the bucket (Rust's `get` returns a shared borrow,
  -- which Ochr does not have).
  def BGet (b : &Bucket) (k : Word) : Opt by b := (
    match *b {
      BNil => None,
      BCons(k', v', t) => (
        let e = EqB(k', k);
        match e {
          false => BGet(&t, k),
          true => Some(clone(v')),
        }
      ),
    }
  )

  def BContains (b : &Bucket) (k : Word) : Bool by b := (
    match *b {
      BNil => false,
      BCons(k', v', t) => (
        let e = EqB(k', k);
        match e {
          false => BContains(&t, k),
          true => true,
        }
      ),
    }
  )

  def BInsert (b : &Bucket) (k : Word) (v : Nat) : Bool by b := (
    match *b {
      BNil => (
        *b := BCons(k, v, BNil);
        true
      ),
      BCons(k', v', t) => (
        let e = EqB(k', k);
        match e {
          false => BInsert(&t, k, v),
          true => (
            v' := v;
            false
          ),
        }
      ),
    }
  )

  def BRemove (b : &Bucket) (k : Word) : Opt by b := (
    match *b {
      BNil => None,
      BCons(k', v', t) => (
        let e = EqB(k', k);
        match e {
          false => BRemove(&t, k),
          true => (
            let x = v';
            *b := t;
            Some(x)
          ),
        }
      ),
    }
  )

  -- A lookup on a copy, for statements (as `Add` runs `AddM` on a copy), and presence.
  def BFind (b : Bucket) (k : Word) : Opt := BGet(&b, k)

  def IsSome (o : Opt) : Prop := (
    match o {
      None => False,
      Some(_) => ⊤,
    }
  )

  -- The borrow of a present key's value. The key is present, so the `BNil` arm cannot
  -- happen: there `h` is a proof of `IsSome(None)`, which is `False`.
  def BGetMut (b : &Bucket) (k : Word) (h : IsSome(BFind(*b, k))) : &Nat by b := (
    match *b {
      BNil => match h {},
      BCons(k', v', t) => (
        let e = EqB(k', k);
        match e {
          false => BGetMut(&t, k, h),
          true => &v',
        }
      ),
    }
  )
  -- ## The slots
  -- The index borrow (Rust's `&mut slots[i]`): a borrow of bucket `i`, or of the last one.
  def Slot (s : &Slots) (i : Word) : &Bucket by s := (
    match *s {
      SOne(b) => &b,
      SCons(b, t) => match i {
        Zero => &b,
        Succ(i') => Slot(&t, i'),
      },
    }
  )

  def EmptySlots (n : Word) : Slots by n := (
    match n {
      Zero => SOne(BNil),
      Succ(m) => SCons(BNil, EmptySlots(m)),
    }
  )

  -- ## The map
  -- Every operation finds the key's bucket through `Slot` and works on it in place.
  def New (n : Word) : HashMap := HM(n, Zero, EmptySlots(n))

  def Get (hm : &HashMap) (k : Word) : Opt := (
    match *hm {
      HM(n, len, slots) => (
        let b = Slot(&slots, Idx(k, n));
        BGet(b, k)
      ),
    }
  )

  def ContainsKey (hm : &HashMap) (k : Word) : Bool := (
    match *hm {
      HM(n, len, slots) => (
        let b = Slot(&slots, Idx(k, n));
        BContains(b, k)
      ),
    }
  )

  def InsertNoResize (hm : &HashMap) (k : Word) (v : Nat) : Unit := (
    match *hm {
      HM(n, len, slots) => (
        let b = Slot(&slots, Idx(k, n));
        let added = BInsert(b, k, v);
        match added {
          false => (),
          true => len := Succ(len),
        }
      ),
    }
  )

  def Remove (hm : &HashMap) (k : Word) : Opt := (
    match *hm {
      HM(n, len, slots) => (
        let b = Slot(&slots, Idx(k, n));
        let x = BRemove(b, k);
        match x {
          None => (),
          Some(_) => len := Pred(len),
        };
        x
      ),
    }
  )

  def Clear (hm : &HashMap) : Unit := (
    match *hm {
      HM(n, len, slots) => (
        len := Zero;
        slots := EmptySlots(n)
      ),
    }
  )

  def Len (m : HashMap) : Word := (
    match m {
      HM(n, len, s) => len,
    }
  )

  -- A lookup on a copy, for statements, and the borrow of a present key's value.
  def Find (m : HashMap) (k : Word) : Opt := Get(&m, k)

  def GetMut (hm : &HashMap) (k : Word) (h : IsSome(Find(*hm, k))) : &Nat := (
    match *hm {
      HM(n, len, slots) => (
        let b = Slot(&slots, Idx(k, n));
        BGetMut(b, k, h)
      ),
    }
  )

  -- ## Resizing
  -- Move every entry into a map with `2n + 2` buckets, by inserting it again. Resizing
  -- happens when the entries outnumber the buckets (load factor 1).
  def MoveBucket (b : Bucket) (hm : &HashMap) : Unit by b := (
    match b {
      BNil => (),
      BCons(k, v, t) => (
        InsertNoResize(&*hm, k, v);
        MoveBucket(t, hm)
      ),
    }
  )

  def MoveSlots (s : Slots) (hm : &HashMap) : Unit by s := (
    match s {
      SOne(b) => MoveBucket(b, hm),
      SCons(b, t) => (
        MoveBucket(b, &*hm);
        MoveSlots(t, hm)
      ),
    }
  )

  def Resize (hm : &HashMap) : Unit := (
    match *hm {
      HM(n, len, slots) => (
        let old = slots;
        *hm := New(Succ(WAdd(n, n)));
        MoveSlots(old, hm)
      ),
    }
  )

  def Insert (hm : &HashMap) (k : Word) (v : Nat) : Unit := (
    InsertNoResize(&*hm, k, v);
    match *hm {
      HM(n, len, slots) => (
        let full = Lt(n, len);
        match full {
          false => (),
          true => Resize(&*hm),
        }
      ),
    }
  )

  -- ## Runs
  -- `W(n)` is the `Word` for the number `n`.
  def W (n : Nat) : Word by n := (
    match n {
      Z => Zero,
      S m => Succ(W(m)),
    }
  )

  -- Three inserts into a map with two buckets: the second reaches the load factor and
  -- resizes to four. Every key is found again, an absent one is not.
  def RunLayout : Id HashMap (
    let m = New(W(1));
    Insert(&m, W(1), 10);
    Insert(&m, W(2), 20);
    Insert(&m, W(3), 30);
    m
  ) (HM(W(3), W(3), SCons(BNil, SCons(BCons(W(1), 10, BNil), SCons(BCons(W(2), 20, BNil), SOne(BCons(W(3), 30, BNil))))))) := refl

  def RunGet : Id (Opt × Opt) (
    let m = New(W(1));
    Insert(&m, W(1), 10);
    Insert(&m, W(2), 20);
    Insert(&m, W(3), 30);
    (Get(&m, W(2)), Get(&m, W(5)))
  ) (Some(20), None) := refl

  reject def RunGetWrong : Id Opt (
    let m = New(W(1));
    Insert(&m, W(1), 10);
    Insert(&m, W(2), 20);
    Get(&m, W(1))
  ) (Some(20)) := refl

  def RunContains : Id (Bool × Bool) (
    let m = New(W(1));
    Insert(&m, W(1), 10);
    Insert(&m, W(2), 20);
    (ContainsKey(&m, W(2)), ContainsKey(&m, W(3)))
  ) (true, false) := refl

  -- Overwriting keeps the length; `5` collides with `1` in a map with four buckets.
  def RunOverwrite : Id (Word × Opt) (
    let m = New(W(1));
    Insert(&m, W(1), 10);
    Insert(&m, W(2), 20);
    Insert(&m, W(2), 25);
    (Len(m), Get(&m, W(2)))
  ) (W(2), Some(25)) := refl

  def RunCollide : Id HashMap (
    let m = New(W(3));
    Insert(&m, W(1), 10);
    Insert(&m, W(5), 50);
    m
  ) (HM(W(3), W(2), SCons(BNil, SCons(BCons(W(1), 10, BCons(W(5), 50, BNil)), SCons(BNil, SOne(BNil)))))) := refl

  -- Remove returns the value it removed; removing an absent key does nothing.
  def RunRemove : Id (Opt × HashMap) (
    let m = New(W(3));
    Insert(&m, W(1), 10);
    Insert(&m, W(5), 50);
    let x = Remove(&m, W(1));
    Remove(&m, W(7));
    (x, m)
  ) (Some(10), HM(W(3), W(1), SCons(BNil, SCons(BCons(W(5), 50, BNil), SCons(BNil, SOne(BNil)))))) := refl

  -- Write through the borrow of a present key. For an absent key the proof `refl` of
  -- `IsSome(Find(m, 5))` does not exist: the precondition computes to `False`.
  def RunGetMut : Id Opt (
    let m = New(W(3));
    Insert(&m, W(1), 10);
    Insert(&m, W(5), 50);
    let q = GetMut(&m, W(5), refl);
    *q := 55;
    Get(&m, W(5))
  ) (Some(55)) := refl

  reject def RunGetMutAbsent : Id Opt (
    let m = New(W(3));
    Insert(&m, W(1), 10);
    let q = GetMut(&m, W(5), refl);
    *q := 55;
    Get(&m, W(5))
  ) (Some(55)) := refl

  -- Clear empties the map and keeps the buckets.
  def RunClear : Id HashMap (
    let m = New(W(1));
    Insert(&m, W(1), 10);
    Clear(&m);
    m
  ) (New(W(1))) := refl

  -- Without its `clone`, the lookup would move the value out of a bucket it only borrows,
  -- and the borrow would end with the bucket partly moved out.
  reject def BGetMoves (b : &Bucket) (k : Word) : Opt by b := (
    match *b {
      BNil => None,
      BCons(k', v', t) => (
        let e = EqB(k', k);
        match e {
          false => BGetMoves(&t, k),
          true => Some(v'),
        }
      ),
    }
  )
}

-- the exact number of declarations (a truncated file changes it)
#guard HashMap.decls.length == 44

/-! ## Lookups after each operation

Each theorem says what `Find` returns after an operation, for the key it touched and for
any other key. The statements use the operations themselves: "after `InsertNoResize(hm, k,
v)`, `Find(*hm, k)` is `Some(v)`" is `Id Opt (InsertNoResize(&*hm, k, v); Find(*hm, k))
(InsertNoResize(&*hm, k, v); Some(v))`. Each is proved first for one bucket, by recursion on
the bucket, then lifted through `Slot` by recursion on the slots, then stated for the map. -/

ochr HashMapLookup uses Std, HashMap {
  -- ## Key comparison
  def EqBRefl (k : Word) : Eq Bool (EqB(k, k)) true by k := (
    match k {
      Zero => refl,
      Succ(k') => EqBRefl(k'),
    }
  )

  -- Where the comparison says the keys are equal, they are. `Succ(a) = Succ(b)` is
  -- `a = b` (injectivity), so the recursive call proves the `Succ` case as it stands.
  def EqBSound (a : Word) (b : Word) (h : Eq Bool (EqB(a, b)) true) : Eq Word a b by a := (
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

  def EqBTrans (a : Word) (b : Word) (c : Word) (h1 : Eq Bool (EqB(a, b)) true) (h2 : Eq Bool (EqB(a, c)) true) :
      Eq Bool (EqB(b, c)) true := rewrite EqBSound(a, b, h1) in h2

  -- A bucket key equal to both `k` and `k2` contradicts `k ≠ k2`.
  def EqBContra (a : Word) (b : Word) (c : Word) (h1 : Eq Bool (EqB(a, b)) true) (h2 : Eq Bool (EqB(a, c)) true)
      (h : Eq Bool (EqB(b, c)) false) : False := (
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
  -- After inserting `k`, looking `k` up gives the inserted value. In the `BNil` arm the
  -- lookup compares `k` with itself, which the checker cannot compute for an abstract `k`:
  -- split on it, and the `false` arm contradicts `EqBRefl`.
  def BInsertFind (b : &Bucket) (k : Word) (v : Nat) :
      Id Opt (BInsert(&*b, k, v); BFind(*b, k)) (BInsert(&*b, k, v); Some(v)) by b := (
    match *b {
      BNil => (
        let e = EqB(k, k);
        match e {
          false => (
            let p = EqBRefl(k);
            match p {}
          ),
          true => refl,
        }
      ),
      BCons(k', v', t) => (
        let e = EqB(k', k);
        match e {
          false => BInsertFind(&t, k, v),
          true => refl,
        }
      ),
    }
  )

  -- Inserting `k` does not change the lookup of another key `k2`.
  def BInsertFindOther (b : &Bucket) (k : Word) (v : Nat) (k2 : Word) (h : Eq Bool (EqB(k, k2)) false) :
      Id Opt (BInsert(&*b, k, v); BFind(*b, k2)) (let r = BFind(*b, k2); BInsert(&*b, k, v); r) by b := (
    match *b {
      BNil => (
        let e = EqB(k, k2);
        match e {
          false => refl,
          true => match h {},
        }
      ),
      BCons(k', v', t) => (
        let e = EqB(k', k);
        let e2 = EqB(k', k2);
        match e {
          false => match e2 {
            false => BInsertFindOther(&t, k, v, k2, h),
            true => refl,
          },
          true => match e2 {
            false => refl,
            true => (
              let f = EqBContra(k', k, k2, refl, refl, h);
              match f {}
            ),
          },
        }
      ),
    }
  )
  -- ## Insert, through the index borrow
  -- `Nth(s, i)` takes bucket `i` out of the slots `s` (leaving an empty one, as Rust's
  -- `mem::take`). Each bucket theorem is lifted by recursion on the slots, following
  -- `Slot`'s own recursion: the recursive call borrows the tail, so the untouched buckets
  -- stay where they are and need no argument.
  def Nth (s : Slots) (i : Word) : Bucket := (
    let r = Slot(&s, i);
    let b = *r;
    *r := BNil;
    b
  )

  def SlotInsertFind (s : &Slots) (i : Word) (k : Word) (v : Nat) :
      Id Opt (let b = Slot(&*s, i); BInsert(b, k, v); BFind(Nth(*s, i), k))
             (let b = Slot(&*s, i); BInsert(b, k, v); Some(v)) by s := (
    match *s {
      SOne(b) => BInsertFind(&b, k, v),
      SCons(b, t) => match i {
        Zero => BInsertFind(&b, k, v),
        Succ(i') => SlotInsertFind(&t, i', k, v),
      },
    }
  )

  -- Writing bucket `i` and reading bucket `j`: the same bucket is the bucket theorem,
  -- different buckets do not interact.
  def SlotInsertFindOther (s : &Slots) (i : Word) (j : Word) (k : Word) (v : Nat) (k2 : Word)
      (h : Eq Bool (EqB(k, k2)) false) :
      Id Opt (let b = Slot(&*s, i); BInsert(b, k, v); BFind(Nth(*s, j), k2))
             (let r = BFind(Nth(*s, j), k2); let b = Slot(&*s, i); BInsert(b, k, v); r) by s := (
    match *s {
      SOne(b) => BInsertFindOther(&b, k, v, k2, h),
      SCons(b, t) => match i {
        Zero => match j {
          Zero => BInsertFindOther(&b, k, v, k2, h),
          Succ(_) => refl,
        },
        Succ(i') => match j {
          Zero => refl,
          Succ(j') => SlotInsertFindOther(&t, i', j', k, v, k2, h),
        },
      },
    }
  )

  -- ## Insert, in the map
  -- `InsertNoResize` updates the length according to whether the bucket insert added an
  -- entry. That result is a sealed program, so the proof reproduces it on a copy of the
  -- slots and splits on it; in each arm the map computes, and the slot theorem applies.
  def InsertFind (hm : &HashMap) (k : Word) (v : Nat) :
      Id Opt (InsertNoResize(&*hm, k, v); Find(*hm, k)) (InsertNoResize(&*hm, k, v); Some(v)) := (
    match *hm {
      HM(n, len, slots) => split BInsert in SlotInsertFind(&slots, Idx(k, n), k, v),
    }
  )

  def InsertFindOther (hm : &HashMap) (k : Word) (v : Nat) (k2 : Word)
      (h : Eq Bool (EqB(k, k2)) false) :
      Id Opt (InsertNoResize(&*hm, k, v); Find(*hm, k2))
             (let r = Find(*hm, k2); InsertNoResize(&*hm, k, v); r) := (
    match *hm {
      HM(n, len, slots) => split BInsert in
        SlotInsertFindOther(&slots, Idx(k, n), Idx(k2, n), k, v, k2, h),
    }
  )
  -- Without the split the goal is stuck on the sealed `InsertNoResize` and does not meet
  -- the slot theorem's statement.
  reject def InsertFindNoSplit (hm : &HashMap) (k : Word) (v : Nat) :
      Id Opt (InsertNoResize(&*hm, k, v); Find(*hm, k)) (InsertNoResize(&*hm, k, v); Some(v)) := (
    match *hm {
      HM(n, len, slots) => SlotInsertFind(&slots, Idx(k, n), k, v),
    }
  )
  -- The bucket insert adds an entry exactly when the key was absent.
  def IsNone (r : Opt) : Bool := (
    match r {
      None => true,
      Some(_) => false,
    }
  )
  def BInsertAdded (b : &Bucket) (k : Word) (v : Nat) :
      Id Bool (BInsert(&*b, k, v)) (let r = BFind(*b, k); BInsert(&*b, k, v); IsNone(r)) by b := (
    match *b {
      BNil => refl,
      BCons(k', v', t) => (
        let e = EqB(k', k);
        match e {
          false => BInsertAdded(&t, k, v),
          true => refl,
        }
      ),
    }
  )
  def SlotInsertAdded (s : &Slots) (i : Word) (k : Word) (v : Nat) :
      Id Bool (let b = Slot(&*s, i); BInsert(b, k, v))
              (let r = BFind(Nth(*s, i), k); let b = Slot(&*s, i); BInsert(b, k, v); IsNone(r)) by s := (
    match *s {
      SOne(b) => BInsertAdded(&b, k, v),
      SCons(b, t) => match i {
        Zero => BInsertAdded(&b, k, v),
        Succ(i') => SlotInsertAdded(&t, i', k, v),
      },
    }
  )
  -- ## Remove
  -- A bucket's keys are distinct (part of the invariant): each key is absent from the rest
  -- of the bucket, stated with the lookup itself. Across the whole table, every bucket.
  def Unique (b : Bucket) : Prop by b := (
    match b {
      BNil => ⊤,
      BCons(k, v, t) => Eq Opt (BFind(t, k)) None ∧ Unique(t),
    }
  )

  def AllUnique (s : Slots) : Prop by s := (
    match s {
      SOne(b) => Unique(b),
      SCons(b, t) => Unique(b) ∧ AllUnique(t),
    }
  )

  -- Remove returns what a lookup would have returned.
  def BRemoveResult (b : &Bucket) (k : Word) :
      Id Opt (BRemove(&*b, k)) (let r = BFind(*b, k); BRemove(&*b, k); r) by b := (
    match *b {
      BNil => refl,
      BCons(k', v', t) => (
        let e = EqB(k', k);
        match e {
          false => BRemoveResult(&t, k),
          true => refl,
        }
      ),
    }
  )

  -- After removing `k`, looking `k` up gives `None`, if the keys are distinct. Where the
  -- first `k` is removed, the rest of the bucket does not hold `k'`, which is `k`: rewrite
  -- along `k' = k`.
  def BRemoveFind (b : &Bucket) (k : Word) (h : Unique(*b)) :
      Id Opt (BRemove(&*b, k); BFind(*b, k)) (BRemove(&*b, k); None) by b := (
    match *b {
      BNil => refl,
      BCons(k', v', t) => (
        let ⟨absent, rest⟩ = h;
        let e = EqB(k', k);
        match e {
          false => BRemoveFind(&t, k, rest),
          true => rewrite EqBSound(k', k, refl) in absent,
        }
      ),
    }
  )

  reject def BRemoveFindDup (b : &Bucket) (k : Word) :
      Id Opt (BRemove(&*b, k); BFind(*b, k)) (BRemove(&*b, k); None) by b := (
    match *b {
      BNil => refl,
      BCons(k', v', t) => (
        let e = EqB(k', k);
        match e {
          false => BRemoveFindDup(&t, k),
          true => refl,
        }
      ),
    }
  )

  def BRemoveFindOther (b : &Bucket) (k : Word) (k2 : Word) (h : Eq Bool (EqB(k, k2)) false) :
      Id Opt (BRemove(&*b, k); BFind(*b, k2)) (let r = BFind(*b, k2); BRemove(&*b, k); r) by b := (
    match *b {
      BNil => refl,
      BCons(k', v', t) => (
        let e = EqB(k', k);
        let e2 = EqB(k', k2);
        match e {
          false => match e2 {
            false => BRemoveFindOther(&t, k, k2, h),
            true => refl,
          },
          true => match e2 {
            false => refl,
            true => (
              let f = EqBContra(k', k, k2, refl, refl, h);
              match f {}
            ),
          },
        }
      ),
    }
  )
  -- Lifted through the index borrow, and stated for the map. The precondition of
  -- `RemoveFind` is the part of the invariant it needs: the keys of each bucket are
  -- distinct.
  def SlotRemoveResult (s : &Slots) (i : Word) (k : Word) :
      Id Opt (let b = Slot(&*s, i); BRemove(b, k))
             (let r = BFind(Nth(*s, i), k); let b = Slot(&*s, i); BRemove(b, k); r) by s := (
    match *s {
      SOne(b) => BRemoveResult(&b, k),
      SCons(b, t) => match i {
        Zero => BRemoveResult(&b, k),
        Succ(i') => SlotRemoveResult(&t, i', k),
      },
    }
  )

  def SlotRemoveFind (s : &Slots) (i : Word) (k : Word) (h : AllUnique(*s)) :
      Id Opt (let b = Slot(&*s, i); BRemove(b, k); BFind(Nth(*s, i), k))
             (let b = Slot(&*s, i); BRemove(b, k); None) by s := (
    match *s {
      SOne(b) => BRemoveFind(&b, k, h),
      SCons(b, t) => (
        let ⟨hb, ht⟩ = h;
        match i {
          Zero => BRemoveFind(&b, k, hb),
          Succ(i') => SlotRemoveFind(&t, i', k, ht),
        }
      ),
    }
  )

  def SlotRemoveFindOther (s : &Slots) (i : Word) (j : Word) (k : Word) (k2 : Word) (h : Eq Bool (EqB(k, k2)) false) :
      Id Opt (let b = Slot(&*s, i); BRemove(b, k); BFind(Nth(*s, j), k2))
             (let r = BFind(Nth(*s, j), k2); let b = Slot(&*s, i); BRemove(b, k); r) by s := (
    match *s {
      SOne(b) => BRemoveFindOther(&b, k, k2, h),
      SCons(b, t) => match i {
        Zero => match j {
          Zero => BRemoveFindOther(&b, k, k2, h),
          Succ(_) => refl,
        },
        Succ(i') => match j {
          Zero => refl,
          Succ(j') => SlotRemoveFindOther(&t, i', j', k, k2, h),
        },
      },
    }
  )

  def Buckets (m : HashMap) : Slots := (
    match m {
      HM(n, len, s) => s,
    }
  )

  def RemoveResult (hm : &HashMap) (k : Word) :
      Id Opt (Remove(&*hm, k)) (let r = Find(*hm, k); Remove(&*hm, k); r) := (
    match *hm {
      HM(n, len, slots) => split BRemove in SlotRemoveResult(&slots, Idx(k, n), k),
    }
  )

  def RemoveFind (hm : &HashMap) (k : Word) (h : AllUnique(Buckets(*hm))) :
      Id Opt (Remove(&*hm, k); Find(*hm, k)) (Remove(&*hm, k); None) := (
    match *hm {
      HM(n, len, slots) => split BRemove in SlotRemoveFind(&slots, Idx(k, n), k, h),
    }
  )

  def RemoveFindOther (hm : &HashMap) (k : Word) (k2 : Word) (h : Eq Bool (EqB(k, k2)) false) :
      Id Opt (Remove(&*hm, k); Find(*hm, k2)) (let r = Find(*hm, k2); Remove(&*hm, k); r) := (
    match *hm {
      HM(n, len, slots) => split BRemove in SlotRemoveFindOther(&slots, Idx(k, n), Idx(k2, n), k, k2, h),
    }
  )
  -- ## GetMut
  -- The borrow points at the value a lookup returns. In the `BNil` arm the split
  -- re-normalises the goal, which runs `BGetMut` into its unreachable `match h {}`: that
  -- match is stuck (D58), so the goal stays a sealed program and the arm's own
  -- `match h {}` proves it.
  def BGetMutRead (b : &Bucket) (k : Word) (w : Nat) (h : IsSome(BFind(*b, k))) :
      Id Opt (let q = BGetMut(&*b, k, h); let x = *q; *q := w; Some(x))
             (let r = BFind(*b, k); let q = BGetMut(&*b, k, h); *q := w; r) by b := (
    match *b {
      BNil => match h {},
      BCons(k', v', t) => (
        let e = EqB(k', k);
        match e {
          false => BGetMutRead(&t, k, w, h),
          true => refl,
        }
      ),
    }
  )

  -- Lifted through the index borrow, and stated for the map. `GetMut` branches on no
  -- sealed result, so the map theorem is the slot theorem at the key's index.
  def SlotGetMutRead (s : &Slots) (i : Word) (k : Word) (w : Nat) (h : IsSome(BFind(Nth(*s, i), k))) :
      Id Opt (let b = Slot(&*s, i); let q = BGetMut(b, k, h); let x = *q; *q := w; Some(x))
             (let r = BFind(Nth(*s, i), k); let b = Slot(&*s, i); let q = BGetMut(b, k, h); *q := w; r) by s := (
    match *s {
      SOne(b) => BGetMutRead(&b, k, w, h),
      SCons(b, t) => match i {
        Zero => BGetMutRead(&b, k, w, h),
        Succ(i') => SlotGetMutRead(&t, i', k, w, h),
      },
    }
  )

  def GetMutRead (hm : &HashMap) (k : Word) (w : Nat) (h : IsSome(Find(*hm, k))) :
      Id Opt (let q = GetMut(&*hm, k, h); let x = *q; *q := w; Some(x)) (let r = Find(*hm, k); let q = GetMut(&*hm, k, h); *q := w; r) := (
    match *hm {
      HM(n, len, slots) => SlotGetMutRead(&slots, Idx(k, n), k, w, h),
    }
  )
  -- Writing `w` through the borrow is inserting `k ↦ w`: the key is present, so the
  -- insert overwrites and adds nothing. Every other theorem about `GetMut` follows from
  -- the insert's.
  def BGetMutIsInsert (b : &Bucket) (k : Word) (w : Nat) (h : IsSome(BFind(*b, k))) :
      Id Unit (let q = BGetMut(&*b, k, h); *q := w) (BInsert(&*b, k, w); ()) by b := (
    match *b {
      BNil => match h {},
      BCons(k', v', t) => (
        let e = EqB(k', k);
        match e {
          false => BGetMutIsInsert(&t, k, w, h),
          true => refl,
        }
      ),
    }
  )

  def SlotGetMutIsInsert (s : &Slots) (i : Word) (k : Word) (w : Nat) (h : IsSome(BFind(Nth(*s, i), k))) :
      Id Unit (let b = Slot(&*s, i); let q = BGetMut(b, k, h); *q := w) (let b = Slot(&*s, i); BInsert(b, k, w); ()) by s := (
    match *s {
      SOne(b) => BGetMutIsInsert(&b, k, w, h),
      SCons(b, t) => match i {
        Zero => BGetMutIsInsert(&b, k, w, h),
        Succ(i') => SlotGetMutIsInsert(&t, i', k, w, h),
      },
    }
  )

  def GetMutIsInsert (hm : &HashMap) (k : Word) (w : Nat) (h : IsSome(Find(*hm, k))) :
      Id Unit (let q = GetMut(&*hm, k, h); *q := w) (InsertNoResize(&*hm, k, w)) := (
    match *hm {
      HM(n, len, slots) => (
        let p = SlotInsertAdded(&slots, Idx(k, n), k, w);
        let r = BFind(Nth(slots, Idx(k, n)), k);
        split BInsert {
          false => SlotGetMutIsInsert(&slots, Idx(k, n), k, w, h),
          true => match r {
            None => match h {},
            Some(_) => match p {},
          },
        }
      ),
    }
  )

  def GetMutFind (hm : &HashMap) (k : Word) (w : Nat) (h : IsSome(Find(*hm, k))) :
      Id Opt (let q = GetMut(&*hm, k, h); *q := w; Find(*hm, k)) (let q = GetMut(&*hm, k, h); *q := w; Some(w)) := (
    match *hm {
      HM(n, len, slots) => rewrite ← SlotGetMutIsInsert(&slots, Idx(k, n), k, w, h) in SlotInsertFind(&slots, Idx(k, n), k, w),
    }
  )

  def GetMutFindOther (hm : &HashMap) (k : Word) (w : Nat) (h : IsSome(Find(*hm, k))) (k2 : Word) (ne : Eq Bool (EqB(k, k2)) false) :
      Id Opt (let q = GetMut(&*hm, k, h); *q := w; Find(*hm, k2)) (let r = Find(*hm, k2); let q = GetMut(&*hm, k, h); *q := w; r) := (
    match *hm {
      HM(n, len, slots) => rewrite ← SlotGetMutIsInsert(&slots, Idx(k, n), k, w, h) in
        SlotInsertFindOther(&slots, Idx(k, n), Idx(k2, n), k, w, k2, ne),
    }
  )

  -- ## Get, through the borrow
  -- `Get` reads through a mutable borrow (Ochr has no shared borrows). When the lookup
  -- is stuck on an abstract bucket, closing it off leaves a sealed program in the bucket
  -- ("look `k` up in `u`, then give `u` back"), which is `u` only by a proof. These three
  -- lemmas are that proof: `Get` returns what `Find` returns, and leaves the map as it was.
  def BGetFind (b : &Bucket) (k : Word) : Id Opt (BGet(&*b, k)) (BFind(*b, k)) by b := (
    match *b {
      BNil => refl,
      BCons(k', v', t) => (
        let e = EqB(k', k);
        match e {
          false => BGetFind(&t, k),
          true => refl,
        }
      ),
    }
  )

  def SlotGetFind (s : &Slots) (i : Word) (k : Word) :
      Id Opt (let b = Slot(&*s, i); BGet(b, k)) (BFind(Nth(*s, i), k)) by s := (
    match *s {
      SOne(b) => BGetFind(&b, k),
      SCons(b, t) => match i {
        Zero => BGetFind(&b, k),
        Succ(i') => SlotGetFind(&t, i', k),
      },
    }
  )

  def GetFind (hm : &HashMap) (k : Word) : Id Opt (Get(&*hm, k)) (Find(*hm, k)) := (
    match *hm {
      HM(n, len, slots) => SlotGetFind(&slots, Idx(k, n), k),
    }
  )

  -- `ContainsKey` also reads through the borrow: it says whether `Find` finds the key.
  def Has (o : Opt) : Bool := (
    match o {
      None => false,
      Some(_) => true,
    }
  )

  def BContainsFind (b : &Bucket) (k : Word) : Id Bool (BContains(&*b, k)) (Has(BFind(*b, k))) by b := (
    match *b {
      BNil => refl,
      BCons(k', v', t) => (
        let e = EqB(k', k);
        match e {
          false => BContainsFind(&t, k),
          true => refl,
        }
      ),
    }
  )

  def SlotContainsFind (s : &Slots) (i : Word) (k : Word) :
      Id Bool (let b = Slot(&*s, i); BContains(b, k)) (Has(BFind(Nth(*s, i), k))) by s := (
    match *s {
      SOne(b) => BContainsFind(&b, k),
      SCons(b, t) => match i {
        Zero => BContainsFind(&b, k),
        Succ(i') => SlotContainsFind(&t, i', k),
      },
    }
  )

  def ContainsFind (hm : &HashMap) (k : Word) : Id Bool (ContainsKey(&*hm, k)) (Has(Find(*hm, k))) := (
    match *hm {
      HM(n, len, slots) => SlotContainsFind(&slots, Idx(k, n), k),
    }
  )

  -- ## New and Clear
  -- Every bucket of a fresh table is empty, so no key is found.
  def NthEmpty (n : Word) (i : Word) : Id Bucket BNil (Nth(EmptySlots(n), i)) by n := (
    match n {
      Zero => refl,
      Succ(m) => match i {
        Zero => refl,
        Succ(i') => NthEmpty(m, i'),
      },
    }
  )

  def NewFind (n : Word) (k : Word) : Id Opt (Find(New(n), k)) None := rewrite NthEmpty(n, Idx(k, n)) in refl

  def ClearFind (hm : &HashMap) (k : Word) : Id Opt (Clear(&*hm); Find(*hm, k)) (Clear(&*hm); None) := (
    match *hm {
      HM(n, len, slots) => NewFind(n, k),
    }
  )
}

-- the exact number of declarations (a truncated file changes it)
#guard HashMapLookup.decls.length == 46

/-! ## The length

`Len` is the map's `len` field. After an insert it grows by one exactly when the key was
absent, and after a remove it shrinks by one exactly when the key was present; with the
invariant `len = Count(slots)` (the number of entries), each operation preserves it. -/

ochr HashMapLength uses Std, HashMap, HashMapLookup {
  -- Sizes, and the two ways a length changes.
  def BLen (b : Bucket) : Word by b := (
    match b {
      BNil => Zero,
      BCons(k, v, t) => Succ(BLen(t)),
    }
  )

  def Count (s : Slots) : Word by s := (
    match s {
      SOne(b) => BLen(b),
      SCons(b, t) => WAdd(BLen(b), Count(t)),
    }
  )

  def IfNew (r : Opt) (l : Word) : Word := (
    match r {
      None => Succ(l),
      Some(_) => l,
    }
  )

  def IfFound (r : Opt) (l : Word) : Word := (
    match r {
      None => l,
      Some(_) => Succ(l),
    }
  )

  -- ## The len field

  -- Split on whether the entry was added and on the earlier lookup; where they disagree,
  -- the lemma's type is `true = false` or `false = true`, which is `False`.
  def InsertLen (hm : &HashMap) (k : Word) (v : Nat) :
      Id Word (InsertNoResize(&*hm, k, v); Len(*hm))
             (let l = Len(*hm); let r = Find(*hm, k); InsertNoResize(&*hm, k, v); IfNew(r, l)) := (
    match *hm {
      HM(n, len, slots) => (
        let p = SlotInsertAdded(&slots, Idx(k, n), k, v);
        split BInsert {
          false => split BGet {
            None => match p {},
            Some(_) => refl,
          },
          true => split BGet {
            None => refl,
            Some(_) => match p {},
          },
        }
      ),
    }
  )
  -- ## The invariant len = Count(slots), for insert
  -- `x + (y + 1) = (x + y) + 1`, by recursion on `x`.
  def WAddS (x : Word) (y : Word) : Eq Word (WAdd(x, Succ(y))) (Succ(WAdd(x, y))) by x := (
    match x {
      Zero => refl,
      Succ(x') => WAddS(x', y),
    }
  )

  -- A bucket grows by one exactly when the key was absent. `Succ(a) = Succ(b)` is
  -- `a = b`, so each arm is the induction hypothesis as it stands.
  def BInsertCount (b : &Bucket) (k : Word) (v : Nat) :
      Id Word (let r = BFind(*b, k); let l = BLen(*b); BInsert(&*b, k, v); IfNew(r, l))
             (BInsert(&*b, k, v); BLen(*b)) by b := (
    match *b {
      BNil => refl,
      BCons(k', v', t) => (
        let e = EqB(k', k);
        match e {
          false => split BGet in BInsertCount(&t, k, v),
          true => refl,
        }
      ),
    }
  )

  -- Lifted to the slots, where `Count` adds the bucket lengths: each arm rewrites once
  -- under `Add`.
  def SlotInsertCount (s : &Slots) (i : Word) (k : Word) (v : Nat) :
      Id Word (let r = BFind(Nth(*s, i), k); let c = Count(*s); let b = Slot(&*s, i); BInsert(b, k, v); IfNew(r, c))
             (let b = Slot(&*s, i); BInsert(b, k, v); Count(*s)) by s := (
    match *s {
      SOne(b) => BInsertCount(&b, k, v),
      SCons(b, t) => match i {
        Zero => split BGet in rewrite BInsertCount(&b, k, v) in refl,
        Succ(i') => split BGet {
          None => rewrite SlotInsertCount(&t, i', k, v) in rewrite WAddS(BLen(b), Count(t)) in refl,
          Some(_) => rewrite SlotInsertCount(&t, i', k, v) in refl,
        },
      },
    }
  )

  -- The map: split on the added flag and on the earlier lookup (the mixed arms contradict
  -- `SlotInsertAdded`), then one rewrite against the hypothesis.
  def InsertCount (hm : &HashMap) (k : Word) (v : Nat) (h : Eq Word (Len(*hm)) (Count(Buckets(*hm)))) :
      Id Word (InsertNoResize(&*hm, k, v); Len(*hm)) (InsertNoResize(&*hm, k, v); Count(Buckets(*hm))) := (
    match *hm {
      HM(n, len, slots) => (
        let p = SlotInsertAdded(&slots, Idx(k, n), k, v);
        let r = BFind(Nth(slots, Idx(k, n)), k);
        split BInsert {
          false => match r {
            None => match p {},
            Some(_) => rewrite SlotInsertCount(&slots, Idx(k, n), k, v) in h,
          },
          true => match r {
            None => rewrite SlotInsertCount(&slots, Idx(k, n), k, v) in h,
            Some(_) => match p {},
          },
        }
      ),
    }
  )

  -- The hypothesis is needed.
  reject def InsertCountNoHyp (hm : &HashMap) (k : Word) (v : Nat) :
      Id Word (InsertNoResize(&*hm, k, v); Len(*hm)) (InsertNoResize(&*hm, k, v); Count(Buckets(*hm))) := (
    match *hm {
      HM(n, len, slots) => SlotInsertCount(&slots, Idx(k, n), k, v),
    }
  )
  -- ## Remove
  -- The len field shrinks by one exactly when the key was found (the code's `Pred`).
  def Shrink (r : Opt) (l : Word) : Word := (
    match r {
      None => l,
      Some(_) => Pred(l),
    }
  )

  def RemoveLen (hm : &HashMap) (k : Word) :
      Id Word (Remove(&*hm, k); Len(*hm)) (let l = Len(*hm); let r = Find(*hm, k); Remove(&*hm, k); Shrink(r, l)) := (
    match *hm {
      HM(n, len, slots) => (
        let p = SlotRemoveResult(&slots, Idx(k, n), k);
        split BRemove {
          None => split BGet {
            None => refl,
            Some(_) => match p {},
          },
          Some(_) => split BGet {
            None => match p {},
            Some(_) => refl,
          },
        }
      ),
    }
  )

  -- The count before a remove is the count after, plus one if the key was found.
  def BRemoveCount (b : &Bucket) (k : Word) :
      Id Word (let l = BLen(*b); BRemove(&*b, k); l) (let r = BFind(*b, k); BRemove(&*b, k); IfFound(r, BLen(*b))) by b := (
    match *b {
      BNil => refl,
      BCons(k', v', t) => (
        let e = EqB(k', k);
        match e {
          false => split BGet in BRemoveCount(&t, k),
          true => refl,
        }
      ),
    }
  )

  def SlotRemoveCount (s : &Slots) (i : Word) (k : Word) :
      Id Word (let c = Count(*s); let b = Slot(&*s, i); BRemove(b, k); c)
             (let r = BFind(Nth(*s, i), k); let b = Slot(&*s, i); BRemove(b, k); IfFound(r, Count(*s))) by s := (
    match *s {
      SOne(b) => BRemoveCount(&b, k),
      SCons(b, t) => match i {
        Zero => split BGet {
          None => rewrite BRemoveCount(&b, k) in refl,
          Some(_) => rewrite ← BRemoveCount(&b, k) in refl,
        },
        Succ(i') => split BGet {
          None => rewrite SlotRemoveCount(&t, i', k) in refl,
          Some(_) => (
            let ct = t;
            let rb = Slot(&ct, i');
            BRemove(rb, k);
            rewrite ← SlotRemoveCount(&t, i', k) in WAddS(BLen(b), Count(ct))
          ),
        },
      },
    }
  )

  def RemoveCount (hm : &HashMap) (k : Word) (h : Eq Word (Len(*hm)) (Count(Buckets(*hm)))) :
      Id Word (Remove(&*hm, k); Len(*hm)) (Remove(&*hm, k); Count(Buckets(*hm))) := (
    match *hm {
      HM(n, len, slots) => (
        let p = SlotRemoveResult(&slots, Idx(k, n), k);
        let r = BFind(Nth(slots, Idx(k, n)), k);
        split BRemove {
          None => match r {
            None => rewrite SlotRemoveCount(&slots, Idx(k, n), k) in h,
            Some(_) => match p {},
          },
          Some(_) => match r {
            None => match p {},
            Some(_) => rewrite ← h in rewrite ← SlotRemoveCount(&slots, Idx(k, n), k) in refl,
          },
        }
      ),
    }
  )

  -- ## New and Clear
  def EmptyCount (n : Word) : Eq Word (Count(EmptySlots(n))) Zero by n := (
    match n {
      Zero => refl,
      Succ(m) => EmptyCount(m),
    }
  )

  def NewCount (n : Word) : Eq Word (Len(New(n))) (Count(Buckets(New(n)))) := rewrite ← EmptyCount(n) in refl

  def ClearCount (hm : &HashMap) : Id Word (Clear(&*hm); Len(*hm)) (Clear(&*hm); Count(Buckets(*hm))) := (
    match *hm {
      HM(n, len, slots) => NewCount(n),
    }
  )
  -- ## GetMut
  -- Writing through the borrow leaves the length as it was.
  def GetMutLen (hm : &HashMap) (k : Word) (w : Nat) (h : IsSome(Find(*hm, k))) :
      Id Word (let q = GetMut(&*hm, k, h); *q := w; Len(*hm)) (let l = Len(*hm); let q = GetMut(&*hm, k, h); *q := w; l) := (
    match *hm {
      HM(n, len, slots) => refl,
    }
  )

}

-- the exact number of declarations (a truncated file changes it)
#guard HashMapLength.decls.length == 19

/-! ## The invariant, and resizing

The invariant (Aeneas's `hash_map_t_inv`, less its load-factor and overflow clauses): the
length counts the entries, the keys of each bucket are distinct, and every key lies only in
its own bucket. The last is a statement about every key, `Π(k : Word). OnlyIn(…)`, proved
for each key by a function of `k`. Every operation keeps the invariant, stated as "run the
operation on a copy, then the invariant holds of the copy". Resizing moves every entry with
`InsertNoResize`, so it keeps every lookup; with the invariant, the insert with resizing
behaves like the insert without. -/

ochr HashMapResize uses Std, HashMap, HashMapLookup, HashMapLength {
  -- ## Helpers
  def EqBSymm (a : Word) (b : Word) (h : Eq Bool (EqB(a, b)) true) : Eq Bool (EqB(b, a)) true := (
    rewrite EqBSound(a, b, h) in EqBRefl(a)
  )

  def NeqFlip (a : Word) (b : Word) (h : Eq Bool (EqB(a, b)) false) : Eq Bool (EqB(b, a)) false := (
    let e = EqB(b, a);
    match e {
      false => refl,
      true => (
        let p = EqBSymm(b, a, refl);
        let e2 = EqB(a, b);
        match e2 {
          false => match p {},
          true => match h {},
        }
      ),
    }
  )

  -- ## Keys stay distinct
  def BInsertUnique (b : Bucket) (k : Word) (v : Nat) (h : Unique(b)) : (let c = b; BInsert(&c, k, v); Unique(c)) by b := (
    match b {
      BNil => ⟨refl, refl⟩,
      BCons(k', v', t) => (
        let ⟨absent, rest⟩ = h;
        let e = EqB(k', k);
        match e {
          false => ⟨rewrite ← BInsertFindOther(&t, k, v, k', NeqFlip(k', k, refl)) in absent, BInsertUnique(t, k, v, rest)⟩,
          true => ⟨absent, rest⟩,
        }
      ),
    }
  )

  def SlotInsertUnique (s : Slots) (i : Word) (k : Word) (v : Nat) (h : AllUnique(s)) :
      (let c = s; let b = Slot(&c, i); BInsert(b, k, v); AllUnique(c)) by s := (
    match s {
      SOne(b) => BInsertUnique(b, k, v, h),
      SCons(b, t) => (
        let ⟨hb, ht⟩ = h;
        match i {
          Zero => ⟨BInsertUnique(b, k, v, hb), ht⟩,
          Succ(i') => ⟨hb, SlotInsertUnique(t, i', k, v, ht)⟩,
        }
      ),
    }
  )

  def BRemoveUnique (b : Bucket) (k : Word) (h : Unique(b)) : (let c = b; BRemove(&c, k); Unique(c)) by b := (
    match b {
      BNil => refl,
      BCons(k', v', t) => (
        let ⟨absent, rest⟩ = h;
        let e = EqB(k', k);
        match e {
          false => ⟨rewrite ← BRemoveFindOther(&t, k, k', NeqFlip(k', k, refl)) in absent, BRemoveUnique(t, k, rest)⟩,
          true => rest,
        }
      ),
    }
  )

  def SlotRemoveUnique (s : Slots) (i : Word) (k : Word) (h : AllUnique(s)) :
      (let c = s; let b = Slot(&c, i); BRemove(b, k); AllUnique(c)) by s := (
    match s {
      SOne(b) => BRemoveUnique(b, k, h),
      SCons(b, t) => (
        let ⟨hb, ht⟩ = h;
        match i {
          Zero => ⟨BRemoveUnique(b, k, hb), ht⟩,
          Succ(i') => ⟨hb, SlotRemoveUnique(t, i', k, ht)⟩,
        }
      ),
    }
  )

  -- ## Keys stay in their bucket
  def Nowhere (s : Slots) (k : Word) : Prop by s := (
    match s {
      SOne(b) => Eq Opt (BFind(b, k)) None,
      SCons(b, t) => Eq Opt (BFind(b, k)) None ∧ Nowhere(t, k),
    }
  )

  def OnlyIn (s : Slots) (d : Word) (k : Word) : Prop by s := (
    match s {
      SOne(b) => ⊤,
      SCons(b, t) => match d {
        Zero => Nowhere(t, k),
        Succ(d') => Eq Opt (BFind(b, k)) None ∧ OnlyIn(t, d', k),
      },
    }
  )

  def Placed (s : Slots) (n : Word) : Prop := Π(k : Word). OnlyIn(s, Idx(k, n), k)

  -- Inserting `k` keeps another key absent where it was absent.
  def BInsertAbsent (b : Bucket) (k : Word) (v : Nat) (k2 : Word) (ne : Eq Bool (EqB(k, k2)) false)
      (h : Eq Opt (BFind(b, k2)) None) : (let c = b; BInsert(&c, k, v); Eq Opt (BFind(c, k2)) None) := (
    rewrite ← BInsertFindOther(&b, k, v, k2, ne) in h
  )

  def NowhereInsert (s : Slots) (i : Word) (k : Word) (v : Nat) (k2 : Word) (ne : Eq Bool (EqB(k, k2)) false)
      (h : Nowhere(s, k2)) : (let c = s; let b = Slot(&c, i); BInsert(b, k, v); Nowhere(c, k2)) by s := (
    match s {
      SOne(b) => BInsertAbsent(b, k, v, k2, ne, h),
      SCons(b, t) => (
        let ⟨hb, ht⟩ = h;
        match i {
          Zero => ⟨BInsertAbsent(b, k, v, k2, ne, hb), ht⟩,
          Succ(i') => ⟨hb, NowhereInsert(t, i', k, v, k2, ne, ht)⟩,
        }
      ),
    }
  )

  def OnlyInOther (s : Slots) (i : Word) (d : Word) (k : Word) (v : Nat) (k2 : Word) (ne : Eq Bool (EqB(k, k2)) false)
      (h : OnlyIn(s, d, k2)) : (let c = s; let b = Slot(&c, i); BInsert(b, k, v); OnlyIn(c, d, k2)) by s := (
    match s {
      SOne(b) => refl,
      SCons(b, t) => match d {
        Zero => match i {
          Zero => h,
          Succ(i') => NowhereInsert(t, i', k, v, k2, ne, h),
        },
        Succ(d') => (
          let ⟨hb, ht⟩ = h;
          match i {
            Zero => ⟨BInsertAbsent(b, k, v, k2, ne, hb), ht⟩,
            Succ(i') => ⟨hb, OnlyInOther(t, i', d', k, v, k2, ne, ht)⟩,
          }
        ),
      },
    }
  )

  def OnlyInSame (s : Slots) (i : Word) (k : Word) (v : Nat) (h : OnlyIn(s, i, k)) :
      (let c = s; let b = Slot(&c, i); BInsert(b, k, v); OnlyIn(c, i, k)) by s := (
    match s {
      SOne(b) => refl,
      SCons(b, t) => match i {
        Zero => h,
        Succ(i') => (
          let ⟨hb, ht⟩ = h;
          ⟨hb, OnlyInSame(t, i', k, v, ht)⟩
        ),
      },
    }
  )

  -- For every key `k2`: if it is `k`, it went into its own bucket; if not, it did not move.
  def SlotInsertPlaced (s : Slots) (n : Word) (k : Word) (v : Nat) (h : Placed(s, n)) :
      (let c = s; let b = Slot(&c, Idx(k, n)); BInsert(b, k, v); Placed(c, n)) := (
    let c = s;
    let b = Slot(&c, Idx(k, n));
    BInsert(b, k, v);
    λ(k2 : Word) : OnlyIn(c, Idx(k2, n), k2) => (
      let e = EqB(k, k2);
      match e {
        false => OnlyInOther(s, Idx(k, n), Idx(k2, n), k, v, k2, refl, h(k2)),
        true => rewrite EqBSound(k, k2, refl) in OnlyInSame(s, Idx(k, n), k, v, h(k)),
      }
    )
  )
  -- Removing never makes a key present.
  def BRemoveAbsent (b : Bucket) (k : Word) (k2 : Word) (h : Eq Opt (BFind(b, k2)) None) :
      (let c = b; BRemove(&c, k); Eq Opt (BFind(c, k2)) None) by b := (
    match b {
      BNil => refl,
      BCons(k', v', t) => (
        let e2 = EqB(k', k2);
        match e2 {
          false => (
            let e = EqB(k', k);
            match e {
              false => BRemoveAbsent(t, k, k2, h),
              true => h,
            }
          ),
          true => match h {},
        }
      ),
    }
  )

  def NowhereRemove (s : Slots) (i : Word) (k : Word) (k2 : Word) (h : Nowhere(s, k2)) :
      (let c = s; let b = Slot(&c, i); BRemove(b, k); Nowhere(c, k2)) by s := (
    match s {
      SOne(b) => BRemoveAbsent(b, k, k2, h),
      SCons(b, t) => (
        let ⟨hb, ht⟩ = h;
        match i {
          Zero => ⟨BRemoveAbsent(b, k, k2, hb), ht⟩,
          Succ(i') => ⟨hb, NowhereRemove(t, i', k, k2, ht)⟩,
        }
      ),
    }
  )

  def OnlyInRemove (s : Slots) (i : Word) (d : Word) (k : Word) (k2 : Word) (h : OnlyIn(s, d, k2)) :
      (let c = s; let b = Slot(&c, i); BRemove(b, k); OnlyIn(c, d, k2)) by s := (
    match s {
      SOne(b) => refl,
      SCons(b, t) => match d {
        Zero => match i {
          Zero => h,
          Succ(i') => NowhereRemove(t, i', k, k2, h),
        },
        Succ(d') => (
          let ⟨hb, ht⟩ = h;
          match i {
            Zero => ⟨BRemoveAbsent(b, k, k2, hb), ht⟩,
            Succ(i') => ⟨hb, OnlyInRemove(t, i', d', k, k2, ht)⟩,
          }
        ),
      },
    }
  )

  def SlotRemovePlaced (s : Slots) (n : Word) (k : Word) (h : Placed(s, n)) :
      (let c = s; let b = Slot(&c, Idx(k, n)); BRemove(b, k); Placed(c, n)) := (
    let c = s;
    let b = Slot(&c, Idx(k, n));
    BRemove(b, k);
    λ(k2 : Word) : OnlyIn(c, Idx(k2, n), k2) => OnlyInRemove(s, Idx(k, n), Idx(k2, n), k, k2, h(k2))
  )

  -- ## The invariant
  -- The length counts the entries, the keys of each bucket are distinct, and every key
  -- lies only in its own bucket (all three are Aeneas's `hash_map_t_inv`, less its load
  -- factor and overflow clauses).
  def Inv (m : HashMap) : Prop := (
    match m {
      HM(n, len, s) => Eq Word len (Count(s)) ∧ (AllUnique(s) ∧ Placed(s, n)),
    }
  )

  def NowhereEmpty (n : Word) (k : Word) : Nowhere(EmptySlots(n), k) by n := (
    match n {
      Zero => refl,
      Succ(m) => ⟨refl, NowhereEmpty(m, k)⟩,
    }
  )

  def OnlyInEmpty (n : Word) (d : Word) (k : Word) : OnlyIn(EmptySlots(n), d, k) by n := (
    match n {
      Zero => refl,
      Succ(m) => match d {
        Zero => NowhereEmpty(m, k),
        Succ(d') => ⟨refl, OnlyInEmpty(m, d', k)⟩,
      },
    }
  )

  def UniqueEmpty (n : Word) : AllUnique(EmptySlots(n)) by n := (
    match n {
      Zero => refl,
      Succ(m) => ⟨refl, UniqueEmpty(m)⟩,
    }
  )

  def NewInv (n : Word) : Inv(New(n)) := (
    ⟨NewCount(n), ⟨UniqueEmpty(n), λ(k : Word) : OnlyIn(EmptySlots(n), Idx(k, n), k) => OnlyInEmpty(n, Idx(k, n), k)⟩⟩
  )

  -- Each operation keeps it. Split on whether the bucket changed its size, as for the
  -- length theorems; the three parts are the lemmas above.
  def InsertInv (m : HashMap) (k : Word) (v : Nat) (h : Inv(m)) : (let c = m; InsertNoResize(&c, k, v); Inv(c)) := (
    match m {
      HM(n, len, s) => (
        let ⟨hl, hu, hp⟩ = h;
        let mc = m;
        split BInsert in ⟨InsertCount(&mc, k, v, hl), ⟨SlotInsertUnique(s, Idx(k, n), k, v, hu), SlotInsertPlaced(s, n, k, v, hp)⟩⟩
      ),
    }
  )

  def RemoveInv (m : HashMap) (k : Word) (h : Inv(m)) : (let c = m; Remove(&c, k); Inv(c)) := (
    match m {
      HM(n, len, s) => (
        let ⟨hl, hu, hp⟩ = h;
        let mc = m;
        split BRemove in ⟨RemoveCount(&mc, k, hl), ⟨SlotRemoveUnique(s, Idx(k, n), k, hu), SlotRemovePlaced(s, n, k, hp)⟩⟩
      ),
    }
  )

  def ClearInv (m : HashMap) : (let c = m; Clear(&c); Inv(c)) := (
    match m {
      HM(n, len, s) => NewInv(n),
    }
  )
  -- `GetMut` keeps the invariant, because writing through it is an insert (`GetMutIsInsert`).

  def GetMutInv (m : HashMap) (k : Word) (w : Nat) (h : IsSome(Find(m, k))) (hi : Inv(m)) :
      (let c = m; let q = GetMut(&c, k, h); *q := w; Inv(c)) := (
    match m {
      HM(n, len, s) => (
        let ⟨hl, hu, hp⟩ = hi;
        let r = BFind(Nth(s, Idx(k, n)), k);
        rewrite ← SlotGetMutIsInsert(&s, Idx(k, n), k, w, h) in match r {
          None => match h {},
          Some(_) => ⟨rewrite SlotInsertCount(&s, Idx(k, n), k, w) in hl,
                      ⟨SlotInsertUnique(s, Idx(k, n), k, w, hu), SlotInsertPlaced(s, n, k, w, hp)⟩⟩,
        }
      ),
    }
  )

  -- ## Resizing keeps the invariant
  -- Every entry is moved by `InsertNoResize`, which keeps the invariant, into a fresh
  -- table, which has it: so the result has it, whatever the old map was.
  def MoveBucketInv (b : Bucket) (m : HashMap) (h : Inv(m)) : (let c = m; MoveBucket(b, &c); Inv(c)) by b := (
    match b {
      BNil => h,
      BCons(k, v, t) => (
        let m2 = m;
        InsertNoResize(&m2, k, v);
        MoveBucketInv(t, m2, InsertInv(m, k, v, h))
      ),
    }
  )

  def MoveSlotsInv (s : Slots) (m : HashMap) (h : Inv(m)) : (let c = m; MoveSlots(s, &c); Inv(c)) by s := (
    match s {
      SOne(b) => MoveBucketInv(b, m, h),
      SCons(b, t) => (
        let m2 = m;
        MoveBucket(b, &m2);
        MoveSlotsInv(t, m2, MoveBucketInv(b, m, h))
      ),
    }
  )

  def ResizeInv (m : HashMap) : (let c = m; Resize(&c); Inv(c)) := (
    match m {
      HM(n, len, s) => MoveSlotsInv(s, New(Succ(WAdd(n, n))), NewInv(Succ(WAdd(n, n)))),
    }
  )

  -- ## Resizing keeps every lookup
  -- Re-inserting overwrites, so after moving a bucket (or all the slots) into a map, a
  -- key's lookup is its last occurrence in what was moved, or else what it was before.
  -- That needs no hypothesis. The invariant then says the last occurrence of `k` in the
  -- old slots is the one `Find` sees: `k` is only in its own bucket, and at most once.
  def OrElse (a : Opt) (b : Opt) : Opt := (
    match a {
      None => b,
      Some(x) => Some(x),
    }
  )

  def BFindLast (b : Bucket) (k : Word) : Opt by b := (
    match b {
      BNil => None,
      BCons(k', v', t) => (
        let e = EqB(k', k);
        match e {
          false => BFindLast(t, k),
          true => OrElse(BFindLast(t, k), Some(v')),
        }
      ),
    }
  )

  def SFindLast (s : Slots) (k : Word) : Opt by s := (
    match s {
      SOne(b) => BFindLast(b, k),
      SCons(b, t) => OrElse(SFindLast(t, k), BFindLast(b, k)),
    }
  )

  def MoveBucketFind (b : Bucket) (m : HashMap) (k : Word) :
      Id Opt (let c = m; MoveBucket(b, &c); Find(c, k)) (OrElse(BFindLast(b, k), Find(m, k))) by b := (
    match b {
      BNil => refl,
      BCons(k', v', t) => (
        let mc = m;
        let m2 = m;
        InsertNoResize(&m2, k', v');
        let e = EqB(k', k);
        match e {
          false => rewrite InsertFindOther(&mc, k', v', k, refl) in MoveBucketFind(t, m2, k),
          true => (
            let found : Eq Opt (Find(m2, k)) (Some(v')) = (rewrite EqBSound(k', k, refl) in InsertFind(&mc, k', v'));
            split BFindLast {
              None => rewrite found in MoveBucketFind(t, m2, k),
              Some(_) => MoveBucketFind(t, m2, k),
            }
          ),
        }
      ),
    }
  )

  def MoveSlotsFind (s : Slots) (m : HashMap) (k : Word) :
      Id Opt (let c = m; MoveSlots(s, &c); Find(c, k)) (OrElse(SFindLast(s, k), Find(m, k))) by s := (
    match s {
      SOne(b) => MoveBucketFind(b, m, k),
      SCons(b, t) => (
        let mb = m;
        MoveBucket(b, &mb);
        split SFindLast {
          None => rewrite MoveBucketFind(b, m, k) in MoveSlotsFind(t, mb, k),
          Some(_) => MoveSlotsFind(t, mb, k),
        }
      ),
    }
  )

  def BFindLastNone (b : Bucket) (k : Word) (h : Eq Opt (BFind(b, k)) None) : Eq Opt (BFindLast(b, k)) None by b := (
    match b {
      BNil => refl,
      BCons(k', v', t) => (
        let e = EqB(k', k);
        match e {
          false => BFindLastNone(t, k, h),
          true => match h {},
        }
      ),
    }
  )

  def BFindLastUnique (b : Bucket) (k : Word) (h : Unique(b)) : Eq Opt (BFindLast(b, k)) (BFind(b, k)) by b := (
    match b {
      BNil => refl,
      BCons(k', v', t) => (
        let ⟨absent, rest⟩ = h;
        let e = EqB(k', k);
        match e {
          false => BFindLastUnique(t, k, rest),
          true => (
            let none = BFindLastNone(t, k, rewrite EqBSound(k', k, refl) in absent);
            split BFindLast {
              None => refl,
              Some(_) => match none {},
            }
          ),
        }
      ),
    }
  )

  def NowhereLast (s : Slots) (k : Word) (h : Nowhere(s, k)) : Eq Opt (SFindLast(s, k)) None by s := (
    match s {
      SOne(b) => BFindLastNone(b, k, h),
      SCons(b, t) => (
        let ⟨hb, ht⟩ = h;
        let none = NowhereLast(t, k, ht);
        split SFindLast {
          None => BFindLastNone(b, k, hb),
          Some(_) => match none {},
        }
      ),
    }
  )

  def OnlyInLast (s : Slots) (d : Word) (k : Word) (h : OnlyIn(s, d, k)) (hu : AllUnique(s)) :
      Eq Opt (SFindLast(s, k)) (BFind(Nth(s, d), k)) by s := (
    match s {
      SOne(b) => BFindLastUnique(b, k, hu),
      SCons(b, t) => (
        let ⟨ub, ut⟩ = hu;
        match d {
          Zero => (
            let none = NowhereLast(t, k, h);
            split SFindLast {
              None => BFindLastUnique(b, k, ub),
              Some(_) => match none {},
            }
          ),
          Succ(d') => (
            let ⟨hb, ht⟩ = h;
            split SFindLast {
              None => rewrite ← BFindLastNone(b, k, hb) in OnlyInLast(t, d', k, ht, ut),
              Some(_) => OnlyInLast(t, d', k, ht, ut),
            }
          ),
        }
      ),
    }
  )

  -- Resizing keeps every lookup, given the invariant.
  def ResizeFind (m : HashMap) (k : Word) (h : Inv(m)) : Id Opt (let c = m; Resize(&c); Find(c, k)) (Find(m, k)) := (
    match m {
      HM(n, len, s) => (
        let ⟨hl, hu, hp⟩ = h;
        let r = SFindLast(s, k);
        match r {
          None => (
            rewrite OnlyInLast(s, Idx(k, n), k, hp(k), hu) in
            rewrite NewFind(Succ(WAdd(n, n)), k) in
            MoveSlotsFind(s, New(Succ(WAdd(n, n))), k)
          ),
          Some(_) => rewrite OnlyInLast(s, Idx(k, n), k, hp(k), hu) in MoveSlotsFind(s, New(Succ(WAdd(n, n))), k),
        }
      ),
    }
  )

  -- ## Resizing keeps the length
  -- Each entry moved is new to the target, so each insert adds one. That needs the keys
  -- of the old table to be distinct across buckets, which follows from placement.
  def WAddZero (x : Word) : Eq Word (WAdd(x, Zero)) x by x := (
    match x {
      Zero => refl,
      Succ(x') => WAddZero(x'),
    }
  )

  def WAddAssoc (x : Word) (y : Word) (z : Word) : Eq Word (WAdd(WAdd(x, y), z)) (WAdd(x, WAdd(y, z))) by x := (
    match x {
      Zero => refl,
      Succ(x') => WAddAssoc(x', y, z),
    }
  )

  -- The keys of `b` are absent from the map `m`.
  def Fresh (b : Bucket) (m : HashMap) : Prop by b := (
    match b {
      BNil => ⊤,
      BCons(k, v, t) => Eq Opt (Find(m, k)) None ∧ Fresh(t, m),
    }
  )

  def FreshInsert (t : Bucket) (m : HashMap) (k : Word) (v : Nat) (h : Fresh(t, m)) (a : Eq Opt (BFind(t, k)) None) :
      (let c = m; InsertNoResize(&c, k, v); Fresh(t, c)) by t := (
    match t {
      BNil => refl,
      BCons(k2, v2, t2) => (
        let ⟨f, ft⟩ = h;
        let e = EqB(k2, k);
        match e {
          false => (
            let mc = m;
            ⟨rewrite ← InsertFindOther(&mc, k, v, k2, NeqFlip(k2, k, refl)) in f, FreshInsert(t2, m, k, v, ft, a)⟩
          ),
          true => match a {},
        }
      ),
    }
  )

  -- Moving a bucket of fresh, distinct keys adds its length.
  def MoveBucketLen (b : Bucket) (m : HashMap) (hf : Fresh(b, m)) (hu : Unique(b)) :
      Id Word (let c = m; MoveBucket(b, &c); Len(c)) (WAdd(Len(m), BLen(b))) by b := (
    match b {
      BNil => rewrite ← WAddZero(Len(m)) in refl,
      BCons(k, v, t) => (
        let ⟨f, ft⟩ = hf;
        let ⟨a, ut⟩ = hu;
        let mc = m;
        let m2 = m;
        InsertNoResize(&m2, k, v);
        rewrite ← WAddS(Len(m), BLen(t)) in
        rewrite ← MoveBucketLen(t, m2, FreshInsert(t, m, k, v, ft, a), ut) in
        rewrite ← InsertLen(&mc, k, v) in
        rewrite ← f in refl
      ),
    }
  )

  -- Moving the slots.
  -- The keys of the slots are absent from `m`; the keys of `b'` are not in `b`; the
  -- buckets' keys are distinct, and apart from every later bucket's.
  def FreshS (s : Slots) (m : HashMap) : Prop by s := (
    match s {
      SOne(b) => Fresh(b, m),
      SCons(b, t) => Fresh(b, m) ∧ FreshS(t, m),
    }
  )

  def AbsentFrom (b' : Bucket) (b : Bucket) : Prop by b' := (
    match b' {
      BNil => ⊤,
      BCons(k, v, r) => Eq Opt (BFind(b, k)) None ∧ AbsentFrom(r, b),
    }
  )

  def Apart (t : Slots) (b : Bucket) : Prop by t := (
    match t {
      SOne(b') => AbsentFrom(b', b),
      SCons(b', t') => AbsentFrom(b', b) ∧ Apart(t', b),
    }
  )

  def GUnique (s : Slots) : Prop by s := (
    match s {
      SOne(b) => Unique(b),
      SCons(b, t) => Unique(b) ∧ (Apart(t, b) ∧ GUnique(t)),
    }
  )

  -- After moving `b`, keys that are not in `b` are still absent.
  def FreshMove (b' : Bucket) (b : Bucket) (m : HashMap) (hf : Fresh(b', m)) (ha : AbsentFrom(b', b)) :
      (let c = m; MoveBucket(b, &c); Fresh(b', c)) by b' := (
    match b' {
      BNil => refl,
      BCons(k, v, r) => (
        let ⟨f, fr⟩ = hf;
        let ⟨a, ar⟩ = ha;
        let none = BFindLastNone(b, k, a);
        let r0 = BFindLast(b, k);
        match r0 {
          None => ⟨rewrite ← MoveBucketFind(b, m, k) in f, FreshMove(r, b, m, fr, ar)⟩,
          Some(_) => match none {},
        }
      ),
    }
  )

  def FreshSMove (t : Slots) (b : Bucket) (m : HashMap) (hf : FreshS(t, m)) (ha : Apart(t, b)) :
      (let c = m; MoveBucket(b, &c); FreshS(t, c)) by t := (
    match t {
      SOne(b') => FreshMove(b', b, m, hf, ha),
      SCons(b', t') => (
        let ⟨fb, ft⟩ = hf;
        let ⟨ab, ap⟩ = ha;
        ⟨FreshMove(b', b, m, fb, ab), FreshSMove(t', b, m, ft, ap)⟩
      ),
    }
  )

  def MoveSlotsLen (s : Slots) (m : HashMap) (hf : FreshS(s, m)) (hg : GUnique(s)) :
      Id Word (let c = m; MoveSlots(s, &c); Len(c)) (WAdd(Len(m), Count(s))) by s := (
    match s {
      SOne(b) => MoveBucketLen(b, m, hf, hg),
      SCons(b, t) => (
        let ⟨fb, ft⟩ = hf;
        let ⟨ub, ap, gt⟩ = hg;
        let mb = m;
        MoveBucket(b, &mb);
        rewrite WAddAssoc(Len(m), BLen(b), Count(t)) in
        rewrite MoveBucketLen(b, m, fb, ub) in
        MoveSlotsLen(t, mb, FreshSMove(t, b, m, ft, ap), gt)
      ),
    }
  )

  -- A new map has no keys.
  def FreshNew (b : Bucket) (n : Word) : Fresh(b, New(n)) by b := (
    match b {
      BNil => refl,
      BCons(k, v, t) => ⟨NewFind(n, k), FreshNew(t, n)⟩,
    }
  )

  def FreshSNew (s : Slots) (n : Word) : FreshS(s, New(n)) by s := (
    match s {
      SOne(b) => FreshNew(b, n),
      SCons(b, t) => ⟨FreshNew(b, n), FreshSNew(t, n)⟩,
    }
  )
  -- Placement gives global uniqueness.
  -- If every key lies only in its own bucket (`D(k)` says which, relative to `s`), keys in
  -- different buckets differ. For a key `k` of a later bucket: if `D(k)` points at the head
  -- bucket, `k` would be nowhere in the rest, where it is; otherwise the head lacks it. The
  -- rest's own `D` is one less.
  def NowhereOnlyIn (t : Slots) (d : Word) (k : Word) (h : Nowhere(t, k)) : OnlyIn(t, d, k) by t := (
    match t {
      SOne(b) => refl,
      SCons(b, t') => (
        let ⟨hb, ht⟩ = h;
        match d {
          Zero => ht,
          Succ(d') => ⟨hb, NowhereOnlyIn(t', d', k, ht)⟩,
        }
      ),
    }
  )

  -- The head key `k` of a bucket of `t` is not in `b`.
  def HeadApart (k : Word) (v : Nat) (r : Bucket) (b : Bucket) (t : Slots) (D : Π(k : Word). Word)
      (hp : Π(k : Word). OnlyIn(SCons(b, t), D(k), k))
      (hin : Π(k2 : Word) (nw : Nowhere(t, k2)). Eq Opt (BFind(BCons(k, v, r), k2)) None) : Eq Opt (BFind(b, k)) None := (
    let dk = D(k);
    let p = hp(k);
    match dk {
      Zero => (
        let f = hin(k, p);
        let e = EqB(k, k);
        match e {
          false => (
            let q = EqBRefl(k);
            match q {}
          ),
          true => match f {},
        }
      ),
      Succ(_) => (
        let ⟨a, rest⟩ = p;
        a
      ),
    }
  )

  -- `cur` is (a suffix of) a bucket of `t`: a key nowhere in `t` is not in `cur`.
  def AbsentFromOf (cur : Bucket) (b : Bucket) (t : Slots) (D : Π(k : Word). Word)
      (hp : Π(k : Word). OnlyIn(SCons(b, t), D(k), k))
      (hin : Π(k : Word) (nw : Nowhere(t, k)). Eq Opt (BFind(cur, k)) None) : AbsentFrom(cur, b) by cur := (
    match cur {
      BNil => refl,
      BCons(k, v, r) => ⟨HeadApart(k, v, r, b, t, D, hp, hin),
        AbsentFromOf(r, b, t, D, hp, λ(k2 : Word) (nw : Nowhere(t, k2)) : Eq Opt (BFind(r, k2)) None => (
          let f = hin(k2, nw);
          let e = EqB(k, k2);
          match e {
            false => f,
            true => match f {},
          }
        ))⟩,
    }
  )
  -- `u` is a suffix of `t`: every bucket of it is apart from `b`.
  def ApartOfGo (u : Slots) (b : Bucket) (t : Slots) (D : Π(k : Word). Word)
      (hp : Π(k : Word). OnlyIn(SCons(b, t), D(k), k))
      (hu : Π(k : Word) (nw : Nowhere(t, k)). Nowhere(u, k)) : Apart(u, b) by u := (
    match u {
      SOne(b') => AbsentFromOf(b', b, t, D, hp, hu),
      SCons(b', u') => ⟨
        AbsentFromOf(b', b, t, D, hp, λ(k : Word) (nw : Nowhere(t, k)) : Eq Opt (BFind(b', k)) None => (
          let ⟨x, y⟩ = hu(k, nw);
          x
        )),
        ApartOfGo(u', b, t, D, hp, λ(k : Word) (nw : Nowhere(t, k)) : Nowhere(u', k) => (
          let ⟨x, y⟩ = hu(k, nw);
          y
        ))⟩,
    }
  )

  def TailOnlyIn (b : Bucket) (t : Slots) (d : Word) (k : Word) (h : OnlyIn(SCons(b, t), d, k)) : OnlyIn(t, Pred(d), k) := (
    match d {
      Zero => NowhereOnlyIn(t, Zero, k, h),
      Succ(_) => (
        let ⟨x, y⟩ = h;
        y
      ),
    }
  )

  def GUniqueOf (s : Slots) (D : Π(k : Word). Word) (hp : Π(k : Word). OnlyIn(s, D(k), k)) (hu : AllUnique(s)) : GUnique(s) by s := (
    match s {
      SOne(b) => hu,
      SCons(b, t) => (
        let ⟨ub, ut⟩ = hu;
        ⟨ub, ⟨
          ApartOfGo(t, b, t, D, hp, λ(k : Word) (nw : Nowhere(t, k)) : Nowhere(t, k) => nw),
          GUniqueOf(t, λ(k : Word) : Word => Pred(D(k)), λ(k : Word) : OnlyIn(t, Pred(D(k)), k) => TailOnlyIn(b, t, D(k), k, hp(k)), ut)⟩⟩
      ),
    }
  )

  -- Resizing keeps the length, given the invariant.
  def ResizeLen (m : HashMap) (h : Inv(m)) : Id Word (let c = m; Resize(&c); Len(c)) (Len(m)) := (
    match m {
      HM(n, len, s) => (
        let ⟨hl, hu, hp⟩ = h;
        rewrite ← hl in
        MoveSlotsLen(s, New(Succ(WAdd(n, n))), FreshSNew(s, Succ(WAdd(n, n))), GUniqueOf(s, λ(k : Word) : Word => Idx(k, n), hp, hu))
      ),
    }
  )

  -- ## Insert, with the resize
  -- Split on whether the entry was added and on whether the table is then full. When it
  -- is, the resize keeps the invariant, every lookup and the length, the last two under
  -- the invariant, which `InsertInv` gives for the map before the resize. The load factor is
  -- last.
  def InsertFindR (m : HashMap) (k : Word) (v : Nat) (h : Inv(m)) :
      Id Opt (let c = m; Insert(&c, k, v); Find(c, k)) (Some(v)) := (
    match m {
      HM(n, len, s) => (
        let mc = m;
        let m2 = m;
        InsertNoResize(&m2, k, v);
        split BInsert in split Lt {
          false => InsertFind(&mc, k, v),
          true => rewrite ← ResizeFind(m2, k, InsertInv(m, k, v, h)) in InsertFind(&mc, k, v),
        }
      ),
    }
  )

  def InsertFindOtherR (m : HashMap) (k : Word) (v : Nat) (k2 : Word) (ne : Eq Bool (EqB(k, k2)) false) (h : Inv(m)) :
      Id Opt (let c = m; Insert(&c, k, v); Find(c, k2)) (Find(m, k2)) := (
    match m {
      HM(n, len, s) => (
        let mc = m;
        let m2 = m;
        InsertNoResize(&m2, k, v);
        split BInsert in split Lt {
          false => InsertFindOther(&mc, k, v, k2, ne),
          true => rewrite ← ResizeFind(m2, k2, InsertInv(m, k, v, h)) in InsertFindOther(&mc, k, v, k2, ne),
        }
      ),
    }
  )

  -- The invariant.
  def InsertInvR (m : HashMap) (k : Word) (v : Nat) (h : Inv(m)) : (let c = m; Insert(&c, k, v); Inv(c)) := (
    match m {
      HM(n, len, s) => (
        let m2 = m;
        InsertNoResize(&m2, k, v);
        split BInsert in split Lt {
          false => InsertInv(m, k, v, h),
          true => ResizeInv(m2),
        }
      ),
    }
  )

  -- The length grows by one exactly when the key was absent.
  def InsertLenR (m : HashMap) (k : Word) (v : Nat) (h : Inv(m)) :
      Id Word (let c = m; Insert(&c, k, v); Len(c)) (IfNew(Find(m, k), Len(m))) := (
    match m {
      HM(n, len, s) => (
        let mc = m;
        let m2 = m;
        InsertNoResize(&m2, k, v);
        split BInsert in split Lt {
          false => InsertLen(&mc, k, v),
          true => rewrite ← ResizeLen(m2, InsertInv(m, k, v, h)) in InsertLen(&mc, k, v),
        }
      ),
    }
  )

  -- ## The load factor
  -- The entries do not outnumber the buckets: `len ≤ n`, with `n + 1` buckets. `Insert`
  -- keeps it by resizing (as Aeneas's `hash_map_not_overloaded_lem`, with a load factor
  -- of 1 rather than a configurable fraction).
  def NOf (m : HashMap) : Word := (
    match m {
      HM(n, len, s) => n,
    }
  )

  def NotOver (m : HashMap) : Prop := Eq Bool (Lt(NOf(m), Len(m))) false

  -- `a ≥ y` gives `a + 1 ≥ y`, `a + z ≥ y`, and `a ≥ y - 1`.
  def LtS (a : Word) (y : Word) (h : Eq Bool (Lt(a, y)) false) : Eq Bool (Lt(Succ(a), y)) false by a := (
    match a {
      Zero => match y {
        Zero => refl,
        Succ(_) => match h {},
      },
      Succ(a') => match y {
        Zero => refl,
        Succ(y') => LtS(a', y', h),
      },
    }
  )

  def LtAdd (x : Word) (y : Word) (z : Word) (h : Eq Bool (Lt(x, y)) false) : Eq Bool (Lt(WAdd(x, z), y)) false by x := (
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
        Succ(y') => LtAdd(x', y', z, h),
      },
    }
  )

  def LtPred (a : Word) (y : Word) (h : Eq Bool (Lt(a, y)) false) : Eq Bool (Lt(a, Pred(y))) false := (
    match y {
      Zero => h,
      Succ(y') => match a {
        Zero => match h {},
        Succ(a') => LtS(a', y', h),
      },
    }
  )

  -- Inserting and moving entries does not change the number of buckets; resizing sets it.
  def InsertN (m : HashMap) (k : Word) (v : Nat) : Id Word (let c = m; InsertNoResize(&c, k, v); NOf(c)) (NOf(m)) := (
    match m {
      HM(n, len, s) => split BInsert in refl,
    }
  )

  def MoveBucketN (b : Bucket) (m : HashMap) : Id Word (let c = m; MoveBucket(b, &c); NOf(c)) (NOf(m)) by b := (
    match b {
      BNil => refl,
      BCons(k, v, t) => (
        let m2 = m;
        InsertNoResize(&m2, k, v);
        rewrite ← MoveBucketN(t, m2) in InsertN(m, k, v)
      ),
    }
  )

  def MoveSlotsN (s : Slots) (m : HashMap) : Id Word (let c = m; MoveSlots(s, &c); NOf(c)) (NOf(m)) by s := (
    match s {
      SOne(b) => MoveBucketN(b, m),
      SCons(b, t) => (
        let mb = m;
        MoveBucket(b, &mb);
        rewrite ← MoveSlotsN(t, mb) in MoveBucketN(b, m)
      ),
    }
  )

  def ResizeN (m : HashMap) : Id Word (let c = m; Resize(&c); NOf(c)) (Succ(WAdd(NOf(m), NOf(m)))) := (
    match m {
      HM(n, len, s) => MoveSlotsN(s, New(Succ(WAdd(n, n)))),
    }
  )

  -- After a resize the bucket count is `2n + 2` and the length is unchanged, so the
  -- entries (at most `n + 1`) do not outnumber the buckets.
  def InsertNotOver (m : HashMap) (k : Word) (v : Nat) (h : Inv(m)) (ho : NotOver(m)) :
      (let c = m; Insert(&c, k, v); NotOver(c)) := (
    match m {
      HM(n, len, s) => (
        let m2 = m;
        InsertNoResize(&m2, k, v);
        split BInsert {
          false => split Lt {
            false => refl,
            true => match ho {},
          },
          true => split Lt {
            false => refl,
            true => rewrite ← ResizeN(m2) in rewrite ← ResizeLen(m2, InsertInv(m, k, v, h)) in LtAdd(n, len, n, ho),
          },
        }
      ),
    }
  )

  def NewNotOver (n : Word) : NotOver(New(n)) := (
    match n {
      Zero => refl,
      Succ(_) => refl,
    }
  )

  def RemoveNotOver (m : HashMap) (k : Word) (ho : NotOver(m)) : (let c = m; Remove(&c, k); NotOver(c)) := (
    match m {
      HM(n, len, s) => split BRemove {
        None => ho,
        Some(_) => LtPred(n, len, ho),
      },
    }
  )
  def GetMutNotOver (m : HashMap) (k : Word) (w : Nat) (h : IsSome(Find(m, k))) (ho : NotOver(m)) :
      (let c = m; let q = GetMut(&c, k, h); *q := w; NotOver(c)) := (
    match m {
      HM(n, len, s) => ho,
    }
  )

  def ClearNotOver (m : HashMap) : (let c = m; Clear(&c); NotOver(c)) := (
    match m {
      HM(n, len, s) => NewNotOver(n),
    }
  )
}

-- the exact number of declarations (a truncated file changes it)
#guard HashMapResize.decls.length == 79
