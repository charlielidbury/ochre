import Ochr.Examples.«00Std»

/-! # 16. A verified hash map

The case study of `notes/hashmap-case-study.md`: the resizing hash map that Aeneas verifies
(ICFP 2022, §6), written once, in place, with its theorems stated and proved about that
program. There is no pure model and no refinement proof: where Aeneas states "after
`insert`, `find_s` of the key is the value" about a hand-written model `find_s`, here the
statement uses `Get` itself, run on a copy of the map (`Find`, as `Add` runs `AddM` on a
copy).

The table is a non-empty list of buckets (Ochr has no arrays yet), each bucket an
association list. `Slot(s, i)` returns a borrow of bucket `i`, as Rust's `&mut slots[i]`,
and saturates at the last bucket, so it needs no bounds proof. Keys and values are `Nat`
and the hash is the identity, as in Aeneas; `k mod (n + 1)` picks the bucket.

The file has four programs: `HashMap`, the implementation with concrete runs; `HashMapLookup`,
lookups after each operation; `HashMapLength`, the length field and the count of entries;
`HashMapResize`, the invariant, resizing, `Insert` with its resize, and the load factor. -/

open Ochr.Test

ochr HashMap uses Std {
  -- ## The data
  -- `n + 1` buckets, `len` entries; `Opt` is the result of a lookup.
  inductive Opt := None | Some(v : Nat)
  inductive Bucket := BNil | BCons(k : Nat, v : Nat, t : Bucket)
  inductive Slots := SOne(b : Bucket) | SCons(b : Bucket, t : Slots)
  inductive HashMap := HM(n : Nat, len : Nat, slots : Slots)

  -- ## Arithmetic
  -- Key comparison, and the bucket index `k mod (n + 1)`, by recursion on `k` with a
  -- running remainder.
  def EqB (a : Nat) (b : Nat) : Bool by a := (
    match a {
      Z => match b {
        Z => true,
        S _ => false,
      },
      S a' => match b {
        Z => false,
        S b' => EqB(a', b'),
      },
    }
  )

  def Lt (a : Nat) (b : Nat) : Bool by a := (
    match a {
      Z => match b {
        Z => false,
        S _ => true,
      },
      S a' => match b {
        Z => false,
        S b' => Lt(a', b'),
      },
    }
  )

  def ModGo (k : Nat) (n : Nat) (r : Nat) : Nat by k := (
    match k {
      Z => r,
      S k' => (
        let e = EqB(r, n);
        match e {
          false => ModGo(k', n, S r),
          true => ModGo(k', n, 0),
        }
      ),
    }
  )

  def Idx (k : Nat) (n : Nat) : Nat := ModGo(k, n, 0)

  def Pred (n : Nat) : Nat := (
    match n {
      Z => 0,
      S m => m,
    }
  )

  -- ## Buckets
  -- Look a key up, test for it, insert or overwrite it (`true` if a new entry was added),
  -- remove it (returning the removed value), and borrow its value.
  def BGet (b : &Bucket) (k : Nat) : Opt by b := (
    match *b {
      BNil => None,
      BCons(k', v', t) => (
        let e = EqB(k', k);
        match e {
          false => BGet(&t, k),
          true => Some(v'),
        }
      ),
    }
  )

  def BContains (b : &Bucket) (k : Nat) : Bool by b := (
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

  def BInsert (b : &Bucket) (k : Nat) (v : Nat) : Bool by b := (
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

  def BRemove (b : &Bucket) (k : Nat) : Opt by b := (
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
  def BFind (b : Bucket) (k : Nat) : Opt := BGet(&b, k)

  def IsSome (o : Opt) : Prop := (
    match o {
      None => False,
      Some(_) => ⊤,
    }
  )

  -- The borrow of a present key's value. The key is present, so the `BNil` arm cannot
  -- happen: there `h` is a proof of `IsSome(None)`, which is `False`.
  def BGetMut (b : &Bucket) (k : Nat) (h : IsSome(BFind(*b, k))) : &Nat by b := (
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
  def Slot (s : &Slots) (i : Nat) : &Bucket by s := (
    match *s {
      SOne(b) => &b,
      SCons(b, t) => match i {
        Z => &b,
        S i' => Slot(&t, i'),
      },
    }
  )

  def EmptySlots (n : Nat) : Slots by n := (
    match n {
      Z => SOne(BNil),
      S m => SCons(BNil, EmptySlots(m)),
    }
  )

  -- ## The map
  -- Every operation finds the key's bucket through `Slot` and works on it in place.
  def New (n : Nat) : HashMap := HM(n, 0, EmptySlots(n))

  def Get (hm : &HashMap) (k : Nat) : Opt := (
    match *hm {
      HM(n, len, slots) => (
        let b = Slot(&slots, Idx(k, n));
        BGet(b, k)
      ),
    }
  )

  def ContainsKey (hm : &HashMap) (k : Nat) : Bool := (
    match *hm {
      HM(n, len, slots) => (
        let b = Slot(&slots, Idx(k, n));
        BContains(b, k)
      ),
    }
  )

  def InsertNoResize (hm : &HashMap) (k : Nat) (v : Nat) : Unit := (
    match *hm {
      HM(n, len, slots) => (
        let b = Slot(&slots, Idx(k, n));
        let added = BInsert(b, k, v);
        match added {
          false => (),
          true => len := S len,
        }
      ),
    }
  )

  def Remove (hm : &HashMap) (k : Nat) : Opt := (
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
        len := 0;
        slots := EmptySlots(n)
      ),
    }
  )

  def Len (m : HashMap) : Nat := (
    match m {
      HM(n, len, s) => len,
    }
  )

  -- A lookup on a copy, for statements, and the borrow of a present key's value.
  def Find (m : HashMap) (k : Nat) : Opt := Get(&m, k)

  def GetMut (hm : &HashMap) (k : Nat) (h : IsSome(Find(*hm, k))) : &Nat := (
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
        *hm := New(S (Add(n, n)));
        MoveSlots(old, hm)
      ),
    }
  )

  def Insert (hm : &HashMap) (k : Nat) (v : Nat) : Unit := (
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
  -- Three inserts into a map with two buckets: the second reaches the load factor and
  -- resizes to four. Every key is found again, an absent one is not.
  def RunLayout : Id HashMap (
    let m = New(1);
    Insert(&m, 1, 10);
    Insert(&m, 2, 20);
    Insert(&m, 3, 30);
    m
  ) (HM(3, 3, SCons(BNil, SCons(BCons(1, 10, BNil), SCons(BCons(2, 20, BNil), SOne(BCons(3, 30, BNil))))))) := refl

  def RunGet : Id (Opt × Opt) (
    let m = New(1);
    Insert(&m, 1, 10);
    Insert(&m, 2, 20);
    Insert(&m, 3, 30);
    (Get(&m, 2), Get(&m, 5))
  ) (Some(20), None) := refl

  reject def RunGetWrong : Id Opt (
    let m = New(1);
    Insert(&m, 1, 10);
    Insert(&m, 2, 20);
    Get(&m, 1)
  ) (Some(20)) := refl

  def RunContains : Id (Bool × Bool) (
    let m = New(1);
    Insert(&m, 1, 10);
    Insert(&m, 2, 20);
    (ContainsKey(&m, 2), ContainsKey(&m, 3))
  ) (true, false) := refl

  -- Overwriting keeps the length; `5` collides with `1` in a map with four buckets.
  def RunOverwrite : Id (Nat × Opt) (
    let m = New(1);
    Insert(&m, 1, 10);
    Insert(&m, 2, 20);
    Insert(&m, 2, 25);
    (Len(m), Get(&m, 2))
  ) (2, Some(25)) := refl

  def RunCollide : Id HashMap (
    let m = New(3);
    Insert(&m, 1, 10);
    Insert(&m, 5, 50);
    m
  ) (HM(3, 2, SCons(BNil, SCons(BCons(1, 10, BCons(5, 50, BNil)), SCons(BNil, SOne(BNil)))))) := refl

  -- Remove returns the value it removed; removing an absent key does nothing.
  def RunRemove : Id (Opt × HashMap) (
    let m = New(3);
    Insert(&m, 1, 10);
    Insert(&m, 5, 50);
    let x = Remove(&m, 1);
    Remove(&m, 7);
    (x, m)
  ) (Some(10), HM(3, 1, SCons(BNil, SCons(BCons(5, 50, BNil), SCons(BNil, SOne(BNil)))))) := refl

  -- Write through the borrow of a present key. For an absent key the proof `refl` of
  -- `IsSome(Find(m, 5))` does not exist: the precondition computes to `False`.
  def RunGetMut : Id Opt (
    let m = New(3);
    Insert(&m, 1, 10);
    Insert(&m, 5, 50);
    let q = GetMut(&m, 5, refl);
    *q := 55;
    Get(&m, 5)
  ) (Some(55)) := refl

  reject def RunGetMutAbsent : Id Opt (
    let m = New(3);
    Insert(&m, 1, 10);
    let q = GetMut(&m, 5, refl);
    *q := 55;
    Get(&m, 5)
  ) (Some(55)) := refl

  -- Clear empties the map and keeps the buckets.
  def RunClear : Id HashMap (
    let m = New(1);
    Insert(&m, 1, 10);
    Clear(&m);
    m
  ) (New(1)) := refl
}

#eval IO.println (run "HashMap" HashMap).show

-- every verdict as expected, and the exact number of declarations (a truncated file changes it)
#guard (run "HashMap" HashMap).allAsExpected
#guard (run "HashMap" HashMap).count == 41

/-! ## Lookups after each operation

Each theorem says what `Find` returns after an operation, for the key it touched and for
any other key. The statements use the operations themselves: "after `InsertNoResize(hm, k,
v)`, `Find(*hm, k)` is `Some(v)`" is `Id Opt (InsertNoResize(&*hm, k, v); Find(*hm, k))
(InsertNoResize(&*hm, k, v); Some(v))`. Each is proved first for one bucket, by recursion on
the bucket, then lifted through `Slot` by recursion on the slots, then stated for the map. -/

ochr HashMapLookup uses Std, HashMap {
  -- ## Key comparison
  def EqBRefl (k : Nat) : Eq Bool (EqB(k, k)) true by k := (
    match k {
      Z => refl,
      S k' => EqBRefl(k'),
    }
  )

  -- Where the comparison says the keys are equal, they are. `S a = S b` is `a = b`
  -- (injectivity), so the recursive call proves the `S` case as it stands.
  def EqBSound (a : Nat) (b : Nat) (h : Eq Bool (EqB(a, b)) true) : Eq Nat a b by a := (
    match a {
      Z => match b {
        Z => refl,
        S _ => match h {},
      },
      S a' => match b {
        Z => match h {},
        S b' => EqBSound(a', b', h),
      },
    }
  )

  def EqBTrans (a : Nat) (b : Nat) (c : Nat) (h1 : Eq Bool (EqB(a, b)) true) (h2 : Eq Bool (EqB(a, c)) true) :
      Eq Bool (EqB(b, c)) true := (
    J(Nat, a, b, λ(z : Nat) : Prop => Eq Bool (EqB(z, c)) true, EqBSound(a, b, h1), h2)
  )

  -- A bucket key equal to both `k` and `k2` contradicts `k ≠ k2`.
  def EqBContra (a : Nat) (b : Nat) (c : Nat) (h1 : Eq Bool (EqB(a, b)) true) (h2 : Eq Bool (EqB(a, c)) true)
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
  def BInsertFind (b : &Bucket) (k : Nat) (v : Nat) :
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
  def BInsertFindOther (b : &Bucket) (k : Nat) (v : Nat) (k2 : Nat) (h : Eq Bool (EqB(k, k2)) false) :
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
  -- `Nth(s, i)` reads bucket `i` of a copy of the slots. Each bucket theorem is lifted by
  -- recursion on the slots, following `Slot`'s own recursion: the recursive call borrows
  -- the tail, so the untouched buckets stay where they are and need no argument.
  def Nth (s : Slots) (i : Nat) : Bucket := (
    let r = Slot(&s, i);
    *r
  )

  def SlotInsertFind (s : &Slots) (i : Nat) (k : Nat) (v : Nat) :
      Id Opt (let b = Slot(&*s, i); BInsert(b, k, v); BFind(Nth(*s, i), k))
             (let b = Slot(&*s, i); BInsert(b, k, v); Some(v)) by s := (
    match *s {
      SOne(b) => BInsertFind(&b, k, v),
      SCons(b, t) => match i {
        Z => BInsertFind(&b, k, v),
        S i' => SlotInsertFind(&t, i', k, v),
      },
    }
  )

  -- Writing bucket `i` and reading bucket `j`: the same bucket is the bucket theorem,
  -- different buckets do not interact.
  def SlotInsertFindOther (s : &Slots) (i : Nat) (j : Nat) (k : Nat) (v : Nat) (k2 : Nat)
      (h : Eq Bool (EqB(k, k2)) false) :
      Id Opt (let b = Slot(&*s, i); BInsert(b, k, v); BFind(Nth(*s, j), k2))
             (let r = BFind(Nth(*s, j), k2); let b = Slot(&*s, i); BInsert(b, k, v); r) by s := (
    match *s {
      SOne(b) => BInsertFindOther(&b, k, v, k2, h),
      SCons(b, t) => match i {
        Z => match j {
          Z => BInsertFindOther(&b, k, v, k2, h),
          S _ => refl,
        },
        S i' => match j {
          Z => refl,
          S j' => SlotInsertFindOther(&t, i', j', k, v, k2, h),
        },
      },
    }
  )

  -- ## Insert, in the map
  -- `InsertNoResize` updates the length according to whether the bucket insert added an
  -- entry. That result is a sealed program, so the proof reproduces it on a copy of the
  -- slots and splits on it; in each arm the map computes, and the slot theorem applies.
  def InsertFind (hm : &HashMap) (k : Nat) (v : Nat) :
      Id Opt (InsertNoResize(&*hm, k, v); Find(*hm, k)) (InsertNoResize(&*hm, k, v); Some(v)) := (
    match *hm {
      HM(n, len, slots) => (
        let c = slots;
        let b = Slot(&c, Idx(k, n));
        let added = BInsert(b, k, v);
        match added {
          false => SlotInsertFind(&slots, Idx(k, n), k, v),
          true => SlotInsertFind(&slots, Idx(k, n), k, v),
        }
      ),
    }
  )

  def InsertFindOther (hm : &HashMap) (k : Nat) (v : Nat) (k2 : Nat) (h : Eq Bool (EqB(k, k2)) false) :
      Id Opt (InsertNoResize(&*hm, k, v); Find(*hm, k2)) (let r = Find(*hm, k2); InsertNoResize(&*hm, k, v); r) := (
    match *hm {
      HM(n, len, slots) => (
        let c = slots;
        let b = Slot(&c, Idx(k, n));
        let added = BInsert(b, k, v);
        match added {
          false => SlotInsertFindOther(&slots, Idx(k, n), Idx(k2, n), k, v, k2, h),
          true => SlotInsertFindOther(&slots, Idx(k, n), Idx(k2, n), k, v, k2, h),
        }
      ),
    }
  )
  -- Without the split the goal is stuck on the sealed `InsertNoResize` and does not meet
  -- the slot theorem's statement.
  reject def InsertFindNoSplit (hm : &HashMap) (k : Nat) (v : Nat) :
      Id Opt (InsertNoResize(&*hm, k, v); Find(*hm, k)) (InsertNoResize(&*hm, k, v); Some(v)) := (
    match *hm {
      HM(n, len, slots) => SlotInsertFind(&slots, Idx(k, n), k, v),
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
  def BRemoveResult (b : &Bucket) (k : Nat) :
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
  -- first `k` is removed, the rest of the bucket does not hold `k'`, which is `k`: `J`
  -- carries that along `k' = k`. (Its motive is a type, which may not capture the borrow
  -- `b` that `t` lies under, so it reads a copy of `t`.)
  def BRemoveFind (b : &Bucket) (k : Nat) (h : Unique(*b)) :
      Id Opt (BRemove(&*b, k); BFind(*b, k)) (BRemove(&*b, k); None) by b := (
    match *b {
      BNil => refl,
      BCons(k', v', t) => (
        let e = EqB(k', k);
        match h {
          Intro(absent, rest) => match e {
            false => BRemoveFind(&t, k, rest),
            true => (
              let c = t;
              J(Nat, k', k, λ(z : Nat) : Prop => Eq Opt (BFind(c, z)) None, EqBSound(k', k, refl), absent)
            ),
          },
        }
      ),
    }
  )

  reject def BRemoveFindDup (b : &Bucket) (k : Nat) :
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

  def BRemoveFindOther (b : &Bucket) (k : Nat) (k2 : Nat) (h : Eq Bool (EqB(k, k2)) false) :
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
  def SlotRemoveResult (s : &Slots) (i : Nat) (k : Nat) :
      Id Opt (let b = Slot(&*s, i); BRemove(b, k))
             (let r = BFind(Nth(*s, i), k); let b = Slot(&*s, i); BRemove(b, k); r) by s := (
    match *s {
      SOne(b) => BRemoveResult(&b, k),
      SCons(b, t) => match i {
        Z => BRemoveResult(&b, k),
        S i' => SlotRemoveResult(&t, i', k),
      },
    }
  )

  def SlotRemoveFind (s : &Slots) (i : Nat) (k : Nat) (h : AllUnique(*s)) :
      Id Opt (let b = Slot(&*s, i); BRemove(b, k); BFind(Nth(*s, i), k))
             (let b = Slot(&*s, i); BRemove(b, k); None) by s := (
    match *s {
      SOne(b) => BRemoveFind(&b, k, h),
      SCons(b, t) => match h {
        Intro(hb, ht) => match i {
          Z => BRemoveFind(&b, k, hb),
          S i' => SlotRemoveFind(&t, i', k, ht),
        },
      },
    }
  )

  def SlotRemoveFindOther (s : &Slots) (i : Nat) (j : Nat) (k : Nat) (k2 : Nat) (h : Eq Bool (EqB(k, k2)) false) :
      Id Opt (let b = Slot(&*s, i); BRemove(b, k); BFind(Nth(*s, j), k2))
             (let r = BFind(Nth(*s, j), k2); let b = Slot(&*s, i); BRemove(b, k); r) by s := (
    match *s {
      SOne(b) => BRemoveFindOther(&b, k, k2, h),
      SCons(b, t) => match i {
        Z => match j {
          Z => BRemoveFindOther(&b, k, k2, h),
          S _ => refl,
        },
        S i' => match j {
          Z => refl,
          S j' => SlotRemoveFindOther(&t, i', j', k, k2, h),
        },
      },
    }
  )

  def Buckets (m : HashMap) : Slots := (
    match m {
      HM(n, len, s) => s,
    }
  )

  def RemoveResult (hm : &HashMap) (k : Nat) :
      Id Opt (Remove(&*hm, k)) (let r = Find(*hm, k); Remove(&*hm, k); r) := (
    match *hm {
      HM(n, len, slots) => (
        let c = slots;
        let b = Slot(&c, Idx(k, n));
        let x = BRemove(b, k);
        match x {
          None => SlotRemoveResult(&slots, Idx(k, n), k),
          Some(_) => SlotRemoveResult(&slots, Idx(k, n), k),
        }
      ),
    }
  )

  def RemoveFind (hm : &HashMap) (k : Nat) (h : AllUnique(Buckets(*hm))) :
      Id Opt (Remove(&*hm, k); Find(*hm, k)) (Remove(&*hm, k); None) := (
    match *hm {
      HM(n, len, slots) => (
        let c = slots;
        let b = Slot(&c, Idx(k, n));
        let x = BRemove(b, k);
        match x {
          None => SlotRemoveFind(&slots, Idx(k, n), k, h),
          Some(_) => SlotRemoveFind(&slots, Idx(k, n), k, h),
        }
      ),
    }
  )

  def RemoveFindOther (hm : &HashMap) (k : Nat) (k2 : Nat) (h : Eq Bool (EqB(k, k2)) false) :
      Id Opt (Remove(&*hm, k); Find(*hm, k2)) (let r = Find(*hm, k2); Remove(&*hm, k); r) := (
    match *hm {
      HM(n, len, slots) => (
        let c = slots;
        let b = Slot(&c, Idx(k, n));
        let x = BRemove(b, k);
        match x {
          None => SlotRemoveFindOther(&slots, Idx(k, n), Idx(k2, n), k, k2, h),
          Some(_) => SlotRemoveFindOther(&slots, Idx(k, n), Idx(k2, n), k, k2, h),
        }
      ),
    }
  )
  -- ## GetMut
  -- The borrow points at the value a lookup returns; after writing `w` through it, `k`
  -- maps to `w`, and every other key is unchanged. Each statement writes through the
  -- borrow on both sides, so that both leave the same map.
  -- In the `BNil` arm the split re-normalises the goal, which runs `BGetMut` into its
  -- unreachable `match h {}`: that match is stuck (D58), so the goal stays a sealed
  -- program and the arm's own `match h {}` proves it.
  def BGetMutRead (b : &Bucket) (k : Nat) (w : Nat) (h : IsSome(BFind(*b, k))) :
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

  def BGetMutFind (b : &Bucket) (k : Nat) (w : Nat) (h : IsSome(BFind(*b, k))) :
      Id Opt (let q = BGetMut(&*b, k, h); *q := w; BFind(*b, k))
             (let q = BGetMut(&*b, k, h); *q := w; Some(w)) by b := (
    match *b {
      BNil => match h {},
      BCons(k', v', t) => (
        let e = EqB(k', k);
        match e {
          false => BGetMutFind(&t, k, w, h),
          true => refl,
        }
      ),
    }
  )

  def BGetMutFindOther (b : &Bucket) (k : Nat) (w : Nat) (h : IsSome(BFind(*b, k))) (k2 : Nat)
      (ne : Eq Bool (EqB(k, k2)) false) :
      Id Opt (let q = BGetMut(&*b, k, h); *q := w; BFind(*b, k2))
             (let r = BFind(*b, k2); let q = BGetMut(&*b, k, h); *q := w; r) by b := (
    match *b {
      BNil => match h {},
      BCons(k', v', t) => (
        let e = EqB(k', k);
        let e2 = EqB(k', k2);
        match e {
          false => match e2 {
            false => BGetMutFindOther(&t, k, w, h, k2, ne),
            true => refl,
          },
          true => match e2 {
            false => refl,
            true => (
              let f = EqBContra(k', k, k2, refl, refl, ne);
              match f {}
            ),
          },
        }
      ),
    }
  )
  -- Lifted through the index borrow, and stated for the map. `GetMut` branches on no
  -- sealed result, so the map theorems are the slot theorems at the key's index.
  def SlotGetMutRead (s : &Slots) (i : Nat) (k : Nat) (w : Nat) (h : IsSome(BFind(Nth(*s, i), k))) :
      Id Opt (let b = Slot(&*s, i); let q = BGetMut(b, k, h); let x = *q; *q := w; Some(x))
             (let r = BFind(Nth(*s, i), k); let b = Slot(&*s, i); let q = BGetMut(b, k, h); *q := w; r) by s := (
    match *s {
      SOne(b) => BGetMutRead(&b, k, w, h),
      SCons(b, t) => match i {
        Z => BGetMutRead(&b, k, w, h),
        S i' => SlotGetMutRead(&t, i', k, w, h),
      },
    }
  )

  def SlotGetMutFind (s : &Slots) (i : Nat) (k : Nat) (w : Nat) (h : IsSome(BFind(Nth(*s, i), k))) :
      Id Opt (let b = Slot(&*s, i); let q = BGetMut(b, k, h); *q := w; BFind(Nth(*s, i), k))
             (let b = Slot(&*s, i); let q = BGetMut(b, k, h); *q := w; Some(w)) by s := (
    match *s {
      SOne(b) => BGetMutFind(&b, k, w, h),
      SCons(b, t) => match i {
        Z => BGetMutFind(&b, k, w, h),
        S i' => SlotGetMutFind(&t, i', k, w, h),
      },
    }
  )

  def SlotGetMutFindOther (s : &Slots) (i : Nat) (j : Nat) (k : Nat) (w : Nat) (h : IsSome(BFind(Nth(*s, i), k))) (k2 : Nat)
      (ne : Eq Bool (EqB(k, k2)) false) :
      Id Opt (let b = Slot(&*s, i); let q = BGetMut(b, k, h); *q := w; BFind(Nth(*s, j), k2))
             (let r = BFind(Nth(*s, j), k2); let b = Slot(&*s, i); let q = BGetMut(b, k, h); *q := w; r) by s := (
    match *s {
      SOne(b) => BGetMutFindOther(&b, k, w, h, k2, ne),
      SCons(b, t) => match i {
        Z => match j {
          Z => BGetMutFindOther(&b, k, w, h, k2, ne),
          S _ => refl,
        },
        S i' => match j {
          Z => refl,
          S j' => SlotGetMutFindOther(&t, i', j', k, w, h, k2, ne),
        },
      },
    }
  )

  def GetMutRead (hm : &HashMap) (k : Nat) (w : Nat) (h : IsSome(Find(*hm, k))) :
      Id Opt (let q = GetMut(&*hm, k, h); let x = *q; *q := w; Some(x)) (let r = Find(*hm, k); let q = GetMut(&*hm, k, h); *q := w; r) := (
    match *hm {
      HM(n, len, slots) => SlotGetMutRead(&slots, Idx(k, n), k, w, h),
    }
  )

  def GetMutFind (hm : &HashMap) (k : Nat) (w : Nat) (h : IsSome(Find(*hm, k))) :
      Id Opt (let q = GetMut(&*hm, k, h); *q := w; Find(*hm, k)) (let q = GetMut(&*hm, k, h); *q := w; Some(w)) := (
    match *hm {
      HM(n, len, slots) => SlotGetMutFind(&slots, Idx(k, n), k, w, h),
    }
  )

  def GetMutFindOther (hm : &HashMap) (k : Nat) (w : Nat) (h : IsSome(Find(*hm, k))) (k2 : Nat) (ne : Eq Bool (EqB(k, k2)) false) :
      Id Opt (let q = GetMut(&*hm, k, h); *q := w; Find(*hm, k2)) (let r = Find(*hm, k2); let q = GetMut(&*hm, k, h); *q := w; r) := (
    match *hm {
      HM(n, len, slots) => SlotGetMutFindOther(&slots, Idx(k, n), Idx(k2, n), k, w, h, k2, ne),
    }
  )

  -- ## Get, through the borrow
  -- `Get` reads through a mutable borrow (Ochr has no shared borrows). When the lookup
  -- is stuck on an abstract bucket, closing it off leaves a sealed program in the bucket
  -- ("look `k` up in `u`, then give `u` back"), which is `u` only by a proof. These three
  -- lemmas are that proof: `Get` returns what `Find` returns, and leaves the map as it was.
  def BGetFind (b : &Bucket) (k : Nat) : Id Opt (BGet(&*b, k)) (BFind(*b, k)) by b := (
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

  def SlotGetFind (s : &Slots) (i : Nat) (k : Nat) :
      Id Opt (let b = Slot(&*s, i); BGet(b, k)) (BFind(Nth(*s, i), k)) by s := (
    match *s {
      SOne(b) => BGetFind(&b, k),
      SCons(b, t) => match i {
        Z => BGetFind(&b, k),
        S i' => SlotGetFind(&t, i', k),
      },
    }
  )

  def GetFind (hm : &HashMap) (k : Nat) : Id Opt (Get(&*hm, k)) (Find(*hm, k)) := (
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

  def BContainsFind (b : &Bucket) (k : Nat) : Id Bool (BContains(&*b, k)) (Has(BFind(*b, k))) by b := (
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

  def SlotContainsFind (s : &Slots) (i : Nat) (k : Nat) :
      Id Bool (let b = Slot(&*s, i); BContains(b, k)) (Has(BFind(Nth(*s, i), k))) by s := (
    match *s {
      SOne(b) => BContainsFind(&b, k),
      SCons(b, t) => match i {
        Z => BContainsFind(&b, k),
        S i' => SlotContainsFind(&t, i', k),
      },
    }
  )

  def ContainsFind (hm : &HashMap) (k : Nat) : Id Bool (ContainsKey(&*hm, k)) (Has(Find(*hm, k))) := (
    match *hm {
      HM(n, len, slots) => SlotContainsFind(&slots, Idx(k, n), k),
    }
  )

  -- ## New and Clear
  -- Every bucket of a fresh table is empty, so no key is found.
  def NthEmpty (n : Nat) (i : Nat) : Id Bucket BNil (Nth(EmptySlots(n), i)) by n := (
    match n {
      Z => refl,
      S m => match i {
        Z => refl,
        S i' => NthEmpty(m, i'),
      },
    }
  )

  def NewFind (n : Nat) (k : Nat) : Id Opt (Find(New(n), k)) None := (
    J(Bucket, BNil, Nth(EmptySlots(n), Idx(k, n)), λ(z : Bucket) : Prop => Eq Opt (BFind(z, k)) None, NthEmpty(n, Idx(k, n)), refl)
  )

  def ClearFind (hm : &HashMap) (k : Nat) : Id Opt (Clear(&*hm); Find(*hm, k)) (Clear(&*hm); None) := (
    match *hm {
      HM(n, len, slots) => NewFind(n, k),
    }
  )
}

#eval IO.println (run "HashMapLookup" HashMapLookup).show

-- every verdict as expected, and the exact number of declarations (a truncated file changes it)
#guard (run "HashMapLookup" HashMapLookup).allAsExpected
#guard (run "HashMapLookup" HashMapLookup).count == 44

/-! ## The length

`Len` is the map's `len` field. After an insert it grows by one exactly when the key was
absent, and after a remove it shrinks by one exactly when the key was present; with the
invariant `len = Count(slots)` (the number of entries), each operation preserves it. -/

ochr HashMapLength uses Std, HashMap, HashMapLookup {
  -- Sizes, and the two ways a length changes.
  def BLen (b : Bucket) : Nat by b := (
    match b {
      BNil => 0,
      BCons(k, v, t) => S (BLen(t)),
    }
  )

  def Count (s : Slots) : Nat by s := (
    match s {
      SOne(b) => BLen(b),
      SCons(b, t) => Add(BLen(b), Count(t)),
    }
  )

  def IfNew (r : Opt) (l : Nat) : Nat := (
    match r {
      None => S l,
      Some(_) => l,
    }
  )

  def IfFound (r : Opt) (l : Nat) : Nat := (
    match r {
      None => l,
      Some(_) => S l,
    }
  )

  -- ## The len field
  -- The bucket insert adds an entry exactly when the key was absent.
  def IsNone (r : Opt) : Bool := (
    match r {
      None => true,
      Some(_) => false,
    }
  )

  def BInsertAdded (b : &Bucket) (k : Nat) (v : Nat) :
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

  def SlotInsertAdded (s : &Slots) (i : Nat) (k : Nat) (v : Nat) :
      Id Bool (let b = Slot(&*s, i); BInsert(b, k, v))
              (let r = BFind(Nth(*s, i), k); let b = Slot(&*s, i); BInsert(b, k, v); IsNone(r)) by s := (
    match *s {
      SOne(b) => BInsertAdded(&b, k, v),
      SCons(b, t) => match i {
        Z => BInsertAdded(&b, k, v),
        S i' => SlotInsertAdded(&t, i', k, v),
      },
    }
  )

  -- Split on whether the entry was added and on the earlier lookup; where they disagree,
  -- the lemma's type is `true = false` or `false = true`, which is `False`.
  def InsertLen (hm : &HashMap) (k : Nat) (v : Nat) :
      Id Nat (InsertNoResize(&*hm, k, v); Len(*hm))
             (let l = Len(*hm); let r = Find(*hm, k); InsertNoResize(&*hm, k, v); IfNew(r, l)) := (
    match *hm {
      HM(n, len, slots) => (
        let p = SlotInsertAdded(&slots, Idx(k, n), k, v);
        let c = slots;
        let b = Slot(&c, Idx(k, n));
        let added = BInsert(b, k, v);
        let r = BFind(Nth(slots, Idx(k, n)), k);
        match added {
          false => match r {
            None => match p {},
            Some(_) => refl,
          },
          true => match r {
            None => refl,
            Some(_) => match p {},
          },
        }
      ),
    }
  )
  -- ## The invariant len = Count(slots), for insert
  -- `x + S y = S (x + y)`, in place by recursion (as in `Trees`), and symmetry.
  def AddMS (x : &Nat) (y : Nat) : Id Unit (AddM(x, S y)) (AddM(&*x, y); *x := S *x) by x := (
    match *x {
      Z => refl,
      S p => AddMS(&p, y),
    }
  )

  def AddS (x : Nat) (y : Nat) : Id Nat (Add(x, S y)) (S (Add(x, y))) := AddMS(&x, y)

  def SymmN (x : Nat) (y : Nat) (h : Eq Nat x y) : Eq Nat y x := (
    J(Nat, x, y, λ(z : Nat) : Prop => Eq Nat z x, h, refl)
  )

  -- A bucket grows by one exactly when the key was absent. `S a = S b` is `a = b`, so
  -- each arm is the induction hypothesis as it stands.
  def BInsertCount (b : &Bucket) (k : Nat) (v : Nat) :
      Id Nat (let r = BFind(*b, k); let l = BLen(*b); BInsert(&*b, k, v); IfNew(r, l))
             (BInsert(&*b, k, v); BLen(*b)) by b := (
    match *b {
      BNil => refl,
      BCons(k', v', t) => (
        let e = EqB(k', k);
        match e {
          false => (
            let r = BFind(t, k);
            match r {
              None => BInsertCount(&t, k, v),
              Some(_) => BInsertCount(&t, k, v),
            }
          ),
          true => refl,
        }
      ),
    }
  )

  -- Lifted to the slots, where `Count` adds the bucket lengths: each arm rewrites once
  -- under `Add`, with `J`.
  def SlotInsertCount (s : &Slots) (i : Nat) (k : Nat) (v : Nat) :
      Id Nat (let r = BFind(Nth(*s, i), k); let c = Count(*s); let b = Slot(&*s, i); BInsert(b, k, v); IfNew(r, c))
             (let b = Slot(&*s, i); BInsert(b, k, v); Count(*s)) by s := (
    match *s {
      SOne(b) => BInsertCount(&b, k, v),
      SCons(b, t) => (
        let bl = BLen(b);
        let c = Count(t);
        match i {
          Z => (
            let cb = b;
            BInsert(&cb, k, v);
            let r = BFind(b, k);
            match r {
              None => J(Nat, S bl, BLen(cb), λ(z : Nat) : Prop => Eq Nat (S (Add(bl, c))) (Add(z, c)), BInsertCount(&b, k, v), refl),
              Some(_) => J(Nat, bl, BLen(cb), λ(z : Nat) : Prop => Eq Nat (Add(bl, c)) (Add(z, c)), BInsertCount(&b, k, v), refl),
            }
          ),
          S i' => (
            let ct = t;
            let rb = Slot(&ct, i');
            BInsert(rb, k, v);
            let r = BFind(Nth(t, i'), k);
            match r {
              None => J(Nat, S c, Count(ct), λ(z : Nat) : Prop => Eq Nat (S (Add(bl, c))) (Add(bl, z)),
                        SlotInsertCount(&t, i', k, v), SymmN(Add(bl, S c), S (Add(bl, c)), AddS(bl, c))),
              Some(_) => J(Nat, c, Count(ct), λ(z : Nat) : Prop => Eq Nat (Add(bl, c)) (Add(bl, z)), SlotInsertCount(&t, i', k, v), refl),
            }
          ),
        }
      ),
    }
  )

  -- The map: split on the added flag and on the earlier lookup (the mixed arms contradict
  -- `SlotInsertAdded`), then one `J` against the hypothesis.
  def InsertCount (hm : &HashMap) (k : Nat) (v : Nat) (h : Eq Nat (Len(*hm)) (Count(Buckets(*hm)))) :
      Id Nat (InsertNoResize(&*hm, k, v); Len(*hm)) (InsertNoResize(&*hm, k, v); Count(Buckets(*hm))) := (
    match *hm {
      HM(n, len, slots) => (
        let l = len;
        let p = SlotInsertAdded(&slots, Idx(k, n), k, v);
        let q = SlotInsertCount(&slots, Idx(k, n), k, v);
        let c = slots;
        let b = Slot(&c, Idx(k, n));
        let added = BInsert(b, k, v);
        let r = BFind(Nth(slots, Idx(k, n)), k);
        match added {
          false => match r {
            None => match p {},
            Some(_) => J(Nat, Count(slots), Count(c), λ(z : Nat) : Prop => Eq Nat l z, q, h),
          },
          true => match r {
            None => J(Nat, S (Count(slots)), Count(c), λ(z : Nat) : Prop => Eq Nat (S l) z, q, h),
            Some(_) => match p {},
          },
        }
      ),
    }
  )

  -- The hypothesis is needed.
  reject def InsertCountNoHyp (hm : &HashMap) (k : Nat) (v : Nat) :
      Id Nat (InsertNoResize(&*hm, k, v); Len(*hm)) (InsertNoResize(&*hm, k, v); Count(Buckets(*hm))) := (
    match *hm {
      HM(n, len, slots) => SlotInsertCount(&slots, Idx(k, n), k, v),
    }
  )
  -- ## Remove
  -- The len field shrinks by one exactly when the key was found (the code's `Pred`).
  def Shrink (r : Opt) (l : Nat) : Nat := (
    match r {
      None => l,
      Some(_) => Pred(l),
    }
  )

  def RemoveLen (hm : &HashMap) (k : Nat) :
      Id Nat (Remove(&*hm, k); Len(*hm)) (let l = Len(*hm); let r = Find(*hm, k); Remove(&*hm, k); Shrink(r, l)) := (
    match *hm {
      HM(n, len, slots) => (
        let p = SlotRemoveResult(&slots, Idx(k, n), k);
        let c = slots;
        let b = Slot(&c, Idx(k, n));
        let x = BRemove(b, k);
        let r = BFind(Nth(slots, Idx(k, n)), k);
        match x {
          None => match r {
            None => refl,
            Some(_) => match p {},
          },
          Some(_) => match r {
            None => match p {},
            Some(_) => refl,
          },
        }
      ),
    }
  )

  -- The count before a remove is the count after, plus one if the key was found.
  def BRemoveCount (b : &Bucket) (k : Nat) :
      Id Nat (let l = BLen(*b); BRemove(&*b, k); l) (let r = BFind(*b, k); BRemove(&*b, k); IfFound(r, BLen(*b))) by b := (
    match *b {
      BNil => refl,
      BCons(k', v', t) => (
        let e = EqB(k', k);
        match e {
          false => (
            let r = BFind(t, k);
            match r {
              None => BRemoveCount(&t, k),
              Some(_) => BRemoveCount(&t, k),
            }
          ),
          true => refl,
        }
      ),
    }
  )

  def SlotRemoveCount (s : &Slots) (i : Nat) (k : Nat) :
      Id Nat (let c = Count(*s); let b = Slot(&*s, i); BRemove(b, k); c)
             (let r = BFind(Nth(*s, i), k); let b = Slot(&*s, i); BRemove(b, k); IfFound(r, Count(*s))) by s := (
    match *s {
      SOne(b) => BRemoveCount(&b, k),
      SCons(b, t) => (
        let bl = BLen(b);
        let c = Count(t);
        match i {
          Z => (
            let cb = b;
            BRemove(&cb, k);
            let r = BFind(b, k);
            match r {
              None => J(Nat, bl, BLen(cb), λ(z : Nat) : Prop => Eq Nat (Add(bl, c)) (Add(z, c)), BRemoveCount(&b, k), refl),
              Some(_) => J(Nat, bl, S (BLen(cb)), λ(z : Nat) : Prop => Eq Nat (Add(bl, c)) (Add(z, c)), BRemoveCount(&b, k), refl),
            }
          ),
          S i' => (
            let ct = t;
            let rb = Slot(&ct, i');
            BRemove(rb, k);
            let ca = Count(ct);
            let r = BFind(Nth(t, i'), k);
            match r {
              None => J(Nat, c, ca, λ(z : Nat) : Prop => Eq Nat (Add(bl, c)) (Add(bl, z)), SlotRemoveCount(&t, i', k), refl),
              Some(_) => J(Nat, S ca, c, λ(z : Nat) : Prop => Eq Nat (Add(bl, z)) (S (Add(bl, ca))),
                           SymmN(c, S ca, SlotRemoveCount(&t, i', k)), AddS(bl, ca)),
            }
          ),
        }
      ),
    }
  )

  def RemoveCount (hm : &HashMap) (k : Nat) (h : Eq Nat (Len(*hm)) (Count(Buckets(*hm)))) :
      Id Nat (Remove(&*hm, k); Len(*hm)) (Remove(&*hm, k); Count(Buckets(*hm))) := (
    match *hm {
      HM(n, len, slots) => (
        let l = len;
        let p = SlotRemoveResult(&slots, Idx(k, n), k);
        let q = SlotRemoveCount(&slots, Idx(k, n), k);
        let c = slots;
        let b = Slot(&c, Idx(k, n));
        let x = BRemove(b, k);
        let r = BFind(Nth(slots, Idx(k, n)), k);
        match x {
          None => match r {
            None => J(Nat, Count(slots), Count(c), λ(z : Nat) : Prop => Eq Nat l z, q, h),
            Some(_) => match p {},
          },
          Some(_) => match r {
            None => match p {},
            Some(_) => J(Nat, Count(slots), S (Count(c)), λ(z : Nat) : Prop => Eq Nat (Pred(l)) (Pred(z)), q,
                         J(Nat, l, Count(slots), λ(z : Nat) : Prop => Eq Nat (Pred(l)) (Pred(z)), h, refl)),
          },
        }
      ),
    }
  )

  -- ## New and Clear
  def EmptyCount (n : Nat) : Eq Nat (Count(EmptySlots(n))) 0 by n := (
    match n {
      Z => refl,
      S m => EmptyCount(m),
    }
  )

  def NewCount (n : Nat) : Eq Nat (Len(New(n))) (Count(Buckets(New(n)))) := SymmN(Count(EmptySlots(n)), 0, EmptyCount(n))

  def ClearCount (hm : &HashMap) : Id Nat (Clear(&*hm); Len(*hm)) (Clear(&*hm); Count(Buckets(*hm))) := (
    match *hm {
      HM(n, len, slots) => NewCount(n),
    }
  )
  -- ## GetMut
  -- Writing through the borrow leaves the length as it was.
  def GetMutLen (hm : &HashMap) (k : Nat) (w : Nat) (h : IsSome(Find(*hm, k))) :
      Id Nat (let q = GetMut(&*hm, k, h); *q := w; Len(*hm)) (let l = Len(*hm); let q = GetMut(&*hm, k, h); *q := w; l) := (
    match *hm {
      HM(n, len, slots) => refl,
    }
  )
  -- The count is unchanged too: writing a value changes no bucket's length.
  def BGetMutCount (b : &Bucket) (k : Nat) (w : Nat) (h : IsSome(BFind(*b, k))) :
      Id Nat (let l = BLen(*b); let q = BGetMut(&*b, k, h); *q := w; l) (let q = BGetMut(&*b, k, h); *q := w; BLen(*b)) by b := (
    match *b {
      BNil => match h {},
      BCons(k', v', t) => (
        let e = EqB(k', k);
        match e {
          false => BGetMutCount(&t, k, w, h),
          true => refl,
        }
      ),
    }
  )
  def SlotGetMutCount (s : &Slots) (i : Nat) (k : Nat) (w : Nat) (h : IsSome(BFind(Nth(*s, i), k))) :
      Id Nat (let c = Count(*s); let b = Slot(&*s, i); let q = BGetMut(b, k, h); *q := w; c)
             (let b = Slot(&*s, i); let q = BGetMut(b, k, h); *q := w; Count(*s)) by s := (
    match *s {
      SOne(b) => BGetMutCount(&b, k, w, h),
      SCons(b, t) => (
        let bl = BLen(b);
        let c = Count(t);
        match i {
          Z => (
            let cb = b;
            let q = BGetMut(&cb, k, h);
            *q := w;
            J(Nat, bl, BLen(cb), λ(z : Nat) : Prop => Eq Nat (Add(bl, c)) (Add(z, c)), BGetMutCount(&b, k, w, h), refl)
          ),
          S i' => (
            let ct = t;
            let rb = Slot(&ct, i');
            let q = BGetMut(rb, k, h);
            *q := w;
            J(Nat, c, Count(ct), λ(z : Nat) : Prop => Eq Nat (Add(bl, c)) (Add(bl, z)), SlotGetMutCount(&t, i', k, w, h), refl)
          ),
        }
      ),
    }
  )
}

#eval IO.println (run "HashMapLength" HashMapLength).show

-- every verdict as expected, and the exact number of declarations (a truncated file changes it)
#guard (run "HashMapLength" HashMapLength).allAsExpected
#guard (run "HashMapLength" HashMapLength).count == 26

/-! ## The invariant, and resizing

The invariant (Aeneas's `hash_map_t_inv`, less its load-factor and overflow clauses): the
length counts the entries, the keys of each bucket are distinct, and every key lies only in
its own bucket. The last is a statement about every key, `Π(k : Nat). OnlyIn(…)`, proved
for each key by a function of `k`. Every operation keeps the invariant, stated as "run the
operation on a copy, then the invariant holds of the copy". Resizing moves every entry with
`InsertNoResize`, so it keeps every lookup; with the invariant, the insert with resizing
behaves like the insert without. -/

ochr HashMapResize uses Std, HashMap, HashMapLookup, HashMapLength {
  -- ## Helpers
  def TransO (x : Opt) (y : Opt) (z : Opt) (h1 : Eq Opt x y) (h2 : Eq Opt y z) : Eq Opt x z := (
    J(Opt, y, z, λ(w : Opt) : Prop => Eq Opt x w, h2, h1)
  )

  def EqBSymm (a : Nat) (b : Nat) (h : Eq Bool (EqB(a, b)) true) : Eq Bool (EqB(b, a)) true := (
    J(Nat, a, b, λ(z : Nat) : Prop => Eq Bool (EqB(z, a)) true, EqBSound(a, b, h), EqBRefl(a))
  )

  def NeqFlip (a : Nat) (b : Nat) (h : Eq Bool (EqB(a, b)) false) : Eq Bool (EqB(b, a)) false := (
    let e = EqB(b, a);
    match e {
      false => refl,
      true => (
        let f = J(Bool, EqB(a, b), true, λ(z : Bool) : Prop => Eq Bool z false, EqBSymm(b, a, refl), h);
        match f {}
      ),
    }
  )

  -- ## Keys stay distinct
  def BInsertUnique (b : Bucket) (k : Nat) (v : Nat) (h : Unique(b)) : (let c = b; BInsert(&c, k, v); Unique(c)) by b := (
    match b {
      BNil => ⟨refl, refl⟩,
      BCons(k', v', t) => match h {
        Intro(absent, rest) => (
          let e = EqB(k', k);
          match e {
            false => (
              let before = t;
              let after = t;
              BInsert(&after, k, v);
              ⟨TransO(BFind(after, k'), BFind(t, k'), None, BInsertFindOther(&before, k, v, k', NeqFlip(k', k, refl)), absent),
               BInsertUnique(t, k, v, rest)⟩
            ),
            true => ⟨absent, rest⟩,
          }
        ),
      },
    }
  )
  def SlotInsertUnique (s : Slots) (i : Nat) (k : Nat) (v : Nat) (h : AllUnique(s)) :
      (let c = s; let b = Slot(&c, i); BInsert(b, k, v); AllUnique(c)) by s := (
    match s {
      SOne(b) => BInsertUnique(b, k, v, h),
      SCons(b, t) => match h {
        Intro(hb, ht) => match i {
          Z => ⟨BInsertUnique(b, k, v, hb), ht⟩,
          S i' => ⟨hb, SlotInsertUnique(t, i', k, v, ht)⟩,
        },
      },
    }
  )

  def BRemoveUnique (b : Bucket) (k : Nat) (h : Unique(b)) : (let c = b; BRemove(&c, k); Unique(c)) by b := (
    match b {
      BNil => refl,
      BCons(k', v', t) => match h {
        Intro(absent, rest) => (
          let e = EqB(k', k);
          match e {
            false => (
              let before = t;
              let after = t;
              BRemove(&after, k);
              ⟨TransO(BFind(after, k'), BFind(t, k'), None, BRemoveFindOther(&before, k, k', NeqFlip(k', k, refl)), absent),
               BRemoveUnique(t, k, rest)⟩
            ),
            true => rest,
          }
        ),
      },
    }
  )

  def SlotRemoveUnique (s : Slots) (i : Nat) (k : Nat) (h : AllUnique(s)) :
      (let c = s; let b = Slot(&c, i); BRemove(b, k); AllUnique(c)) by s := (
    match s {
      SOne(b) => BRemoveUnique(b, k, h),
      SCons(b, t) => match h {
        Intro(hb, ht) => match i {
          Z => ⟨BRemoveUnique(b, k, hb), ht⟩,
          S i' => ⟨hb, SlotRemoveUnique(t, i', k, ht)⟩,
        },
      },
    }
  )

  -- ## Keys stay in their bucket
  def Nowhere (s : Slots) (k : Nat) : Prop by s := (
    match s {
      SOne(b) => Eq Opt (BFind(b, k)) None,
      SCons(b, t) => Eq Opt (BFind(b, k)) None ∧ Nowhere(t, k),
    }
  )

  def OnlyIn (s : Slots) (d : Nat) (k : Nat) : Prop by s := (
    match s {
      SOne(b) => ⊤,
      SCons(b, t) => match d {
        Z => Nowhere(t, k),
        S d' => Eq Opt (BFind(b, k)) None ∧ OnlyIn(t, d', k),
      },
    }
  )

  def Placed (s : Slots) (n : Nat) : Prop := Π(k : Nat). OnlyIn(s, Idx(k, n), k)

  -- Inserting `k` keeps another key absent where it was absent.
  def BInsertAbsent (b : Bucket) (k : Nat) (v : Nat) (k2 : Nat) (ne : Eq Bool (EqB(k, k2)) false)
      (h : Eq Opt (BFind(b, k2)) None) : (let c = b; BInsert(&c, k, v); Eq Opt (BFind(c, k2)) None) := (
    let before = b;
    let after = b;
    BInsert(&after, k, v);
    TransO(BFind(after, k2), BFind(b, k2), None, BInsertFindOther(&before, k, v, k2, ne), h)
  )

  def NowhereInsert (s : Slots) (i : Nat) (k : Nat) (v : Nat) (k2 : Nat) (ne : Eq Bool (EqB(k, k2)) false)
      (h : Nowhere(s, k2)) : (let c = s; let b = Slot(&c, i); BInsert(b, k, v); Nowhere(c, k2)) by s := (
    match s {
      SOne(b) => BInsertAbsent(b, k, v, k2, ne, h),
      SCons(b, t) => match h {
        Intro(hb, ht) => match i {
          Z => ⟨BInsertAbsent(b, k, v, k2, ne, hb), ht⟩,
          S i' => ⟨hb, NowhereInsert(t, i', k, v, k2, ne, ht)⟩,
        },
      },
    }
  )

  def OnlyInOther (s : Slots) (i : Nat) (d : Nat) (k : Nat) (v : Nat) (k2 : Nat) (ne : Eq Bool (EqB(k, k2)) false)
      (h : OnlyIn(s, d, k2)) : (let c = s; let b = Slot(&c, i); BInsert(b, k, v); OnlyIn(c, d, k2)) by s := (
    match s {
      SOne(b) => refl,
      SCons(b, t) => match d {
        Z => match i {
          Z => h,
          S i' => NowhereInsert(t, i', k, v, k2, ne, h),
        },
        S d' => match h {
          Intro(hb, ht) => match i {
            Z => ⟨BInsertAbsent(b, k, v, k2, ne, hb), ht⟩,
            S i' => ⟨hb, OnlyInOther(t, i', d', k, v, k2, ne, ht)⟩,
          },
        },
      },
    }
  )

  def OnlyInSame (s : Slots) (i : Nat) (k : Nat) (v : Nat) (h : OnlyIn(s, i, k)) :
      (let c = s; let b = Slot(&c, i); BInsert(b, k, v); OnlyIn(c, i, k)) by s := (
    match s {
      SOne(b) => refl,
      SCons(b, t) => match i {
        Z => h,
        S i' => match h {
          Intro(hb, ht) => ⟨hb, OnlyInSame(t, i', k, v, ht)⟩,
        },
      },
    }
  )

  -- For every key `k2`: if it is `k`, it went into its own bucket; if not, it did not move.
  def SlotInsertPlaced (s : Slots) (n : Nat) (k : Nat) (v : Nat) (h : Placed(s, n)) :
      (let c = s; let b = Slot(&c, Idx(k, n)); BInsert(b, k, v); Placed(c, n)) := (
    let c = s;
    let b = Slot(&c, Idx(k, n));
    BInsert(b, k, v);
    λ(k2 : Nat) : OnlyIn(c, Idx(k2, n), k2) => (
      let e = EqB(k, k2);
      match e {
        false => OnlyInOther(s, Idx(k, n), Idx(k2, n), k, v, k2, refl, h(k2)),
        true => J(Nat, k, k2, λ(z : Nat) : Prop => OnlyIn(c, Idx(z, n), z), EqBSound(k, k2, refl), OnlyInSame(s, Idx(k, n), k, v, h(k))),
      }
    )
  )
  -- Removing never makes a key present.
  def BRemoveAbsent (b : Bucket) (k : Nat) (k2 : Nat) (h : Eq Opt (BFind(b, k2)) None) :
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

  def NowhereRemove (s : Slots) (i : Nat) (k : Nat) (k2 : Nat) (h : Nowhere(s, k2)) :
      (let c = s; let b = Slot(&c, i); BRemove(b, k); Nowhere(c, k2)) by s := (
    match s {
      SOne(b) => BRemoveAbsent(b, k, k2, h),
      SCons(b, t) => match h {
        Intro(hb, ht) => match i {
          Z => ⟨BRemoveAbsent(b, k, k2, hb), ht⟩,
          S i' => ⟨hb, NowhereRemove(t, i', k, k2, ht)⟩,
        },
      },
    }
  )

  def OnlyInRemove (s : Slots) (i : Nat) (d : Nat) (k : Nat) (k2 : Nat) (h : OnlyIn(s, d, k2)) :
      (let c = s; let b = Slot(&c, i); BRemove(b, k); OnlyIn(c, d, k2)) by s := (
    match s {
      SOne(b) => refl,
      SCons(b, t) => match d {
        Z => match i {
          Z => h,
          S i' => NowhereRemove(t, i', k, k2, h),
        },
        S d' => match h {
          Intro(hb, ht) => match i {
            Z => ⟨BRemoveAbsent(b, k, k2, hb), ht⟩,
            S i' => ⟨hb, OnlyInRemove(t, i', d', k, k2, ht)⟩,
          },
        },
      },
    }
  )

  def SlotRemovePlaced (s : Slots) (n : Nat) (k : Nat) (h : Placed(s, n)) :
      (let c = s; let b = Slot(&c, Idx(k, n)); BRemove(b, k); Placed(c, n)) := (
    let c = s;
    let b = Slot(&c, Idx(k, n));
    BRemove(b, k);
    λ(k2 : Nat) : OnlyIn(c, Idx(k2, n), k2) => OnlyInRemove(s, Idx(k, n), Idx(k2, n), k, k2, h(k2))
  )

  -- ## The invariant
  -- The length counts the entries, the keys of each bucket are distinct, and every key
  -- lies only in its own bucket (all three are Aeneas's `hash_map_t_inv`, less its load
  -- factor and overflow clauses).
  def Inv (m : HashMap) : Prop := (
    match m {
      HM(n, len, s) => Eq Nat len (Count(s)) ∧ (AllUnique(s) ∧ Placed(s, n)),
    }
  )

  def NowhereEmpty (n : Nat) (k : Nat) : Nowhere(EmptySlots(n), k) by n := (
    match n {
      Z => refl,
      S m => ⟨refl, NowhereEmpty(m, k)⟩,
    }
  )

  def OnlyInEmpty (n : Nat) (d : Nat) (k : Nat) : OnlyIn(EmptySlots(n), d, k) by n := (
    match n {
      Z => refl,
      S m => match d {
        Z => NowhereEmpty(m, k),
        S d' => ⟨refl, OnlyInEmpty(m, d', k)⟩,
      },
    }
  )

  def UniqueEmpty (n : Nat) : AllUnique(EmptySlots(n)) by n := (
    match n {
      Z => refl,
      S m => ⟨refl, UniqueEmpty(m)⟩,
    }
  )

  def NewInv (n : Nat) : Inv(New(n)) := (
    ⟨NewCount(n), ⟨UniqueEmpty(n), λ(k : Nat) : OnlyIn(EmptySlots(n), Idx(k, n), k) => OnlyInEmpty(n, Idx(k, n), k)⟩⟩
  )

  -- Each operation keeps it. Split on whether the bucket changed its size, as for the
  -- length theorems; the three parts are the lemmas above.
  def InsertInv (m : HashMap) (k : Nat) (v : Nat) (h : Inv(m)) : (let c = m; InsertNoResize(&c, k, v); Inv(c)) := (
    match m {
      HM(n, len, s) => match h {
        Intro(hl, hr) => match hr {
          Intro(hu, hp) => (
            let mc = m;
            let cs = s;
            let b = Slot(&cs, Idx(k, n));
            let added = BInsert(b, k, v);
            match added {
              false => ⟨InsertCount(&mc, k, v, hl), ⟨SlotInsertUnique(s, Idx(k, n), k, v, hu), SlotInsertPlaced(s, n, k, v, hp)⟩⟩,
              true => ⟨InsertCount(&mc, k, v, hl), ⟨SlotInsertUnique(s, Idx(k, n), k, v, hu), SlotInsertPlaced(s, n, k, v, hp)⟩⟩,
            }
          ),
        },
      },
    }
  )

  def RemoveInv (m : HashMap) (k : Nat) (h : Inv(m)) : (let c = m; Remove(&c, k); Inv(c)) := (
    match m {
      HM(n, len, s) => match h {
        Intro(hl, hr) => match hr {
          Intro(hu, hp) => (
            let mc = m;
            let cs = s;
            let b = Slot(&cs, Idx(k, n));
            let x = BRemove(b, k);
            match x {
              None => ⟨RemoveCount(&mc, k, hl), ⟨SlotRemoveUnique(s, Idx(k, n), k, hu), SlotRemovePlaced(s, n, k, hp)⟩⟩,
              Some(_) => ⟨RemoveCount(&mc, k, hl), ⟨SlotRemoveUnique(s, Idx(k, n), k, hu), SlotRemovePlaced(s, n, k, hp)⟩⟩,
            }
          ),
        },
      },
    }
  )

  def ClearInv (m : HashMap) : (let c = m; Clear(&c); Inv(c)) := (
    match m {
      HM(n, len, s) => NewInv(n),
    }
  )
  -- `GetMut` changes a value, never a key: the keys stay distinct and in their bucket,
  -- and the count is unchanged.
  def BGetMutUnique (b : Bucket) (k : Nat) (w : Nat) (h : IsSome(BFind(b, k))) (hu : Unique(b)) :
      (let c = b; let q = BGetMut(&c, k, h); *q := w; Unique(c)) by b := (
    match b {
      BNil => match h {},
      BCons(k', v', t) => match hu {
        Intro(absent, rest) => (
          let e = EqB(k', k);
          match e {
            false => (
              let before = t;
              let after = t;
              let q = BGetMut(&after, k, h);
              *q := w;
              ⟨TransO(BFind(after, k'), BFind(t, k'), None, BGetMutFindOther(&before, k, w, h, k', NeqFlip(k', k, refl)), absent),
               BGetMutUnique(t, k, w, h, rest)⟩
            ),
            true => hu,
          }
        ),
      },
    }
  )
  def SlotGetMutUnique (s : Slots) (i : Nat) (k : Nat) (w : Nat) (h : IsSome(BFind(Nth(s, i), k))) (hu : AllUnique(s)) :
      (let c = s; let b = Slot(&c, i); let q = BGetMut(b, k, h); *q := w; AllUnique(c)) by s := (
    match s {
      SOne(b) => BGetMutUnique(b, k, w, h, hu),
      SCons(b, t) => match hu {
        Intro(hb, ht) => match i {
          Z => ⟨BGetMutUnique(b, k, w, h, hb), ht⟩,
          S i' => ⟨hb, SlotGetMutUnique(t, i', k, w, h, ht)⟩,
        },
      },
    }
  )
  def BGetMutAbsent (b : Bucket) (k : Nat) (w : Nat) (h : IsSome(BFind(b, k))) (k2 : Nat) (a : Eq Opt (BFind(b, k2)) None) :
      (let c = b; let q = BGetMut(&c, k, h); *q := w; Eq Opt (BFind(c, k2)) None) by b := (
    match b {
      BNil => match h {},
      BCons(k', v', t) => (
        let e2 = EqB(k', k2);
        match e2 {
          false => (
            let e = EqB(k', k);
            match e {
              false => BGetMutAbsent(t, k, w, h, k2, a),
              true => a,
            }
          ),
          true => match a {},
        }
      ),
    }
  )
  def NowhereGetMut (s : Slots) (i : Nat) (k : Nat) (w : Nat) (h : IsSome(BFind(Nth(s, i), k))) (k2 : Nat) (hn : Nowhere(s, k2)) :
      (let c = s; let b = Slot(&c, i); let q = BGetMut(b, k, h); *q := w; Nowhere(c, k2)) by s := (
    match s {
      SOne(b) => BGetMutAbsent(b, k, w, h, k2, hn),
      SCons(b, t) => match hn {
        Intro(hb, ht) => match i {
          Z => ⟨BGetMutAbsent(b, k, w, h, k2, hb), ht⟩,
          S i' => ⟨hb, NowhereGetMut(t, i', k, w, h, k2, ht)⟩,
        },
      },
    }
  )
  def OnlyInGetMut (s : Slots) (i : Nat) (d : Nat) (k : Nat) (w : Nat) (h : IsSome(BFind(Nth(s, i), k))) (k2 : Nat)
      (ho : OnlyIn(s, d, k2)) : (let c = s; let b = Slot(&c, i); let q = BGetMut(b, k, h); *q := w; OnlyIn(c, d, k2)) by s := (
    match s {
      SOne(b) => refl,
      SCons(b, t) => match d {
        Z => match i {
          Z => ho,
          S i' => NowhereGetMut(t, i', k, w, h, k2, ho),
        },
        S d' => match ho {
          Intro(hb, ht) => match i {
            Z => ⟨BGetMutAbsent(b, k, w, h, k2, hb), ht⟩,
            S i' => ⟨hb, OnlyInGetMut(t, i', d', k, w, h, k2, ht)⟩,
          },
        },
      },
    }
  )
  def SlotGetMutPlaced (s : Slots) (n : Nat) (k : Nat) (w : Nat) (h : IsSome(BFind(Nth(s, Idx(k, n)), k))) (hp : Placed(s, n)) :
      (let c = s; let b = Slot(&c, Idx(k, n)); let q = BGetMut(b, k, h); *q := w; Placed(c, n)) := (
    let c = s;
    let b = Slot(&c, Idx(k, n));
    let q = BGetMut(b, k, h);
    *q := w;
    λ(k2 : Nat) : OnlyIn(c, Idx(k2, n), k2) => OnlyInGetMut(s, Idx(k, n), Idx(k2, n), k, w, h, k2, hp(k2))
  )
  def GetMutInv (m : HashMap) (k : Nat) (w : Nat) (h : IsSome(Find(m, k))) (hi : Inv(m)) :
      (let c = m; let q = GetMut(&c, k, h); *q := w; Inv(c)) := (
    match m {
      HM(n, len, s) => match hi {
        Intro(hl, hr) => match hr {
          Intro(hu, hp) => (
            let cs = s;
            let b = Slot(&cs, Idx(k, n));
            let q = BGetMut(b, k, h);
            *q := w;
            let sc = s;
            ⟨J(Nat, Count(s), Count(cs), λ(z : Nat) : Prop => Eq Nat len z, SlotGetMutCount(&sc, Idx(k, n), k, w, h), hl),
             ⟨SlotGetMutUnique(s, Idx(k, n), k, w, h, hu), SlotGetMutPlaced(s, n, k, w, h, hp)⟩⟩
          ),
        },
      },
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
      HM(n, len, s) => MoveSlotsInv(s, New(S (Add(n, n))), NewInv(S (Add(n, n)))),
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

  def BFindLast (b : Bucket) (k : Nat) : Opt by b := (
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

  def SFindLast (s : Slots) (k : Nat) : Opt by s := (
    match s {
      SOne(b) => BFindLast(b, k),
      SCons(b, t) => OrElse(SFindLast(t, k), BFindLast(b, k)),
    }
  )

  def MoveBucketFind (b : Bucket) (m : HashMap) (k : Nat) :
      Id Opt (let c = m; MoveBucket(b, &c); Find(c, k)) (OrElse(BFindLast(b, k), Find(m, k))) by b := (
    match b {
      BNil => refl,
      BCons(k', v', t) => (
        let mc = m;
        let m2 = m;
        InsertNoResize(&m2, k', v');
        let mb = m;
        MoveBucket(b, &mb);
        let e = EqB(k', k);
        match e {
          false => J(Opt, Find(m2, k), Find(m, k), λ(z : Opt) : Prop => Eq Opt (Find(mb, k)) (OrElse(BFindLast(t, k), z)),
                     InsertFindOther(&mc, k', v', k, refl), MoveBucketFind(t, m2, k)),
          true => (
            let r = BFindLast(t, k);
            let found = J(Nat, k', k, λ(z : Nat) : Prop => Eq Opt (Find(m2, z)) (Some(v')), EqBSound(k', k, refl), InsertFind(&mc, k', v'));
            match r {
              None => J(Opt, Find(m2, k), Some(v'), λ(z : Opt) : Prop => Eq Opt (Find(mb, k)) (OrElse(BFindLast(t, k), z)),
                        found, MoveBucketFind(t, m2, k)),
              Some(_) => J(Opt, Find(m2, k), Some(v'), λ(z : Opt) : Prop => Eq Opt (Find(mb, k)) (OrElse(BFindLast(t, k), z)),
                           found, MoveBucketFind(t, m2, k)),
            }
          ),
        }
      ),
    }
  )
  def MoveSlotsFind (s : Slots) (m : HashMap) (k : Nat) :
      Id Opt (let c = m; MoveSlots(s, &c); Find(c, k)) (OrElse(SFindLast(s, k), Find(m, k))) by s := (
    match s {
      SOne(b) => MoveBucketFind(b, m, k),
      SCons(b, t) => (
        let mb = m;
        MoveBucket(b, &mb);
        let ms = m;
        MoveSlots(s, &ms);
        let r = SFindLast(t, k);
        match r {
          None => J(Opt, Find(mb, k), OrElse(BFindLast(b, k), Find(m, k)), λ(z : Opt) : Prop => Eq Opt (Find(ms, k)) (OrElse(SFindLast(t, k), z)),
                    MoveBucketFind(b, m, k), MoveSlotsFind(t, mb, k)),
          Some(_) => J(Opt, Find(mb, k), OrElse(BFindLast(b, k), Find(m, k)), λ(z : Opt) : Prop => Eq Opt (Find(ms, k)) (OrElse(SFindLast(t, k), z)),
                       MoveBucketFind(b, m, k), MoveSlotsFind(t, mb, k)),
        }
      ),
    }
  )

  def BFindLastNone (b : Bucket) (k : Nat) (h : Eq Opt (BFind(b, k)) None) : Eq Opt (BFindLast(b, k)) None by b := (
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

  def BFindLastUnique (b : Bucket) (k : Nat) (h : Unique(b)) : Eq Opt (BFindLast(b, k)) (BFind(b, k)) by b := (
    match b {
      BNil => refl,
      BCons(k', v', t) => match h {
        Intro(absent, rest) => (
          let e = EqB(k', k);
          match e {
            false => BFindLastUnique(t, k, rest),
            true => (
              let none = BFindLastNone(t, k, J(Nat, k', k, λ(z : Nat) : Prop => Eq Opt (BFind(t, z)) None, EqBSound(k', k, refl), absent));
              let r = BFindLast(t, k);
              match r {
                None => refl,
                Some(_) => match none {},
              }
            ),
          }
        ),
      },
    }
  )

  def NowhereLast (s : Slots) (k : Nat) (h : Nowhere(s, k)) : Eq Opt (SFindLast(s, k)) None by s := (
    match s {
      SOne(b) => BFindLastNone(b, k, h),
      SCons(b, t) => match h {
        Intro(hb, ht) => (
          let none = NowhereLast(t, k, ht);
          let r = SFindLast(t, k);
          match r {
            None => BFindLastNone(b, k, hb),
            Some(_) => match none {},
          }
        ),
      },
    }
  )

  def OnlyInLast (s : Slots) (d : Nat) (k : Nat) (h : OnlyIn(s, d, k)) (hu : AllUnique(s)) :
      Eq Opt (SFindLast(s, k)) (BFind(Nth(s, d), k)) by s := (
    match s {
      SOne(b) => BFindLastUnique(b, k, hu),
      SCons(b, t) => match hu {
        Intro(ub, ut) => match d {
          Z => (
            let none = NowhereLast(t, k, h);
            let r = SFindLast(t, k);
            match r {
              None => BFindLastUnique(b, k, ub),
              Some(_) => match none {},
            }
          ),
          S d' => match h {
            Intro(hb, ht) => (
              let ih = OnlyInLast(t, d', k, ht, ut);
              let r = SFindLast(t, k);
              match r {
                None => TransO(BFindLast(b, k), None, BFind(Nth(t, d'), k), BFindLastNone(b, k, hb), ih),
                Some(_) => ih,
              }
            ),
          },
        },
      },
    }
  )

  -- Resizing keeps every lookup, given the invariant.
  def ResizeFind (m : HashMap) (k : Nat) (h : Inv(m)) : Id Opt (let c = m; Resize(&c); Find(c, k)) (Find(m, k)) := (
    match m {
      HM(n, len, s) => match h {
        Intro(hl, hr) => match hr {
          Intro(hu, hp) => (
            let mc = m;
            Resize(&mc);
            let moved = J(Opt, Find(New(S (Add(n, n))), k), None, λ(z : Opt) : Prop => Eq Opt (Find(mc, k)) (OrElse(SFindLast(s, k), z)),
                          NewFind(S (Add(n, n)), k), MoveSlotsFind(s, New(S (Add(n, n))), k));
            let r = SFindLast(s, k);
            match r {
              None => TransO(Find(mc, k), None, BFind(Nth(s, Idx(k, n)), k), moved, OnlyInLast(s, Idx(k, n), k, hp(k), hu)),
              Some(x) => TransO(Find(mc, k), Some(x), BFind(Nth(s, Idx(k, n)), k), moved, OnlyInLast(s, Idx(k, n), k, hp(k), hu)),
            }
          ),
        },
      },
    }
  )
  -- ## Resizing keeps the length
  -- Each entry moved is new to the target, so each insert adds one. That needs the keys
  -- of the old table to be distinct across buckets, which follows from placement.
  def AddZero (x : Nat) : Id Nat (Add(x, 0)) x := AddMZero(&x)

  def AddAssoc (x : Nat) (y : Nat) (z : Nat) : Eq Nat (Add(Add(x, y), z)) (Add(x, Add(y, z))) by x := (
    match x {
      Z => refl,
      S x' => AddAssoc(x', y, z),
    }
  )

  def TransN (x : Nat) (y : Nat) (z : Nat) (h1 : Eq Nat x y) (h2 : Eq Nat y z) : Eq Nat x z := (
    J(Nat, y, z, λ(w : Nat) : Prop => Eq Nat x w, h2, h1)
  )

  -- The keys of `b` are absent from the map `m`.
  def Fresh (b : Bucket) (m : HashMap) : Prop by b := (
    match b {
      BNil => ⊤,
      BCons(k, v, t) => Eq Opt (Find(m, k)) None ∧ Fresh(t, m),
    }
  )

  def FreshInsert (t : Bucket) (m : HashMap) (k : Nat) (v : Nat) (h : Fresh(t, m)) (a : Eq Opt (BFind(t, k)) None) :
      (let c = m; InsertNoResize(&c, k, v); Fresh(t, c)) by t := (
    match t {
      BNil => refl,
      BCons(k2, v2, t2) => match h {
        Intro(f, ft) => (
          let e = EqB(k2, k);
          match e {
            false => (
              let mc = m;
              let m2 = m;
              InsertNoResize(&m2, k, v);
              ⟨TransO(Find(m2, k2), Find(m, k2), None, InsertFindOther(&mc, k, v, k2, NeqFlip(k2, k, refl)), f),
               FreshInsert(t2, m, k, v, ft, a)⟩
            ),
            true => match a {},
          }
        ),
      },
    }
  )

  -- Moving a bucket of fresh, distinct keys adds its length.
  def MoveBucketLen (b : Bucket) (m : HashMap) (hf : Fresh(b, m)) (hu : Unique(b)) :
      Id Nat (let c = m; MoveBucket(b, &c); Len(c)) (Add(Len(m), BLen(b))) by b := (
    match b {
      BNil => SymmN(Add(Len(m), 0), Len(m), AddZero(Len(m))),
      BCons(k, v, t) => match hf {
        Intro(f, ft) => match hu {
          Intro(a, ut) => (
            let mc = m;
            let m2 = m;
            InsertNoResize(&m2, k, v);
            let mb = m;
            MoveBucket(b, &mb);
            let grew = J(Opt, Find(m, k), None, λ(z : Opt) : Prop => Eq Nat (Len(m2)) (IfNew(z, Len(m))), f, InsertLen(&mc, k, v));
            let ih = MoveBucketLen(t, m2, FreshInsert(t, m, k, v, ft, a), ut);
            TransN(Len(mb), Add(S (Len(m)), BLen(t)), Add(Len(m), S (BLen(t))),
                   J(Nat, Len(m2), S (Len(m)), λ(z : Nat) : Prop => Eq Nat (Len(mb)) (Add(z, BLen(t))), grew, ih),
                   SymmN(Add(Len(m), S (BLen(t))), S (Add(Len(m), BLen(t))), AddS(Len(m), BLen(t))))
          ),
        },
      },
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
      BCons(k, v, r) => match hf {
        Intro(f, fr) => match ha {
          Intro(a, ar) => (
            let mb = m;
            MoveBucket(b, &mb);
            let none = BFindLastNone(b, k, a);
            let r0 = BFindLast(b, k);
            match r0 {
              None => ⟨TransO(Find(mb, k), Find(m, k), None, MoveBucketFind(b, m, k), f), FreshMove(r, b, m, fr, ar)⟩,
              Some(_) => match none {},
            }
          ),
        },
      },
    }
  )

  def FreshSMove (t : Slots) (b : Bucket) (m : HashMap) (hf : FreshS(t, m)) (ha : Apart(t, b)) :
      (let c = m; MoveBucket(b, &c); FreshS(t, c)) by t := (
    match t {
      SOne(b') => FreshMove(b', b, m, hf, ha),
      SCons(b', t') => match hf {
        Intro(fb, ft) => match ha {
          Intro(ab, ap) => ⟨FreshMove(b', b, m, fb, ab), FreshSMove(t', b, m, ft, ap)⟩,
        },
      },
    }
  )

  def MoveSlotsLen (s : Slots) (m : HashMap) (hf : FreshS(s, m)) (hg : GUnique(s)) :
      Id Nat (let c = m; MoveSlots(s, &c); Len(c)) (Add(Len(m), Count(s))) by s := (
    match s {
      SOne(b) => MoveBucketLen(b, m, hf, hg),
      SCons(b, t) => match hf {
        Intro(fb, ft) => match hg {
          Intro(ub, rest) => match rest {
            Intro(ap, gt) => (
              let mb = m;
              MoveBucket(b, &mb);
              let ms = m;
              MoveSlots(s, &ms);
              TransN(Len(ms), Add(Add(Len(m), BLen(b)), Count(t)), Add(Len(m), Add(BLen(b), Count(t))),
                     J(Nat, Len(mb), Add(Len(m), BLen(b)), λ(z : Nat) : Prop => Eq Nat (Len(ms)) (Add(z, Count(t))),
                       MoveBucketLen(b, m, fb, ub), MoveSlotsLen(t, mb, FreshSMove(t, b, m, ft, ap), gt)),
                     AddAssoc(Len(m), BLen(b), Count(t)))
            ),
          },
        },
      },
    }
  )

  -- A new map has no keys.
  def FreshNew (b : Bucket) (n : Nat) : Fresh(b, New(n)) by b := (
    match b {
      BNil => refl,
      BCons(k, v, t) => ⟨NewFind(n, k), FreshNew(t, n)⟩,
    }
  )

  def FreshSNew (s : Slots) (n : Nat) : FreshS(s, New(n)) by s := (
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
  def NowhereOnlyIn (t : Slots) (d : Nat) (k : Nat) (h : Nowhere(t, k)) : OnlyIn(t, d, k) by t := (
    match t {
      SOne(b) => refl,
      SCons(b, t') => match h {
        Intro(hb, ht) => match d {
          Z => ht,
          S d' => ⟨hb, NowhereOnlyIn(t', d', k, ht)⟩,
        },
      },
    }
  )

  -- The head key `k` of a bucket of `t` is not in `b`.
  def HeadApart (k : Nat) (v : Nat) (r : Bucket) (b : Bucket) (t : Slots) (D : Π(k : Nat). Nat)
      (hp : Π(k : Nat). OnlyIn(SCons(b, t), D(k), k))
      (hin : Π(k2 : Nat) (nw : Nowhere(t, k2)). Eq Opt (BFind(BCons(k, v, r), k2)) None) : Eq Opt (BFind(b, k)) None := (
    let dk = D(k);
    let p = hp(k);
    match dk {
      Z => (
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
      S _ => match p {
        Intro(a, rest) => a,
      },
    }
  )

  -- `cur` is (a suffix of) a bucket of `t`: a key nowhere in `t` is not in `cur`.
  def AbsentFromOf (cur : Bucket) (b : Bucket) (t : Slots) (D : Π(k : Nat). Nat)
      (hp : Π(k : Nat). OnlyIn(SCons(b, t), D(k), k))
      (hin : Π(k : Nat) (nw : Nowhere(t, k)). Eq Opt (BFind(cur, k)) None) : AbsentFrom(cur, b) by cur := (
    match cur {
      BNil => refl,
      BCons(k, v, r) => ⟨HeadApart(k, v, r, b, t, D, hp, hin),
        AbsentFromOf(r, b, t, D, hp, λ(k2 : Nat) (nw : Nowhere(t, k2)) : Eq Opt (BFind(r, k2)) None => (
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
  def ApartOfGo (u : Slots) (b : Bucket) (t : Slots) (D : Π(k : Nat). Nat)
      (hp : Π(k : Nat). OnlyIn(SCons(b, t), D(k), k))
      (hu : Π(k : Nat) (nw : Nowhere(t, k)). Nowhere(u, k)) : Apart(u, b) by u := (
    match u {
      SOne(b') => AbsentFromOf(b', b, t, D, hp, hu),
      SCons(b', u') => ⟨
        AbsentFromOf(b', b, t, D, hp, λ(k : Nat) (nw : Nowhere(t, k)) : Eq Opt (BFind(b', k)) None => (
          let p = hu(k, nw);
          match p {
            Intro(x, y) => x,
          }
        )),
        ApartOfGo(u', b, t, D, hp, λ(k : Nat) (nw : Nowhere(t, k)) : Nowhere(u', k) => (
          let p = hu(k, nw);
          match p {
            Intro(x, y) => y,
          }
        ))⟩,
    }
  )

  def TailOnlyIn (b : Bucket) (t : Slots) (d : Nat) (k : Nat) (h : OnlyIn(SCons(b, t), d, k)) : OnlyIn(t, Pred(d), k) := (
    match d {
      Z => NowhereOnlyIn(t, 0, k, h),
      S _ => match h {
        Intro(x, y) => y,
      },
    }
  )

  def GUniqueOf (s : Slots) (D : Π(k : Nat). Nat) (hp : Π(k : Nat). OnlyIn(s, D(k), k)) (hu : AllUnique(s)) : GUnique(s) by s := (
    match s {
      SOne(b) => hu,
      SCons(b, t) => match hu {
        Intro(ub, ut) => ⟨ub, ⟨
          ApartOfGo(t, b, t, D, hp, λ(k : Nat) (nw : Nowhere(t, k)) : Nowhere(t, k) => nw),
          GUniqueOf(t, λ(k : Nat) : Nat => Pred(D(k)), λ(k : Nat) : OnlyIn(t, Pred(D(k)), k) => TailOnlyIn(b, t, D(k), k, hp(k)), ut)⟩⟩,
      },
    }
  )

  -- Resizing keeps the length, given the invariant.
  def ResizeLen (m : HashMap) (h : Inv(m)) : Id Nat (let c = m; Resize(&c); Len(c)) (Len(m)) := (
    match m {
      HM(n, len, s) => match h {
        Intro(hl, hr) => match hr {
          Intro(hu, hp) => (
            let mc = m;
            Resize(&mc);
            TransN(Len(mc), Count(s), len,
                   MoveSlotsLen(s, New(S (Add(n, n))), FreshSNew(s, S (Add(n, n))), GUniqueOf(s, λ(k : Nat) : Nat => Idx(k, n), hp, hu)),
                   SymmN(len, Count(s), hl))
          ),
        },
      },
    }
  )

  -- ## Insert, with the resize
  -- Split on whether the entry was added and on whether the table is then full. When it
  -- is, the resize keeps the invariant, every lookup and the length, the last two under
  -- the invariant, which `InsertInv` gives for the map before the resize. The load factor is
  -- last.
  def InsertFindR (m : HashMap) (k : Nat) (v : Nat) (h : Inv(m)) :
      Id Opt (let c = m; Insert(&c, k, v); Find(c, k)) (Some(v)) := (
    match m {
      HM(n, len, s) => (
        let mc = m;
        let m2 = m;
        InsertNoResize(&m2, k, v);
        let m3 = m2;
        Resize(&m3);
        let cs = s;
        let b = Slot(&cs, Idx(k, n));
        let added = BInsert(b, k, v);
        match added {
          false => (
            let full = Lt(n, len);
            match full {
              false => InsertFind(&mc, k, v),
              true => TransO(Find(m3, k), Find(m2, k), Some(v), ResizeFind(m2, k, InsertInv(m, k, v, h)), InsertFind(&mc, k, v)),
            }
          ),
          true => (
            let full = Lt(n, S len);
            match full {
              false => InsertFind(&mc, k, v),
              true => TransO(Find(m3, k), Find(m2, k), Some(v), ResizeFind(m2, k, InsertInv(m, k, v, h)), InsertFind(&mc, k, v)),
            }
          ),
        }
      ),
    }
  )

  def InsertFindOtherR (m : HashMap) (k : Nat) (v : Nat) (k2 : Nat) (ne : Eq Bool (EqB(k, k2)) false) (h : Inv(m)) :
      Id Opt (let c = m; Insert(&c, k, v); Find(c, k2)) (Find(m, k2)) := (
    match m {
      HM(n, len, s) => (
        let mc = m;
        let m2 = m;
        InsertNoResize(&m2, k, v);
        let m3 = m2;
        Resize(&m3);
        let cs = s;
        let b = Slot(&cs, Idx(k, n));
        let added = BInsert(b, k, v);
        match added {
          false => (
            let full = Lt(n, len);
            match full {
              false => InsertFindOther(&mc, k, v, k2, ne),
              true => TransO(Find(m3, k2), Find(m2, k2), Find(m, k2), ResizeFind(m2, k2, InsertInv(m, k, v, h)), InsertFindOther(&mc, k, v, k2, ne)),
            }
          ),
          true => (
            let full = Lt(n, S len);
            match full {
              false => InsertFindOther(&mc, k, v, k2, ne),
              true => TransO(Find(m3, k2), Find(m2, k2), Find(m, k2), ResizeFind(m2, k2, InsertInv(m, k, v, h)), InsertFindOther(&mc, k, v, k2, ne)),
            }
          ),
        }
      ),
    }
  )

  -- The invariant.
  def InsertInvR (m : HashMap) (k : Nat) (v : Nat) (h : Inv(m)) : (let c = m; Insert(&c, k, v); Inv(c)) := (
    match m {
      HM(n, len, s) => (
        let cs = s;
        let b = Slot(&cs, Idx(k, n));
        let added = BInsert(b, k, v);
        let m2 = m;
        InsertNoResize(&m2, k, v);
        match added {
          false => (
            let full = Lt(n, len);
            match full {
              false => InsertInv(m, k, v, h),
              true => ResizeInv(m2),
            }
          ),
          true => (
            let full = Lt(n, S len);
            match full {
              false => InsertInv(m, k, v, h),
              true => ResizeInv(m2),
            }
          ),
        }
      ),
    }
  )

  -- The length grows by one exactly when the key was absent.
  def InsertLenR (m : HashMap) (k : Nat) (v : Nat) (h : Inv(m)) :
      Id Nat (let c = m; Insert(&c, k, v); Len(c)) (IfNew(Find(m, k), Len(m))) := (
    match m {
      HM(n, len, s) => (
        let mc = m;
        let m2 = m;
        InsertNoResize(&m2, k, v);
        let m3 = m2;
        Resize(&m3);
        let cs = s;
        let b = Slot(&cs, Idx(k, n));
        let added = BInsert(b, k, v);
        match added {
          false => (
            let full = Lt(n, len);
            match full {
              false => InsertLen(&mc, k, v),
              true => TransN(Len(m3), Len(m2), IfNew(Find(m, k), len), ResizeLen(m2, InsertInv(m, k, v, h)), InsertLen(&mc, k, v)),
            }
          ),
          true => (
            let full = Lt(n, S len);
            match full {
              false => InsertLen(&mc, k, v),
              true => TransN(Len(m3), Len(m2), IfNew(Find(m, k), len), ResizeLen(m2, InsertInv(m, k, v, h)), InsertLen(&mc, k, v)),
            }
          ),
        }
      ),
    }
  )

  -- ## The load factor
  -- The entries do not outnumber the buckets: `len ≤ n`, with `n + 1` buckets. `Insert`
  -- keeps it by resizing (as Aeneas's `hash_map_not_overloaded_lem`, with a load factor
  -- of 1 rather than a configurable fraction).
  def NOf (m : HashMap) : Nat := (
    match m {
      HM(n, len, s) => n,
    }
  )

  def NotOver (m : HashMap) : Prop := Eq Bool (Lt(NOf(m), Len(m))) false

  -- `a ≥ y` gives `a + 1 ≥ y`, `a + z ≥ y`, and `a ≥ y - 1`.
  def LtS (a : Nat) (y : Nat) (h : Eq Bool (Lt(a, y)) false) : Eq Bool (Lt(S a, y)) false by a := (
    match a {
      Z => match y {
        Z => refl,
        S _ => match h {},
      },
      S a' => match y {
        Z => refl,
        S y' => LtS(a', y', h),
      },
    }
  )

  def LtAdd (x : Nat) (y : Nat) (z : Nat) (h : Eq Bool (Lt(x, y)) false) : Eq Bool (Lt(Add(x, z), y)) false by x := (
    match x {
      Z => match y {
        Z => match z {
          Z => refl,
          S _ => refl,
        },
        S _ => match h {},
      },
      S x' => match y {
        Z => refl,
        S y' => LtAdd(x', y', z, h),
      },
    }
  )

  def LtPred (a : Nat) (y : Nat) (h : Eq Bool (Lt(a, y)) false) : Eq Bool (Lt(a, Pred(y))) false := (
    match y {
      Z => h,
      S y' => match a {
        Z => match h {},
        S a' => LtS(a', y', h),
      },
    }
  )

  -- Inserting and moving entries does not change the number of buckets; resizing sets it.
  def InsertN (m : HashMap) (k : Nat) (v : Nat) : Id Nat (let c = m; InsertNoResize(&c, k, v); NOf(c)) (NOf(m)) := (
    match m {
      HM(n, len, s) => (
        let cs = s;
        let b = Slot(&cs, Idx(k, n));
        let added = BInsert(b, k, v);
        match added {
          false => refl,
          true => refl,
        }
      ),
    }
  )

  def MoveBucketN (b : Bucket) (m : HashMap) : Id Nat (let c = m; MoveBucket(b, &c); NOf(c)) (NOf(m)) by b := (
    match b {
      BNil => refl,
      BCons(k, v, t) => (
        let m2 = m;
        InsertNoResize(&m2, k, v);
        let mb = m;
        MoveBucket(b, &mb);
        TransN(NOf(mb), NOf(m2), NOf(m), MoveBucketN(t, m2), InsertN(m, k, v))
      ),
    }
  )

  def MoveSlotsN (s : Slots) (m : HashMap) : Id Nat (let c = m; MoveSlots(s, &c); NOf(c)) (NOf(m)) by s := (
    match s {
      SOne(b) => MoveBucketN(b, m),
      SCons(b, t) => (
        let mb = m;
        MoveBucket(b, &mb);
        let ms = m;
        MoveSlots(s, &ms);
        TransN(NOf(ms), NOf(mb), NOf(m), MoveSlotsN(t, mb), MoveBucketN(b, m))
      ),
    }
  )

  def ResizeN (m : HashMap) : Id Nat (let c = m; Resize(&c); NOf(c)) (S (Add(NOf(m), NOf(m)))) := (
    match m {
      HM(n, len, s) => MoveSlotsN(s, New(S (Add(n, n)))),
    }
  )

  -- After a resize the bucket count is `2n + 2` and the length is unchanged, so the
  -- entries (at most `n + 1`) do not outnumber the buckets.
  def InsertNotOver (m : HashMap) (k : Nat) (v : Nat) (h : Inv(m)) (ho : NotOver(m)) :
      (let c = m; Insert(&c, k, v); NotOver(c)) := (
    match m {
      HM(n, len, s) => (
        let m2 = m;
        InsertNoResize(&m2, k, v);
        let m3 = m2;
        Resize(&m3);
        let cs = s;
        let b = Slot(&cs, Idx(k, n));
        let added = BInsert(b, k, v);
        match added {
          false => (
            let full = Lt(n, len);
            match full {
              false => refl,
              true => match ho {},
            }
          ),
          true => (
            let full = Lt(n, S len);
            match full {
              false => refl,
              true => J(Nat, Len(m2), Len(m3), λ(z : Nat) : Prop => Eq Bool (Lt(NOf(m3), z)) false,
                        SymmN(Len(m3), Len(m2), ResizeLen(m2, InsertInv(m, k, v, h))),
                        J(Nat, S (Add(n, n)), NOf(m3), λ(z : Nat) : Prop => Eq Bool (Lt(z, S len)) false,
                          SymmN(NOf(m3), S (Add(n, n)), ResizeN(m2)), LtAdd(n, len, n, ho))),
            }
          ),
        }
      ),
    }
  )

  def NewNotOver (n : Nat) : NotOver(New(n)) := (
    match n {
      Z => refl,
      S _ => refl,
    }
  )

  def RemoveNotOver (m : HashMap) (k : Nat) (ho : NotOver(m)) : (let c = m; Remove(&c, k); NotOver(c)) := (
    match m {
      HM(n, len, s) => (
        let cs = s;
        let b = Slot(&cs, Idx(k, n));
        let x = BRemove(b, k);
        match x {
          None => ho,
          Some(_) => LtPred(n, len, ho),
        }
      ),
    }
  )
  def GetMutNotOver (m : HashMap) (k : Nat) (w : Nat) (h : IsSome(Find(m, k))) (ho : NotOver(m)) :
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

#eval IO.println (run "HashMapResize" HashMapResize).show

-- every verdict as expected, and the exact number of declarations (a truncated file changes it)
#guard (run "HashMapResize" HashMapResize).allAsExpected
#guard (run "HashMapResize" HashMapResize).count == 87
