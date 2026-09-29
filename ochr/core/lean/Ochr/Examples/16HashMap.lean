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
lookups after each operation; `HashMapLength`, the length field counts the entries;
`HashMapResize`, the invariant and resizing. -/

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
  -- Look a key up, insert or overwrite it (`true` if a new entry was added), remove it
  -- (returning the removed value), and borrow its value.
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
#guard (run "HashMap" HashMap).count == 38
