import Ochr.Test

/-! # The hashmap flagship (notes/hashmap-design.md, notes/hashmap-impl.md)

An Aeneas-style resizing hash table written as in-place Ochr code, with theorems about
that code (no pure model), inside the core calculus with no new rules. The slot "array"
is a non-empty list of buckets and the index borrow `NthM` saturates at the last slot,
so indexing is total without a bounds proof. -/

open Ochr.Test

ochr HashMap {
  inductive Bool := False | True
  inductive Opt := None | Some(v : Nat)
  inductive Bucket := BNil | BCons(k : Nat, v : Nat, t : Bucket)
  inductive Slots := SOne(b : Bucket) | SCons(b : Bucket, t : Slots)
  inductive HashMap := HM(n : Nat, len : Nat, slots : Slots)

  -- structural comparisons
  def EqB (a : Nat) (b : Nat) : Bool by a :=
    match a { Z => match b { Z => True | S _ => False } | S a' => match b { Z => False | S b' => EqB(a', b') } }
  def Lt (a : Nat) (b : Nat) : Bool by a :=
    match a { Z => match b { Z => False | S _ => True } | S a' => match b { Z => False | S b' => Lt(a', b') } }
  def AddM (x : &Nat) (y : Nat) : Unit by x := match *x { Z => *x := y | S p => AddM(&p, y) }
  def Add (x : Nat) (y : Nat) : Nat := AddM(&x, y); x

  -- the slot index: k mod (S n), by structural recursion on k with a running remainder
  def ModGo (k : Nat) (n : Nat) (r : Nat) : Nat by k :=
    match k { Z => r | S k' => let e = EqB(r, n); match e { False => ModGo(k', n, S r) | True => ModGo(k', n, 0) } }
  def Idx (k : Nat) (n : Nat) : Nat := ModGo(k, n, 0)

  -- the index borrow (Aeneas's Vec::index_mut): a returned borrow of slot i, saturating
  def NthM (s : &Slots) (i : Nat) : &Bucket by s :=
    match *s { SOne(b) => &b | SCons(b, t) => match i { Z => &b | S i' => NthM(&t, i') } }
  -- the pure read
  def Nth (s : Slots) (i : Nat) : Bucket by s :=
    match s { SOne(b) => b | SCons(b, t) => match i { Z => b | S i' => Nth(t, i') } }

  -- buckets: lookup through a borrow, insert/overwrite and remove in place
  def BGet (b : &Bucket) (k : Nat) : Opt by b :=
    match *b { BNil => None | BCons(k', v', t) => let e = EqB(k', k); match e { False => BGet(&t, k) | True => Some(v') } }
  def BInsertM (b : &Bucket) (k : Nat) (v : Nat) : Bool by b :=
    match *b {
      BNil => *b := BCons(k, v, BNil); True
    | BCons(k', v', t) => let e = EqB(k', k); match e { False => BInsertM(&t, k, v) | True => v' := v; False } }
  def BRemoveM (b : &Bucket) (k : Nat) : Bool by b :=
    match *b {
      BNil => False
    | BCons(k', v', t) => let e = EqB(k', k); match e { False => BRemoveM(&t, k) | True => *b := t; True } }

  -- the map
  def InsertNoResize (hm : &HashMap) (k : Nat) (v : Nat) : Unit :=
    match *hm { HM(n, len, slots) =>
      let r = NthM(&slots, Idx(k, n)); let added = BInsertM(r, k, v);
      match added { False => () | True => len := S len } }
  def Get (hm : &HashMap) (k : Nat) : Opt :=
    match *hm { HM(n, len, slots) => let r = NthM(&slots, Idx(k, n)); BGet(r, k) }
  def Pred (n : Nat) : Nat := match n { Z => 0 | S m => m }
  def Remove (hm : &HashMap) (k : Nat) : Unit :=
    match *hm { HM(n, len, slots) =>
      let r = NthM(&slots, Idx(k, n)); let removed = BRemoveM(r, k);
      match removed { False => () | True => len := Pred(len) } }

  -- sizes (pure)
  def BLen (b : Bucket) : Nat by b := match b { BNil => 0 | BCons(k, v, t) => S (BLen(t)) }
  def Count (s : Slots) : Nat by s := match s { SOne(b) => BLen(b) | SCons(b, t) => Add(BLen(b), Count(t)) }

  -- resizing: S n empty slots, re-insert every entry, double the slot count
  def EmptySlots (n : Nat) : Slots by n := match n { Z => SOne(BNil) | S m => SCons(BNil, EmptySlots(m)) }
  def New (n : Nat) : HashMap := HM(n, 0, EmptySlots(n))
  def MoveBucket (b : Bucket) (hm : &HashMap) : Unit by b :=
    match b { BNil => () | BCons(k, v, t) => InsertNoResize(&*hm, k, v); MoveBucket(t, hm) }
  def MoveSlots (s : Slots) (hm : &HashMap) : Unit by s :=
    match s { SOne(b) => MoveBucket(b, hm) | SCons(b, t) => MoveBucket(b, &*hm); MoveSlots(t, hm) }
  def Resize (hm : &HashMap) : Unit :=
    match *hm { HM(n, len, slots) =>
      let old = slots; let n2 = S (Add(n, n)); *hm := New(n2); MoveSlots(old, hm) }
  -- load factor 1: resize once the entries reach the slot count
  def Insert (hm : &HashMap) (k : Nat) (v : Nat) : Unit :=
    InsertNoResize(&*hm, k, v);
    match *hm { HM(n, len, slots) => let b = Lt(n, len); match b { False => () | True => Resize(&*hm) } }
  -- concrete runs (phase 1): insert three keys into a 2-slot table; the second insert
  -- reaches the load factor and resizes to 4 slots; every key is found again
  def RunLayout : Id HashMap
      (let m = New(1); Insert(&m, 1, 10); Insert(&m, 2, 20); Insert(&m, 3, 30); m)
      (HM(3, 3, SCons(BNil, SCons(BCons(1, 10, BNil), SCons(BCons(2, 20, BNil), SOne(BCons(3, 30, BNil))))))) := refl
  def RunGet1 : Id Opt (let m = New(1); Insert(&m, 1, 10); Insert(&m, 2, 20); Insert(&m, 3, 30); Get(&m, 1)) (Some(10)) := refl
  def RunGet2 : Id Opt (let m = New(1); Insert(&m, 1, 10); Insert(&m, 2, 20); Insert(&m, 3, 30); Get(&m, 2)) (Some(20)) := refl
  def RunGet3 : Id Opt (let m = New(1); Insert(&m, 1, 10); Insert(&m, 2, 20); Insert(&m, 3, 30); Get(&m, 3)) (Some(30)) := refl
  def RunGetAbsent : Id Opt (let m = New(1); Insert(&m, 1, 10); Insert(&m, 2, 20); Insert(&m, 3, 30); Get(&m, 5)) None := refl
  reject def RunGetWrong : Id Opt (let m = New(1); Insert(&m, 1, 10); Insert(&m, 2, 20); Insert(&m, 3, 30); Get(&m, 1)) (Some(20)) := refl
  -- overwriting keeps the length; a colliding key (5 = 1 mod 4) shares slot 1
  def RunOverwrite : Id Nat
      (let m = New(1); Insert(&m, 1, 10); Insert(&m, 2, 20); Insert(&m, 2, 25); match m { HM(n, len, s) => len }) 2 := refl
  def RunOverwriteGet : Id Opt
      (let m = New(1); Insert(&m, 1, 10); Insert(&m, 2, 20); Insert(&m, 2, 25); Get(&m, 2)) (Some(25)) := refl
  def RunCollide : Id HashMap
      (let m = New(3); Insert(&m, 1, 10); Insert(&m, 5, 50); m)
      (HM(3, 2, SCons(BNil, SCons(BCons(1, 10, BCons(5, 50, BNil)), SCons(BNil, SOne(BNil)))))) := refl
  -- remove: the key is gone, the other stays, the length drops; removing an absent key is a no-op
  def RunRemove : Id HashMap
      (let m = New(3); Insert(&m, 1, 10); Insert(&m, 5, 50); Remove(&m, 1); Remove(&m, 7); m)
      (HM(3, 1, SCons(BNil, SCons(BCons(5, 50, BNil), SCons(BNil, SOne(BNil)))))) := refl
  def RunRemoveGet : Id Opt
      (let m = New(3); Insert(&m, 1, 10); Insert(&m, 5, 50); Remove(&m, 1); Get(&m, 1)) None := refl
  -- the length field agrees with the count of entries after a mixed run
  def RunCount : Id Nat
      (let m = New(1); Insert(&m, 1, 10); Insert(&m, 2, 20); Insert(&m, 3, 30); Insert(&m, 7, 70); Remove(&m, 2);
       match m { HM(n, len, s) => len })
      (let m = New(1); Insert(&m, 1, 10); Insert(&m, 2, 20); Insert(&m, 3, 30); Insert(&m, 7, 70); Remove(&m, 2);
       match m { HM(n, len, s) => Count(s) }) := refl
  -- ## Phase 2: bucket-level theorems

  -- ex falso into Prop (E5's ExFalso, and its Bool forms) and facts about EqB
  def ExFalso (G : Prop) (h : Eq Nat Z (S Z)) : G :=
    J(Nat, Z, S Z, λ(n : Nat) : Prop => match n { Z => ⊤ | S _ => G }, h, refl)
  def ExFalsoFT (G : Prop) (h : Eq Bool False True) : G :=
    J(Bool, False, True, λ(z : Bool) : Prop => match z { False => ⊤ | True => G }, h, refl)
  def BoolAbsurd (x : Bool) (h1 : Id Bool x False) (h2 : Id Bool x True) : Eq Bool False True :=
    J(Bool, x, False, λ(z : Bool) : Prop => Id Bool z True, h1, h2)
  def EqBRefl (k : Nat) : Id Bool (EqB(k, k)) True by k := match k { Z => refl | S k' => EqBRefl(k') }
  def EqBSound (a : Nat) (b : Nat) (h : Id Bool (EqB(a, b)) True) : Id Nat a b by a :=
    match a {
      Z => match b { Z => refl | S _ => ExFalsoFT(Id Nat a b, h) }
    | S a' => match b {
        Z => ExFalsoFT(Id Nat a b, h)
      | S b' => J(Nat, a', b', λ(z : Nat) : Prop => Id Nat (S a') (S z), EqBSound(a', b', h), refl) } }
  def EqBTrans (a : Nat) (b : Nat) (c : Nat) (h1 : Id Bool (EqB(a, b)) True) (h2 : Id Bool (EqB(a, c)) True) :
      Id Bool (EqB(b, c)) True :=
    J(Nat, a, b, λ(z : Nat) : Prop => Id Bool (EqB(z, c)) True, EqBSound(a, b, h1), h2)

  -- H1: after inserting k, looking k up gives the inserted value
  def BInsertGet (b : &Bucket) (k : Nat) (v : Nat) :
      Id Opt (BInsertM(&*b, k, v); BGet(&*b, k)) (BInsertM(&*b, k, v); Some(v)) by b :=
    match *b {
      BNil => let e = EqB(k, k); match e {
          False => ExFalsoFT(Id Opt (BInsertM(&*b, k, v); BGet(&*b, k)) (BInsertM(&*b, k, v); Some(v)), EqBRefl(k))
        | True => refl }
    | BCons(k', v', t) => let e = EqB(k', k); match e { False => BInsertGet(&t, k, v) | True => refl } }

  -- H2: inserting k does not change the lookup of another key k2
  def BInsertGetOther (b : &Bucket) (k : Nat) (v : Nat) (k2 : Nat) (h : Id Bool (EqB(k, k2)) False) :
      Id Opt (BInsertM(&*b, k, v); BGet(&*b, k2)) (let r = BGet(&*b, k2); BInsertM(&*b, k, v); r) by b :=
    match *b {
      BNil => let e = EqB(k, k2); match e {
          False => refl
        | True => ExFalsoFT(Id Opt (BInsertM(&*b, k, v); BGet(&*b, k2)) (let r = BGet(&*b, k2); BInsertM(&*b, k, v); r),
                    BoolAbsurd(EqB(k, k2), h, refl)) }
    | BCons(k', v', t) => let e = EqB(k', k); match e {
        False => let e2 = EqB(k', k2); match e2 { False => BInsertGetOther(&t, k, v, k2, h) | True => refl }
      | True => let e2 = EqB(k', k2); match e2 {
          False => refl
        | True => ExFalsoFT(Id Opt (BInsertM(&*b, k, v); BGet(&*b, k2)) (let r = BGet(&*b, k2); BInsertM(&*b, k, v); r),
                    BoolAbsurd(EqB(k, k2), h, EqBTrans(k', k, k2, refl, refl))) } } }
  -- without the EqB lemma the fresh-bucket case does not check (EqB(k, k) is stuck on an abstract k)
  reject def BInsertGetNoLemma (b : &Bucket) (k : Nat) (v : Nat) :
      Id Opt (BInsertM(&*b, k, v); BGet(&*b, k)) (BInsertM(&*b, k, v); Some(v)) by b :=
    match *b { BNil => refl | BCons(k', v', t) => let e = EqB(k', k); match e { False => BInsertGetNoLemma(&t, k, v) | True => refl } }
  reject def BInsertGetWrongValue (b : &Bucket) (k : Nat) (v : Nat) :
      Id Opt (BInsertM(&*b, k, v); BGet(&*b, k)) (BInsertM(&*b, k, v); Some(k)) by b :=
    match *b {
      BNil => let e = EqB(k, k); match e {
          False => ExFalsoFT(Id Opt (BInsertM(&*b, k, v); BGet(&*b, k)) (BInsertM(&*b, k, v); Some(k)), EqBRefl(k))
        | True => refl }
    | BCons(k', v', t) => let e = EqB(k', k); match e { False => BInsertGetWrongValue(&t, k, v) | True => refl } }
  -- without k ≠ k2 the lookup of k2 can change
  reject def BInsertGetOtherNoHyp (b : &Bucket) (k : Nat) (v : Nat) (k2 : Nat) :
      Id Opt (BInsertM(&*b, k, v); BGet(&*b, k2)) (let r = BGet(&*b, k2); BInsertM(&*b, k, v); r) by b :=
    match *b {
      BNil => let e = EqB(k, k2); match e { False => refl | True => refl }
    | BCons(k', v', t) => let e = EqB(k', k); match e {
        False => let e2 = EqB(k', k2); match e2 { False => BInsertGetOtherNoHyp(&t, k, v, k2) | True => refl }
      | True => let e2 = EqB(k', k2); match e2 { False => refl | True => refl } } }

  -- remove. Buckets may hold a key twice in general (only insert keeps them duplicate-free),
  -- so "remove k, then k is gone" needs k to occur at most once
  def BAbsent (b : Bucket) (k : Nat) : Prop by b :=
    match b { BNil => ⊤ | BCons(k', v', t) => let e = EqB(k', k); match e { False => BAbsent(t, k) | True => Eq Nat Z (S Z) } }
  def AtMostOnce (b : Bucket) (k : Nat) : Prop by b :=
    match b { BNil => ⊤ | BCons(k', v', t) => let e = EqB(k', k); match e { False => AtMostOnce(t, k) | True => BAbsent(t, k) } }
  def BGetAbsent (b : &Bucket) (k : Nat) (h : BAbsent(*b, k)) : Id Opt (BGet(&*b, k)) None by b :=
    match *b {
      BNil => refl
    | BCons(k', v', t) => let e = EqB(k', k); match e { False => BGetAbsent(&t, k, h) | True => ExFalso(Id Opt (BGet(&*b, k)) None, h) } }
  -- H1': after removing k, looking k up gives None. The found case uses the lemma on a copy of
  -- the tail (a place the proof owns), so that its footprint is the tail, not the whole cell
  def BRemoveGet (b : &Bucket) (k : Nat) (h : AtMostOnce(*b, k)) :
      Id Opt (BRemoveM(&*b, k); BGet(&*b, k)) (BRemoveM(&*b, k); None) by b :=
    match *b {
      BNil => refl
    | BCons(k', v', t) => let e = EqB(k', k); match e { False => BRemoveGet(&t, k, h) | True => let c = t; BGetAbsent(&c, k, h) } }
  reject def BRemoveGetNoHyp (b : &Bucket) (k : Nat) :
      Id Opt (BRemoveM(&*b, k); BGet(&*b, k)) (BRemoveM(&*b, k); None) by b :=
    match *b {
      BNil => refl
    | BCons(k', v', t) => let e = EqB(k', k); match e { False => BRemoveGetNoHyp(&t, k) | True => refl } }
  -- H2': removing k does not change the lookup of another key k2
  def BRemoveGetOther (b : &Bucket) (k : Nat) (k2 : Nat) (h : Id Bool (EqB(k, k2)) False) :
      Id Opt (BRemoveM(&*b, k); BGet(&*b, k2)) (let r = BGet(&*b, k2); BRemoveM(&*b, k); r) by b :=
    match *b {
      BNil => refl
    | BCons(k', v', t) => let e = EqB(k', k); match e {
        False => let e2 = EqB(k', k2); match e2 { False => BRemoveGetOther(&t, k, k2, h) | True => refl }
      | True => let e2 = EqB(k', k2); match e2 {
          False => refl
        | True => ExFalsoFT(Id Opt (BRemoveM(&*b, k); BGet(&*b, k2)) (let r = BGet(&*b, k2); BRemoveM(&*b, k); r),
                    BoolAbsurd(EqB(k, k2), h, EqBTrans(k', k, k2, refl, refl))) } } }
  -- ## Phase 3: the index borrow (slot level)

  def Le (a : Nat) (b : Nat) : Prop by a :=
    match a { Z => ⊤ | S a' => match b { Z => Eq Nat Z (S Z) | S b' => Le(a', b') } }
  def Last (s : Slots) : Nat by s := match s { SOne(b) => 0 | SCons(b, t) => S (Last(t)) }

  -- H3a: writing through NthM(s, i), then reading slot i, gives the written bucket
  def NthWriteSame (s : &Slots) (i : Nat) (x : Bucket) :
      Id Bucket (let r = NthM(&*s, i); *r := x; Nth(*s, i)) (let r = NthM(&*s, i); *r := x; x) by s :=
    match *s { SOne(b) => refl | SCons(b, t) => match i { Z => refl | S i' => NthWriteSame(&t, i', x) } }
  -- H3b: ... and slot j ≠ i is unchanged, when both are in range (the index saturates)
  def NthWriteOther (s : &Slots) (i : Nat) (j : Nat) (x : Bucket) (h : Id Bool (EqB(i, j)) False)
      (hi : Le(i, Last(*s))) (hj : Le(j, Last(*s))) :
      Id Bucket (let r = NthM(&*s, i); *r := x; Nth(*s, j)) (let v = Nth(*s, j); let r = NthM(&*s, i); *r := x; v) by s :=
    match *s {
      SOne(b) => match i {
          Z => match j {
              Z => ExFalsoFT(Id Bucket (let r = NthM(&*s, i); *r := x; Nth(*s, j)) (let v = Nth(*s, j); let r = NthM(&*s, i); *r := x; v),
                     BoolAbsurd(EqB(i, j), h, refl))
            | S _ => ExFalso(Id Bucket (let r = NthM(&*s, i); *r := x; Nth(*s, j)) (let v = Nth(*s, j); let r = NthM(&*s, i); *r := x; v), hj) }
        | S _ => ExFalso(Id Bucket (let r = NthM(&*s, i); *r := x; Nth(*s, j)) (let v = Nth(*s, j); let r = NthM(&*s, i); *r := x; v), hi) }
    | SCons(b, t) => match i {
          Z => match j {
              Z => ExFalsoFT(Id Bucket (let r = NthM(&*s, i); *r := x; Nth(*s, j)) (let v = Nth(*s, j); let r = NthM(&*s, i); *r := x; v),
                     BoolAbsurd(EqB(i, j), h, refl))
            | S _ => refl }
        | S i' => match j { Z => refl | S j' => NthWriteOther(&t, i', j', x, h, hi, hj) } } }
  -- out of range the index saturates: two different indices past the end hit the same slot
  reject def NthWriteOtherNoRange (s : &Slots) (i : Nat) (j : Nat) (x : Bucket) (h : Id Bool (EqB(i, j)) False) :
      Id Bucket (let r = NthM(&*s, i); *r := x; Nth(*s, j)) (let v = Nth(*s, j); let r = NthM(&*s, i); *r := x; v) by s :=
    match *s {
      SOne(b) => refl
    | SCons(b, t) => match i {
          Z => match j { Z => ExFalsoFT(Id Bucket (let r = NthM(&*s, i); *r := x; Nth(*s, j)) (let v = Nth(*s, j); let r = NthM(&*s, i); *r := x; v),
                                 BoolAbsurd(EqB(i, j), h, refl)) | S _ => refl }
        | S i' => match j { Z => refl | S j' => NthWriteOtherNoRange(&t, i', j', x, h) } } }

  -- ## Phase 4: map level

  -- H1 lifted through the index borrow, by recursion on the slots: the environment carries
  -- the untouched slots, so no congruence lemma and no H3 is needed
  def NthInsertGet (s : &Slots) (i : Nat) (k : Nat) (v : Nat) :
      Id Opt (let r = NthM(&*s, i); BInsertM(r, k, v); let r2 = NthM(&*s, i); BGet(r2, k))
             (let r = NthM(&*s, i); BInsertM(r, k, v); Some(v)) by s :=
    match *s {
      SOne(b) => BInsertGet(&b, k, v)
    | SCons(b, t) => match i { Z => BInsertGet(&b, k, v) | S i' => NthInsertGet(&t, i', k, v) } }
  -- H4 for InsertNoResize: split on the map and on whether the key was added (reproducing
  -- the sealed `added` on a copy of the slots), then the slot lemma on a copy of the map
  -- with the new length, so that the lemma observes a whole map
  def InsertGet (hm : &HashMap) (k : Nat) (v : Nat) :
      Id Opt (InsertNoResize(&*hm, k, v); Get(&*hm, k)) (InsertNoResize(&*hm, k, v); Some(v)) :=
    match *hm { HM(n, len, slots) =>
      let c = slots; let r = NthM(&c, Idx(k, n)); let a = BInsertM(r, k, v);
      match a {
        False => let d = HM(n, len, slots); match d { HM(n2, l2, s2) => NthInsertGet(&s2, Idx(k, n), k, v) }
      | True => let d = HM(n, S len, slots); match d { HM(n2, l2, s2) => NthInsertGet(&s2, Idx(k, n), k, v) } } }
  -- the length update matters: swapping the two arms is rejected
  reject def InsertGetSwapLen (hm : &HashMap) (k : Nat) (v : Nat) :
      Id Opt (InsertNoResize(&*hm, k, v); Get(&*hm, k)) (InsertNoResize(&*hm, k, v); Some(v)) :=
    match *hm { HM(n, len, slots) =>
      let c = slots; let r = NthM(&c, Idx(k, n)); let a = BInsertM(r, k, v);
      match a {
        False => let d = HM(n, S len, slots); match d { HM(n2, l2, s2) => NthInsertGet(&s2, Idx(k, n), k, v) }
      | True => let d = HM(n, len, slots); match d { HM(n2, l2, s2) => NthInsertGet(&s2, Idx(k, n), k, v) } } }

  -- H2 lifted through the index borrow (write at i, read at j): the same bucket is H2,
  -- different buckets commute by computation
  def NthInsertGetOther (s : &Slots) (i : Nat) (j : Nat) (k : Nat) (v : Nat) (k2 : Nat) (h : Id Bool (EqB(k, k2)) False) :
      Id Opt (let r = NthM(&*s, i); BInsertM(r, k, v); let r2 = NthM(&*s, j); BGet(r2, k2))
             (let r2 = NthM(&*s, j); let x = BGet(r2, k2); let r = NthM(&*s, i); BInsertM(r, k, v); x) by s :=
    match *s {
      SOne(b) => BInsertGetOther(&b, k, v, k2, h)
    | SCons(b, t) => match i {
        Z => match j { Z => BInsertGetOther(&b, k, v, k2, h) | S j' => refl }
      | S i' => match j { Z => refl | S j' => NthInsertGetOther(&t, i', j', k, v, k2, h) } } }
  -- finding F1 at the map level: in the RHS the lookup runs first, so the insert's `added`
  -- is computed from the bucket's read-residue, a different sealed program; these two
  -- lemmas say the insert's result does not see a previous lookup (on copies, so their
  -- footprints are unchanged and their types are one equation)
  def BInsertAfterGet (b : &Bucket) (k : Nat) (v : Nat) (k2 : Nat) :
      Id Bool (let c = *b; BInsertM(&c, k, v)) (let c = *b; BGet(&c, k2); BInsertM(&c, k, v)) by b :=
    match *b {
      BNil => refl
    | BCons(k', v', t) => let e2 = EqB(k', k2); match e2 {
        False => let e = EqB(k', k); match e { False => BInsertAfterGet(&t, k, v, k2) | True => refl }
      | True => refl } }
  def NthInsertAfterGet (s : &Slots) (i : Nat) (j : Nat) (k : Nat) (v : Nat) (k2 : Nat) :
      Id Bool (let c = *s; let r = NthM(&c, i); BInsertM(r, k, v))
              (let c = *s; let r0 = NthM(&c, j); BGet(r0, k2); let r = NthM(&c, i); BInsertM(r, k, v)) by s :=
    match *s {
      SOne(b) => BInsertAfterGet(&b, k, v, k2)
    | SCons(b, t) => match i {
        Z => match j { Z => BInsertAfterGet(&b, k, v, k2) | S j' => refl }
      | S i' => match j { Z => refl | S j' => NthInsertAfterGet(&t, i', j', k, v, k2) } } }
  -- H5 for InsertNoResize: split on the two `added` programs (the LHS's, and the RHS's
  -- after the lookup); the mixed arms contradict NthInsertAfterGet
  def InsertGetOther (hm : &HashMap) (k : Nat) (v : Nat) (k2 : Nat) (h : Id Bool (EqB(k, k2)) False) :
      Id Opt (InsertNoResize(&*hm, k, v); Get(&*hm, k2)) (let r = Get(&*hm, k2); InsertNoResize(&*hm, k, v); r) :=
    match *hm { HM(n, len, slots) =>
      let c = slots; let r = NthM(&c, Idx(k, n)); let a = BInsertM(r, k, v);
      let c2 = slots; let r0 = NthM(&c2, Idx(k2, n)); let x = BGet(r0, k2); let r2 = NthM(&c2, Idx(k, n)); let a2 = BInsertM(r2, k, v);
      let c3 = slots; let p = NthInsertAfterGet(&c3, Idx(k, n), Idx(k2, n), k, v, k2);
      match a {
        False => match a2 {
            False => let d = HM(n, len, slots); match d { HM(n2, l2, s2) => NthInsertGetOther(&s2, Idx(k, n), Idx(k2, n), k, v, k2, h) }
          | True => ExFalsoFT(Id Opt (InsertNoResize(&*hm, k, v); Get(&*hm, k2)) (let r = Get(&*hm, k2); InsertNoResize(&*hm, k, v); r), p) }
      | True => match a2 {
            False => ExFalsoFT(Id Opt (InsertNoResize(&*hm, k, v); Get(&*hm, k2)) (let r = Get(&*hm, k2); InsertNoResize(&*hm, k, v); r),
                       BoolAbsurd(a, p, refl))
          | True => let d = HM(n, S len, slots); match d { HM(n2, l2, s2) => NthInsertGetOther(&s2, Idx(k, n), Idx(k2, n), k, v, k2, h) } } } }
  -- without NthInsertAfterGet the mixed arms (the two `added` disagree) do not check
  reject def InsertGetOtherNoIndep (hm : &HashMap) (k : Nat) (v : Nat) (k2 : Nat) (h : Id Bool (EqB(k, k2)) False) :
      Id Opt (InsertNoResize(&*hm, k, v); Get(&*hm, k2)) (let r = Get(&*hm, k2); InsertNoResize(&*hm, k, v); r) :=
    match *hm { HM(n, len, slots) =>
      let c = slots; let r = NthM(&c, Idx(k, n)); let a = BInsertM(r, k, v);
      let c2 = slots; let r0 = NthM(&c2, Idx(k2, n)); let x = BGet(r0, k2); let r2 = NthM(&c2, Idx(k, n)); let a2 = BInsertM(r2, k, v);
      match a {
        False => match a2 {
            False => let d = HM(n, len, slots); match d { HM(n2, l2, s2) => NthInsertGetOther(&s2, Idx(k, n), Idx(k2, n), k, v, k2, h) }
          | True => refl }
      | True => match a2 {
            False => refl
          | True => let d = HM(n, S len, slots); match d { HM(n2, l2, s2) => NthInsertGetOther(&s2, Idx(k, n), Idx(k2, n), k, v, k2, h) } } } }

  -- ## Phase 5: the length invariant len = Count(slots)

  -- x + S y = S (x + y), in place by bare recursion (as in Inductives.lean), both orientations
  def AddMS (x : &Nat) (y : Nat) : Id Unit (AddM(&*x, y); *x := S *x) (AddM(x, S y)) by x :=
    match *x { Z => refl | S p => AddMS(&p, y) }
  def AddS (x : Nat) (y : Nat) : Id Nat (S (Add(x, y))) (Add(x, S y)) := AddMS(&x, y)
  def SymmN (x : Nat) (y : Nat) (h : Id Nat x y) : Id Nat y x := J(Nat, x, y, λ(z : Nat) : Prop => Id Nat z x, h, refl)

  -- a bucket grows by one exactly when the insert added the key. `Bump` is a helper, not an
  -- inline match: an inline `match a {…}` in the statement is split while the type is
  -- formed, which generalises the sealed `a` for good, and the later split on the bucket
  -- cannot reach it (finding F2; `BInsertLenInline` below)
  def Bump (a : Bool) (n : Nat) : Nat := match a { False => n | True => S n }
  -- F2 in miniature: IsZ(x) is sealed at the generic call; forming the type splits the
  -- inline match on it, generalising ⌈IsZ(σx)⌉ to a fresh σ for good, so the later split
  -- x := Z cannot reach the block. The same statement through a helper function is proved
  def IsZ (x : Nat) : Bool := match x { Z => True | S _ => False }
  def B2N (a : Bool) : Nat := match a { False => 0 | True => 1 }
  reject def InlineLost (x : Nat) : Id Nat (let a = IsZ(x); match a { False => 0 | True => 1 }) (match x { Z => 1 | S _ => 0 }) :=
    match x { Z => refl | S _ => refl }
  def HelperKept (x : Nat) : Id Nat (let a = IsZ(x); B2N(a)) (match x { Z => 1 | S _ => 0 }) :=
    match x { Z => refl | S _ => refl }
  def BInsertLen (b : &Bucket) (k : Nat) (v : Nat) :
      Id Nat (let c = *b; let a = BInsertM(&c, k, v); Bump(a, BLen(*b))) (let c = *b; let a = BInsertM(&c, k, v); BLen(c)) by b :=
    match *b {
      BNil => refl
    | BCons(k', v', t) => let e = EqB(k', k); match e {
        True => refl
      | False => let t0 = t; let ct = t; let a = BInsertM(&ct, k, v); let L = BLen(ct); match a {
          False => J(Nat, BLen(t0), L, λ(z : Nat) : Prop => Id Nat (S (BLen(t0))) (S z), BInsertLen(&t, k, v), refl)
        | True => J(Nat, S (BLen(t0)), L, λ(z : Nat) : Prop => Id Nat (S (S (BLen(t0)))) (S z), BInsertLen(&t, k, v), refl) } } }
  reject def BInsertLenInline (b : &Bucket) (k : Nat) (v : Nat) :
      Id Nat (let c = *b; let a = BInsertM(&c, k, v); match a { False => BLen(*b) | True => S (BLen(*b)) })
             (let c = *b; let a = BInsertM(&c, k, v); BLen(c)) by b :=
    match *b {
      BNil => refl
    | BCons(k', v', t) => let e = EqB(k', k); match e {
        True => refl
      | False => let t0 = t; let ct = t; let a = BInsertM(&ct, k, v); let L = BLen(ct); match a {
          False => J(Nat, BLen(t0), L, λ(z : Nat) : Prop => Id Nat (S (BLen(t0))) (S z), BInsertLenInline(&t, k, v), refl)
        | True => J(Nat, S (BLen(t0)), L, λ(z : Nat) : Prop => Id Nat (S (S (BLen(t0)))) (S z), BInsertLenInline(&t, k, v), refl) } } }
  -- ... lifted through the index borrow; Count sums with Add, so each arm rewrites once
  def NthInsertCount (s : &Slots) (i : Nat) (k : Nat) (v : Nat) :
      Id Nat (let c = *s; let r = NthM(&c, i); let a = BInsertM(r, k, v); Bump(a, Count(*s)))
             (let c = *s; let r = NthM(&c, i); let a = BInsertM(r, k, v); Count(c)) by s :=
    match *s {
      SOne(b) => BInsertLen(&b, k, v)
    | SCons(b, t) => let b0 = b; let t0 = t; match i {
        Z => let cb = b; let a = BInsertM(&cb, k, v); let L = BLen(cb); match a {
            False => J(Nat, BLen(b0), L, λ(z : Nat) : Prop => Id Nat (Add(BLen(b0), Count(t0))) (Add(z, Count(t0))), BInsertLen(&b, k, v), refl)
          | True => J(Nat, S (BLen(b0)), L, λ(z : Nat) : Prop => Id Nat (S (Add(BLen(b0), Count(t0)))) (Add(z, Count(t0))), BInsertLen(&b, k, v), refl) }
      | S i' => let ct = t; let r = NthM(&ct, i'); let a = BInsertM(r, k, v); let C = Count(ct); match a {
            False => J(Nat, Count(t0), C, λ(z : Nat) : Prop => Id Nat (Add(BLen(b0), Count(t0))) (Add(BLen(b0), z)), NthInsertCount(&t, i', k, v), refl)
          | True => J(Nat, S (Count(t0)), C, λ(z : Nat) : Prop => Id Nat (S (Add(BLen(b0), Count(t0)))) (Add(BLen(b0), z)),
                      NthInsertCount(&t, i', k, v), AddS(BLen(b0), Count(t0))) } } }
  -- H6 for InsertNoResize: len = Count(slots) is preserved. Split on the map and on `added`;
  -- the slot lemma on a copy of the slots, and one or two J steps against the hypothesis
  def Len (m : HashMap) : Nat := match m { HM(n, len, s) => len }
  def CountHM (m : HashMap) : Nat := match m { HM(n, len, s) => Count(s) }
  def InsertLen (hm : &HashMap) (k : Nat) (v : Nat) (h : Id Nat (Len(*hm)) (CountHM(*hm))) :
      Id Nat (InsertNoResize(&*hm, k, v); Len(*hm)) (InsertNoResize(&*hm, k, v); CountHM(*hm)) :=
    match *hm { HM(n, len, slots) =>
      let l0 = len; let s0 = slots;
      let c = slots; let r = NthM(&c, Idx(k, n)); let a = BInsertM(r, k, v); let C = Count(c);
      let c3 = slots; let p = NthInsertCount(&c3, Idx(k, n), k, v);
      match a {
        False => J(Nat, Count(s0), C, λ(z : Nat) : Prop => Id Nat l0 z, p, h)
      | True => J(Nat, S (Count(s0)), C, λ(z : Nat) : Prop => Id Nat (S l0) z, p,
                  J(Nat, l0, Count(s0), λ(z : Nat) : Prop => Id Nat (S l0) (S z), h, refl)) } }
  -- the invariant is needed: without h the arms do not check
  reject def InsertLenNoHyp (hm : &HashMap) (k : Nat) (v : Nat) :
      Id Nat (InsertNoResize(&*hm, k, v); Len(*hm)) (InsertNoResize(&*hm, k, v); CountHM(*hm)) :=
    match *hm { HM(n, len, slots) =>
      let c3 = slots; let p = NthInsertCount(&c3, Idx(k, n), k, v); p }

  -- remove: the bucket shrinks by one exactly when the key was removed.
  -- Finding F3 (checker gap, lean-checker §11.2): a λ that captures a computed local (a
  -- sealed value) and uses it in a typed position cannot be formed, since captured values
  -- carry no type in the checker; RULES accepts it. So congruence under S is a lemma
  reject def CaptureSealed (x : Nat) (y : Nat) (h : Id Nat (Add(x, y)) y) : Id Nat (S (Add(x, y))) (S y) :=
    let L = Add(x, y); J(Nat, L, y, λ(z : Nat) : Prop => Id Nat (S L) (S z), h, refl)
  def CongS (x : Nat) (y : Nat) (h : Id Nat x y) : Id Nat (S x) (S y) :=
    J(Nat, x, y, λ(z : Nat) : Prop => Id Nat (S x) (S z), h, refl)
  def CaptureSealedLemma (x : Nat) (y : Nat) (h : Id Nat (Add(x, y)) y) : Id Nat (S (Add(x, y))) (S y) :=
    CongS(Add(x, y), y, h)
  def BRemoveLen (b : &Bucket) (k : Nat) :
      Id Nat (let c = *b; let a = BRemoveM(&c, k); Bump(a, BLen(c))) (BLen(*b)) by b :=
    match *b {
      BNil => refl
    | BCons(k', v', t) => let e = EqB(k', k); match e {
        True => refl
      | False => let ct = t; let a = BRemoveM(&ct, k); match a {
          False => CongS(BLen(ct), BLen(t), BRemoveLen(&t, k))
        | True => CongS(S (BLen(ct)), BLen(t), BRemoveLen(&t, k)) } } }
  def CongAddL (x : Nat) (y : Nat) (w : Nat) (h : Id Nat x y) : Id Nat (Add(x, w)) (Add(y, w)) :=
    J(Nat, x, y, λ(z : Nat) : Prop => Id Nat (Add(x, w)) (Add(z, w)), h, refl)
  def CongAddR (w : Nat) (x : Nat) (y : Nat) (h : Id Nat x y) : Id Nat (Add(w, x)) (Add(w, y)) :=
    J(Nat, x, y, λ(z : Nat) : Prop => Id Nat (Add(w, x)) (Add(w, z)), h, refl)
  def TransN (x : Nat) (y : Nat) (z : Nat) (h1 : Id Nat x y) (h2 : Id Nat y z) : Id Nat x z :=
    J(Nat, y, z, λ(w : Nat) : Prop => Id Nat x w, h2, h1)
  def NthRemoveCount (s : &Slots) (i : Nat) (k : Nat) :
      Id Nat (let c = *s; let r = NthM(&c, i); let a = BRemoveM(r, k); Bump(a, Count(c))) (Count(*s)) by s :=
    match *s {
      SOne(b) => BRemoveLen(&b, k)
    | SCons(b, t) => let b0 = b; let t0 = t; match i {
        Z => let cb = b; let a = BRemoveM(&cb, k); let L = BLen(cb); match a {
            False => CongAddL(L, BLen(b0), Count(t0), BRemoveLen(&b, k))
          | True => CongAddL(S L, BLen(b0), Count(t0), BRemoveLen(&b, k)) }
      | S i' => let ct = t; let r = NthM(&ct, i'); let a = BRemoveM(r, k); let C = Count(ct); match a {
            False => CongAddR(BLen(b0), C, Count(t0), NthRemoveCount(&t, i', k))
          | True => TransN(S (Add(BLen(b0), C)), Add(BLen(b0), S C), Add(BLen(b0), Count(t0)),
                      AddS(BLen(b0), C), CongAddR(BLen(b0), S C, Count(t0), NthRemoveCount(&t, i', k))) } } }
  def CongPred (x : Nat) (y : Nat) (h : Id Nat x y) : Id Nat (Pred(x)) (Pred(y)) :=
    J(Nat, x, y, λ(z : Nat) : Prop => Id Nat (Pred(x)) (Pred(z)), h, refl)
  -- H6 for Remove (len := Pred(len) when removed)
  def RemoveLen (hm : &HashMap) (k : Nat) (h : Id Nat (Len(*hm)) (CountHM(*hm))) :
      Id Nat (Remove(&*hm, k); Len(*hm)) (Remove(&*hm, k); CountHM(*hm)) :=
    match *hm { HM(n, len, slots) =>
      let l0 = len; let s0 = slots;
      let c = slots; let r = NthM(&c, Idx(k, n)); let a = BRemoveM(r, k); let C = Count(c);
      let c3 = slots; let p = NthRemoveCount(&c3, Idx(k, n), k);
      match a {
        False => TransN(l0, Count(s0), C, h, SymmN(C, Count(s0), p))
      | True => CongPred(l0, S C, TransN(l0, Count(s0), S C, h, SymmN(S C, Count(s0), p))) } }
}

#eval IO.println (run "HashMap" HashMap).show

-- every verdict as expected, and exactly 95 assertions (a truncated file changes the count)
#guard (run "HashMap" HashMap).allAsExpected
#guard (run "HashMap" HashMap).count == 95
