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
}

#eval IO.println (run "HashMap" HashMap).show

-- every verdict as expected, and exactly 57 assertions (a truncated file changes the count)
#guard (run "HashMap" HashMap).allAsExpected
#guard (run "HashMap" HashMap).count == 57
