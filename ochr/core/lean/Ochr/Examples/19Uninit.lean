import Ochr.Examples.«16Arrays»

/-! # 19. Uninitialised cells (a feasibility prototype, docs/10; not on ochr-core)

Rust's `MaybeUninit<T>` in Ochr: a cell that holds a `T` or nothing, with no runtime tag.
Checked under switches that are off by default (`set_option ochr.<switch> true in`):

* `uninitTypes`: an `untagged` inductive has no runtime tag. Its constructors are built
  anywhere, and statements and proofs match on it freely, but a match on it in runtime code
  has one live arm: every other arm is `match h {}` on a hypothesis that the arm's case
  refutes ([Untagged]). Its first constructor has no fields: its empty value. With it,
  `Uninit(E) := Empty | Full(x : E)` and its operations (`Init`, `UGet`, `UTake`, `UWrite`)
  are ordinary Ochr definitions, with no native and no other new rule. Rust's `MaybeUninit`
  copies when `T` does, and so does `Uninit(E)` (a non-recursive inductive of copy fields).
* `lentProofs`: a proof field assigned while part of its value is lent is checked with each
  lent part an unknown value of its type ([Lent-proof]; landed on ochr-core as "D64 amended",
  8e036130, on by default there, with witnesses DepFields.BoomLent and BoomGetLent). Without it, ochr-core accepts a
  closed proof of `False` (`LentProofs.Boom`). With it, a value with an invariant can hand
  out a borrow into the data its invariant is about, provided the invariant holds whatever
  is written through that borrow: `UVec.Get` returns `&E` into the buffer of a user-land
  `Vec(E)` whose invariant ("the first `len` cells are full") lives inside the `Vec`.
* `moveEmpty`, the merge proposed in docs/10 (a move out of an `Uninit` place leaves it
  empty, so the moved-out marker and the empty value are one thing). Unsound on ochr-core,
  where statements read by copying: the move is observable to runtime code but never happens
  in a statement (`MoveEmpty`). It needs statements that move, as the `erased-moves` branch
  (D68) makes them, and a stuck block that takes such a cell by `&` (`moveEmptyByRef`). On that
  base it checks out (`Scratch/Uninit/MoveEmptyD68.lean`: the probes as expected, 0 fuzz
  findings in 2·10⁴ cases; without the `&` capture, a closed proof of `False`).

`Uninit(E)` here is the "four natives" design of docs/10 with its four natives written in
Ochr instead, and the empty value a constructor rather than the `⊥` a move leaves. -/

open Ochr.Test

/-! ## The untagged type and its operations -/

set_option ochr.uninitTypes true in
ochr Untagged uses Std {
  untagged inductive Uninit (E : Type) := Empty | Full(x : E)
  -- statements and proofs may tell the two apart
  def Init (E : Type) (u : Uninit(E)) : Prop := (
    match u {
      Empty => False,
      Full(x) => ⊤,
    }
  )
  -- Rust's `assume_init_mut`: the live arm is `Full`, the other is refuted by `h`
  def UGet (E : Type) (u : &Uninit(E)) (h : Init(E, *u)) : &E := (
    match *u {
      Full(x) => &x,
      Empty => match h {},
    }
  )
  -- Rust's `assume_init_read`, then the cell is empty again
  def UTake (E : Type) (u : &Uninit(E)) (h : Init(E, *u)) : E := (
    let y = *u;
    *u := Empty;
    match y {
      Full(x) => x,
      Empty => match h {},
    }
  )
  -- Rust's `write`: the old content is not dropped (leaked, as the user accepts)
  def UWrite (E : Type) (u : &Uninit(E)) (x : E) : Unit := *u := Full(x)
  -- whatever is written through `UGet`'s borrow, the cell is full afterwards
  def UGetPut (E : Type) (u : Uninit(E)) (h : Init(E, u)) (w : E) :
      Eq(Uninit(E), (let c = u; let r = UGet(E, &c, h); *r := w; c), Full(w)) := (
    match u {
      Full(x) => refl,
      Empty => match h {},
    }
  )
  def UGetPutAll (E : Type) (u : Uninit(E)) (h : Init(E, u)) :
      (Π(w : E). Eq(Uninit(E), (let c = u; let r = UGet(E, &c, h); *r := w; c), Full(w))) := (
    λ(w : E) : Eq(Uninit(E), (let c = u; let r = UGet(E, &c, h); *r := w; c), Full(w)) => UGetPut(E, u, h, w)
  )
  -- no tag: a runtime match with two live arms is refused
  reject def IsFull (E : Type) (u : &Uninit(E)) : Bool := (
    match *u {
      Full(x) => true,
      Empty => false,
    }
  )
  -- a known value: its hypothesis is `refl`
  def KnownFull (x : Word) : Word := (
    let u = Full(x);
    let h : Init(Word, u) = refl;
    match u {
      Full(y) => y,
      Empty => match h {},
    }
  )
  reject def KnownEmpty (x : Word) : Word := (
    let u : Uninit(Word) = Empty;
    let h : Init(Word, u) = refl;
    match u {
      Full(y) => y,
      Empty => match h {},
    }
  )
  -- a copy type exactly when its element type is
  def CopyW (u : Uninit(Word)) : Uninit(Word) × Uninit(Word) := (u, u)
  reject def CopyN (u : Uninit(Nat)) : Uninit(Nat) × Uninit(Nat) := (u, u)
  -- take, then write back
  def TakeThenWrite (u : &Uninit(Nat)) (h : Init(Nat, *u)) : Unit := (
    let x = UTake(Nat, &*u, h);
    UWrite(Nat, u, S(x))
  )
  def TakeRun : Id(Uninit(Nat), (let c = Full(3); let h : Init(Nat, c) = refl; TakeThenWrite(&c, h); c), Full(4)) := refl
  def GetRun : Id(Uninit(Nat), (let c = Full(3); let h : Init(Nat, c) = refl; let r = UGet(Nat, &c, h); *r := 7; c), Full(7)) := refl
  -- the empty value is a value: equations over it compute
  def EmptyEq (E : Type) : Eq(Uninit(E), Empty[E], Empty[E]) := refl
  reject def EmptyFull (E : Type) (x : E) : Eq(Uninit(E), Empty[E], Full(x)) := refl
  def EmptyFullNeg (E : Type) (x : E) (e : Eq(Uninit(E), Empty[E], Full(x))) : False := match e {}
  -- a moved-out cell is not empty: reading it is an error, as for any moved place
  reject def MovedNotEmpty (u : Uninit(Nat)) : Uninit(Nat) := (
    let y = u;
    u
  )
}

#guard Untagged.decls.length == 19

/-! ## A proof field while part of its value is lent ([Lent-proof])

On ochr-core a proof field may be re-assigned while the field its type mentions is lent: the
assigned proof's type is computed with the borrow ended at its current content, and the live
borrow can then write something else, which nothing invalidates (it is not a write through a
field place, and [Repack] cannot check a proof, `⋆`). `Boom` is a closed proof of `False`.
With `lentProofs` the lent part is an unknown value of its type, so the proof must hold
whatever the borrow leaves there: `GetP` returns a borrow of an element inside a value whose
invariant says the cell is full, re-proved by `UGetPutAll` for any value written back. -/

set_option ochr.uninitTypes true in
set_option ochr.lentProofs true in
ochr LentProofs uses Untagged {
  def IsZ (n : Word) : Prop := (
    match n {
      Zero => ⊤,
      Succ(m) => False,
    }
  )
  inductive ZBox := MkZ(x : Word, h : IsZ(x))
  reject def Lie (b : &ZBox) : Unit := (
    match *b {
      MkZ(x, h) => (
        let h0 = h;
        let r = &x;
        h := h0;
        *r := Succ(Zero)
      ),
    }
  )
  reject def Boom : False := (
    let b = MkZ(Zero, refl);
    Lie(&b);
    match b {
      MkZ(x, h) => h,
    }
  )
  -- the same through a returned borrow: the caller writes
  reject def GetX (b : &ZBox) : &Word := (
    match *b {
      MkZ(x, h) => (
        let h0 = h;
        let r = &x;
        h := h0;
        r
      ),
    }
  )
  inductive PBox := MkP(x : Uninit(Word), h : Init(Word, x))
  def GetP (b : &PBox) : &Word := (
    match *b {
      MkP(x, h) => (
        let h0 = h;
        let hp = UGetPutAll(Word, x, h0);
        let res = UGet(Word, &x, h0);
        h := (rewrite ← hp(*res) in refl);
        res
      ),
    }
  )
  def UseP : Id(Word, (
      let b = MkP(Full(Zero), refl);
      let r = GetP(&b);
      *r := Succ(Zero);
      match b {
        MkP(x, h) => (
          let k : Init(Word, x) = h;
          let g = UGet(Word, &x, k);
          *g
        ),
      }), Succ(Zero)) := refl
  -- a borrow of the whole cell could empty it: no proof holds whatever it writes
  reject def GetCellP (b : &PBox) : &Uninit(Word) := (
    match *b {
      MkP(x, h) => (
        let h0 = h;
        let r = &x;
        h := h0;
        r
      ),
    }
  )
  -- what GetCellP would allow: the caller empties the cell, and the invariant proves False
  reject def BoomP : False := (
    let b = MkP(Full(Zero), refl);
    let r = GetCellP(&b);
    *r := Empty[Word];
    match b {
      MkP(x, h) => h,
    }
  )
}

#guard LentProofs.decls.length == 10

/-! ## The merge's rule 4 (`moveEmpty`), and why it is unsound on ochr-core

The merge says a move out of an `Uninit` place leaves it empty, so runtime code may read the
moved-out place and gets `Empty`. A move is then observable. On ochr-core a statement reads by
copying (D53 (a), ghosts), so the same code run inside a statement does not move, and the two
disagree: `MTClaim` proves `MoveThenRead(Full(0))` is `Full(0)`, while its run returns `Empty`;
`G` is accepted, and its run at `0` reaches the arm its hypothesis refutes (compiled, with no
tag, it would read the element out of an empty cell). Without `moveEmpty` these are rejected at
`MoveThenRead`: reading a moved-out place is an error. On a base where statements move as
runtime code does (D68, branch `erased-moves`), `MTClaim` is false and `MTRunEmpty` holds. -/

set_option ochr.uninitTypes true in
ochr MoveEmpty uses Untagged {
  reject def MoveThenRead (u : Uninit(Nat)) : Uninit(Nat) := (
    let y = u;
    u
  )
  reject def MT (n : Nat) (u : Uninit(Nat)) : Uninit(Nat) := (
    match n {
      Z => (
        let y = u;
        u
      ),
      S m => u,
    }
  )
  -- in a statement the read copies: the move does not happen
  reject def Claim (n : Nat) (u : Uninit(Nat)) : Eq(Uninit(Nat), MT(n, u), u) := (
    match n {
      Z => refl,
      S m => refl,
    }
  )
  reject def MTClaim : Id(Uninit(Nat), MoveThenRead(Full(0)), Full(0)) := refl
  reject def G (n : Nat) : Nat := (
    let r = MT(n, Full(0));
    let e = Claim(n, Full(0));
    let h : Init(Nat, r) = (rewrite ← e in refl);
    match r {
      Full(y) => y,
      Empty => match h {},
    }
  )
  -- what the merge intends, which needs statements that move
  reject def MTRunEmpty : Id(Uninit(Nat), MoveThenRead(Full(0)), Empty[Nat]) := refl
}

#guard MoveEmpty.decls.length == 6

/-! ## A user-land `Vec(E)` over `Array(Uninit(E), cap)`

`Vec(E) := MkVec(cap, len, buf : Array(Uninit(E), cap), hl : Le(len, cap), hs : AllInit(…))`:
the first `len` cells of `buf` are full and the rest are spare capacity, uninitialised. The
invariant `hs` is a proof field, so callers carry nothing. First the model's facts about
`AllInitS` (each by recursion on the count), then the same through an owned array's view. -/

set_option ochr.uninitTypes true in
set_option ochr.lentProofs true in
ochr UVecModel uses Untagged, ArrayLemmas {
  -- the first `k` cells are full
  def AllInitS (E : Type) (n : Word) (s : Slice(Uninit(E), n)) (k : Word) : Prop by k := (
    match k {
      Zero => ⊤,
      Succ(k') => match n {
        Zero => False,
        Succ(m) => match s {
          MkSlice(c) => match c {
            MkC(x, t) => Init(E, x) ∧ AllInitS(E, m, t, k'),
          },
        },
      },
    }
  )
  -- writing a full cell anywhere keeps them full
  def AllInitSetFull (E : Type) (n : Word) (s : Slice(Uninit(E), n)) (k : Word) (i : Word) (y : E)
      (h : AllInitS(E, n, s, k)) : AllInitS(E, n, SetS(Uninit(E), n, s, i, Full(y)), k) by k := (
    match k {
      Zero => refl,
      Succ(k') => match n {
        Zero => match h {},
        Succ(m) => match s {
          MkSlice(c) => match c {
            MkC(x, t) => (
              let ⟨hx, ht⟩ = h;
              match i {
                Zero => ⟨refl, ht⟩,
                Succ(i') => ⟨hx, AllInitSetFull(E, m, t, k', i', y, ht)⟩,
              }
            ),
          },
        },
      },
    }
  )
  -- writing a full cell at `k` makes the first `k + 1` full
  def AllInitSnoc (E : Type) (n : Word) (s : Slice(Uninit(E), n)) (k : Word) (y : E) (hk : Lt(k, n))
      (h : AllInitS(E, n, s, k)) : AllInitS(E, n, SetS(Uninit(E), n, s, k, Full(y)), Succ(k)) by k := (
    match n {
      Zero => match hk {},
      Succ(m) => match s {
        MkSlice(c) => match c {
          MkC(x, t) => match k {
            Zero => ⟨refl, refl⟩,
            Succ(k') => (
              let ⟨hx, ht⟩ = h;
              ⟨hx, AllInitSnoc(E, m, t, k', y, hk, ht)⟩
            ),
          },
        },
      },
    }
  )
  def AllInitDown (E : Type) (n : Word) (s : Slice(Uninit(E), n)) (k : Word)
      (h : AllInitS(E, n, s, Succ(k))) : AllInitS(E, n, s, k) by k := (
    match k {
      Zero => refl,
      Succ(k') => match n {
        Zero => match h {},
        Succ(m) => match s {
          MkSlice(c) => match c {
            MkC(x, t) => (
              let ⟨hx, ht⟩ = h;
              ⟨hx, AllInitDown(E, m, t, k', ht)⟩
            ),
          },
        },
      },
    }
  )
  -- writing at or beyond `k` leaves the first `k` alone
  def AllInitSetAbove (E : Type) (n : Word) (s : Slice(Uninit(E), n)) (k : Word) (i : Word) (w : Uninit(E))
      (hki : Le(k, i)) (h : AllInitS(E, n, s, k)) : AllInitS(E, n, SetS(Uninit(E), n, s, i, w), k) by k := (
    match k {
      Zero => refl,
      Succ(k') => match n {
        Zero => match h {},
        Succ(m) => match s {
          MkSlice(c) => match c {
            MkC(x, t) => match i {
              Zero => match hki {},
              Succ(i') => (
                let ⟨hx, ht⟩ = h;
                ⟨hx, AllInitSetAbove(E, m, t, k', i', w, hki, ht)⟩
              ),
            },
          },
        },
      },
    }
  )
  -- a cell below `k` is full
  def AllInitNthS (E : Type) (n : Word) (s : Slice(Uninit(E), n)) (k : Word) (i : Word) (hik : Lt(i, k))
      (hin : Lt(i, n)) (h : AllInitS(E, n, s, k)) : Init(E, Nth(Uninit(E), n, s, i, hin)) by k := (
    match k {
      Zero => match hik {},
      Succ(k') => match n {
        Zero => match h {},
        Succ(m) => match s {
          MkSlice(c) => match c {
            MkC(x, t) => (
              let ⟨hx, ht⟩ = h;
              match i {
                Zero => hx,
                Succ(i') => AllInitNthS(E, m, t, k', i', hik, hin, ht),
              }
            ),
          },
        },
      },
    }
  )
  -- the view an owned array wraps (model code)
  def SliceOfA (E : Type) (n : Word) (a : Array(E, n)) : Slice(E, n) := (
    match a {
      MkArray(s) => s,
    }
  )
  def AllInit (E : Type) (n : Word) (a : Array(Uninit(E), n)) (k : Word) : Prop := AllInitS(E, n, SliceOfA(Uninit(E), n, a), k)
  -- reading an element through the array's view is the model's element
  def AsGetReadA (E : Type) (n : Word) (a : Array(E, n)) (i : Word) (h : Lt(i, n)) :
      Eq(E, (let c = a; clone(*GetMut(E, n, AsSlice(E, n, &c), i, h))), Nth(E, n, SliceOfA(E, n, a), i, h)) := (
    match a {
      MkArray(s) => (
        let ⟨hv, hp⟩ = GetMutReadV(E, n, s, i, h);
        hv
      ),
    }
  )
  def AllInitNth (E : Type) (n : Word) (a : Array(Uninit(E), n)) (k : Word) (i : Word) (hik : Lt(i, k))
      (hin : Lt(i, n)) (h : AllInit(E, n, a, k)) : Init(E, Nth(Uninit(E), n, SliceOfA(Uninit(E), n, a), i, hin)) := (
    AllInitNthS(E, n, SliceOfA(Uninit(E), n, a), k, i, hik, hin, h)
  )
  -- the three operations keep the invariant, stated about the programs they run
  def PushPreserves (E : Type) (n : Word) (a : Array(Uninit(E), n)) (k : Word) (x : E) (hk : Lt(k, n))
      (h : AllInit(E, n, a, k)) :
      AllInit(E, n, (let c = a; *GetMut(Uninit(E), n, AsSlice(Uninit(E), n, &c), k, hk) := Full(x); c), Succ(k)) := (
    match a {
      MkArray(s) => rewrite ← GetMutSetV(Uninit(E), n, s, k, Full(x), hk) in AllInitSnoc(E, n, s, k, x, hk, h),
    }
  )
  def PopPreserves (E : Type) (n : Word) (a : Array(Uninit(E), n)) (k : Word) (hk : Lt(k, n))
      (h : AllInit(E, n, a, Succ(k))) :
      AllInit(E, n, (let c = a; *GetMut(Uninit(E), n, AsSlice(Uninit(E), n, &c), k, hk) := Empty[E]; c), k) := (
    match a {
      MkArray(s) => rewrite ← GetMutSetV(Uninit(E), n, s, k, Empty[E], hk) in
        AllInitSetAbove(E, n, s, k, k, Empty[E], LeRefl(k), AllInitDown(E, n, s, k, h)),
    }
  )
  -- whatever is written back through the element borrow `Get` returns
  def GetPreserves (E : Type) (n : Word) (a : Array(Uninit(E), n)) (k : Word) (i : Word) (hc : Lt(i, n))
      (h : AllInit(E, n, a, k)) (hu : Init(E, (let c = a; clone(*GetMut(Uninit(E), n, AsSlice(Uninit(E), n, &c), i, hc))))) (y : E) :
      AllInit(E, n, (let c = a; let r = GetMut(Uninit(E), n, AsSlice(Uninit(E), n, &c), i, hc); let r2 = UGet(E, r, hu); *r2 := y; c), k) := (
    match a {
      MkArray(s) =>
        rewrite ← UGetPut(E, (let c = s; clone(*GetMut(Uninit(E), n, &c, i, hc))), hu, y) in
        rewrite ← GetMutSetV(Uninit(E), n, s, i, Full(y), hc) in
        AllInitSetFull(E, n, s, k, i, y, h),
    }
  )
  def GetPreservesAll (E : Type) (n : Word) (a : Array(Uninit(E), n)) (k : Word) (i : Word) (hc : Lt(i, n))
      (h : AllInit(E, n, a, k)) (hu : Init(E, (let c = a; clone(*GetMut(Uninit(E), n, AsSlice(Uninit(E), n, &c), i, hc))))) :
      (Π(y : E). AllInit(E, n, (let c = a; let r = GetMut(Uninit(E), n, AsSlice(Uninit(E), n, &c), i, hc); let r2 = UGet(E, r, hu); *r2 := y; c), k)) := (
    λ(y : E) : AllInit(E, n, (let c = a; let r = GetMut(Uninit(E), n, AsSlice(Uninit(E), n, &c), i, hc); let r2 = UGet(E, r, hu); *r2 := y; c), k) =>
      GetPreserves(E, n, a, k, i, hc, h, hu, y)
  )
}

#guard UVecModel.decls.length == 14

/-! The `Vec` itself. `Push` (within capacity) writes `Full(x)` into the first empty cell,
`Pop` takes the last full one and leaves it empty, and `Get` returns `&E` into the buffer:
it lends the buffer, which invalidates `hs` ([Open]), and re-proves `hs` for whatever value the
caller writes back through the returned borrow ([Lent-proof]). -/

set_option ochr.uninitTypes true in
set_option ochr.lentProofs true in
ochr UVec uses UVecModel {
  inductive Vec (E : Type) := MkVec(cap : Word, len : Word, buf : Array(Uninit(E), cap), hl : Le(len, cap), hs : AllInit(E, cap, buf, len))
  def VLen (E : Type) (v : Vec(E)) : Word := (
    match v {
      MkVec(cap, len, buf, hl, hs) => len,
    }
  )
  def VCap (E : Type) (v : Vec(E)) : Word := (
    match v {
      MkVec(cap, len, buf, hl, hs) => cap,
    }
  )
  def VNew (E : Type) (cap : Word) : Vec(E) := MkVec[E](cap, Zero, Replicate(Uninit(E), cap, Empty[E]), refl, refl)
  def Push (E : Type) (v : &Vec(E)) (x : E) (hc : Lt(VLen(E, *v), VCap(E, *v))) : Unit := (
    match *v {
      MkVec(cap, len, buf, hl, hs) => (
        let hk : Lt(len, cap) = hc;
        let hp = PushPreserves(E, cap, buf, len, x, hk, hs);
        *GetMut(Uninit(E), cap, AsSlice(Uninit(E), cap, &buf), len, hk) := Full(x);
        len := Succ(len);
        hl := hk;
        hs := hp
      ),
    }
  )
  def LeSuccL (a : Word) (b : Word) (h : Le(Succ(a), b)) : Le(a, b) by a := (
    match a {
      Zero => refl,
      Succ(a') => match b {
        Zero => match h {},
        Succ(b') => LeSuccL(a', b', h),
      },
    }
  )
  def LtLe (i : Word) (k : Word) (n : Word) (hik : Lt(i, k)) (hkn : Le(k, n)) : Lt(i, n) := LeTrans(Succ(i), k, n, hik, hkn)
  def Pop (E : Type) (v : &Vec(E)) (hn : Lt(Zero, VLen(E, *v))) : E := (
    match *v {
      MkVec(cap, len, buf, hl, hs) => match len {
        Zero => match hn {},
        Succ(k0) => (
          let k = k0;
          let hk : Lt(k, cap) = hl;
          let hi = AllInitNth(E, cap, buf, Succ(k), k, LeRefl(Succ(k)), hk, hs);
          let hu : Init(E, (let c = buf; clone(*GetMut(Uninit(E), cap, AsSlice(Uninit(E), cap, &c), k, hk)))) =
            (rewrite ← AsGetReadA(Uninit(E), cap, buf, k, hk) in hi);
          let hp = PopPreserves(E, cap, buf, k, hk, hs);
          let y = (
            let cell = GetMut(Uninit(E), cap, AsSlice(Uninit(E), cap, &buf), k, hk);
            let t = *cell;
            *cell := Empty[E];
            t
          );
          len := k;
          hl := LeSuccL(k, cap, hk);
          hs := hp;
          match y {
            Full(x) => x,
            Empty => match hu {},
          }
        ),
      },
    }
  )
  def Get (E : Type) (v : &Vec(E)) (i : Word) (h : Lt(i, VLen(E, *v))) : &E := (
    match *v {
      MkVec(cap, len, buf, hl, hs) => (
        let hik : Lt(i, len) = h;
        let hc = LtLe(i, len, cap, hik, hl);
        let hi = AllInitNth(E, cap, buf, len, i, hik, hc, hs);
        let hu : Init(E, (let c = buf; clone(*GetMut(Uninit(E), cap, AsSlice(Uninit(E), cap, &c), i, hc)))) =
          (rewrite ← AsGetReadA(Uninit(E), cap, buf, i, hc) in hi);
        let hp = GetPreservesAll(E, cap, buf, len, i, hc, hs, hu);
        let res = (
          let r = GetMut(Uninit(E), cap, AsSlice(Uninit(E), cap, &buf), i, hc);
          UGet(E, r, hu)
        );
        hs := hp(*res);
        res
      ),
    }
  )
  -- runs on concrete values
  def PushGet : Id(Word, (
      let v = VNew(Word, W(3));
      Push(Word, &v, W(5), refl);
      Push(Word, &v, W(7), refl);
      let r = Get(Word, &v, Succ(Zero), refl);
      *r), W(7)) := refl
  def WriteThrough : Id(Word, (
      let v = VNew(Word, W(2));
      Push(Word, &v, W(5), refl);
      let r = Get(Word, &v, Zero, refl);
      *r := W(9);
      let r2 = Get(Word, &v, Zero, refl);
      *r2), W(9)) := refl
  def PushPop : Id(Word, (
      let v = VNew(Word, W(2));
      Push(Word, &v, W(5), refl);
      Push(Word, &v, W(7), refl);
      let a = Pop(Word, &v, refl);
      let b = Pop(Word, &v, refl);
      WAdd(a, b)), W(12)) := refl
  def PopLen : Id(Word, (
      let v = VNew(Word, W(2));
      Push(Word, &v, W(5), refl);
      let a = Pop(Word, &v, refl);
      VLen(Word, v)), Zero) := refl
  -- a non-copy element, written in place through the borrow `Get` returns
  def ListElem : Id(Word, (
      let v = VNew(List(Word), W(1));
      Push(List(Word), &v, Nil, refl);
      let r = Get(List(Word), &v, Zero, refl);
      *r := Cons(W(4), Nil);
      let l = Pop(List(Word), &v, refl);
      match l {
        Nil => Zero,
        Cons(h, t) => h,
      }), W(4)) := refl
  reject def PushPopWrong : Id(Word, (
      let v = VNew(Word, W(2));
      Push(Word, &v, W(5), refl);
      Pop(Word, &v, refl)), W(6)) := refl
  -- out of capacity, past the length, empty: refused by the bounds
  reject def PushFull : Unit := (
    let v = VNew(Word, Zero);
    Push(Word, &v, W(5), refl)
  )
  reject def GetPastLen : Word := (
    let v = VNew(Word, W(2));
    Push(Word, &v, W(5), refl);
    let r = Get(Word, &v, Succ(Zero), refl);
    *r
  )
  reject def PopEmpty : Word := (
    let v = VNew(Word, W(2));
    Pop(Word, &v, refl)
  )
  -- a borrow of the whole cell could empty it: the invariant does not hold whatever it writes
  reject def GetCell (E : Type) (v : &Vec(E)) (i : Word) (h : Lt(i, VLen(E, *v))) : &Uninit(E) := (
    match *v {
      MkVec(cap, len, buf, hl, hs) => (
        let hs0 = hs;
        let hc = LtLe(i, len, cap, h, hl);
        let res = GetMut(Uninit(E), cap, AsSlice(Uninit(E), cap, &buf), i, hc);
        hs := hs0;
        res
      ),
    }
  )
  -- without the re-proof, the lent buffer leaves the invariant invalidated
  reject def GetNoReproof (E : Type) (v : &Vec(E)) (i : Word) (h : Lt(i, VLen(E, *v))) : &E := (
    match *v {
      MkVec(cap, len, buf, hl, hs) => (
        let hik : Lt(i, len) = h;
        let hc = LtLe(i, len, cap, hik, hl);
        let hi = AllInitNth(E, cap, buf, len, i, hik, hc, hs);
        let hu : Init(E, (let c = buf; clone(*GetMut(Uninit(E), cap, AsSlice(Uninit(E), cap, &c), i, hc)))) =
          (rewrite ← AsGetReadA(Uninit(E), cap, buf, i, hc) in hi);
        let r = GetMut(Uninit(E), cap, AsSlice(Uninit(E), cap, &buf), i, hc);
        UGet(E, r, hu)
      ),
    }
  )
}

#guard UVec.decls.length == 20

/-! ## The ledger rows of the three switches (asserted)

Each row runs a block with the switch flipped and lists the verdicts that change. The `Vec`
blocks are not re-run here (each run re-checks the arrays library): with `lentProofs` off they
flip nothing (`Get`'s re-proof also goes through with the borrow at its current content; what
the switch refuses is a re-proof that holds only of that content, `LentProofs`), and with
`moveEmpty` on they flip nothing (measured by `Scratch/Uninit/Flips.lean`). -/

namespace Ochr.Uninit
open Ochr.Surface

def flips (name : String) (b : Block) (base alt : Config) : List String :=
  let r := run name b base
  let r' := run name b alt
  (r.rows.zip r'.rows).filterMap fun (x, y) =>
    if x.verdict.ok != y.verdict.ok then
      some s!"{name}.{x.name}:{if y.verdict.ok then "accepted" else "rejected"}"
    else none

end Ochr.Uninit

-- uninitTypes, completeness: without it, `untagged` is refused and everything built on it
#guard Ochr.Uninit.flips "Untagged" Untagged { uninitTypes := true } {} ==
  ["Untagged.Uninit:rejected", "Untagged.Init:rejected", "Untagged.UGet:rejected", "Untagged.UTake:rejected",
   "Untagged.UWrite:rejected", "Untagged.UGetPut:rejected", "Untagged.UGetPutAll:rejected",
   "Untagged.KnownFull:rejected", "Untagged.CopyW:rejected", "Untagged.TakeThenWrite:rejected",
   "Untagged.TakeRun:rejected", "Untagged.GetRun:rejected", "Untagged.EmptyEq:rejected",
   "Untagged.EmptyFullNeg:rejected"]
-- lentProofs, soundness (witnesses Boom, BoomP: closed proofs of False). GetP and UseP flip to
-- rejected only because the assignment's proof then has no goal to rewrite against
#guard Ochr.Uninit.flips "LentProofs" LentProofs { uninitTypes := true, lentProofs := true } { uninitTypes := true } ==
  ["LentProofs.Lie:accepted", "LentProofs.Boom:accepted", "LentProofs.GetX:accepted", "LentProofs.GetP:rejected",
   "LentProofs.UseP:rejected", "LentProofs.GetCellP:accepted", "LentProofs.BoomP:accepted"]
-- moveEmpty switched on, soundness (witnesses MTClaim, a false Id, and G, whose run reaches a
-- refuted arm): unsound on ochr-core, where statements copy
#guard Ochr.Uninit.flips "MoveEmpty" MoveEmpty { uninitTypes := true } { uninitTypes := true, moveEmpty := true } ==
  ["MoveEmpty.MoveThenRead:accepted", "MoveEmpty.MT:accepted", "MoveEmpty.Claim:accepted",
   "MoveEmpty.MTClaim:accepted", "MoveEmpty.G:accepted"]
