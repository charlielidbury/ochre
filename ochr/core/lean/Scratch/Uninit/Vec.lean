import Ochr.Examples.«16Arrays»
open Ochr Ochr.Test

set_option ochr.uninitTypes true in
set_option ochr.lentProofs true in
ochr UninitLib uses Std {
  untagged inductive Uninit (E : Type) := Empty | Full(x : E)
  def Init (E : Type) (u : Uninit(E)) : Prop := (
    match u {
      Empty => False,
      Full(x) => ⊤,
    }
  )
  def UGet (E : Type) (u : &Uninit(E)) (h : Init(E, *u)) : &E := (
    match *u {
      Full(x) => &x,
      Empty => match h {},
    }
  )
  def UGetPut (E : Type) (u : Uninit(E)) (h : Init(E, u)) (w : E) :
      Eq(Uninit(E), (let c = u; let r = UGet(E, &c, h); *r := w; c), Full(w)) := (
    match u {
      Full(x) => refl,
      Empty => match h {},
    }
  )
}

set_option ochr.uninitTypes true in
set_option ochr.lentProofs true in
ochr UVecModel uses UninitLib, ArrayLemmas {
  -- cells below `k` are full, by recursion on `k`
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
}
set_option ochr.uninitTypes true in
set_option ochr.lentProofs true in
ochr UVec uses UVecModel {
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
  -- writing Full(x) at `k` keeps the first `k + 1` full
  def PushPreserves (E : Type) (n : Word) (a : Array(Uninit(E), n)) (k : Word) (x : E) (hk : Lt(k, n))
      (h : AllInit(E, n, a, k)) :
      AllInit(E, n, (let c = a; *GetMut(Uninit(E), n, AsSlice(Uninit(E), n, &c), k, hk) := Full(x); c), Succ(k)) := (
    match a {
      MkArray(s) => rewrite ← GetMutSetV(Uninit(E), n, s, k, Full(x), hk) in AllInitSnoc(E, n, s, k, x, hk, h),
    }
  )
  -- emptying cell `k` keeps the first `k` full
  def PopPreserves (E : Type) (n : Word) (a : Array(Uninit(E), n)) (k : Word) (hk : Lt(k, n))
      (h : AllInit(E, n, a, Succ(k))) :
      AllInit(E, n, (let c = a; *GetMut(Uninit(E), n, AsSlice(Uninit(E), n, &c), k, hk) := Empty[E]; c), k) := (
    match a {
      MkArray(s) => rewrite ← GetMutSetV(Uninit(E), n, s, k, Empty[E], hk) in
        AllInitSetAbove(E, n, s, k, k, Empty[E], LeRefl(k), AllInitDown(E, n, s, k, h)),
    }
  )
  -- whatever is written back through the element borrow `Get` returns, the first `k` stay full
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
set_option ochr.uninitTypes true in
set_option ochr.lentProofs true in
ochr UVecOps uses UVec {
  -- the buffer's first `len` cells are full; the rest are spare capacity, uninitialised
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
  -- push within capacity: write Full(x) into the first empty cell
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
  -- pop the last element: take its cell (empty again), shorten
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
  -- an element borrow: `&E` into the buffer, the invariant re-proved for whatever is written through it
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
}
set_option ochr.uninitTypes true in
set_option ochr.lentProofs true in
ochr UVecTests uses UVecOps {
  -- runs: the checker evaluates the user-land Vec on concrete values
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
  -- a non-copy element: the borrow Get returns writes in place
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
  -- out of capacity and out of length are refused by their bounds
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
  -- returning a borrow of the cell itself (`&Uninit(E)`): the caller could empty it, so the
  -- invariant cannot be re-proved for whatever the borrow writes ([Lent-proof])
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
  -- without re-proving the invariant, the borrow leaves it invalidated
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
#eval (run "UVecTests" UVecTests { uninitTypes := true, lentProofs := true }).rows.map fun r => (r.name, r.expectAccept == r.verdict.ok, match r.verdict with | .accepted => "" | .rejected m _ => m)
#eval (run "UVecTests" UVecTests { uninitTypes := true, lentProofs := false }).rows.map fun r => (r.name, r.verdict.ok)
#eval (run "UVecOps" UVecOps { uninitTypes := true, lentProofs := true }).rows.map fun r => (r.name, r.expectAccept == r.verdict.ok, match r.verdict with | .accepted => "" | .rejected m _ => m)
#eval (run "UVec" UVec { uninitTypes := true, lentProofs := true }).rows.map fun r => (r.name, r.expectAccept == r.verdict.ok, match r.verdict with | .accepted => "" | .rejected m _ => m)
#eval (run "UVecModel" UVecModel { uninitTypes := true, lentProofs := true }).rows.map fun r => (r.name, r.expectAccept == r.verdict.ok, match r.verdict with | .accepted => "" | .rejected m _ => m)
