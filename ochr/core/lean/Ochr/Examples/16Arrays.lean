import Ochr.Examples.«00Std»

/-! # 16. Arrays: a library over a type-level model

Arrays are not built into Ochr (D57). An array of `n` elements is modelled by `Cells(E, n)`,
a type computed by recursion on `n`: `Unit` at zero, and a cell holding an element and the
rest at `S m`. So the length lives only in the type, and a value of `Cells(E, n)` has exactly
`n` elements. Proofs reason about this model directly; compiled code will use a flat buffer
instead, through a small set of native functions (marked `[native]` below) whose models are
the Ochr bodies given here.

The rules (D57): nothing recurses over an array, only over an index; runtime code never owns
part of an array; a borrow of part of an array is scoped by a continuation (`WithSplit`).

Phase A uses today's checker, so these workarounds are marked where they occur, for phase B to
remove:
* `[K1]` There is no universe of data types yet, so `&E` is not well formed for a type
  variable `E`, nor `&Cells(E, n)` at an unknown `n` (D48). Each cell's tail is therefore
  wrapped in the view type `SliceOf`, whose borrows are always well formed, and the one
  function that returns a borrow of an element, `GetMut`, is written for `Nat` elements.
* `[K2]` `SliceOf` should be unsized: runtime code could only borrow it.
* `[K3]` `SliceOf`, `ArrayOf` and `Cell` should be abstract: runtime code could not match on
  them, and the `[native]` functions would be linked to native code.
* `[K6]` Quicksort recurses on fuel; with recursion on a measure it recurses on the length.
* `[⋆]` A checker incompleteness ("cannot infer the type of the value ⋆") is avoided by passing
  a value through a parameter.

Defined in D57 and notes/arrays-library.md. -/

open Ochr.Test

/-! ## Indices

Everything recurses over an index, so the order on `Nat` and a few facts about it come
first. `Lt(i, n)` is the bounds proof that indexing takes. -/

ochr Index uses Std {
  def Le (a : Nat) (b : Nat) : Prop by a := (
    match a {
      Z => ⊤,
      S a' => match b {
        Z => False,
        S b' => Le(a', b'),
      },
    }
  )

  def Lt (a : Nat) (b : Nat) : Prop := Le(S a, b)

  def Sub (a : Nat) (b : Nat) : Nat by b := (
    match b {
      Z => a,
      S b' => match a {
        Z => Z,
        S a' => Sub(a', b'),
      },
    }
  )

  def Leb (a : Nat) (b : Nat) : Bool by a := (
    match a {
      Z => true,
      S a' => match b {
        Z => false,
        S b' => Leb(a', b'),
      },
    }
  )

  def Eqb (a : Nat) (b : Nat) : Bool by a := (
    match a {
      Z => match b {
        Z => true,
        S _ => false,
      },
      S a' => match b {
        Z => false,
        S b' => Eqb(a', b'),
      },
    }
  )

  -- A decision that carries its evidence: a comparison at runtime yields the proof an index
  -- needs (B4). At runtime `Dec` is a boolean; its fields are proofs, which are erased.
  inductive Dec (P : Prop) (Q : Prop) := Yes(h : P) | No(k : Q)

  def LeDec (a : Nat) (b : Nat) : Dec(Le(a, b), Lt(b, a)) by a := (
    match a {
      Z => Yes(refl),
      S a' => match b {
        Z => No(refl),
        S b' => LeDec(a', b'),
      },
    }
  )

  def LtDec (i : Nat) (n : Nat) : Dec(Lt(i, n), Le(n, i)) := LeDec(S i, n)

  -- Equations between numbers are symmetric and transitive, by transport.
  def EqSym (a : Nat) (b : Nat) (h : Eq Nat a b) : Eq Nat b a := J(Nat, a, b, λ(z : Nat) : Prop => Eq Nat z a, h, refl)

  def EqTrans (a : Nat) (b : Nat) (c : Nat) (h1 : Eq Nat a b) (h2 : Eq Nat b c) : Eq Nat a c := (
    J(Nat, b, c, λ(z : Nat) : Prop => Eq Nat a z, h2, h1)
  )

  -- Facts about the order, each by recursion on a number.
  def LeRefl (a : Nat) : Le(a, a) by a := (
    match a {
      Z => refl,
      S a' => LeRefl(a'),
    }
  )

  def LeStep (a : Nat) (b : Nat) (h : Le(a, b)) : Le(a, S b) by a := (
    match a {
      Z => refl,
      S a' => match b {
        Z => match h {},
        S b' => LeStep(a', b', h),
      },
    }
  )

  def LeTrans (a : Nat) (b : Nat) (c : Nat) (h1 : Le(a, b)) (h2 : Le(b, c)) : Le(a, c) by a := (
    match a {
      Z => refl,
      S a' => match b {
        Z => match h1 {},
        S b' => match c {
          Z => match h2 {},
          S c' => LeTrans(a', b', c', h1, h2),
        },
      },
    }
  )

  def LeAddL (r : Nat) (j : Nat) : Le(j, Add(r, j)) by r := (
    match r {
      Z => LeRefl(j),
      S r' => LeStep(j, Add(r', j), LeAddL(r', j)),
    }
  )

  def AddRS (r : Nat) (j : Nat) : Eq Nat (S (Add(r, j))) (Add(r, S j)) by r := (
    match r {
      Z => refl,
      S r' => AddRS(r', j),
    }
  )

  def AddZeroR (m : Nat) : Eq Nat (Add(m, 0)) m by m := (
    match m {
      Z => refl,
      S m' => AddZeroR(m'),
    }
  )

  def AddOneR (m : Nat) : Eq Nat (Add(m, 1)) (S m) by m := (
    match m {
      Z => refl,
      S m' => AddOneR(m'),
    }
  )

  def SubPos (m : Nat) (k : Nat) (h : Le(k, m)) : Le(1, Sub(S m, k)) by k := (
    match k {
      Z => refl,
      S k' => match m {
        Z => match h {},
        S m' => SubPos(m', k', h),
      },
    }
  )

  -- What is left after a pivot at `k` is at most `m` long.
  def SubOneLe (m : Nat) (k : Nat) : Le(Sub(Sub(S m, k), 1), m) by k := (
    match k {
      Z => LeRefl(m),
      S k' => match m {
        Z => match k' {
          Z => refl,
          S _ => refl,
        },
        S m' => LeStep(Sub(Sub(S m', k'), 1), m', SubOneLe(m', k')),
      },
    }
  )
}

#eval IO.println (run "Index" Index).show

-- every verdict as expected, and the exact number of declarations (a truncated file changes it)
#guard (run "Index" Index).allAsExpected
#guard (run "Index" Index).count == 19

/-! ## The model

`Cells(E, n)` is `CellsEnd` at zero and a `Cell` at `S m`. A view `Slice(E, n)` wraps the
cells; a cell holds an element and the rest of the view, so the rest is itself a view. An owned array `Array(E, n)` wraps a view. None of them stores a
length. The functions on the model take their arguments by value and recurse over an index;
proofs use them, and they are the models of the native functions below. -/

ochr Arrays uses Index {
  -- [K2] [K3] A view: unsized and abstract in phase B.
  inductive SliceOf (R : Type) := MkSlice(c : R)
  -- [K1] [K3] A cell: an element and the rest, which is a view so that it can be borrowed.
  inductive Cell (E : Type) (R : Type) := MkC(h : E, t : SliceOf(R))
  -- [K3] The end of the cells. (Not `Unit`: an unknown `Unit` cannot be taken apart, so a
  -- proof about an empty view could not see that it is the empty view.)
  inductive CellsEnd := End

  def Cells (E : Type) (n : Nat) : Type by n := (
    match n {
      Z => CellsEnd,
      S m => Cell(E, Cells(E, m)),
    }
  )

  def Slice (E : Type) (n : Nat) : Type := SliceOf(Cells(E, n))

  -- [K3] An owned array: at runtime, a pointer to a block of `n` elements.
  inductive ArrayOf (R : Type) := MkArray(s : SliceOf(R))
  def Array (E : Type) (n : Nat) : Type := ArrayOf(Cells(E, n))

  -- Element `i`.
  def Nth (E : Type) (n : Nat) (s : Slice(E, n)) (i : Nat) (h : Lt(i, n)) : E by i := (
    match n {
      Z => match h {},
      S m => match s {
        MkSlice(c) => match c {
          MkC(x, t) => match i {
            Z => x,
            S i' => Nth(E, m, t, i', h),
          },
        },
      },
    }
  )

  -- The view with element `i` replaced by `x`.
  def SetS (E : Type) (n : Nat) (s : Slice(E, n)) (i : Nat) (x : E) : Slice(E, n) by i := (
    match n {
      Z => s,
      S m => match s {
        MkSlice(c) => match c {
          MkC(y, t) => match i {
            Z => MkSlice(MkC(x, t)),
            S i' => MkSlice(MkC(y, SetS(E, m, t, i', x))),
          },
        },
      },
    }
  )

  -- The first `k` elements, the rest, and the two put back together.
  def TakeS (E : Type) (n : Nat) (k : Nat) (s : Slice(E, n)) (h : Le(k, n)) : Slice(E, k) by k := (
    match k {
      Z => MkSlice(End),
      S k' => match n {
        Z => match h {},
        S m => match s {
          MkSlice(c) => match c {
            MkC(x, t) => MkSlice(MkC(x, TakeS(E, m, k', t, h))),
          },
        },
      },
    }
  )

  def DropS (E : Type) (n : Nat) (k : Nat) (s : Slice(E, n)) : Slice(E, Sub(n, k)) by k := (
    match k {
      Z => s,
      S k' => match n {
        Z => MkSlice(End),
        S m => match s {
          MkSlice(c) => match c {
            MkC(x, t) => DropS(E, m, k', t),
          },
        },
      },
    }
  )

  def JoinS (E : Type) (n : Nat) (k : Nat) (l : Slice(E, k)) (r : Slice(E, Sub(n, k))) : Slice(E, n) by k := (
    match k {
      Z => r,
      S k' => match n {
        Z => MkSlice(End),
        S m => match l {
          MkSlice(c) => match c {
            MkC(x, t) => MkSlice(MkC(x, JoinS(E, m, k', t, r))),
          },
        },
      },
    }
  )

  -- One more element at the end, and the last element taken off.
  def SnocS (E : Type) (n : Nat) (s : Slice(E, n)) (x : E) : Slice(E, S n) by n := (
    match n {
      Z => MkSlice(MkC(x, MkSlice(End))),
      S m => match s {
        MkSlice(c) => match c {
          MkC(y, t) => MkSlice(MkC(y, SnocS(E, m, t, x))),
        },
      },
    }
  )

  def PopS (E : Type) (n : Nat) (s : Slice(E, S n)) : Slice(E, n) × E by n := (
    match s {
      MkSlice(c) => match c {
        MkC(y, t) => match n {
          Z => (MkSlice(End), y),
          S m => (
            let p = PopS(E, m, t);
            match p {
              Mk(init, last) => (MkSlice(MkC(y, init)), last),
            }
          ),
        },
      },
    }
  )

  -- ## The native functions
  -- Each `[native]` body is the model the checker runs; compiled code calls a native
  -- function instead (phase B, K3). Runtime code reaches arrays only through these.

  -- [native] The view of an owned array: at runtime, the same pointer.
  def AsSlice (E : Type) (n : Nat) (a : &Array(E, n)) : &Slice(E, n) := (
    match *a {
      MkArray(s) => &s,
    }
  )

  -- [native] Read element `i`. The model reads a copy of the view (with D53, `clone(*s)`),
  -- so the view itself is left exactly as it was.
  def Read (E : Type) (n : Nat) (s : &Slice(E, n)) (i : Nat) (h : Lt(i, n)) : E := Nth(E, n, *s, i, h)

  -- [native] Write element `i`.
  def Set (E : Type) (n : Nat) (s : &Slice(E, n)) (i : Nat) (x : E) (h : Lt(i, n)) : Unit := (
    *s := SetS(E, n, *s, i, x)
  )

  -- [native] [K1] A borrow of element `i`, for `Nat` elements until `&E` is well formed.
  def GetMut (n : Nat) (s : &Slice(Nat, n)) (i : Nat) (h : Lt(i, n)) : &Nat by i := (
    match n {
      Z => match h {},
      S m => match *s {
        MkSlice(c) => match c {
          MkC(x, t) => match i {
            Z => &x,
            S i' => GetMut(m, &t, i', h),
          },
        },
      },
    }
  )

  -- [native] Borrow the first `k` elements and the rest while `f` runs. The model takes the
  -- two pieces out as values and joins them again after `f` returns; at runtime `f` gets two
  -- pointers into the same block, and nothing is moved.
  def WithSplit (E : Type) (R : Type) (n : Nat) (k : Nat) (s : &Slice(E, n)) (h : Le(k, n))
      (f : Π(l : &Slice(E, k)) (r : &Slice(E, Sub(n, k))). R) : R := (
    let v = *s;
    let l = TakeS(E, n, k, v, h);
    let r = DropS(E, n, k, v);
    let res = f(&l, &r);
    *s := JoinS(E, n, k, l, r);
    res
  )

  -- [native] An empty array, and growing or shrinking at the end. `ArrPush` takes the array
  -- by value, so no borrow into its block is live when the block is reallocated.
  def ArrEmpty (E : Type) : Array(E, 0) := MkArray(MkSlice(End))

  def ArrPush (E : Type) (n : Nat) (a : Array(E, n)) (x : E) : Array(E, S n) := (
    match a {
      MkArray(s) => MkArray(SnocS(E, n, s, x)),
    }
  )

  def ArrPop (E : Type) (n : Nat) (a : Array(E, S n)) : Array(E, n) × E := (
    match a {
      MkArray(s) => (
        let p = PopS(E, n, s);
        match p {
          Mk(init, last) => (MkArray(init), last),
        }
      ),
    }
  )

  -- ## Built from those, in Ochr

  def Swap (E : Type) (n : Nat) (s : &Slice(E, n)) (i : Nat) (j : Nat) (hi : Lt(i, n)) (hj : Lt(j, n)) : Unit := (
    let a = Read(E, n, &*s, i, hi);
    let b = Read(E, n, &*s, j, hj);
    Set(E, n, &*s, i, b, hi);
    Set(E, n, s, j, a, hj)
  )

  -- `n` copies of `x`, by recursion on `n`.
  def Replicate (E : Type) (n : Nat) (x : E) : Array(E, n) by n := (
    match n {
      Z => ArrEmpty(E),
      S m => ArrPush(E, m, Replicate(E, m, x), x),
    }
  )

  -- Write `x` at `i, …, n - 1`, by recursion on the count `rem` still to go (`rem + i = n`).
  def FillFrom (E : Type) (n : Nat) (s : &Slice(E, n)) (x : E) (i : Nat) (rem : Nat)
      (hr : Eq Nat (Add(rem, i)) n) : Unit by rem := (
    match rem {
      Z => (),
      S r => (
        let hi : Lt(i, n) = J(Nat, S (Add(r, i)), n, λ(z : Nat) : Prop => Lt(i, z), hr, LeAddL(r, i));
        let hr2 : Eq Nat (Add(r, S i)) n =
          J(Nat, S (Add(r, i)), Add(r, S i), λ(z : Nat) : Prop => Eq Nat z n, AddRS(r, i), hr);
        Set(E, n, &*s, i, x, hi);
        FillFrom(E, n, s, x, S i, r, hr2)
      ),
    }
  )

  def Fill (E : Type) (n : Nat) (s : &Slice(E, n)) (x : E) : Unit := FillFrom(E, n, s, x, 0, n, AddZeroR(n))
}


#eval IO.println (run "Arrays" Arrays).show

-- every verdict as expected, and the exact number of declarations (a truncated file changes it)
#guard (run "Arrays" Arrays).allAsExpected
#guard (run "Arrays" Arrays).count == 26


/-! ## The lemma library

The facts a user of the library relies on, each by recursion on an index. Three of them are
what a primitive array would give by definition (D57): putting the two halves of a split back
together gives the original view (`JoinTakeDrop`), the halves of a join are what was joined
(`TakeJoin`, `DropJoin`), and reading after a write (`NthSetSame`, `NthSetOther`). Counting
(`Count`) is how permutations are stated. -/

ochr ArrayLemmas uses Arrays {
  def NthSetSame (E : Type) (n : Nat) (s : Slice(E, n)) (i : Nat) (x : E) (h : Lt(i, n)) :
      Eq E (Nth(E, n, SetS(E, n, s, i, x), i, h)) x by i := (
    match n {
      Z => match h {},
      S m => match s {
        MkSlice(c) => match c {
          MkC(y, t) => match i {
            Z => refl,
            S i' => NthSetSame(E, m, t, i', x, h),
          },
        },
      },
    }
  )

  def NthSetOther (E : Type) (n : Nat) (s : Slice(E, n)) (i : Nat) (j : Nat) (x : E) (hi : Lt(i, n))
      (hj : Lt(j, n)) (ne : Π(e : Eq Nat i j). False) :
      Eq E (Nth(E, n, SetS(E, n, s, i, x), j, hj)) (Nth(E, n, s, j, hj)) by i := (
    match n {
      Z => match hi {},
      S m => match s {
        MkSlice(c) => match c {
          MkC(y, t) => match i {
            Z => match j {
              Z => (
                let no = ne(refl);
                match no {}
              ),
              S j' => refl,
            },
            S i' => match j {
              Z => refl,
              S j' => NthSetOther(E, m, t, i', j', x, hi, hj, ne),
            },
          },
        },
      },
    }
  )

  def JoinTakeDrop (E : Type) (n : Nat) (k : Nat) (s : Slice(E, n)) (h : Le(k, n)) :
      Eq (Slice(E, n)) (JoinS(E, n, k, TakeS(E, n, k, s, h), DropS(E, n, k, s))) s by k := (
    match k {
      Z => refl,
      S k' => match n {
        Z => match h {},
        S m => match s {
          MkSlice(c) => match c {
            MkC(x, t) => JoinTakeDrop(E, m, k', t, h),
          },
        },
      },
    }
  )

  def TakeJoin (E : Type) (n : Nat) (k : Nat) (l : Slice(E, k)) (r : Slice(E, Sub(n, k))) (h : Le(k, n)) :
      Eq (Slice(E, k)) (TakeS(E, n, k, JoinS(E, n, k, l, r), h)) l by k := (
    match k {
      Z => match l {
        MkSlice(c) => match c {
          End => refl,
        },
      },
      S k' => match n {
        Z => match h {},
        S m => match l {
          MkSlice(c) => match c {
            MkC(x, t) => TakeJoin(E, m, k', t, r, h),
          },
        },
      },
    }
  )

  def DropJoin (E : Type) (n : Nat) (k : Nat) (l : Slice(E, k)) (r : Slice(E, Sub(n, k))) (h : Le(k, n)) :
      Eq (Slice(E, Sub(n, k))) (DropS(E, n, k, JoinS(E, n, k, l, r))) r by k := (
    match k {
      Z => refl,
      S k' => match n {
        Z => match h {},
        S m => match l {
          MkSlice(c) => match c {
            MkC(x, t) => DropJoin(E, m, k', t, r, h),
          },
        },
      },
    }
  )

  -- ## Counting
  -- `Count(q, n, s)` is how many elements of `s` equal `q`. Two views with the same counts
  -- for every `q` are permutations of each other.
  def Count (q : Nat) (n : Nat) (s : Slice(Nat, n)) : Nat by n := (
    match n {
      Z => 0,
      S m => match s {
        MkSlice(c) => match c {
          MkC(x, t) => (
            let e = Eqb(q, x);
            match e {
              true => S (Count(q, m, t)),
              false => Count(q, m, t),
            }
          ),
        },
      },
    }
  )

  -- 1 if `x` is `q`, else 0.
  def Ind (q : Nat) (x : Nat) : Nat := (
    let e = Eqb(q, x);
    match e {
      true => 1,
      false => 0,
    }
  )

  def CountJoin (q : Nat) (n : Nat) (k : Nat) (l : Slice(Nat, k)) (r : Slice(Nat, Sub(n, k))) (h : Le(k, n)) :
      Eq Nat (Count(q, n, JoinS(Nat, n, k, l, r))) (Add(Count(q, k, l), Count(q, Sub(n, k), r))) by k := (
    match k {
      Z => refl,
      S k' => match n {
        Z => match h {},
        S m => match l {
          MkSlice(c) => match c {
            MkC(x, t) => (
              let e = Eqb(q, x);
              match e {
                true => CountJoin(q, m, k', t, r, h),
                false => CountJoin(q, m, k', t, r, h),
              }
            ),
          },
        },
      },
    }
  )

  -- Writing `x` over element `i` trades one occurrence of the old element for one of `x`.
  def CountSet (q : Nat) (n : Nat) (s : Slice(Nat, n)) (i : Nat) (x : Nat) (h : Lt(i, n)) :
      Eq Nat (Add(Count(q, n, SetS(Nat, n, s, i, x)), Ind(q, Nth(Nat, n, s, i, h))))
        (Add(Count(q, n, s), Ind(q, x))) by i := (
    match n {
      Z => match h {},
      S m => match s {
        MkSlice(c) => match c {
          MkC(y, t) => match i {
            Z => (
              let ex = Eqb(q, x);
              let ey = Eqb(q, y);
              match ex {
                true => match ey {
                  true => refl,
                  false => AddRS(Count(q, m, t), 0),
                },
                false => match ey {
                  true => EqSym(S (Add(Count(q, m, t), 0)), Add(Count(q, m, t), 1), AddRS(Count(q, m, t), 0)),
                  false => refl,
                },
              }
            ),
            S i' => (
              let ey = Eqb(q, y);
              match ey {
                true => CountSet(q, m, t, i', x, h),
                false => CountSet(q, m, t, i', x, h),
              }
            ),
          },
        },
      },
    }
  )

  -- ## Swapping
  -- The model of `Swap`: `Swap` is, by definition, this write to its view.
  def SwapS (E : Type) (n : Nat) (s : Slice(E, n)) (i : Nat) (j : Nat) (hi : Lt(i, n)) (hj : Lt(j, n)) :
      Slice(E, n) := SetS(E, n, SetS(E, n, s, i, Nth(E, n, s, j, hj)), j, Nth(E, n, s, i, hi))

  def SwapIsSwapS (E : Type) (n : Nat) (s : &Slice(E, n)) (i : Nat) (j : Nat) (hi : Lt(i, n)) (hj : Lt(j, n)) :
      Id Unit (Swap(E, n, s, i, j, hi, hj)) (*s := SwapS(E, n, *s, i, j, hi, hj)) := refl

  -- A swap with the head: the head moves to position `i + 1` of the rest, whose old element
  -- becomes the head. Counts are unchanged, by `CountSet` on the rest.
  def CountSwapHead (q : Nat) (m : Nat) (y : Nat) (t : Slice(Nat, m)) (i : Nat) (h : Lt(i, m)) :
      Eq Nat (Count(q, S m, MkSlice(MkC(Nth(Nat, m, t, i, h), SetS(Nat, m, t, i, y)))))
        (Count(q, S m, MkSlice(MkC(y, t)))) := (
    let a = Count(q, m, SetS(Nat, m, t, i, y));
    let b = Count(q, m, t);
    let hs = CountSet(q, m, t, i, y, h);
    let eb = Eqb(q, Nth(Nat, m, t, i, h));
    let ey = Eqb(q, y);
    match eb {
      true => match ey {
        true => EqTrans(S a, Add(a, 1), S b, EqSym(Add(a, 1), S a, AddOneR(a)), EqTrans(Add(a, 1), Add(b, 1), S b, hs, AddOneR(b))),
        false => EqTrans(S a, Add(a, 1), b, EqSym(Add(a, 1), S a, AddOneR(a)), EqTrans(Add(a, 1), Add(b, 0), b, hs, AddZeroR(b))),
      },
      false => match ey {
        true => EqTrans(a, Add(a, 0), S b, EqSym(Add(a, 0), a, AddZeroR(a)), EqTrans(Add(a, 0), Add(b, 1), S b, hs, AddOneR(b))),
        false => EqTrans(a, Add(a, 0), b, EqSym(Add(a, 0), a, AddZeroR(a)), EqTrans(Add(a, 0), Add(b, 0), b, hs, AddZeroR(b))),
      },
    }
  )

  -- A swap leaves every count unchanged.
  def CountSwap (q : Nat) (n : Nat) (s : Slice(Nat, n)) (i : Nat) (j : Nat) (hi : Lt(i, n)) (hj : Lt(j, n)) :
      Eq Nat (Count(q, n, SwapS(Nat, n, s, i, j, hi, hj))) (Count(q, n, s)) by i := (
    match n {
      Z => match hi {},
      S m => match s {
        MkSlice(c) => match c {
          MkC(y, t) => match i {
            Z => match j {
              Z => refl,
              S j' => CountSwapHead(q, m, y, t, j', hj),
            },
            S i' => match j {
              Z => CountSwapHead(q, m, y, t, i', hi),
              S j' => (
                let ey = Eqb(q, y);
                match ey {
                  true => CountSwap(q, m, t, i', j', hi, hj),
                  false => CountSwap(q, m, t, i', j', hi, hj),
                }
              ),
            },
          },
        },
      },
    }
  )

  -- ## Element borrows
  -- Writing through a borrow of element `i` is `Set` (in place is functional), by the same
  -- bare recursion as `AddMEq`. [checker] This should be accepted, and is rejected by a
  -- checker incompleteness: `GetMut`'s unreachable arm `Z => match h {}` yields ⋆ for the
  -- borrow, and refining `n := Z` (a dead branch: `h : False`) re-runs the goal into that arm,
  -- which then writes through ⋆ ("no such place *r"). The branch is dead, so the error should
  -- not be. When the checker is fixed this verdict flips and the guard below says so.
  reject def GetMutSet (n : Nat) (s : &Slice(Nat, n)) (i : Nat) (w : Nat) (h : Lt(i, n)) :
      Id Unit (let r = GetMut(n, s, i, h); *r := w) (Set(Nat, n, s, i, w, h)) by i := (
    match n {
      Z => match h {},
      S m => match *s {
        MkSlice(c) => match c {
          MkC(x, t) => match i {
            Z => refl,
            S i' => GetMutSet(m, &t, i', w, h),
          },
        },
      },
    }
  )
}

#eval IO.println (run "ArrayLemmas" ArrayLemmas).show

-- every verdict as expected, and the exact number of declarations (a truncated file changes it)
#guard (run "ArrayLemmas" ArrayLemmas).allAsExpected
#guard (run "ArrayLemmas" ArrayLemmas).count == 14

/-! ## The benchmarks (D57)

B1: borrow the first `k` elements, run anything on them, and the rest is unchanged.
B2: quicksort (the next section). B3: insert into a hashmap's bucket in place. B4: a bounds
proof from a runtime comparison. Each is stated about the program itself. -/

ochr ArrayBench uses ArrayLemmas {
  -- ## B1
  -- By definition, for any `g`: after the split, the view is `g`'s result on the old first
  -- `k` elements, joined to the old rest.
  def B1Join (E : Type) (n : Nat) (k : Nat) (g : Π(x : &Slice(E, k)). Unit) (s : &Slice(E, n)) (h : Le(k, n)) :
      Id Unit (WithSplit(E, Unit, n, k, s, h, λ(l : &Slice(E, k)) (r : &Slice(E, Sub(n, k))) : Unit => g(l)))
        (*s := JoinS(E, n, k, (let c = TakeS(E, n, k, *s, h); g(&c); c), DropS(E, n, k, *s))) := refl

  -- Stated about the rest alone, it takes one lemma, for any `g`: `g`'s result has length `k`
  -- by its type, so the rest starts where it did.
  def B1 (E : Type) (n : Nat) (k : Nat) (g : Π(x : &Slice(E, k)). Unit) (s : &Slice(E, n)) (h : Le(k, n)) :
      Eq (Slice(E, Sub(n, k)))
        (let c = *s; WithSplit(E, Unit, n, k, &c, h, λ(l : &Slice(E, k)) (r : &Slice(E, Sub(n, k))) : Unit => g(l)); DropS(E, n, k, c))
        (DropS(E, n, k, *s)) := (
    DropJoin(E, n, k, (let c = TakeS(E, n, k, *s, h); g(&c); c), DropS(E, n, k, *s), h)
  )

  -- A primitive array would give that by definition; here it is not.
  reject def B1Refl (E : Type) (n : Nat) (k : Nat) (g : Π(x : &Slice(E, k)). Unit) (s : &Slice(E, n)) (h : Le(k, n)) :
      Eq (Slice(E, Sub(n, k)))
        (let c = *s; WithSplit(E, Unit, n, k, &c, h, λ(l : &Slice(E, k)) (r : &Slice(E, Sub(n, k))) : Unit => g(l)); DropS(E, n, k, c))
        (DropS(E, n, k, *s)) := refl

  -- Nor is splitting and doing nothing the identity by definition; it is `JoinTakeDrop`.
  reject def SplitNoopRefl (E : Type) (n : Nat) (k : Nat) (s : &Slice(E, n)) (h : Le(k, n)) :
      Id Unit (WithSplit(E, Unit, n, k, s, h, λ(l : &Slice(E, k)) (r : &Slice(E, Sub(n, k))) : Unit => ())) () := refl

  def SplitNoop (E : Type) (n : Nat) (k : Nat) (s : &Slice(E, n)) (h : Le(k, n)) :
      Eq (Slice(E, n)) (let c = *s; WithSplit(E, Unit, n, k, &c, h, λ(l : &Slice(E, k)) (r : &Slice(E, Sub(n, k))) : Unit => ()); c) (*s) := (
    JoinTakeDrop(E, n, k, *s, h)
  )

  -- The motivating use, on a concrete array: zero the first two of five.
  def ZeroFirst2 (s : &Slice(Nat, 5)) : Unit := (
    WithSplit(Nat, Unit, 5, 2, s, refl, λ(l : &Slice(Nat, 2)) (r : &Slice(Nat, 3)) : Unit => Fill(Nat, 2, l, 0))
  )

  def ZeroFirst2Run : Id Nat
      (let a = Replicate(Nat, 5, 7); ZeroFirst2(AsSlice(Nat, 5, &a)); Read(Nat, 5, AsSlice(Nat, 5, &a), 1, refl)
        ) 0 := refl

  def ZeroFirst2Rest : Id Nat
      (let a = Replicate(Nat, 5, 7); ZeroFirst2(AsSlice(Nat, 5, &a)); Read(Nat, 5, AsSlice(Nat, 5, &a), 2, refl)
        ) 7 := refl

  -- ## Reading and writing
  -- A read leaves the view exactly as it was, by definition ...
  def ReadNoop (E : Type) (n : Nat) (s : &Slice(E, n)) (i : Nat) (h : Lt(i, n)) :
      Id Unit (let x = Read(E, n, s, i, h); ()) () := refl

  -- ... a read through a borrow of the element does not: it leaves a put-back program.
  reject def GetMutReadNoop (n : Nat) (s : &Slice(Nat, n)) (i : Nat) (h : Lt(i, n)) :
      Id Unit (let r = GetMut(n, s, i, h); let x = *r; ()) () := refl

  -- Reading after a write, at the same index and at another.
  def ReadAfterSet (E : Type) (n : Nat) (s : &Slice(E, n)) (i : Nat) (x : E) (h : Lt(i, n)) :
      Eq E (let c = *s; Set(E, n, &c, i, x, h); Read(E, n, &c, i, h)) x := NthSetSame(E, n, *s, i, x, h)

  def ReadAfterSetOther (E : Type) (n : Nat) (s : &Slice(E, n)) (i : Nat) (j : Nat) (x : E) (hi : Lt(i, n))
      (hj : Lt(j, n)) (ne : Π(e : Eq Nat i j). False) :
      Eq E (let c = *s; Set(E, n, &c, i, x, hi); Read(E, n, &c, j, hj)) (Read(E, n, s, j, hj)) := (
    NthSetOther(E, n, *s, i, j, x, hi, hj, ne)
  )

  reject def ReadAfterSetRefl (E : Type) (n : Nat) (s : &Slice(E, n)) (i : Nat) (x : E) (h : Lt(i, n)) :
      Eq E (let c = *s; Set(E, n, &c, i, x, h); Read(E, n, &c, i, h)) x := refl

  -- A bounds proof mentions only the index and the length in the type, so no write makes it
  -- stale ...
  def SetTwice (n : Nat) (s : &Slice(Nat, n)) (i : Nat) (h : Lt(i, n)) : Unit := (
    Set(Nat, n, &*s, i, 1, h);
    Set(Nat, n, s, i, 2, h)
  )

  -- ... and without one there is no read.
  reject def ReadPastEnd (s : &Slice(Nat, 2)) : Nat := Read(Nat, 2, s, 2, refl)

  -- ## B4: a bounds proof from a runtime comparison
  def GetOr (E : Type) (n : Nat) (s : &Slice(E, n)) (i : Nat) (d : E) : E := (
    let dec = LtDec(i, n);
    match dec {
      Yes(h) => Read(E, n, s, i, h),
      No(k) => d,
    }
  )

  def GetOrIn : Id Nat (let a = Replicate(Nat, 3, 7); GetOr(Nat, 3, AsSlice(Nat, 3, &a), 1, 0)) 7 := refl
  def GetOrOut : Id Nat (let a = Replicate(Nat, 3, 7); GetOr(Nat, 3, AsSlice(Nat, 3, &a), 5, 0)) 0 := refl

  -- ## Growth
  -- The length is in the type: pushing onto an `Array(E, n)` gives an `Array(E, S n)`.
  def PushPop : Id Nat (let a = ArrPush(Nat, 0, ArrEmpty(Nat), 4); let p = ArrPop(Nat, 0, a); p.2) 4 := refl
  reject def PushWrongLength (a : Array(Nat, 2)) : Array(Nat, 2) := ArrPush(Nat, 2, a, 0)

  -- ## B3: insert into a hashmap's bucket, in place
  -- The slot is `k mod cap`, whose bound is a lemma: no runtime check.
  def ModS (k : Nat) (c : Nat) : Nat by k := (
    match k {
      Z => 0,
      S k' => (
        let r = S (ModS(k', c));
        let e = Eqb(r, c);
        match e {
          true => 0,
          false => r,
        }
      ),
    }
  )

  def LeNext (a : Nat) (c : Nat) (h : Le(a, c)) (e : Eq Bool (Eqb(a, c)) false) : Le(S a, c) by a := (
    match a {
      Z => match c {
        Z => match e {},
        S _ => refl,
      },
      S a' => match c {
        Z => match h {},
        S c' => LeNext(a', c', h, e),
      },
    }
  )

  def ModLt (k : Nat) (c : Nat) (hc : Lt(0, c)) : Lt(ModS(k, c), c) by k := (
    match k {
      Z => hc,
      S k' => (
        let e = Eqb(S (ModS(k', c)), c);
        match e {
          true => hc,
          false => LeNext(S (ModS(k', c)), c, ModLt(k', c, hc), refl),
        }
      ),
    }
  )

  inductive Entry := MkE(key : Nat, val : Nat)

  -- [native] [K1] `GetMut` at the element type `List(Entry)`, until one generic `GetMut` can
  -- return `&E`.
  def GetMutB (n : Nat) (s : &Slice(List(Entry), n)) (i : Nat) (h : Lt(i, n)) : &List(Entry) by i := (
    match n {
      Z => match h {},
      S m => match *s {
        MkSlice(c) => match c {
          MkC(x, t) => match i {
            Z => &x,
            S i' => GetMutB(m, &t, i', h),
          },
        },
      },
    }
  )

  -- [K4] A struct holding an array: the model type is a parameter until a field may be written
  -- `Array(E, cap)`. The capacity is a type parameter, so no dependent field is needed.
  inductive HashMapOf (R : Type) := MkHM(slots : ArrayOf(R), size : Nat)
  def HashMap (cap : Nat) : Type := HashMapOf(Cells(List(Entry), cap))

  -- Insert into a bucket (a list, which may be recursed over): overwrite, or add at the end.
  -- `true` if the key is new.
  def InsertB (b : &List(Entry)) (k : Nat) (v : Nat) : Bool by b := (
    match *b {
      Nil => (
        *b := Cons(MkE(k, v), Nil);
        true
      ),
      Cons(e, t) => match e {
        MkE(k2, v2) => (
          let same = Eqb(k, k2);
          match same {
            true => (
              v2 := v;
              false
            ),
            false => InsertB(&t, k, v),
          }
        ),
      },
    }
  )

  def Insert (cap : Nat) (hm : &HashMap(cap)) (k : Nat) (v : Nat) (hc : Lt(0, cap)) : Unit := (
    match *hm {
      MkHM(slots, size) => (
        let i = ModS(k, cap);
        let b = GetMutB(cap, AsSlice(List(Entry), cap, &slots), i, ModLt(k, cap, hc));
        let fresh = InsertB(b, k, v);
        match fresh {
          true => size := S size,
          false => (),
        }
      ),
    }
  )

  def Size (cap : Nat) (hm : HashMap(cap)) : Nat := (
    match hm {
      MkHM(slots, size) => size,
    }
  )

  -- Keys 5 and 3 collide in a table of two; 5 is inserted twice.
  def InsertRun : Id Nat (
      let hm = MkHM(Replicate(List(Entry), 2, Nil), 0);
      Insert(2, &hm, 5, 50, refl);
      Insert(2, &hm, 3, 30, refl);
      Insert(2, &hm, 5, 51, refl);
      Size(2, hm)) 2 := refl

  def InsertRunBucket : Id (List(Entry)) (
      let hm = MkHM(Replicate(List(Entry), 2, Nil), 0);
      Insert(2, &hm, 5, 50, refl);
      Insert(2, &hm, 3, 30, refl);
      Insert(2, &hm, 5, 51, refl);
      match hm {
        MkHM(slots, size) => Read(List(Entry), 2, AsSlice(List(Entry), 2, &slots), 1, refl),
      }) (Cons(MkE(5, 51), Cons(MkE(3, 30), Nil))) := refl

  -- Without a proof that the slot is in bounds there is no borrow of it.
  reject def InsertUnbounded (cap : Nat) (hm : &HashMap(cap)) (k : Nat) (v : Nat) : Unit := (
    match *hm {
      MkHM(slots, size) => (
        let b = GetMutB(cap, AsSlice(List(Entry), cap, &slots), ModS(k, cap), refl);
        let fresh = InsertB(b, k, v);
        ()
      ),
    }
  )
}

#eval IO.println (run "ArrayBench" ArrayBench).show

-- every verdict as expected, and the exact number of declarations (a truncated file changes it)
#guard (run "ArrayBench" ArrayBench).allAsExpected
#guard (run "ArrayBench" ArrayBench).count == 33

/-! ## B2: quicksort

In place, over a view, recursing over indices only. The partition is Lomuto's scan with index
bounds proved from its invariant; the recursive calls get the two sides of the pivot as
borrowed pieces. What is proved:
* quicksort permutes its view (every count is unchanged), for any fuel (`QSPerm`);
* quicksort sorts its view, for fuel at least the length, given the partition's contract
  (`QSSorted`): four facts about `Partition`, each checked on examples (`ContractRun1`,
  `ContractRun2`) but not yet proved for all inputs. Proving them is Lomuto's positional
  invariant, the one piece of the development still open. -/

ochr Quicksort uses ArrayLemmas {
  -- Lomuto's partition around the pivot `p`, which sits at index 0. Elements `1 … i` are at
  -- most `p` and `i + 1 … j - 1` are greater; `rem` elements are still to scan (`rem + j = n`).
  -- The recursion is on `rem`, never on the view. Every bound is a lemma about indices.
  def Scan (n : Nat) (s : &Slice(Nat, n)) (p : Nat) (i : Nat) (j : Nat) (rem : Nat)
      (hij : Lt(i, j)) (hr : Eq Nat (Add(rem, j)) n) : Nat by rem := (
    match rem {
      Z => (
        let hin : Lt(i, n) = J(Nat, j, n, λ(z : Nat) : Prop => Lt(i, z), hr, hij);
        Swap(Nat, n, s, 0, i, LeTrans(1, S i, n, refl, hin), hin);
        i
      ),
      S r => (
        let hjn : Lt(j, n) = J(Nat, S (Add(r, j)), n, λ(z : Nat) : Prop => Lt(j, z), hr, LeAddL(r, j));
        let hr2 : Eq Nat (Add(r, S j)) n = J(Nat, S (Add(r, j)), Add(r, S j), λ(z : Nat) : Prop => Eq Nat z n, AddRS(r, j), hr);
        let x = Read(Nat, n, &*s, j, hjn);
        let b = Leb(x, p);
        match b {
          true => (
            Swap(Nat, n, &*s, S i, j, LeTrans(S (S i), S j, n, hij, hjn), hjn);
            Scan(n, s, p, S i, S j, r, hij, hr2)
          ),
          false => Scan(n, s, p, i, S j, r, LeStep(S i, j, hij), hr2),
        }
      ),
    }
  )

  -- The pivot's final index.
  def Partition (m : Nat) (s : &Slice(Nat, S m)) : Nat := (
    let p = Read(Nat, S m, &*s, 0, refl);
    Scan(S m, s, p, 0, 1, m, refl, AddOneR(m))
  )

  -- Sort both sides of the pivot at `k`, with `rec`. The pieces are borrowed by continuations
  -- (`WithSplit`), so each recursive call sees only its own piece. Written once for any `rec`,
  -- which is also what its lemmas are about.
  def Recurse (rec : Π(n : Nat) (s : &Slice(Nat, n)). Unit) (m : Nat) (k : Nat) (s : &Slice(Nat, S m)) : Unit := (
    let d = LeDec(k, m);
    match d {
      Yes(hk) => WithSplit(Nat, Unit, S m, k, s, LeStep(k, m, hk),
        λ(l : &Slice(Nat, k)) (r : &Slice(Nat, Sub(S m, k))) : Unit => (
          rec(k, l);
          WithSplit(Nat, Unit, Sub(S m, k), 1, r, SubPos(m, k, hk),
            λ(p : &Slice(Nat, 1)) (rr : &Slice(Nat, Sub(Sub(S m, k), 1))) : Unit => rec(Sub(Sub(S m, k), 1), rr))
        )),
      No(nk) => (),
    }
  )

  -- [K6] The recursion is on the length, but the lengths `k` and `m - k` of the pieces are not
  -- structural subterms of `S m`; until recursion on a measure exists, fuel bounds the depth
  -- (`QS(n, n, s)` sorts).
  def QS (fuel : Nat) (n : Nat) (s : &Slice(Nat, n)) : Unit by fuel := (
    match fuel {
      Z => (),
      S f => match n {
        Z => (),
        S m => (
          let k = Partition(m, &*s);
          Recurse(λ(n' : Nat) (s' : &Slice(Nat, n')) : Unit => QS(f, n', s'), m, k, s)
        ),
      },
    }
  )

  def SortArray (n : Nat) (a : &Array(Nat, n)) : Unit := QS(n, n, AsSlice(Nat, n, a))

  def SortRun : Id (Array(Nat, 5))
      (let a = MkArray(MkSlice(MkC(3, MkSlice(MkC(1, MkSlice(MkC(4, MkSlice(MkC(1, MkSlice(MkC(2, MkSlice(End)))))))))))); SortArray(5, &a); a)
      (MkArray(MkSlice(MkC(1, MkSlice(MkC(1, MkSlice(MkC(2, MkSlice(MkC(3, MkSlice(MkC(4, MkSlice(End))))))))))))) := refl

  reject def SortRunWrong : Id (Array(Nat, 5))
      (let a = MkArray(MkSlice(MkC(3, MkSlice(MkC(1, MkSlice(MkC(4, MkSlice(MkC(1, MkSlice(MkC(2, MkSlice(End)))))))))))); SortArray(5, &a); a)
      (MkArray(MkSlice(MkC(1, MkSlice(MkC(1, MkSlice(MkC(2, MkSlice(MkC(4, MkSlice(MkC(3, MkSlice(End))))))))))))) := refl

  -- ## Quicksort permutes: every count is unchanged
  -- Rewriting under `Add` and `Count` is transport.
  def AddCongL (a : Nat) (a2 : Nat) (b : Nat) (e : Eq Nat a a2) : Eq Nat (Add(a, b)) (Add(a2, b)) := (
    J(Nat, a, a2, λ(z : Nat) : Prop => Eq Nat (Add(a, b)) (Add(z, b)), e, refl)
  )

  def AddCongR (a : Nat) (b : Nat) (b2 : Nat) (e : Eq Nat b b2) : Eq Nat (Add(a, b)) (Add(a, b2)) := (
    J(Nat, b, b2, λ(z : Nat) : Prop => Eq Nat (Add(a, b)) (Add(a, z)), e, refl)
  )

  def CountCong (q : Nat) (n : Nat) (s : Slice(Nat, n)) (s2 : Slice(Nat, n)) (e : Eq (Slice(Nat, n)) s s2) :
      Eq Nat (Count(q, n, s)) (Count(q, n, s2)) := (
    J(Slice(Nat, n), s, s2, λ(z : Slice(Nat, n)) : Prop => Eq Nat (Count(q, n, s)) (Count(q, n, z)), e, refl)
  )

  -- The scan only swaps.
  def ScanPerm (n : Nat) (s : &Slice(Nat, n)) (p : Nat) (i : Nat) (j : Nat) (rem : Nat)
      (hij : Lt(i, j)) (hr : Eq Nat (Add(rem, j)) n) (q : Nat) :
      (let old = *s; Eq Nat (Count(q, n, (Scan(n, &*s, p, i, j, rem, hij, hr); *s))) (Count(q, n, old))) by rem := (
    match rem {
      Z => (
        let hin : Lt(i, n) = J(Nat, j, n, λ(z : Nat) : Prop => Lt(i, z), hr, hij);
        CountSwap(q, n, *s, 0, i, LeTrans(1, S i, n, refl, hin), hin)
      ),
      S r => (
        let hjn : Lt(j, n) = J(Nat, S (Add(r, j)), n, λ(z : Nat) : Prop => Lt(j, z), hr, LeAddL(r, j));
        let hr2 : Eq Nat (Add(r, S j)) n = J(Nat, S (Add(r, j)), Add(r, S j), λ(z : Nat) : Prop => Eq Nat z n, AddRS(r, j), hr);
        let x = Nth(Nat, n, *s, j, hjn);
        let b = Leb(x, p);
        match b {
          true => (
            let c = SwapS(Nat, n, *s, S i, j, LeTrans(S (S i), S j, n, hij, hjn), hjn);
            let e1 = ScanPerm(n, &c, p, S i, S j, r, hij, hr2, q);
            let e2 = CountSwap(q, n, *s, S i, j, LeTrans(S (S i), S j, n, hij, hjn), hjn);
            EqTrans(Count(q, n, (let d = c; Scan(n, &d, p, S i, S j, r, hij, hr2); d)), Count(q, n, c), Count(q, n, *s), e1, e2)
          ),
          false => ScanPerm(n, s, p, i, S j, r, LeStep(S i, j, hij), hr2, q),
        }
      ),
    }
  )
  def PartitionPerm (m : Nat) (s : &Slice(Nat, S m)) (q : Nat) :
      (let old = *s; Eq Nat (Count(q, S m, (Partition(m, &*s); *s))) (Count(q, S m, old))) := (
    let p = Nth(Nat, S m, *s, 0, refl);
    ScanPerm(S m, s, p, 0, 1, m, refl, AddOneR(m), q)
  )

  -- The recursive step permutes, for any `rec` that does.
  def RecursePerm (rec : Π(n : Nat) (s : &Slice(Nat, n)). Unit)
      (ih : Π(n : Nat) (s : &Slice(Nat, n)) (q : Nat). (let old = *s; Eq Nat (Count(q, n, (rec(n, &*s); *s))) (Count(q, n, old))))
      (m : Nat) (k : Nat) (s : &Slice(Nat, S m)) (q : Nat) :
      (let old = *s; Eq Nat (Count(q, S m, (Recurse(rec, m, k, &*s); *s))) (Count(q, S m, old))) := (
    let d = LeDec(k, m);
    match d {
      Yes(hk) => (
        let hk2 = LeStep(k, m, hk);
        let h1 = SubPos(m, k, hk);
        -- the pieces before, and after the two recursive calls
        let tk = TakeS(Nat, S m, k, *s, hk2);
        let r0 = DropS(Nat, S m, k, *s);
        let pv = TakeS(Nat, Sub(S m, k), 1, r0, h1);
        let rr = DropS(Nat, Sub(S m, k), 1, r0);
        let l2 = (let c = tk; rec(k, &c); c);
        let rr2 = (let c = rr; rec(Sub(Sub(S m, k), 1), &c); c);
        let x2 = JoinS(Nat, Sub(S m, k), 1, pv, rr2);
        -- their counts
        let cf = Count(q, S m, JoinS(Nat, S m, k, l2, x2));
        let cl2 = Count(q, k, l2);
        let ctk = Count(q, k, tk);
        let cx2 = Count(q, Sub(S m, k), x2);
        let cpv = Count(q, 1, pv);
        let crr2 = Count(q, Sub(Sub(S m, k), 1), rr2);
        let crr = Count(q, Sub(Sub(S m, k), 1), rr);
        let cj = Count(q, Sub(S m, k), JoinS(Nat, Sub(S m, k), 1, pv, rr));
        let cr0 = Count(q, Sub(S m, k), r0);
        let cj0 = Count(q, S m, JoinS(Nat, S m, k, tk, r0));
        let cs = Count(q, S m, *s);
        -- the left part: the recursive call permutes it
        let s1 : Eq Nat cf (Add(ctk, cx2)) = EqTrans(cf, Add(cl2, cx2), Add(ctk, cx2),
          CountJoin(q, S m, k, l2, x2, hk2), AddCongL(cl2, ctk, cx2, (let c = tk; ih(k, &c, q))));
        -- the right part: the pivot is untouched and the recursive call permutes the rest
        let s2 : Eq Nat cx2 cr0 = EqTrans(cx2, Add(cpv, crr2), cr0, CountJoin(q, Sub(S m, k), 1, pv, rr2, h1),
          EqTrans(Add(cpv, crr2), Add(cpv, crr), cr0, AddCongR(cpv, crr2, crr, (let c = rr; ih(Sub(Sub(S m, k), 1), &c, q))),
            EqTrans(Add(cpv, crr), cj, cr0, EqSym(cj, Add(cpv, crr), CountJoin(q, Sub(S m, k), 1, pv, rr, h1)),
              CountCong(q, Sub(S m, k), JoinS(Nat, Sub(S m, k), 1, pv, rr), r0, JoinTakeDrop(Nat, Sub(S m, k), 1, r0, h1)))));
        -- and the two parts are the view, split
        let s3 : Eq Nat (Add(ctk, cr0)) cs = EqTrans(Add(ctk, cr0), cj0, cs, EqSym(cj0, Add(ctk, cr0), CountJoin(q, S m, k, tk, r0, hk2)),
          CountCong(q, S m, JoinS(Nat, S m, k, tk, r0), *s, JoinTakeDrop(Nat, S m, k, *s, hk2)));
        EqTrans(cf, Add(ctk, cx2), cs, s1, EqTrans(Add(ctk, cx2), Add(ctk, cr0), cs, AddCongR(ctk, cx2, cr0, s2), s3))
      ),
      No(nk) => refl,
    }
  )

  -- The closure `QS` passes to `Recurse`, built outside `QS`: it captures the sort and the fuel,
  -- as the one inside `QS` captures `QS` itself and its fuel, so the two are the same value.
  def RecWith (qs : Π(fuel : Nat) (n : Nat) (s : &Slice(Nat, n)). Unit) (fuel : Nat) : (Π(n : Nat) (s : &Slice(Nat, n)). Unit) := (
    match fuel {
      Z => (λ(n : Nat) (s : &Slice(Nat, n)) : Unit => ()),
      S f => (λ(n : Nat) (s : &Slice(Nat, n)) : Unit => qs(f, n, s)),
    }
  )

  -- Quicksort permutes its view: every count is unchanged.
  def QSPerm (fuel : Nat) (n : Nat) (s : &Slice(Nat, n)) (q : Nat) :
      (let old = *s; Eq Nat (Count(q, n, (QS(fuel, n, &*s); *s))) (Count(q, n, old))) by fuel := (
    match fuel {
      Z => refl,
      S f => match n {
        Z => refl,
        S m => (
          let rec = RecWith(QS, fuel);
          let c = *s;
          let k = Partition(m, &c);
          let e1 = RecursePerm(rec,
            λ(n2 : Nat) (s2 : &Slice(Nat, n2)) (q2 : Nat) :
                (let old = *s2; Eq Nat (Count(q2, n2, (QS(f, n2, &*s2); *s2))) (Count(q2, n2, old))) =>
              QSPerm(f, n2, s2, q2),
            m, k, &c, q);
          EqTrans(Count(q, S m, (let d = c; Recurse(rec, m, k, &d); d)), Count(q, S m, c), Count(q, S m, *s),
            e1, PartitionPerm(m, s, q))
        ),
      },
    }
  )
  -- ## Quicksort sorts, given the partition's contract
  -- Every element is at most `p`; at least `p`; and the view is sorted. Each is a
  -- proposition computed by recursion on the length.
  def AllLe (n : Nat) (s : Slice(Nat, n)) (p : Nat) : Prop by n := (
    match n {
      Z => ⊤,
      S m => match s {
        MkSlice(c) => match c {
          MkC(x, t) => Le(x, p) ∧ AllLe(m, t, p),
        },
      },
    }
  )

  def AllGe (n : Nat) (s : Slice(Nat, n)) (p : Nat) : Prop by n := (
    match n {
      Z => ⊤,
      S m => match s {
        MkSlice(c) => match c {
          MkC(x, t) => Le(p, x) ∧ AllGe(m, t, p),
        },
      },
    }
  )

  def Sorted (n : Nat) (s : Slice(Nat, n)) : Prop by n := (
    match n {
      Z => ⊤,
      S m => match s {
        MkSlice(c) => match c {
          MkC(x, t) => AllGe(m, t, x) ∧ Sorted(m, t),
        },
      },
    }
  )

  -- A lower bound can be lowered.
  def AllGeWeaken (n : Nat) (s : Slice(Nat, n)) (x : Nat) (a : Nat) (h : AllGe(n, s, x)) (hax : Le(a, x)) :
      AllGe(n, s, a) by n := (
    match n {
      Z => refl,
      S m => match s {
        MkSlice(c) => match c {
          MkC(y, t) => match h {
            Intro(hy, ht) => ⟨LeTrans(a, x, y, hax, hy), AllGeWeaken(m, t, x, a, ht, hax)⟩,
          },
        },
      },
    }
  )

  -- Taking a conjunction apart, and building one with its conjuncts named. [⋆] `⟨p, q⟩`,
  -- whose conjuncts are inferred from the expected type, trips the checker incompleteness in
  -- `AllGeJoin` and `SortedJoin`; naming them avoids it.
  def AndL (P : Prop) (Q : Prop) (h : P ∧ Q) : P := match h { Intro(p, q) => p }
  def AndR (P : Prop) (Q : Prop) (h : P ∧ Q) : Q := match h { Intro(p, q) => q }

  def AndI (P : Prop) (Q : Prop) (p : P) (q : Q) : P ∧ Q := ⟨p, q⟩

  -- variant A: no annotation, explicit And parameters via AndI
  def AllGeJoin (n : Nat) (k : Nat) (l : Slice(Nat, k)) (r : Slice(Nat, Sub(n, k))) (h : Le(k, n)) (a : Nat)
      (hl : AllGe(k, l, a)) (hr : AllGe(Sub(n, k), r, a)) : AllGe(n, JoinS(Nat, n, k, l, r), a) by k := (
    match k {
      Z => hr,
      S k' => match n {
        Z => match h {},
        S m => match l {
          MkSlice(c) => match c {
            MkC(y, t) => AndI(Le(a, y), AllGe(m, JoinS(Nat, m, k', t, r), a), AndL(Le(a, y), AllGe(k', t, a), hl),
              AllGeJoin(m, k', t, r, h, a, AndR(Le(a, y), AllGe(k', t, a), hl), hr)),
          },
        },
      },
    }
  )

  -- Two sorted views joined, everything on the left at most `x` and on the right at least
  -- `x`, are sorted.
  def SortedJoin (n : Nat) (k : Nat) (l : Slice(Nat, k)) (r : Slice(Nat, Sub(n, k))) (h : Le(k, n)) (x : Nat)
      (hl : Sorted(k, l)) (hlx : AllLe(k, l, x)) (hr : Sorted(Sub(n, k), r)) (hrx : AllGe(Sub(n, k), r, x)) :
      Sorted(n, JoinS(Nat, n, k, l, r)) by k := (
    match k {
      Z => hr,
      S k' => match n {
        Z => match h {},
        S m => match l {
          MkSlice(c) => match c {
            MkC(a, t) => AndI(AllGe(m, JoinS(Nat, m, k', t, r), a), Sorted(m, JoinS(Nat, m, k', t, r)),
              AllGeJoin(m, k', t, r, h, a, AndL(AllGe(k', t, a), Sorted(k', t), hl),
                AllGeWeaken(Sub(m, k'), r, x, a, hrx, AndL(Le(a, x), AllLe(k', t, x), hlx))),
              SortedJoin(m, k', t, r, h, x, AndR(AllGe(k', t, a), Sorted(k', t), hl), AndR(Le(a, x), AllLe(k', t, x), hlx), hr, hrx)),
          },
        },
      },
    }
  )

  -- ## Bounds survive a permutation, by counting
  def EqbRefl (x : Nat) : Eq Bool (Eqb(x, x)) true by x := (
    match x {
      Z => refl,
      S x' => EqbRefl(x'),
    }
  )

  -- If q = x (by Eqb), x <= p and p < q is impossible; and the mirror image.
  def EqbLeLt (q : Nat) (x : Nat) (p : Nat) (e : Eq Bool (Eqb(q, x)) true) (h1 : Le(x, p)) (h2 : Lt(p, q)) : False by q := (
    match q {
      Z => match h2 {},
      S q' => match x {
        Z => match e {},
        S x' => match p {
          Z => match h1 {},
          S p' => EqbLeLt(q', x', p', e, h1, h2),
        },
      },
    }
  )

  def EqbGeLt (q : Nat) (x : Nat) (p : Nat) (e : Eq Bool (Eqb(q, x)) true) (h1 : Le(p, x)) (h2 : Lt(q, p)) : False by q := (
    match q {
      Z => match x {
        Z => match p {
          Z => match h2 {},
          S p' => match h1 {},
        },
        S x' => match e {},
      },
      S q' => match x {
        Z => match e {},
        S x' => match p {
          Z => match h2 {},
          S p' => EqbGeLt(q', x', p', e, h1, h2),
        },
      },
    }
  )

  -- Every element at most `p`: no value above `p` occurs.
  def CountAboveZero (n : Nat) (s : Slice(Nat, n)) (p : Nat) (h : AllLe(n, s, p)) (q : Nat) (hq : Lt(p, q)) :
      Eq Nat (Count(q, n, s)) 0 by n := (
    match n {
      Z => refl,
      S m => match s {
        MkSlice(c) => match c {
          MkC(x, t) => (
            let e = Eqb(q, x);
            match e {
              true => (
                let no = EqbLeLt(q, x, p, refl, AndL(Le(x, p), AllLe(m, t, p), h), hq);
                match no {}
              ),
              false => CountAboveZero(m, t, p, AndR(Le(x, p), AllLe(m, t, p), h), q, hq),
            }
          ),
        },
      },
    }
  )

  def CountBelowZero (n : Nat) (s : Slice(Nat, n)) (p : Nat) (h : AllGe(n, s, p)) (q : Nat) (hq : Lt(q, p)) :
      Eq Nat (Count(q, n, s)) 0 by n := (
    match n {
      Z => refl,
      S m => match s {
        MkSlice(c) => match c {
          MkC(x, t) => (
            let e = Eqb(q, x);
            match e {
              true => (
                let no = EqbGeLt(q, x, p, refl, AndL(Le(p, x), AllGe(m, t, p), h), hq);
                match no {}
              ),
              false => CountBelowZero(m, t, p, AndR(Le(p, x), AllGe(m, t, p), h), q, hq),
            }
          ),
        },
      },
    }
  )

  -- A count of zero for the whole is a count of zero for the rest.
  def CountTailZero (q : Nat) (m : Nat) (x : Nat) (t : Slice(Nat, m)) (e0 : Eq Nat (Count(q, S m, MkSlice(MkC(x, t)))) 0) :
      Eq Nat (Count(q, m, t)) 0 := (
    let e = Eqb(q, x);
    match e {
      true => match e0 {},
      false => e0,
    }
  )

  -- Conversely: if no value above `p` occurs, every element is at most `p`.
  def AllLeOfCounts (n : Nat) (s : Slice(Nat, n)) (p : Nat)
      (hz : Π(q : Nat) (hq : Lt(p, q)). Eq Nat (Count(q, n, s)) 0) : AllLe(n, s, p) by n := (
    match n {
      Z => refl,
      S m => match s {
        MkSlice(c) => match c {
          MkC(x, t) => (
            let d = LeDec(x, p);
            match d {
              Yes(hle) => AndI(Le(x, p), AllLe(m, t, p), hle,
                AllLeOfCounts(m, t, p, λ(q : Nat) (hq : Lt(p, q)) : Eq Nat (Count(q, m, t)) 0 => CountTailZero(q, m, x, t, hz(q, hq)))),
              No(nk) => (
                let e1 = hz(x, nk);
                let r1 = EqbRefl(x);
                let e = Eqb(x, x);
                match e {
                  true => match e1 {},
                  false => match r1 {},
                }
              ),
            }
          ),
        },
      },
    }
  )

  def AllGeOfCounts (n : Nat) (s : Slice(Nat, n)) (p : Nat)
      (hz : Π(q : Nat) (hq : Lt(q, p)). Eq Nat (Count(q, n, s)) 0) : AllGe(n, s, p) by n := (
    match n {
      Z => refl,
      S m => match s {
        MkSlice(c) => match c {
          MkC(x, t) => (
            let d = LeDec(p, x);
            match d {
              Yes(hle) => AndI(Le(p, x), AllGe(m, t, p), hle,
                AllGeOfCounts(m, t, p, λ(q : Nat) (hq : Lt(q, p)) : Eq Nat (Count(q, m, t)) 0 => CountTailZero(q, m, x, t, hz(q, hq)))),
              No(nk) => (
                let e1 = hz(x, nk);
                let r1 = EqbRefl(x);
                let e = Eqb(x, x);
                match e {
                  true => match e1 {},
                  false => match r1 {},
                }
              ),
            }
          ),
        },
      },
    }
  )

  -- So a bound on every element survives any permutation.
  def AllLePerm (n : Nat) (s : Slice(Nat, n)) (s2 : Slice(Nat, n)) (p : Nat) (h : AllLe(n, s, p))
      (perm : Π(q : Nat). Eq Nat (Count(q, n, s2)) (Count(q, n, s))) : AllLe(n, s2, p) := (
    AllLeOfCounts(n, s2, p, λ(q : Nat) (hq : Lt(p, q)) : Eq Nat (Count(q, n, s2)) 0 =>
      EqTrans(Count(q, n, s2), Count(q, n, s), 0, perm(q), CountAboveZero(n, s, p, h, q, hq)))
  )

  def AllGePerm (n : Nat) (s : Slice(Nat, n)) (s2 : Slice(Nat, n)) (p : Nat) (h : AllGe(n, s, p))
      (perm : Π(q : Nat). Eq Nat (Count(q, n, s2)) (Count(q, n, s))) : AllGe(n, s2, p) := (
    AllGeOfCounts(n, s2, p, λ(q : Nat) (hq : Lt(q, p)) : Eq Nat (Count(q, n, s2)) 0 =>
      EqTrans(Count(q, n, s2), Count(q, n, s), 0, perm(q), CountBelowZero(n, s, p, h, q, hq)))
  )

  def LeSuccFalse (m : Nat) (h : Le(S m, m)) : False by m := (
    match m {
      Z => match h {},
      S m' => LeSuccFalse(m', h),
    }
  )

  -- [⋆] `rec` permutes a piece, as a function of `q`. A helper, so that the λ captures a
  -- parameter rather than a piece that embeds a bounds proof.
  def PermOf (n : Nat) (rec : Π(n : Nat) (s : &Slice(Nat, n)). Unit)
      (ihP : Π(n : Nat) (s : &Slice(Nat, n)) (q : Nat). (let old = *s; Eq Nat (Count(q, n, (rec(n, &*s); *s))) (Count(q, n, old))))
      (t : Slice(Nat, n)) : (Π(q : Nat). Eq Nat (Count(q, n, (let c = t; rec(n, &c); c))) (Count(q, n, t))) := (
    λ(q : Nat) : Eq Nat (Count(q, n, (let c = t; rec(n, &c); c))) (Count(q, n, t)) => (let c = t; ihP(n, &c, q))
  )

  -- [⋆] The bounds on a piece survive `rec`, stated for a piece given as a parameter.
  def AllLeRec (n : Nat) (rec : Π(n : Nat) (s : &Slice(Nat, n)). Unit)
      (ihP : Π(n : Nat) (s : &Slice(Nat, n)) (q : Nat). (let old = *s; Eq Nat (Count(q, n, (rec(n, &*s); *s))) (Count(q, n, old))))
      (t : Slice(Nat, n)) (p : Nat) (h : AllLe(n, t, p)) : AllLe(n, (let c = t; rec(n, &c); c), p) := (
    AllLePerm(n, t, (let c = t; rec(n, &c); c), p, h, PermOf(n, rec, ihP, t))
  )

  def AllGeRec (n : Nat) (rec : Π(n : Nat) (s : &Slice(Nat, n)). Unit)
      (ihP : Π(n : Nat) (s : &Slice(Nat, n)) (q : Nat). (let old = *s; Eq Nat (Count(q, n, (rec(n, &*s); *s))) (Count(q, n, old))))
      (t : Slice(Nat, n)) (p : Nat) (h : AllGe(n, t, p)) : AllGe(n, (let c = t; rec(n, &c); c), p) := (
    AllGePerm(n, t, (let c = t; rec(n, &c); c), p, h, PermOf(n, rec, ihP, t))
  )

  -- ## Sorting
  -- The recursive step sorts the view, given the partition's facts about it (the pivot `x`
  -- ends at `k`; everything before is at most `x`, everything after at least `x`) and a
  -- `rec` that sorts and permutes views no longer than `m`.
  def RecurseSorted (m : Nat) (rec : Π(n : Nat) (s : &Slice(Nat, n)). Unit)
      (ihS : Π(n : Nat) (s : &Slice(Nat, n)) (hn : Le(n, m)). (let c = *s; rec(n, &c); Sorted(n, c)))
      (ihP : Π(n : Nat) (s : &Slice(Nat, n)) (q : Nat). (let old = *s; Eq Nat (Count(q, n, (rec(n, &*s); *s))) (Count(q, n, old))))
      (k : Nat) (hk : Le(k, m)) (x : Nat) (s : &Slice(Nat, S m))
      (hL : AllLe(k, TakeS(Nat, S m, k, *s, LeStep(k, m, hk)), x))
      (hP : Eq (Slice(Nat, 1)) (MkSlice(MkC(x, MkSlice(End)))) (TakeS(Nat, Sub(S m, k), 1, DropS(Nat, S m, k, *s), SubPos(m, k, hk))))
      (hR : AllGe(Sub(Sub(S m, k), 1), DropS(Nat, Sub(S m, k), 1, DropS(Nat, S m, k, *s)), x)) :
      (let c = *s; Recurse(rec, m, k, &c); Sorted(S m, c)) := (
    let d = LeDec(k, m);
    match d {
      Yes(hk3) => (
        let hk2 = LeStep(k, m, hk);
        let h1 = SubPos(m, k, hk);
        let tk = TakeS(Nat, S m, k, *s, hk2);
        let r0 = DropS(Nat, S m, k, *s);
        let pv = TakeS(Nat, Sub(S m, k), 1, r0, h1);
        let rr = DropS(Nat, Sub(S m, k), 1, r0);
        let l2 = (let c = tk; rec(k, &c); c);
        let rr2 = (let c = rr; rec(Sub(Sub(S m, k), 1), &c); c);
        let x2 = JoinS(Nat, Sub(S m, k), 1, pv, rr2);
        let one = MkSlice(MkC(x, MkSlice(End)));
        -- the left part: sorted by `rec`, and still at most `x` because `rec` permutes
        let sl2 : Sorted(k, l2) = (let c = tk; ihS(k, &c, hk));
        let bl2 : AllLe(k, l2, x) = AllLeRec(k, rec, ihP, tk, x, hL);
        -- the right part: likewise, at least `x`
        let srr2 : Sorted(Sub(Sub(S m, k), 1), rr2) = (let c = rr; ihS(Sub(Sub(S m, k), 1), &c, SubOneLe(m, k)));
        let brr2 : AllGe(Sub(Sub(S m, k), 1), rr2, x) = AllGeRec(Sub(Sub(S m, k), 1), rec, ihP, rr, x, hR);
        -- the pivot piece is `[x]`
        let spv : Sorted(1, pv) = J(Slice(Nat, 1), one, pv, λ(z : Slice(Nat, 1)) : Prop => Sorted(1, z), hP, refl);
        let lpv : AllLe(1, pv, x) = J(Slice(Nat, 1), one, pv, λ(z : Slice(Nat, 1)) : Prop => AllLe(1, z, x), hP,
          AndI(Le(x, x), ⊤, LeRefl(x), refl));
        let gpv : AllGe(1, pv, x) = J(Slice(Nat, 1), one, pv, λ(z : Slice(Nat, 1)) : Prop => AllGe(1, z, x), hP,
          AndI(Le(x, x), ⊤, LeRefl(x), refl));
        -- glue: pivot and right part, then left part and the rest
        let sx2 : Sorted(Sub(S m, k), x2) = SortedJoin(Sub(S m, k), 1, pv, rr2, h1, x, spv, lpv, srr2, brr2);
        let gx2 : AllGe(Sub(S m, k), x2, x) = AllGeJoin(Sub(S m, k), 1, pv, rr2, h1, x, gpv, brr2);
        SortedJoin(S m, k, l2, x2, hk2, x, sl2, bl2, sx2, gx2)
      ),
      No(nk) => (
        let no = LeSuccFalse(m, LeTrans(S m, k, m, nk, hk));
        match no {}
      ),
    }
  )

  -- ## The partition's contract
  -- Run on a copy of its input `v`, the partition returns `k` and leaves `PartV(m, v)`. Its
  -- contract: the pivot `x` (the first element of `v`) ends at `k <= m`, everything before
  -- it is at most `x`, and everything after it at least `x`.
  def PartK (m : Nat) (v : Slice(Nat, S m)) : Nat := (
    let c = v;
    Partition(m, &c)
  )

  def PartV (m : Nat) (v : Slice(Nat, S m)) : Slice(Nat, S m) := (
    let c = v;
    Partition(m, &c);
    c
  )

  def PartLe (m : Nat) (v : Slice(Nat, S m)) : Prop := Le(PartK(m, v), m)

  def PartLeft (m : Nat) (v : Slice(Nat, S m)) (hk : PartLe(m, v)) : Prop := (
    AllLe(PartK(m, v), TakeS(Nat, S m, PartK(m, v), PartV(m, v), LeStep(PartK(m, v), m, hk)), Nth(Nat, S m, v, 0, refl))
  )

  def PartPivot (m : Nat) (v : Slice(Nat, S m)) (hk : PartLe(m, v)) : Prop := (
    Eq (Slice(Nat, 1)) (MkSlice(MkC(Nth(Nat, S m, v, 0, refl), MkSlice(End))))
      (TakeS(Nat, Sub(S m, PartK(m, v)), 1, DropS(Nat, S m, PartK(m, v), PartV(m, v)), SubPos(m, PartK(m, v), hk)))
  )

  def PartRight (m : Nat) (v : Slice(Nat, S m)) (hk : PartLe(m, v)) : Prop := (
    AllGe(Sub(Sub(S m, PartK(m, v)), 1), DropS(Nat, Sub(S m, PartK(m, v)), 1, DropS(Nat, S m, PartK(m, v), PartV(m, v))),
      Nth(Nat, S m, v, 0, refl))
  )

  -- Quicksort sorts, for fuel at least the length, given the partition's contract.
  def QSSorted (specLe : Π(m : Nat) (v : Slice(Nat, S m)). PartLe(m, v))
      (specL : Π(m : Nat) (v : Slice(Nat, S m)) (hk : PartLe(m, v)). PartLeft(m, v, hk))
      (specP : Π(m : Nat) (v : Slice(Nat, S m)) (hk : PartLe(m, v)). PartPivot(m, v, hk))
      (specR : Π(m : Nat) (v : Slice(Nat, S m)) (hk : PartLe(m, v)). PartRight(m, v, hk))
      (fuel : Nat) (n : Nat) (s : &Slice(Nat, n)) (hf : Le(n, fuel)) :
      (let c = *s; QS(fuel, n, &c); Sorted(n, c)) by fuel := (
    match fuel {
      Z => match n {
        Z => refl,
        S m => match hf {},
      },
      S f => match n {
        Z => refl,
        S m => (
          let rec = RecWith(QS, fuel);
          let v = *s;
          let hk = specLe(m, v);
          let c = *s;
          let k = Partition(m, &c);
          RecurseSorted(m, rec,
            λ(n2 : Nat) (s2 : &Slice(Nat, n2)) (hn : Le(n2, m)) : (let c2 = *s2; QS(f, n2, &c2); Sorted(n2, c2)) =>
              QSSorted(specLe, specL, specP, specR, f, n2, s2, LeTrans(n2, m, f, hn, hf)),
            λ(n2 : Nat) (s2 : &Slice(Nat, n2)) (q2 : Nat) :
                (let old = *s2; Eq Nat (Count(q2, n2, (QS(f, n2, &*s2); *s2))) (Count(q2, n2, old))) =>
              QSPerm(f, n2, s2, q2),
            k, hk, Nth(Nat, S m, v, 0, refl), &c, specL(m, v, hk), specP(m, v, hk), specR(m, v, hk))
        ),
      },
    }
  )

  -- The contract holds on examples (it is what remains to prove about `Scan`).
  def ContractRun1 : PartLe(4, MkSlice(MkC(3, MkSlice(MkC(1, MkSlice(MkC(4, MkSlice(MkC(1, MkSlice(MkC(2, MkSlice(End)))))))))))) ∧ PartLeft(4, MkSlice(MkC(3, MkSlice(MkC(1, MkSlice(MkC(4, MkSlice(MkC(1, MkSlice(MkC(2, MkSlice(End))))))))))), refl) ∧ PartPivot(4, MkSlice(MkC(3, MkSlice(MkC(1, MkSlice(MkC(4, MkSlice(MkC(1, MkSlice(MkC(2, MkSlice(End))))))))))), refl) ∧ PartRight(4, MkSlice(MkC(3, MkSlice(MkC(1, MkSlice(MkC(4, MkSlice(MkC(1, MkSlice(MkC(2, MkSlice(End))))))))))), refl) := refl
  def ContractRun2 : PartLe(5, MkSlice(MkC(2, MkSlice(MkC(5, MkSlice(MkC(1, MkSlice(MkC(5, MkSlice(MkC(0, MkSlice(MkC(2, MkSlice(End)))))))))))))) ∧ PartLeft(5, MkSlice(MkC(2, MkSlice(MkC(5, MkSlice(MkC(1, MkSlice(MkC(5, MkSlice(MkC(0, MkSlice(MkC(2, MkSlice(End))))))))))))), refl) ∧ PartPivot(5, MkSlice(MkC(2, MkSlice(MkC(5, MkSlice(MkC(1, MkSlice(MkC(5, MkSlice(MkC(0, MkSlice(MkC(2, MkSlice(End))))))))))))), refl) ∧ PartRight(5, MkSlice(MkC(2, MkSlice(MkC(5, MkSlice(MkC(1, MkSlice(MkC(5, MkSlice(MkC(0, MkSlice(MkC(2, MkSlice(End))))))))))))), refl) := refl
  -- A wrong pivot position is not.
  reject def ContractWrong : PartPivot(4, MkSlice(MkC(3, MkSlice(MkC(1, MkSlice(MkC(4, MkSlice(MkC(1, MkSlice(MkC(2, MkSlice(End))))))))))), refl) ∧ Eq Nat (PartK(4, MkSlice(MkC(3, MkSlice(MkC(1, MkSlice(MkC(4, MkSlice(MkC(1, MkSlice(MkC(2, MkSlice(End))))))))))))) 2 := refl
}

#eval IO.println (run "Quicksort" Quicksort).show

-- every verdict as expected, and the exact number of declarations (a truncated file changes it)
#guard (run "Quicksort" Quicksort).allAsExpected
#guard (run "Quicksort" Quicksort).count == 49
