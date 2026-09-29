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
  def SetS (E : Type) (n : Nat) (s : Slice(E, n)) (i : Nat) (x : E) (h : Lt(i, n)) : Slice(E, n) by i := (
    match n {
      Z => match h {},
      S m => match s {
        MkSlice(c) => match c {
          MkC(y, t) => match i {
            Z => MkSlice(MkC(x, t)),
            S i' => MkSlice(MkC(y, SetS(E, m, t, i', x, h))),
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

  def DropS (E : Type) (n : Nat) (k : Nat) (s : Slice(E, n)) (h : Le(k, n)) : Slice(E, Sub(n, k)) by k := (
    match k {
      Z => s,
      S k' => match n {
        Z => match h {},
        S m => match s {
          MkSlice(c) => match c {
            MkC(x, t) => DropS(E, m, k', t, h),
          },
        },
      },
    }
  )

  def JoinS (E : Type) (n : Nat) (k : Nat) (l : Slice(E, k)) (r : Slice(E, Sub(n, k))) (h : Le(k, n)) :
      Slice(E, n) by k := (
    match k {
      Z => r,
      S k' => match n {
        Z => match h {},
        S m => match l {
          MkSlice(c) => match c {
            MkC(x, t) => MkSlice(MkC(x, JoinS(E, m, k', t, r, h))),
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
    *s := SetS(E, n, *s, i, x, h)
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
    let r = DropS(E, n, k, v, h);
    let res = f(&l, &r);
    *s := JoinS(E, n, k, l, r, h);
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
      Eq E (Nth(E, n, SetS(E, n, s, i, x, h), i, h)) x by i := (
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
      Eq E (Nth(E, n, SetS(E, n, s, i, x, hi), j, hj)) (Nth(E, n, s, j, hj)) by i := (
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
      Eq (Slice(E, n)) (JoinS(E, n, k, TakeS(E, n, k, s, h), DropS(E, n, k, s, h), h)) s by k := (
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
      Eq (Slice(E, k)) (TakeS(E, n, k, JoinS(E, n, k, l, r, h), h)) l by k := (
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
      Eq (Slice(E, Sub(n, k))) (DropS(E, n, k, JoinS(E, n, k, l, r, h), h)) r by k := (
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
      Eq Nat (Count(q, n, JoinS(Nat, n, k, l, r, h))) (Add(Count(q, k, l), Count(q, Sub(n, k), r))) by k := (
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
      Eq Nat (Add(Count(q, n, SetS(Nat, n, s, i, x, h)), Ind(q, Nth(Nat, n, s, i, h))))
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
      Slice(E, n) := SetS(E, n, SetS(E, n, s, i, Nth(E, n, s, j, hj), hi), j, Nth(E, n, s, i, hi), hj)

  def SwapIsSwapS (E : Type) (n : Nat) (s : &Slice(E, n)) (i : Nat) (j : Nat) (hi : Lt(i, n)) (hj : Lt(j, n)) :
      Id Unit (Swap(E, n, s, i, j, hi, hj)) (*s := SwapS(E, n, *s, i, j, hi, hj)) := refl

  -- A swap with the head: the head moves to position `i + 1` of the rest, whose old element
  -- becomes the head. Counts are unchanged, by `CountSet` on the rest.
  def CountSwapHead (q : Nat) (m : Nat) (y : Nat) (t : Slice(Nat, m)) (i : Nat) (h : Lt(i, m)) :
      Eq Nat (Count(q, S m, MkSlice(MkC(Nth(Nat, m, t, i, h), SetS(Nat, m, t, i, y, h)))))
        (Count(q, S m, MkSlice(MkC(y, t)))) := (
    let a = Count(q, m, SetS(Nat, m, t, i, y, h));
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
        (*s := JoinS(E, n, k, (let c = TakeS(E, n, k, *s, h); g(&c); c), DropS(E, n, k, *s, h), h)) := refl

  -- Stated about the rest alone, it takes one lemma, for any `g`: `g`'s result has length `k`
  -- by its type, so the rest starts where it did.
  def B1 (E : Type) (n : Nat) (k : Nat) (g : Π(x : &Slice(E, k)). Unit) (s : &Slice(E, n)) (h : Le(k, n)) :
      Eq (Slice(E, Sub(n, k)))
        (let c = *s; WithSplit(E, Unit, n, k, &c, h, λ(l : &Slice(E, k)) (r : &Slice(E, Sub(n, k))) : Unit => g(l)); DropS(E, n, k, c, h))
        (DropS(E, n, k, *s, h)) := (
    DropJoin(E, n, k, (let c = TakeS(E, n, k, *s, h); g(&c); c), DropS(E, n, k, *s, h), h)
  )

  -- A primitive array would give that by definition; here it is not.
  reject def B1Refl (E : Type) (n : Nat) (k : Nat) (g : Π(x : &Slice(E, k)). Unit) (s : &Slice(E, n)) (h : Le(k, n)) :
      Eq (Slice(E, Sub(n, k)))
        (let c = *s; WithSplit(E, Unit, n, k, &c, h, λ(l : &Slice(E, k)) (r : &Slice(E, Sub(n, k))) : Unit => g(l)); DropS(E, n, k, c, h))
        (DropS(E, n, k, *s, h)) := refl

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
