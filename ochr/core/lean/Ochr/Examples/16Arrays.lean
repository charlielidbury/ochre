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
#guard (run "Index" Index).count == 17

/-! ## The model

A view `Slice(E, n)` wraps the cells; a cell holds an element and the rest of the view, so
the rest is itself a view. An owned array `Array(E, n)` wraps a view. None of them stores a
length. The functions on the model take their arguments by value and recurse over an index;
proofs use them, and they are the models of the native functions below. -/

ochr Arrays uses Index {
  -- [K2] [K3] A view: unsized and abstract in phase B.
  inductive SliceOf (R : Type) := MkSlice(c : R)
  -- [K1] [K3] A cell: an element and the rest, which is a view so that it can be borrowed.
  inductive Cell (E : Type) (R : Type) := MkC(h : E, t : SliceOf(R))

  def Cells (E : Type) (n : Nat) : Type by n := (
    match n {
      Z => Unit,
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
      Z => MkSlice(()),
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
      Z => MkSlice(MkC(x, MkSlice(()))),
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
          Z => (MkSlice(()), y),
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
  def ArrEmpty (E : Type) : Array(E, 0) := MkArray(MkSlice(()))

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
#guard (run "Arrays" Arrays).count == 25
