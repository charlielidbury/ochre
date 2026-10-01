import Ochr.Examples.«00Std»

/-! # 16. Arrays: a library over a type-level model

Arrays are not built into Ochr (D57). An array of `n` elements is modelled by `Cells(E, n)`,
a type computed by recursion on `n`: `CellsEnd` at zero, and a cell holding an element and
the rest at `Succ(m)`. So the length lives only in the type, and a value of `Cells(E, n)` has exactly
`n` elements. Proofs reason about this model directly; compiled code will use a flat buffer
instead, through a small set of native functions (marked `[native]` below) whose models are
the Ochr bodies given here.

The rules (D57): nothing recurses over an array, only over an index; runtime code never owns
part of an array; a borrow of part of an array is scoped by a continuation (`WithSplit`).

Proofs rewrite with `rewrite h in t` and take conjunctions apart with a destructuring `let`
(D60); no proof here writes `J` or a motive.

Reads move (D53). Indices, lengths and quicksort's elements are `Word`s, which are copies, so
only a generic element `x : E`, a whole view or a closure is ever used twice, and that takes a
`clone`. Copying an element is the caller's to write: there is no read native, and an element
is read through its borrow, `*GetMut(Word, …)` for a copy type (the scan's and the partition's
reads) and `clone(*GetMut(E, …))` otherwise (`GetOr`). Six `clone`s are in code: `Replicate`
and `FillFrom` copy the element they repeat, two model bodies copy a view (`WithSplit`'s, and
`SwapS`'s twice; model code never runs at runtime), and quicksort's `Recurse` passes the
recursion `rec` on to a second closure. `Swap` copies nothing: it exchanges through two
element borrows, by moves.

What is done through an element borrow at an unknown index is a sealed program, not the
model's `Nth` or `SetS`, so a proof about code that reads, writes or swaps elements calls
`GetMutRead`, `GetMutSet` or `SwapIsSwapS` (or their forms about a view given by value) where
the program does so (see `ScanPerm`).

The representation is enforced (K2, K3): `SliceOf` is `unsized abstract`, and `Cell`,
`CellsEnd` and `ArrayOf` are `abstract`, so outside model code (the `implemented by` bodies,
and the model functions, which take or return a view by value) runtime code only borrows a
view and never builds or takes apart the representation. The remaining workarounds are marked
where they occur:
* `[K1]` (resolved by D66) `&A` is well formed for every `A : Type₀`, so `GetMut` returns `&E`
  for any element type `E`. Each cell's tail is wrapped in the view type `SliceOf`, which made
  the tail borrowable while `&Cells(E, n)` at an unknown `n` was not well formed (D48). It now
  is, so borrows no longer need the wrapping; it stays because `GetMut` and the model
  functions recurse on the tail as a view (`GetMut(E, m, &t, i', h)`, `DropS(E, m, k', t)`).
* `[K4]` A struct cannot yet have a field of type `Array(E, cap)` (a type function applied to a
  parameter, D36), so the hashmap takes the model type as a parameter.
* `[K6]` Quicksort recurses on fuel; with recursion on a measure it recurses on the length.
* `[checker]` The scan's invariant is stated pointwise, one lemma per fact, where one
  proposition with `Π`s inside went stale after a case split (see there).

Defined in D57 and notes/arrays-library.md. -/

open Ochr.Test

/-! ## Indices

Everything recurses over an index, so the order on `Word` and a few facts about it come
first. `Lt(i, n)` is the bounds proof that indexing takes. -/

ochr Index uses Std {
  def Le (a : Word) (b : Word) : Prop by a := (
    match a {
      Zero => ⊤,
      Succ(a') => match b {
        Zero => False,
        Succ(b') => Le(a', b'),
      },
    }
  )

  def Lt (a : Word) (b : Word) : Prop := Le(Succ(a), b)

  -- Addition, by recursion on the first number.
  def WAdd (a : Word) (b : Word) : Word by a := (
    match a {
      Zero => b,
      Succ(a') => Succ(WAdd(a', b)),
    }
  )

  -- `W(n)`, the `Word` for the numeral `n` (for the runs).
  def W (n : Nat) : Word by n := (
    match n {
      Z => Zero,
      S m => Succ(W(m)),
    }
  )

  def Sub (a : Word) (b : Word) : Word by b := (
    match b {
      Zero => a,
      Succ(b') => match a {
        Zero => Zero,
        Succ(a') => Sub(a', b'),
      },
    }
  )

  def Leb (a : Word) (b : Word) : Bool by a := (
    match a {
      Zero => true,
      Succ(a') => match b {
        Zero => false,
        Succ(b') => Leb(a', b'),
      },
    }
  )

  def Eqb (a : Word) (b : Word) : Bool by a := (
    match a {
      Zero => match b {
        Zero => true,
        Succ(_) => false,
      },
      Succ(a') => match b {
        Zero => false,
        Succ(b') => Eqb(a', b'),
      },
    }
  )

  -- A decision that carries its evidence: a comparison at runtime yields the proof an index
  -- needs (B4). At runtime `Dec` is a boolean; its fields are proofs, which are erased.
  inductive Dec (P : Prop) (Q : Prop) := Yes(h : P) | No(k : Q)

  def LeDec (a : Word) (b : Word) : Dec(Le(a, b), Lt(b, a)) by a := (
    match a {
      Zero => Yes(refl),
      Succ(a') => match b {
        Zero => No(refl),
        Succ(b') => LeDec(a', b'),
      },
    }
  )

  def LtDec (i : Word) (n : Word) : Dec(Lt(i, n), Le(n, i)) := LeDec(Succ(i), n)

  -- Facts about the order, each by recursion on a number.
  def LeRefl (a : Word) : Le(a, a) by a := (
    match a {
      Zero => refl,
      Succ(a') => LeRefl(a'),
    }
  )

  def LeStep (a : Word) (b : Word) (h : Le(a, b)) : Le(a, Succ(b)) by a := (
    match a {
      Zero => refl,
      Succ(a') => match b {
        Zero => match h {},
        Succ(b') => LeStep(a', b', h),
      },
    }
  )

  def LeTrans (a : Word) (b : Word) (c : Word) (h1 : Le(a, b)) (h2 : Le(b, c)) : Le(a, c) by a := (
    match a {
      Zero => refl,
      Succ(a') => match b {
        Zero => match h1 {},
        Succ(b') => match c {
          Zero => match h2 {},
          Succ(c') => LeTrans(a', b', c', h1, h2),
        },
      },
    }
  )

  def LeAddL (r : Word) (j : Word) : Le(j, WAdd(r, j)) by r := (
    match r {
      Zero => LeRefl(j),
      Succ(r') => LeStep(j, WAdd(r', j), LeAddL(r', j)),
    }
  )

  def AddRS (r : Word) (j : Word) : Eq Word (Succ(WAdd(r, j))) (WAdd(r, Succ(j))) by r := (
    match r {
      Zero => refl,
      Succ(r') => AddRS(r', j),
    }
  )

  def AddZeroR (m : Word) : Eq Word (WAdd(m, Zero)) m by m := (
    match m {
      Zero => refl,
      Succ(m') => AddZeroR(m'),
    }
  )

  def AddOneR (m : Word) : Eq Word (WAdd(m, Succ(Zero))) (Succ(m)) by m := (
    match m {
      Zero => refl,
      Succ(m') => AddOneR(m'),
    }
  )

  def SubPos (m : Word) (k : Word) (h : Le(k, m)) : Le(Succ(Zero), Sub(Succ(m), k)) by k := (
    match k {
      Zero => refl,
      Succ(k') => match m {
        Zero => match h {},
        Succ(m') => SubPos(m', k', h),
      },
    }
  )

  -- What is left after a pivot at `k` is at most `m` long.
  def SubOneLe (m : Word) (k : Word) : Le(Sub(Sub(Succ(m), k), Succ(Zero)), m) by k := (
    match k {
      Zero => LeRefl(m),
      Succ(k') => match m {
        Zero => match k' {
          Zero => refl,
          Succ(_) => refl,
        },
        Succ(m') => LeStep(Sub(Sub(Succ(m'), k'), Succ(Zero)), m', SubOneLe(m', k')),
      },
    }
  )

  -- a < b gives a ≠ b
  def LtNe (a : Word) (b : Word) (h : Lt(a, b)) (e : Eq(Word, a, b)) : False by a := (
    match a {
      Zero => match b {
        Zero => match h {},
        Succ(_) => match e {},
      },
      Succ(a') => match b {
        Zero => match e {},
        Succ(b') => LtNe(a', b', h, e),
      },
    }
  )

  def LeAntisym (a : Word) (b : Word) (h1 : Le(a, b)) (h2 : Le(b, a)) : Eq(Word, a, b) by a := (
    match a {
      Zero => match b {
        Zero => refl,
        Succ(_) => match h2 {},
      },
      Succ(a') => match b {
        Zero => match h1 {},
        Succ(b') => LeAntisym(a', b', h1, h2),
      },
    }
  )

  -- What is left after `k < n` is not empty.
  def SubPosLt (n : Word) (k : Word) (h : Lt(k, n)) : Le(Succ(Zero), Sub(n, k)) by k := (
    match k {
      Zero => match n {
        Zero => match h {},
        Succ(_) => refl,
      },
      Succ(k') => match n {
        Zero => match h {},
        Succ(m) => SubPosLt(m, k', h),
      },
    }
  )
}

-- the exact number of declarations (a truncated file changes it)
#guard Index.decls.length == 22

/-! ## The model

`Cells(E, n)` is `CellsEnd` at zero and a `Cell` at `Succ(m)`. A view `Slice(E, n)` wraps the
cells; a cell holds an element and the rest of the view, so the rest is itself a view. An owned array `Array(E, n)` wraps a view. None of them stores a
length. The functions on the model take their arguments by value and recurse over an index;
proofs use them, and they are the models of the native functions below. -/

ochr Arrays uses Index {
  -- [K2] [K3] A view: unsized and abstract (runtime code only borrows it).
  unsized abstract inductive SliceOf (R : Type) := MkSlice(c : R)
  -- [K1] [K3] A cell: an element and the rest, which is a view, so that what recurses on the
  -- rest recurses on a view.
  abstract inductive Cell (E : Type) (R : Type) := MkC(h : E, t : SliceOf(R))
  -- [K3] The end of the cells. (Not `Unit`: an unknown `Unit` cannot be taken apart, so a
  -- proof about an empty view could not see that it is the empty view.)
  abstract inductive CellsEnd := End

  def Cells (E : Type) (n : Word) : Type by n := (
    match n {
      Zero => CellsEnd,
      Succ(m) => Cell(E, Cells(E, m)),
    }
  )

  def Slice (E : Type) (n : Word) : Type := SliceOf(Cells(E, n))

  -- [K3] An owned array: at runtime, a pointer to a block of `n` elements.
  abstract inductive ArrayOf (R : Type) := MkArray(s : SliceOf(R))
  def Array (E : Type) (n : Word) : Type := ArrayOf(Cells(E, n))

  -- Element `i`.
  def Nth (E : Type) (n : Word) (s : Slice(E, n)) (i : Word) (h : Lt(i, n)) : E by i := (
    match n {
      Zero => match h {},
      Succ(m) => match s {
        MkSlice(c) => match c {
          MkC(x, t) => match i {
            Zero => x,
            Succ(i') => Nth(E, m, t, i', h),
          },
        },
      },
    }
  )

  -- The view with element `i` replaced by `x`.
  def SetS (E : Type) (n : Word) (s : Slice(E, n)) (i : Word) (x : E) : Slice(E, n) by i := (
    match n {
      Zero => s,
      Succ(m) => match s {
        MkSlice(c) => match c {
          MkC(y, t) => match i {
            Zero => MkSlice(MkC(x, t)),
            Succ(i') => MkSlice(MkC(y, SetS(E, m, t, i', x))),
          },
        },
      },
    }
  )

  -- The first `k` elements, the rest, and the two put back together.
  def TakeS (E : Type) (n : Word) (k : Word) (s : Slice(E, n)) (h : Le(k, n)) : Slice(E, k) by k := (
    match k {
      Zero => MkSlice(End),
      Succ(k') => match n {
        Zero => match h {},
        Succ(m) => match s {
          MkSlice(c) => match c {
            MkC(x, t) => MkSlice(MkC(x, TakeS(E, m, k', t, h))),
          },
        },
      },
    }
  )

  def DropS (E : Type) (n : Word) (k : Word) (s : Slice(E, n)) : Slice(E, Sub(n, k)) by k := (
    match k {
      Zero => s,
      Succ(k') => match n {
        Zero => MkSlice(End),
        Succ(m) => match s {
          MkSlice(c) => match c {
            MkC(x, t) => DropS(E, m, k', t),
          },
        },
      },
    }
  )

  def JoinS (E : Type) (n : Word) (k : Word) (l : Slice(E, k)) (r : Slice(E, Sub(n, k))) : Slice(E, n) by k := (
    match k {
      Zero => r,
      Succ(k') => match n {
        Zero => MkSlice(End),
        Succ(m) => match l {
          MkSlice(c) => match c {
            MkC(x, t) => MkSlice(MkC(x, JoinS(E, m, k', t, r))),
          },
        },
      },
    }
  )

  -- The view `f(k), f(k + 1), …` of `n` elements, the model of `ArrFromFn`.
  def FromFnS (E : Type) (n : Word) (f : Π(i : Word). E) (k : Word) : Slice(E, n) by n := (
    match n {
      Zero => MkSlice(End),
      Succ(m) => MkSlice(MkC(f(k), FromFnS(E, m, f, Succ(k)))),
    }
  )

  -- The length of a list, and the view of a list of `n` elements, the model of `ArrOfList`.
  def LenL (E : Type) (l : List(E)) : Word by l := (
    match l {
      Nil => Zero,
      Cons(x, t) => Succ(LenL(E, t)),
    }
  )

  def OfListS (E : Type) (n : Word) (l : List(E)) (h : Eq(Word, LenL(E, l), n)) : Slice(E, n) by n := (
    match n {
      Zero => MkSlice(End),
      Succ(m) => match l {
        Nil => match h {},
        Cons(x, t) => MkSlice(MkC(x, OfListS(E, m, t, h))),
      },
    }
  )

  -- ## The native functions
  -- Each `[native]` body is the model the checker runs; compiled code calls the native
  -- function it is `implemented by` instead (K3). Runtime code reaches arrays only through these.

  -- [native] The view of an owned array: at runtime, the same pointer.
  def AsSlice (E : Type) (n : Word) (a : &Array(E, n)) : &Slice(E, n) := (
    match *a {
      MkArray(s) => &s,
    }
  ) implemented by "ochr_arr_as_slice"

  -- [native] A borrow of element `i`. Reading an element is reading through it, which moves
  -- unless the element is a copy: `*GetMut(Word, n, s, i, h)` copies a `Word`, and
  -- `clone(*GetMut(E, n, s, i, h))` copies any element, so a copy is always written by the caller.
  def GetMut (E : Type) (n : Word) (s : &Slice(E, n)) (i : Word) (h : Lt(i, n)) : &E by i := (
    match n {
      Zero => match h {},
      Succ(m) => match *s {
        MkSlice(c) => match c {
          MkC(x, t) => match i {
            Zero => &x,
            Succ(i') => GetMut(E, m, &t, i', h),
          },
        },
      },
    }
  ) implemented by "ochr_arr_get_mut"

  -- [native] Borrow the first `k` elements and the rest while `f` runs. The model takes the
  -- two pieces out as values and joins them again after `f` returns; at runtime `f` gets two
  -- pointers into the same block, and nothing is moved.
  def WithSplit (E : Type) (R : Type) (n : Word) (k : Word) (s : &Slice(E, n)) (h : Le(k, n))
      (f : Π(l : &Slice(E, k)) (r : &Slice(E, Sub(n, k))). R) : R := (
    let v = *s;
    let l = TakeS(E, n, k, clone(v), h);
    let r = DropS(E, n, k, v);
    let res = f(&l, &r);
    *s := JoinS(E, n, k, l, r);
    res
  ) implemented by "ochr_arr_with_split"

  -- [native] A new array of `n` elements, element `i` being `f(i)` (Rust's `array::from_fn`):
  -- the one allocation. An array never changes its length.
  def ArrFromFn (E : Type) (n : Word) (f : Π(i : Word). E) : Array(E, n) := (
    MkArray(FromFnS(E, n, f, Zero))
  ) implemented by "ochr_arr_from_fn"

  -- [native] A new array holding the elements of a list of `n` elements, moved in. An array
  -- literal `[x, y, z]`, written at its type `Array(E, n)`, is `ArrOfList(E, n, [x, y, z] as a
  -- list, refl)` (a surface form), so a literal computes to its cells.
  def ArrOfList (E : Type) (n : Word) (l : List(E)) (h : Eq(Word, LenL(E, l), n)) : Array(E, n) := (
    MkArray(OfListS(E, n, l, h))
  ) implemented by "ochr_arr_of_list"

  -- ## Built from those, in Ochr
  -- An element is written through its borrow, `*GetMut(E, n, s, i, h) := x`; that is `SetS`'s
  -- write by `GetMutSet`.

  -- Exchange what two borrows point to, by moves: nothing is copied.
  def SwapRefs (E : Type) (a : &E) (b : &E) : Unit := (
    let t = *a;
    *a := *b;
    *b := t
  )

  -- Exchange elements `i < j`: split at `j`, so that `i` is in the first part and `j` is the
  -- first of the rest, and exchange through the two element borrows.
  def SwapLt (E : Type) (n : Word) (s : &Slice(E, n)) (i : Word) (j : Word) (hij : Lt(i, j)) (hj : Lt(j, n)) : Unit := (
    WithSplit(E, Unit, n, j, s, LeTrans(j, Succ(j), n, LeStep(j, j, LeRefl(j)), hj),
      λ(l : &Slice(E, j)) (r : &Slice(E, Sub(n, j))) : Unit =>
        SwapRefs(E, GetMut(E, j, l, i, hij), GetMut(E, Sub(n, j), r, Zero, SubPosLt(n, j, hj))))
  )

  -- Exchange elements `i` and `j` in place (Rust's `slice::swap`), copying nothing. It is the
  -- write of the model `SwapS` (below) by the lemma `SwapIsSwapS`.
  def Swap (E : Type) (n : Word) (s : &Slice(E, n)) (i : Word) (j : Word) (hi : Lt(i, n)) (hj : Lt(j, n)) : Unit := (
    let d = LtDec(i, j);
    match d {
      Yes(hij) => SwapLt(E, n, s, i, j, hij, hj),
      No(nij) => (
        let d2 = LtDec(j, i);
        match d2 {
          Yes(hji) => SwapLt(E, n, s, j, i, hji, hi),
          No(nji) => (),
        }
      ),
    }
  )

  -- The view with elements `i` and `j` exchanged, the model of `Swap`. (A model function takes
  -- the view by value and never runs at runtime, so its `clone`s copy nothing at runtime.)
  def SwapS (E : Type) (n : Word) (s : Slice(E, n)) (i : Word) (j : Word) (hi : Lt(i, n)) (hj : Lt(j, n)) :
      Slice(E, n) := SetS(E, n, SetS(E, n, clone(s), i, Nth(E, n, clone(s), j, hj)), j, Nth(E, n, s, i, hi))

  -- `n` copies of `x`.
  def Replicate (E : Type) (n : Word) (x : E) : Array(E, n) := ArrFromFn(E, n, λ(i : Word) : E => clone(x))

  -- Write `x` at `i, …, n - 1`, by recursion on the count `rem` still to go (`rem + i = n`).
  def FillFrom (E : Type) (n : Word) (s : &Slice(E, n)) (x : E) (i : Word) (rem : Word)
      (hr : Eq Word (WAdd(rem, i)) n) : Unit by rem := (
    match rem {
      Zero => (),
      Succ(r) => (
        let hi : Lt(i, n) = (rewrite hr in LeAddL(r, i));
        let hr2 : Eq Word (WAdd(r, Succ(i))) n = (rewrite AddRS(r, i) in hr);
        *GetMut(E, n, &*s, i, hi) := clone(x);
        FillFrom(E, n, s, x, Succ(i), r, hr2)
      ),
    }
  )

  def Fill (E : Type) (n : Word) (s : &Slice(E, n)) (x : E) : Unit := FillFrom(E, n, s, x, Zero, n, AddZeroR(n))
}

-- the exact number of declarations (a truncated file changes it)
#guard Arrays.decls.length == 27

/-! ## The lemma library

The facts a user of the library relies on, each by recursion on an index. Three of them are
what a primitive array would give by definition (D57): putting the two halves of a split back
together gives the original view (`JoinTakeDrop`), the halves of a join are what was joined
(`TakeJoin`, `DropJoin`), and reading after a write (`NthSetSame`, `NthSetOther`). Counting
(`Count`) is how permutations are stated. -/

ochr ArrayLemmas uses Arrays {
  def NthSetSame (E : Type) (n : Word) (s : Slice(E, n)) (i : Word) (x : E) (h : Lt(i, n)) :
      Eq E (Nth(E, n, SetS(E, n, s, i, x), i, h)) x by i := (
    match n {
      Zero => match h {},
      Succ(m) => match s {
        MkSlice(c) => match c {
          MkC(y, t) => match i {
            Zero => refl,
            Succ(i') => NthSetSame(E, m, t, i', x, h),
          },
        },
      },
    }
  )

  def NthSetOther (E : Type) (n : Word) (s : Slice(E, n)) (i : Word) (j : Word) (x : E) (hi : Lt(i, n))
      (hj : Lt(j, n)) (ne : Π(e : Eq Word i j). False) :
      Eq E (Nth(E, n, SetS(E, n, s, i, x), j, hj)) (Nth(E, n, s, j, hj)) by i := (
    match n {
      Zero => match hi {},
      Succ(m) => match s {
        MkSlice(c) => match c {
          MkC(y, t) => match i {
            Zero => match j {
              Zero => (
                let no = ne(refl);
                match no {}
              ),
              Succ(j') => refl,
            },
            Succ(i') => match j {
              Zero => refl,
              Succ(j') => NthSetOther(E, m, t, i', j', x, hi, hj, ne),
            },
          },
        },
      },
    }
  )

  def JoinTakeDrop (E : Type) (n : Word) (k : Word) (s : Slice(E, n)) (h : Le(k, n)) :
      Eq (Slice(E, n)) (JoinS(E, n, k, TakeS(E, n, k, clone(s), h), DropS(E, n, k, s))) s by k := (
    match k {
      Zero => refl,
      Succ(k') => match n {
        Zero => match h {},
        Succ(m) => match s {
          MkSlice(c) => match c {
            MkC(x, t) => JoinTakeDrop(E, m, k', t, h),
          },
        },
      },
    }
  )

  def TakeJoin (E : Type) (n : Word) (k : Word) (l : Slice(E, k)) (r : Slice(E, Sub(n, k))) (h : Le(k, n)) :
      Eq (Slice(E, k)) (TakeS(E, n, k, JoinS(E, n, k, l, r), h)) l by k := (
    match k {
      Zero => match l {
        MkSlice(c) => match c {
          End => refl,
        },
      },
      Succ(k') => match n {
        Zero => match h {},
        Succ(m) => match l {
          MkSlice(c) => match c {
            MkC(x, t) => TakeJoin(E, m, k', t, r, h),
          },
        },
      },
    }
  )

  def DropJoin (E : Type) (n : Word) (k : Word) (l : Slice(E, k)) (r : Slice(E, Sub(n, k))) (h : Le(k, n)) :
      Eq (Slice(E, Sub(n, k))) (DropS(E, n, k, JoinS(E, n, k, l, r))) r by k := (
    match k {
      Zero => refl,
      Succ(k') => match n {
        Zero => match h {},
        Succ(m) => match l {
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
  def Count (q : Word) (n : Word) (s : Slice(Word, n)) : Word by n := (
    match n {
      Zero => Zero,
      Succ(m) => match s {
        MkSlice(c) => match c {
          MkC(x, t) => (
            let e = Eqb(q, x);
            match e {
              true => Succ(Count(q, m, t)),
              false => Count(q, m, t),
            }
          ),
        },
      },
    }
  )

  -- 1 if `x` is `q`, else 0.
  def Ind (q : Word) (x : Word) : Word := (
    let e = Eqb(q, x);
    match e {
      true => Succ(Zero),
      false => Zero,
    }
  )

  def CountJoin (q : Word) (n : Word) (k : Word) (l : Slice(Word, k)) (r : Slice(Word, Sub(n, k))) (h : Le(k, n)) :
      Eq Word (Count(q, n, JoinS(Word, n, k, l, r))) (WAdd(Count(q, k, l), Count(q, Sub(n, k), r))) by k := (
    match k {
      Zero => refl,
      Succ(k') => match n {
        Zero => match h {},
        Succ(m) => match l {
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
  def CountSet (q : Word) (n : Word) (s : Slice(Word, n)) (i : Word) (x : Word) (h : Lt(i, n)) :
      Eq Word (WAdd(Ind(q, Nth(Word, n, clone(s), i, h)), Count(q, n, SetS(Word, n, s, i, x))))
        (WAdd(Ind(q, x), Count(q, n, s))) by i := (
    match n {
      Zero => match h {},
      Succ(m) => match s {
        MkSlice(c) => match c {
          MkC(y, t) => match i {
            Zero => (
              let ex = Eqb(q, x);
              let ey = Eqb(q, y);
              match ex {
                true => match ey {
                  true => refl,
                  false => refl,
                },
                false => match ey {
                  true => refl,
                  false => refl,
                },
              }
            ),
            Succ(i') => (
              let ih = CountSet(q, m, t, i', x, h);
              let ey = Eqb(q, y);
              match ey {
                true => rewrite AddRS(Ind(q, Nth(Word, m, t, i', h)), Count(q, m, SetS(Word, m, t, i', x))) in
                  rewrite AddRS(Ind(q, x), Count(q, m, t)) in ih,
                false => ih,
              }
            ),
          },
        },
      },
    }
  )

  -- ## Swapping
  -- A swap with the head: the head moves to position `i + 1` of the rest, whose old element
  -- becomes the head. Counts are unchanged, by `CountSet` on the rest.
  def CountSwapHead (q : Word) (m : Word) (y : Word) (t : Slice(Word, m)) (i : Word) (h : Lt(i, m)) :
      Eq Word (Count(q, Succ(m), MkSlice(MkC(Nth(Word, m, clone(t), i, h), SetS(Word, m, t, i, y)))))
        (Count(q, Succ(m), MkSlice(MkC(y, t)))) := (
    let hs = CountSet(q, m, t, i, y, h);
    let eb = Eqb(q, Nth(Word, m, t, i, h));
    let ey = Eqb(q, y);
    match eb {
      true => match ey {
        true => hs,
        false => hs,
      },
      false => match ey {
        true => hs,
        false => hs,
      },
    }
  )

  -- A swap leaves every count unchanged.
  def CountSwap (q : Word) (n : Word) (s : Slice(Word, n)) (i : Word) (j : Word) (hi : Lt(i, n)) (hj : Lt(j, n)) :
      Eq Word (Count(q, n, SwapS(Word, n, s, i, j, hi, hj))) (Count(q, n, s)) by i := (
    match n {
      Zero => match hi {},
      Succ(m) => match s {
        MkSlice(c) => match c {
          MkC(y, t) => match i {
            Zero => match j {
              Zero => refl,
              Succ(j') => CountSwapHead(q, m, y, t, j', hj),
            },
            Succ(i') => match j {
              Zero => CountSwapHead(q, m, y, t, i', hi),
              Succ(j') => (
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
  -- At an unknown index, a borrow of an element is a sealed program, so what is done through it
  -- is known by these two lemmas, by the same bare recursion as `AddMEq`. Writing through it is
  -- the model's write `SetS` (in place is functional).
  def GetMutSet (E : Type) (n : Word) (s : &Slice(E, n)) (i : Word) (w : E) (h : Lt(i, n)) :
      Id(Unit, (*GetMut(E, n, s, i, h) := w), (*s := SetS(E, n, *s, i, w))) by i := (
    match n {
      Zero => match h {},
      Succ(m) => match *s {
        MkSlice(c) => match c {
          MkC(x, t) => match i {
            Zero => refl,
            Succ(i') => GetMutSet(E, m, &t, i', w, h),
          },
        },
      },
    }
  )

  -- Reading through it gives the model's element, and puts the view back as it was. (It
  -- computes to the two facts, `let ⟨hv, hp⟩ = GetMutRead(…)`: the value read is `Nth(…)`, and
  -- the view afterwards, a put-back program, is `*s`.)
  def GetMutRead (E : Type) (n : Word) (s : &Slice(E, n)) (i : Word) (h : Lt(i, n)) :
      Id(E, clone(*GetMut(E, n, s, i, h)), Nth(E, n, clone(*s), i, h)) by i := (
    match n {
      Zero => match h {},
      Succ(m) => match *s {
        MkSlice(c) => match c {
          MkC(x, t) => match i {
            Zero => refl,
            Succ(i') => GetMutRead(E, m, &t, i', h),
          },
        },
      },
    }
  )

  -- The same about a view `v` given by value (a model function's run), as the two facts.
  def GetMutReadV (E : Type) (n : Word) (v : Slice(E, n)) (i : Word) (h : Lt(i, n)) :
      Eq(E, (let c = v; clone(*GetMut(E, n, &c, i, h))), Nth(E, n, v, i, h)) ∧
        Eq(Slice(E, n), (let c = v; let x = clone(*GetMut(E, n, &c, i, h)); c), v) := (
    let c = v;
    GetMutRead(E, n, &c, i, h)
  )

  -- The write, about a view `v` given by value.
  def GetMutSetV (E : Type) (n : Word) (v : Slice(E, n)) (i : Word) (w : E) (h : Lt(i, n)) :
      Eq(Slice(E, n), (let c = v; *GetMut(E, n, &c, i, h) := w; c), SetS(E, n, v, i, w)) by i := (
    match n {
      Zero => match h {},
      Succ(m) => match v {
        MkSlice(c) => match c {
          MkC(x, t) => match i {
            Zero => refl,
            Succ(i') => GetMutSetV(E, m, t, i', w, h),
          },
        },
      },
    }
  )

  -- ## Swap is its model
  -- `Swap` exchanges through two element borrows inside a split, so what it does is known by
  -- `SwapIsSwapS`, from the element-borrow lemmas and these facts about the model.
  -- Element `i < k` of the first `k`, and element 0 of the rest, are elements `i` and `k`.
  def NthTakeS (E : Type) (n : Word) (k : Word) (v : Slice(E, n)) (hk : Le(k, n)) (i : Word) (hik : Lt(i, k)) (hin : Lt(i, n)) :
      Eq(E, Nth(E, k, TakeS(E, n, k, v, hk), i, hik), Nth(E, n, v, i, hin)) by i := (
    match k {
      Zero => match hik {},
      Succ(k') => match n {
        Zero => match hk {},
        Succ(m) => match v {
          MkSlice(c) => match c {
            MkC(z, t) => match i {
              Zero => refl,
              Succ(i') => NthTakeS(E, m, k', t, hk, i', hik, hin),
            },
          },
        },
      },
    }
  )

  def NthDropS (E : Type) (n : Word) (k : Word) (v : Slice(E, n)) (hkn : Lt(k, n)) (h0 : Lt(Zero, Sub(n, k))) :
      Eq(E, Nth(E, Sub(n, k), DropS(E, n, k, v), Zero, h0), Nth(E, n, v, k, hkn)) by k := (
    match k {
      Zero => refl,
      Succ(k') => match n {
        Zero => match hkn {},
        Succ(m) => match v {
          MkSlice(c) => match c {
            MkC(z, t) => NthDropS(E, m, k', t, hkn, h0),
          },
        },
      },
    }
  )

  -- Writing element 0 of the rest after `k`, and joining, is writing element `k` ...
  def JoinSetRight (E : Type) (n : Word) (k : Word) (v : Slice(E, n)) (hk : Le(k, n)) (y : E) :
      Eq(Slice(E, n), JoinS(E, n, k, TakeS(E, n, k, clone(v), hk), SetS(E, Sub(n, k), DropS(E, n, k, v), Zero, y)), SetS(E, n, v, k, y)) by k := (
    match k {
      Zero => refl,
      Succ(k') => match n {
        Zero => match hk {},
        Succ(m) => match v {
          MkSlice(c) => match c {
            MkC(z, t) => JoinSetRight(E, m, k', t, hk, y),
          },
        },
      },
    }
  )

  -- ... and writing element `i < k` of the first `k` as well is writing both.
  def JoinSetS (E : Type) (n : Word) (k : Word) (v : Slice(E, n)) (hk : Le(k, n)) (i : Word) (hik : Lt(i, k)) (x : E) (y : E) :
      Eq(Slice(E, n), JoinS(E, n, k, SetS(E, k, TakeS(E, n, k, clone(v), hk), i, x), SetS(E, Sub(n, k), DropS(E, n, k, v), Zero, y)),
        SetS(E, n, SetS(E, n, v, i, x), k, y)) by i := (
    match k {
      Zero => match hik {},
      Succ(k') => match n {
        Zero => match hk {},
        Succ(m) => match v {
          MkSlice(c) => match c {
            MkC(z, t) => match i {
              Zero => JoinSetRight(E, m, k', t, hk, y),
              Succ(i') => JoinSetS(E, m, k', t, hk, i', hik, x, y),
            },
          },
        },
      },
    }
  )

  -- Writes to different elements commute (so `SwapS(v, j, i)` is `SwapS(v, i, j)`) ...
  def SetSComm (E : Type) (n : Word) (v : Slice(E, n)) (p : Word) (q : Word) (a : E) (b : E) (ne : Π(e : Eq(Word, p, q)). False) :
      Eq(Slice(E, n), SetS(E, n, SetS(E, n, v, p, a), q, b), SetS(E, n, SetS(E, n, v, q, b), p, a)) by p := (
    match n {
      Zero => refl,
      Succ(m) => match v {
        MkSlice(c) => match c {
          MkC(z, t) => match p {
            Zero => match q {
              Zero => (
                let no = ne(refl);
                match no {}
              ),
              Succ(q') => refl,
            },
            Succ(p') => match q {
              Zero => refl,
              Succ(q') => SetSComm(E, m, t, p', q', a, b, ne),
            },
          },
        },
      },
    }
  )

  -- ... and exchanging an element with itself changes nothing.
  def SwapSSame (E : Type) (n : Word) (v : Slice(E, n)) (i : Word) (h : Lt(i, n)) :
      Eq(Slice(E, n), v, SwapS(E, n, v, i, i, h, h)) by i := (
    match n {
      Zero => match h {},
      Succ(m) => match v {
        MkSlice(c) => match c {
          MkC(z, t) => match i {
            Zero => refl,
            Succ(i') => SwapSSame(E, m, t, i', h),
          },
        },
      },
    }
  )

  -- `SwapLt` leaves the split's two pieces written through the element borrows, each with what
  -- was read through the other, and joins them.
  def SwapLtIsSwapS (E : Type) (n : Word) (s : &Slice(E, n)) (i : Word) (j : Word) (hij : Lt(i, j)) (hi : Lt(i, n)) (hj : Lt(j, n)) :
      Id(Unit, SwapLt(E, n, s, i, j, hij, hj), (*s := SwapS(E, n, clone(*s), i, j, hi, hj))) := (
    let hk : Le(j, n) = LeTrans(j, Succ(j), n, LeStep(j, j, LeRefl(j)), hj);
    let h0 : Lt(Zero, Sub(n, j)) = SubPosLt(n, j, hj);
    let tk = TakeS(E, n, j, clone(*s), hk);
    let dr = DropS(E, n, j, clone(*s));
    let ra = (let c = clone(tk); clone(*GetMut(E, j, &c, i, hij)));
    let rb = (let c = clone(dr); clone(*GetMut(E, Sub(n, j), &c, Zero, h0)));
    let ⟨ha, ha2⟩ = GetMutReadV(E, j, tk, i, hij);
    let ⟨hb, hb2⟩ = GetMutReadV(E, Sub(n, j), dr, Zero, h0);
    rewrite ← GetMutSetV(E, j, tk, i, rb, hij) in
    rewrite ← GetMutSetV(E, Sub(n, j), dr, Zero, ra, h0) in
    rewrite ← JoinSetS(E, n, j, clone(*s), hk, i, hij, rb, ra) in
    rewrite ← hb in rewrite ← ha in
    rewrite ← NthDropS(E, n, j, clone(*s), hj, h0) in
    rewrite ← NthTakeS(E, n, j, clone(*s), hk, i, hij, hi) in
    refl
  )

  def SwapIsSwapS (E : Type) (n : Word) (s : &Slice(E, n)) (i : Word) (j : Word) (hi : Lt(i, n)) (hj : Lt(j, n)) :
      Id(Unit, Swap(E, n, s, i, j, hi, hj), (*s := SwapS(E, n, *s, i, j, hi, hj))) := (
    let d = LtDec(i, j);
    match d {
      Yes(hij) => SwapLtIsSwapS(E, n, s, i, j, hij, hi, hj),
      No(nij) => (
        let d2 = LtDec(j, i);
        match d2 {
          Yes(hji) => (
            rewrite SetSComm(E, n, *s, j, i, Nth(E, n, *s, i, hi), Nth(E, n, *s, j, hj), λ(e : Eq(Word, j, i)) : False => LtNe(j, i, hji, e)) in
              SwapLtIsSwapS(E, n, s, j, i, hji, hj, hi)
          ),
          No(nji) => (
            let e : Eq(Word, i, j) = LeAntisym(i, j, nji, nij);
            rewrite e in SwapSSame(E, n, *s, i, hi)
          ),
        }
      ),
    }
  )

  -- The same about a view `v` given by value.
  def SwapIsSwapSV (E : Type) (n : Word) (v : Slice(E, n)) (i : Word) (j : Word) (hi : Lt(i, n)) (hj : Lt(j, n)) :
      Eq(Slice(E, n), (let c = v; Swap(E, n, &c, i, j, hi, hj); c), SwapS(E, n, v, i, j, hi, hj)) := (
    let c = v;
    SwapIsSwapS(E, n, &c, i, j, hi, hj)
  )
}

-- the exact number of declarations (a truncated file changes it)
#guard ArrayLemmas.decls.length == 24

/-! ## The benchmarks (D57)

B1: borrow the first `k` elements, run anything on them, and the rest is unchanged.
B2: quicksort (the next section). B3: insert into a hashmap's bucket in place. B4: a bounds
proof from a runtime comparison. Each is stated about the program itself. -/

ochr ArrayBench uses ArrayLemmas {
  -- ## B1
  -- By definition, for any `g`: after the split, the view is `g`'s result on the old first
  -- `k` elements, joined to the old rest.
  def B1Join (E : Type) (n : Word) (k : Word) (g : Π(x : &Slice(E, k)). Unit) (s : &Slice(E, n)) (h : Le(k, n)) :
      Id Unit (WithSplit(E, Unit, n, k, s, h, λ(l : &Slice(E, k)) (r : &Slice(E, Sub(n, k))) : Unit => g(l)))
        (*s := JoinS(E, n, k, (let c = TakeS(E, n, k, clone(*s), h); g(&c); c), DropS(E, n, k, clone(*s)))) := refl

  -- Stated about the rest alone, it takes one lemma, for any `g`: `g`'s result has length `k`
  -- by its type, so the rest starts where it did.
  def B1 (E : Type) (n : Word) (k : Word) (g : Π(x : &Slice(E, k)). Unit) (s : &Slice(E, n)) (h : Le(k, n)) :
      Eq (Slice(E, Sub(n, k)))
        (let c = *s; WithSplit(E, Unit, n, k, &c, h, λ(l : &Slice(E, k)) (r : &Slice(E, Sub(n, k))) : Unit => g(l)); DropS(E, n, k, c))
        (DropS(E, n, k, *s)) := (
    DropJoin(E, n, k, (let c = TakeS(E, n, k, *s, h); g(&c); c), DropS(E, n, k, *s), h)
  )

  -- A primitive array would give that by definition; here it is not.
  reject def B1Refl (E : Type) (n : Word) (k : Word) (g : Π(x : &Slice(E, k)). Unit) (s : &Slice(E, n)) (h : Le(k, n)) :
      Eq (Slice(E, Sub(n, k)))
        (let c = *s; WithSplit(E, Unit, n, k, &c, h, λ(l : &Slice(E, k)) (r : &Slice(E, Sub(n, k))) : Unit => g(l)); DropS(E, n, k, c))
        (DropS(E, n, k, *s)) := refl

  -- Nor is splitting and doing nothing the identity by definition; it is `JoinTakeDrop`.
  reject def SplitNoopRefl (E : Type) (n : Word) (k : Word) (s : &Slice(E, n)) (h : Le(k, n)) :
      Id Unit (WithSplit(E, Unit, n, k, s, h, λ(l : &Slice(E, k)) (r : &Slice(E, Sub(n, k))) : Unit => ())) () := refl

  def SplitNoop (E : Type) (n : Word) (k : Word) (s : &Slice(E, n)) (h : Le(k, n)) :
      Eq (Slice(E, n)) (let c = *s; WithSplit(E, Unit, n, k, &c, h, λ(l : &Slice(E, k)) (r : &Slice(E, Sub(n, k))) : Unit => ()); c) (*s) := (
    JoinTakeDrop(E, n, k, *s, h)
  )

  -- The motivating use, on a concrete array: zero the first two of five.
  def ZeroFirst2 (s : &Slice(Word, W(5))) : Unit := (
    WithSplit(Word, Unit, W(5), W(2), s, refl, λ(l : &Slice(Word, W(2))) (r : &Slice(Word, W(3))) : Unit => Fill(Word, W(2), l, Zero))
  )

  def ZeroFirst2Run : Id(Word,
      (let a = Replicate(Word, W(5), W(7)); ZeroFirst2(AsSlice(Word, W(5), &a)); *GetMut(Word, W(5), AsSlice(Word, W(5), &a), Succ(Zero), refl)),
      Zero) := refl

  def ZeroFirst2Rest : Id(Word,
      (let a = Replicate(Word, W(5), W(7)); ZeroFirst2(AsSlice(Word, W(5), &a)); *GetMut(Word, W(5), AsSlice(Word, W(5), &a), W(2), refl)),
      W(7)) := refl

  -- ## Reading and writing
  -- An element is read and written through its borrow. `*GetMut(…)` is a place (a surface
  -- desugaring of `let r = GetMut(…); … *r …`, Rust's `*v.get_mut(i)`): reading it copies a
  -- `Word`, `clone` copies any element, and a write is one line.
  def ReadE (E : Type) (n : Word) (s : &Slice(E, n)) (i : Word) (h : Lt(i, n)) : E := clone(*GetMut(E, n, s, i, h))
  def WriteE (E : Type) (n : Word) (s : &Slice(E, n)) (i : Word) (x : E) (h : Lt(i, n)) : Unit := *GetMut(E, n, s, i, h) := x
  def Bump (n : Word) (s : &Slice(Word, n)) (i : Word) (h : Lt(i, n)) : Unit := (
    *GetMut(Word, n, &*s, i, h) := Succ(*GetMut(Word, n, &*s, i, h))
  )
  def BumpRun : Id(Word,
      (let a = Replicate(Word, W(3), W(7)); Bump(W(3), AsSlice(Word, W(3), &a), Succ(Zero), refl); *GetMut(Word, W(3), AsSlice(Word, W(3), &a), Succ(Zero), refl)),
      W(8)) := refl
  -- Reading a generic element without `clone` would move it out through the borrow, which then
  -- ends with the element moved out (D53): the copy is the caller's to write.
  reject def ReadMove (E : Type) (n : Word) (s : &Slice(E, n)) (i : Word) (h : Lt(i, n)) : E := *GetMut(E, n, s, i, h)
  -- `*f(…)` is a place only for a call that returns a borrow.
  reject def NotAPlace (a : Word) (b : Word) : Unit := *Leb(a, b) := true

  -- A read leaves the view as it was, but not by definition: at an unknown index the view
  -- afterwards is a put-back program ...
  reject def ReadNoopRefl (E : Type) (n : Word) (s : &Slice(E, n)) (i : Word) (h : Lt(i, n)) :
      Id(Unit, (let x = clone(*GetMut(E, n, s, i, h)); ()), ()) := refl

  -- ... which is the view by `GetMutRead`.
  def ReadNoop (E : Type) (n : Word) (s : &Slice(E, n)) (i : Word) (h : Lt(i, n)) :
      Eq(Slice(E, n), (let c = *s; let x = clone(*GetMut(E, n, &c, i, h)); c), *s) := (
    let ⟨hv, hp⟩ = GetMutRead(E, n, s, i, h);
    hp
  )

  -- Reading after a write, at the same index and at another: the model's lemmas, once
  -- `GetMutSetV` has made the write `SetS`'s and `GetMutRead` each read the model's element.
  def ReadAfterSet (E : Type) (n : Word) (s : &Slice(E, n)) (i : Word) (x : E) (h : Lt(i, n)) :
      Eq(E, (let c = clone(*s); *GetMut(E, n, &c, i, h) := x; clone(*GetMut(E, n, &c, i, h))), x) := (
    let c = SetS(E, n, clone(*s), i, clone(x));
    let ⟨hv, hp⟩ = GetMutRead(E, n, &c, i, h);
    rewrite ← GetMutSetV(E, n, clone(*s), i, x, h) in rewrite ← hv in NthSetSame(E, n, clone(*s), i, x, h)
  )

  def ReadAfterSetOther (E : Type) (n : Word) (s : &Slice(E, n)) (i : Word) (j : Word) (x : E) (hi : Lt(i, n))
      (hj : Lt(j, n)) (ne : Π(e : Eq(Word, i, j)). False) :
      Eq(E, (let c = clone(*s); *GetMut(E, n, &c, i, hi) := x; clone(*GetMut(E, n, &c, j, hj))), clone(*GetMut(E, n, s, j, hj))) := (
    let c = SetS(E, n, clone(*s), i, clone(x));
    let ⟨hv, hp⟩ = GetMutRead(E, n, &c, j, hj);
    let ⟨hv2, hp2⟩ = GetMutRead(E, n, s, j, hj);
    rewrite ← GetMutSetV(E, n, clone(*s), i, x, hi) in rewrite ← hv in rewrite ← hv2 in NthSetOther(E, n, clone(*s), i, j, x, hi, hj, ne)
  )

  reject def ReadAfterSetRefl (E : Type) (n : Word) (s : &Slice(E, n)) (i : Word) (x : E) (h : Lt(i, n)) :
      Eq(E, (let c = *s; *GetMut(E, n, &c, i, h) := x; clone(*GetMut(E, n, &c, i, h))), x) := refl

  -- A bounds proof mentions only the index and the length in the type, so no write makes it
  -- stale ...
  def SetTwice (n : Word) (s : &Slice(Word, n)) (i : Word) (h : Lt(i, n)) : Unit := (
    *GetMut(Word, n, &*s, i, h) := Succ(Zero);
    *GetMut(Word, n, s, i, h) := W(2)
  )

  -- ... and without one there is no read.
  reject def ReadPastEnd (s : &Slice(Word, W(2))) : Word := *GetMut(Word, W(2), s, W(2), refl)

  -- ## Swapping, copy-free
  -- Two element borrows of one view at once are refused: taking the second ends the first (the
  -- view is used again). So `Swap` splits the view first (`WithSplit`), and borrows one element
  -- in each piece.
  reject def TwoGetMut (E : Type) (n : Word) (s : &Slice(E, n)) (i : Word) (j : Word) (hi : Lt(i, n)) (hj : Lt(j, n)) : Unit := (
    let a = GetMut(E, n, &*s, i, hi);
    let b = GetMut(E, n, &*s, j, hj);
    SwapRefs(E, a, b)
  )

  -- On `[4, 9]`, in both orders of the indices, and at one index.
  def SwapRun : Id(Word,
      (let a : Array(Word, W(2)) = [W(4), W(9)];
       Swap(Word, W(2), AsSlice(Word, W(2), &a), Succ(Zero), Zero, refl, refl);
       *GetMut(Word, W(2), AsSlice(Word, W(2), &a), Zero, refl)),
      W(9)) := refl
  def SwapRunLt : Id(Word,
      (let a : Array(Word, W(2)) = [W(4), W(9)];
       Swap(Word, W(2), AsSlice(Word, W(2), &a), Zero, Succ(Zero), refl, refl);
       *GetMut(Word, W(2), AsSlice(Word, W(2), &a), Succ(Zero), refl)),
      W(4)) := refl
  def SwapRunSame : Id(Word,
      (let a : Array(Word, W(2)) = [W(4), W(9)];
       Swap(Word, W(2), AsSlice(Word, W(2), &a), Zero, Zero, refl, refl);
       *GetMut(Word, W(2), AsSlice(Word, W(2), &a), Zero, refl)),
      W(4)) := refl
  -- By definition `Swap` is not its model's write: that is the lemma `SwapIsSwapS`.
  reject def SwapIsSwapSRefl (E : Type) (n : Word) (s : &Slice(E, n)) (i : Word) (j : Word) (hi : Lt(i, n)) (hj : Lt(j, n)) :
      Id(Unit, Swap(E, n, s, i, j, hi, hj), (*s := SwapS(E, n, *s, i, j, hi, hj))) := refl

  -- ## B4: a bounds proof from a runtime comparison
  def GetOr (E : Type) (n : Word) (s : &Slice(E, n)) (i : Word) (d : E) : E := (
    let dec = LtDec(i, n);
    match dec {
      Yes(h) => clone(*GetMut(E, n, s, i, h)),
      No(k) => d,
    }
  )

  def GetOrIn : Id Word (let a = Replicate(Word, W(3), W(7)); GetOr(Word, W(3), AsSlice(Word, W(3), &a), Succ(Zero), Zero)) W(7) := refl
  def GetOrOut : Id Word (let a = Replicate(Word, W(3), W(7)); GetOr(Word, W(3), AsSlice(Word, W(3), &a), W(5), Zero)) Zero := refl

  -- ## Making arrays
  -- An array has the length in its type and never changes it. A literal is written at its type;
  -- it computes to its cells, so a statement about one holds by evaluation.
  def Lit : Id(Word, (let a : Array(Word, W(3)) = [W(4), W(9), W(2)]; *GetMut(Word, W(3), AsSlice(Word, W(3), &a), Succ(Zero), refl)), W(9)) := refl
  def LitCells : Eq(Array(Word, W(2)), ([W(4), W(9)] : Array(Word, W(2))), MkArray(MkSlice(MkC(W(4), MkSlice(MkC(W(9), MkSlice(End))))))) := refl
  def LitEmpty : Eq(Array(Word, Zero), ([] : Array(Word, Zero)), MkArray(MkSlice(End))) := refl
  -- A literal moves its elements in: a generic one copies nothing.
  def LitGeneric (E : Type) (x : E) (y : E) : Array(E, W(2)) := [x, y]
  reject def LitWrongLength : Array(Word, W(2)) := [W(4)]
  -- `ArrFromFn(E, n, f)` allocates `n` cells, element `i` being `f(i)`.
  def FromFn : Id(Word, (let a = ArrFromFn(Word, W(4), λ(i : Word) : Word => Succ(i)); *GetMut(Word, W(4), AsSlice(Word, W(4), &a), W(3), refl)), W(4)) := refl
  def ReplicateList : Id(List(Word),
      (let a = Replicate(List(Word), W(2), Cons(W(1), Nil)); clone(*GetMut(List(Word), W(2), AsSlice(List(Word), W(2), &a), Succ(Zero), refl))),
      Cons(W(1), Nil)) := refl

  -- ## B3: insert into a hashmap's bucket, in place
  -- The slot is `k mod cap`, whose bound is a lemma: no runtime check.
  def ModS (k : Word) (c : Word) : Word by k := (
    match k {
      Zero => Zero,
      Succ(k') => (
        let r = Succ(ModS(k', c));
        let e = Eqb(r, c);
        match e {
          true => Zero,
          false => r,
        }
      ),
    }
  )

  def LeNext (a : Word) (c : Word) (h : Le(a, c)) (e : Eq Bool (Eqb(a, c)) false) : Le(Succ(a), c) by a := (
    match a {
      Zero => match c {
        Zero => match e {},
        Succ(_) => refl,
      },
      Succ(a') => match c {
        Zero => match h {},
        Succ(c') => LeNext(a', c', h, e),
      },
    }
  )

  def ModLt (k : Word) (c : Word) (hc : Lt(Zero, c)) : Lt(ModS(k, c), c) by k := (
    match k {
      Zero => hc,
      Succ(k') => (
        let e = Eqb(Succ(ModS(k', c)), c);
        match e {
          true => hc,
          false => LeNext(Succ(ModS(k', c)), c, ModLt(k', c, hc), refl),
        }
      ),
    }
  )

  inductive Entry := MkE(key : Word, val : Word)

  -- [K4] A struct holding an array: the model type is a parameter until a field may be written
  -- `Array(E, cap)`. The capacity is a type parameter, so no dependent field is needed.
  inductive HashMapOf (R : Type) := MkHM(slots : ArrayOf(R), size : Word)
  def HashMap (cap : Word) : Type := HashMapOf(Cells(List(Entry), cap))

  -- Insert into a bucket (a list, which may be recursed over): overwrite, or add at the end.
  -- `true` if the key is new.
  def InsertB (b : &List(Entry)) (k : Word) (v : Word) : Bool by b := (
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

  def Insert (cap : Word) (hm : &HashMap(cap)) (k : Word) (v : Word) (hc : Lt(Zero, cap)) : Unit := (
    match *hm {
      MkHM(slots, size) => (
        let i = ModS(k, cap);
        let b = GetMut(List(Entry), cap, AsSlice(List(Entry), cap, &slots), i, ModLt(k, cap, hc));
        let fresh = InsertB(b, k, v);
        match fresh {
          true => size := Succ(size),
          false => (),
        }
      ),
    }
  )

  def Size (cap : Word) (hm : HashMap(cap)) : Word := (
    match hm {
      MkHM(slots, size) => size,
    }
  )

  -- Keys 5 and 3 collide in a table of two; 5 is inserted twice.
  def InsertRun : Id Word (
      let hm = MkHM(Replicate(List(Entry), W(2), Nil), Zero);
      Insert(W(2), &hm, W(5), W(50), refl);
      Insert(W(2), &hm, W(3), W(30), refl);
      Insert(W(2), &hm, W(5), W(51), refl);
      Size(W(2), hm)) W(2) := refl

  def InsertRunBucket : Id (List(Entry)) (
      let hm = MkHM(Replicate(List(Entry), W(2), Nil), Zero);
      Insert(W(2), &hm, W(5), W(50), refl);
      Insert(W(2), &hm, W(3), W(30), refl);
      Insert(W(2), &hm, W(5), W(51), refl);
      match hm {
        MkHM(slots, size) => clone(*GetMut(List(Entry), W(2), AsSlice(List(Entry), W(2), &slots), Succ(Zero), refl)),
      }) (Cons(MkE(W(5), W(51)), Cons(MkE(W(3), W(30)), Nil))) := refl

  -- Without a proof that the slot is in bounds there is no borrow of it.
  reject def InsertUnbounded (cap : Word) (hm : &HashMap(cap)) (k : Word) (v : Word) : Unit := (
    match *hm {
      MkHM(slots, size) => (
        let b = GetMut(List(Entry), cap, AsSlice(List(Entry), cap, &slots), ModS(k, cap), refl);
        let fresh = InsertB(b, k, v);
        ()
      ),
    }
  )

  -- ## The abstraction is enforced (K2, K3)
  -- `SliceOf` is `unsized abstract`, `Cell`, `CellsEnd` and `ArrayOf` are `abstract`, and the
  -- five natives are `implemented by` native code. Outside model code (their bodies, and
  -- the model functions, which take or return a view by value and so never run at runtime),
  -- runtime code never reads, moves, assigns or matches a view, and never builds or takes
  -- apart the representation. reviewer-7's three programs bypassed the natives: `Suffix`
  -- returns a borrow of a sub-view, `TwoParts` holds two disjoint borrows without
  -- `WithSplit`, and `Rebuild` replaces the representation wholesale.
  reject def Suffix (m : Word) (s : &Slice(Word, Succ(m))) : &Slice(Word, m) := (
    match *s { MkSlice(c) => match c { MkC(x, t) => &t } })
  reject def TwoParts (m : Word) (s : &Slice(Word, Succ(m))) : Unit := (
    match *s { MkSlice(c) => match c { MkC(x, t) => (let a = &x; let b = &t; *a := Zero; Fill(Word, m, b, Succ(Zero))) } })
  reject def Rebuild (s : &Slice(Word, Succ(Zero))) : Unit := (*s := MkSlice(MkC(W(7), MkSlice(End))))
  -- A model function at runtime would need a view by value. (Under D53 alone, reading `*s`
  -- would also end the borrow with the view moved out.)
  reject def ReadModel (n : Word) (s : &Slice(Word, n)) (i : Word) (h : Lt(i, n)) : Word := Nth(Word, n, *s, i, h)
  -- In a statement, the model is unrestricted.
  def ReadIsNth (n : Word) (s : &Slice(Word, n)) (i : Word) (h : Lt(i, n)) :
      Id(Word, *GetMut(Word, n, s, i, h), Nth(Word, n, clone(*s), i, h)) := GetMutRead(Word, n, s, i, h)
}

-- the exact number of declarations (a truncated file changes it)
#guard ArrayBench.decls.length == 53
-- the element reads' rejections, each for its reason
#guard (run "ArrayBench" ArrayBench).rejectedWith [
  ("ReadMove", "[D53] reading *GetMut(…) moves its content out through the borrow GetMut(…) returns, which then ends with it moved out (⊥): copy it with clone(*GetMut(…))"),
  ("NotAPlace", "*Leb(…): Leb(…) does not return a borrow (type Bool), so *Leb(…) is not a place"),
  ("ReadPastEnd", "argument 5 (h) has type ⊤, expected False"),
  ("LitWrongLength", "argument 4 (h) has type ⊤, expected False"),
  ("TwoGetMut", "[Read] a was moved out or its borrow ended")]

/-! ## B2: quicksort

In place, over a view, recursing over indices only. The partition is Lomuto's scan with index
bounds proved from its invariant; the recursive calls get the two sides of the pivot as
borrowed pieces. What is proved (`QSCorrect`): quicksort's result is sorted and is a permutation
of its input, with fuel equal to the length.
* `QSPerm`: quicksort permutes its view (every count is unchanged), for any fuel.
* `QSSorted`: quicksort sorts its view, for fuel at least the length, given the partition's
  contract: four facts about `Partition` (`PartLe`, `PartLeft`, `PartPivot`, `PartRight`).
* `PartLeProof` … `PartRightProof`: the partition meets that contract, for every input. This is
  Lomuto's invariant: the pivot stays at 0, cells `1 … i` are at most it, cells
  `i + 1 … j - 1` are greater (`ScanLt`, `ScanPivot`, `ScanLeft`, `ScanRight`, by recursion on
  the countdown). It is bridged to the contract's pieces by `AllLeTakeOf`, `TakeOneDrop` and
  `AllGeDropOf`.
-/

ochr Quicksort uses ArrayLemmas {
  -- Lomuto's partition around the pivot `p`, which sits at index 0. Elements `1 … i` are at
  -- most `p` and `i + 1 … j - 1` are greater; `rem` elements are still to scan (`rem + j = n`).
  -- The recursion is on `rem`, never on the view. Every bound is a lemma about indices.
  def Scan (n : Word) (s : &Slice(Word, n)) (p : Word) (i : Word) (j : Word) (rem : Word)
      (hij : Lt(i, j)) (hr : Eq Word (WAdd(rem, j)) n) : Word by rem := (
    match rem {
      Zero => (
        let hin : Lt(i, n) = (rewrite hr in hij);
        Swap(Word, n, s, Zero, i, LeTrans(Succ(Zero), Succ(i), n, refl, hin), hin);
        i
      ),
      Succ(r) => (
        let hjn : Lt(j, n) = (rewrite hr in LeAddL(r, j));
        let hr2 : Eq Word (WAdd(r, Succ(j))) n = (rewrite AddRS(r, j) in hr);
        let x = *GetMut(Word, n, &*s, j, hjn);
        let b = Leb(x, p);
        match b {
          true => (
            Swap(Word, n, &*s, Succ(i), j, LeTrans(Succ(Succ(i)), Succ(j), n, hij, hjn), hjn);
            Scan(n, s, p, Succ(i), Succ(j), r, hij, hr2)
          ),
          false => Scan(n, s, p, i, Succ(j), r, LeStep(Succ(i), j, hij), hr2),
        }
      ),
    }
  )

  -- The pivot's final index.
  def Partition (m : Word) (s : &Slice(Word, Succ(m))) : Word := (
    let p = *GetMut(Word, Succ(m), &*s, Zero, refl);
    Scan(Succ(m), s, p, Zero, Succ(Zero), m, refl, AddOneR(m))
  )

  -- Sort both sides of the pivot at `k`, with `rec`. The pieces are borrowed by continuations
  -- (`WithSplit`), so each recursive call sees only its own piece. Written once for any `rec`,
  -- which is also what its lemmas are about. The first closure calls `rec` and hands it on to
  -- the second, which would move it out of the first closure's captures, so the second gets a
  -- clone (a closure may run again, D53).
  def Recurse (rec : Π(n : Word) (s : &Slice(Word, n)). Unit) (m : Word) (k : Word) (s : &Slice(Word, Succ(m))) : Unit := (
    let d = LeDec(k, m);
    match d {
      Yes(hk) => WithSplit(Word, Unit, Succ(m), k, s, LeStep(k, m, hk),
        λ(l : &Slice(Word, k)) (r : &Slice(Word, Sub(Succ(m), k))) : Unit => (
          rec(k, l);
          let rec2 = clone(rec);
          WithSplit(Word, Unit, Sub(Succ(m), k), Succ(Zero), r, SubPos(m, k, hk),
            λ(p : &Slice(Word, Succ(Zero))) (rr : &Slice(Word, Sub(Sub(Succ(m), k), Succ(Zero)))) : Unit => rec2(Sub(Sub(Succ(m), k), Succ(Zero)), rr))
        )),
      No(nk) => (),
    }
  )

  -- [K6] The recursion is on the length, but the lengths `k` and `m - k` of the pieces are not
  -- structural subterms of `Succ(m)`; until recursion on a measure exists, fuel bounds the depth
  -- (`QS(n, n, s)` sorts).
  def QS (fuel : Word) (n : Word) (s : &Slice(Word, n)) : Unit by fuel := (
    match fuel {
      Zero => (),
      Succ(f) => match n {
        Zero => (),
        Succ(m) => (
          let k = Partition(m, &*s);
          Recurse(λ(n' : Word) (s' : &Slice(Word, n')) : Unit => QS(f, n', s'), m, k, s)
        ),
      },
    }
  )

  def SortArray (n : Word) (a : &Array(Word, n)) : Unit := QS(n, n, AsSlice(Word, n, a))

  def SortRun : Id(Array(Word, W(5)),
      (let a : Array(Word, W(5)) = [W(3), W(1), W(4), W(1), W(2)]; SortArray(W(5), &a); a),
      ([W(1), W(1), W(2), W(3), W(4)] : Array(Word, W(5)))) := refl

  reject def SortRunWrong : Id(Array(Word, W(5)),
      (let a : Array(Word, W(5)) = [W(3), W(1), W(4), W(1), W(2)]; SortArray(W(5), &a); a),
      ([W(1), W(1), W(2), W(4), W(3)] : Array(Word, W(5)))) := refl

  -- ## Quicksort permutes: every count is unchanged
  -- The scan only swaps.
  def ScanPerm (n : Word) (s : &Slice(Word, n)) (p : Word) (i : Word) (j : Word) (rem : Word)
      (hij : Lt(i, j)) (hr : Eq Word (WAdd(rem, j)) n) (q : Word) :
      (let old = clone(*s); Eq Word (Count(q, n, (Scan(n, &*s, p, i, j, rem, hij, hr); clone(*s)))) (Count(q, n, old))) by rem := (
    match rem {
      Zero => (
        let hin : Lt(i, n) = (rewrite hr in hij);
        let h0 : Lt(Zero, n) = LeTrans(Succ(Zero), Succ(i), n, refl, hin);
        rewrite ← SwapIsSwapS(Word, n, s, Zero, i, h0, hin) in CountSwap(q, n, clone(*s), Zero, i, h0, hin)
      ),
      Succ(r) => (
        let hjn : Lt(j, n) = (rewrite hr in LeAddL(r, j));
        let hr2 : Eq Word (WAdd(r, Succ(j))) n = (rewrite AddRS(r, j) in hr);
        -- the scan reads element `j` through its borrow: the value `x`, and the view `v`
        -- afterwards, a put-back program with the same counts by `GetMutRead`
        let x = (let c = clone(*s); *GetMut(Word, n, &c, j, hjn));
        let v = (let c = clone(*s); let y = *GetMut(Word, n, &c, j, hjn); c);
        let ⟨hx, hv⟩ = GetMutRead(Word, n, s, j, hjn);
        let hc : Eq(Word, Count(q, n, v), Count(q, n, clone(*s))) = (rewrite ← hv in refl);
        let b = Leb(x, p);
        rewrite hc in
        match b {
          true => (
            let hsi : Lt(Succ(i), n) = LeTrans(Succ(Succ(i)), Succ(j), n, hij, hjn);
            let c = (let c1 = clone(v); Swap(Word, n, &c1, Succ(i), j, hsi, hjn); c1);
            rewrite CountSwap(q, n, v, Succ(i), j, hsi, hjn) in
            rewrite SwapIsSwapSV(Word, n, v, Succ(i), j, hsi, hjn) in
              ScanPerm(n, &c, p, Succ(i), Succ(j), r, hij, hr2, q)
          ),
          false => ScanPerm(n, &v, p, i, Succ(j), r, LeStep(Succ(i), j, hij), hr2, q),
        }
      ),
    }
  )
  def PartitionPerm (m : Word) (s : &Slice(Word, Succ(m))) (q : Word) :
      (let old = clone(*s); Eq Word (Count(q, Succ(m), (Partition(m, &*s); clone(*s)))) (Count(q, Succ(m), old))) := (
    -- the pivot is read at 0: once the view's first cell is split off, the read computes
    match *s {
      MkSlice(c) => match c {
        MkC(y, t) => (
          let p = y;
          ScanPerm(Succ(m), s, p, Zero, Succ(Zero), m, refl, AddOneR(m), q)
        ),
      },
    }
  )

  -- The recursive step permutes, for any `rec` that does.
  def RecursePerm (rec : Π(n : Word) (s : &Slice(Word, n)). Unit)
      (ih : Π(n : Word) (s : &Slice(Word, n)) (q : Word). (let old = clone(*s); Eq Word (Count(q, n, (rec(n, &*s); clone(*s)))) (Count(q, n, old))))
      (m : Word) (k : Word) (s : &Slice(Word, Succ(m))) (q : Word) :
      (let old = clone(*s); Eq Word (Count(q, Succ(m), (Recurse(rec, m, k, &*s); clone(*s)))) (Count(q, Succ(m), old))) := (
    let d = LeDec(k, m);
    match d {
      Yes(hk) => (
        let hk2 = LeStep(k, m, hk);
        let h1 = SubPos(m, k, hk);
        -- the pieces before, and after the two recursive calls
        let tk = TakeS(Word, Succ(m), k, clone(*s), hk2);
        let r0 = DropS(Word, Succ(m), k, clone(*s));
        let pv = TakeS(Word, Sub(Succ(m), k), Succ(Zero), clone(r0), h1);
        let rr = DropS(Word, Sub(Succ(m), k), Succ(Zero), clone(r0));
        let l2 = (let c = clone(tk); rec(k, &c); c);
        let rr2 = (let c = clone(rr); rec(Sub(Sub(Succ(m), k), Succ(Zero)), &c); c);
        let x2 = JoinS(Word, Sub(Succ(m), k), Succ(Zero), clone(pv), clone(rr2));
        -- the left part: the recursive call permutes it
        rewrite ← CountJoin(q, Succ(m), k, l2, x2, hk2) in
        rewrite ← (let c = clone(tk); ih(k, &c, q)) in
        -- the right part: the pivot is untouched and the recursive call permutes the rest
        rewrite ← CountJoin(q, Sub(Succ(m), k), Succ(Zero), pv, rr2, h1) in
        rewrite ← (let c = clone(rr); ih(Sub(Sub(Succ(m), k), Succ(Zero)), &c, q)) in
        rewrite CountJoin(q, Sub(Succ(m), k), Succ(Zero), pv, rr, h1) in
        rewrite ← JoinTakeDrop(Word, Sub(Succ(m), k), Succ(Zero), r0, h1) in
        -- and the two parts are the view, split
        rewrite CountJoin(q, Succ(m), k, tk, r0, hk2) in
        rewrite ← JoinTakeDrop(Word, Succ(m), k, clone(*s), hk2) in refl
      ),
      No(nk) => refl,
    }
  )

  -- The closure `QS` passes to `Recurse`, built outside `QS`: it captures the sort and the fuel,
  -- as the one inside `QS` captures `QS` itself and its fuel, so the two are the same value.
  def RecWith (qs : Π(fuel : Word) (n : Word) (s : &Slice(Word, n)). Unit) (fuel : Word) : (Π(n : Word) (s : &Slice(Word, n)). Unit) := (
    match fuel {
      Zero => (λ(n : Word) (s : &Slice(Word, n)) : Unit => ()),
      Succ(f) => (λ(n : Word) (s : &Slice(Word, n)) : Unit => qs(f, n, s)),
    }
  )

  -- Quicksort permutes its view: every count is unchanged.
  def QSPerm (fuel : Word) (n : Word) (s : &Slice(Word, n)) (q : Word) :
      (let old = clone(*s); Eq Word (Count(q, n, (QS(fuel, n, &*s); clone(*s)))) (Count(q, n, old))) by fuel := (
    match fuel {
      Zero => refl,
      Succ(f) => match n {
        Zero => refl,
        Succ(m) => (
          let rec = RecWith(QS, fuel);
          let c = clone(*s);
          let k = Partition(m, &c);
          let e1 = RecursePerm(rec,
            λ(n2 : Word) (s2 : &Slice(Word, n2)) (q2 : Word) :
                (let old = clone(*s2); Eq Word (Count(q2, n2, (QS(f, n2, &*s2); clone(*s2)))) (Count(q2, n2, old))) =>
              QSPerm(f, n2, s2, q2),
            m, k, &c, q);
          rewrite PartitionPerm(m, s, q) in e1
        ),
      },
    }
  )
  -- ## Quicksort sorts, given the partition's contract
  -- Every element is at most `p`; at least `p`; and the view is sorted. Each is a
  -- proposition computed by recursion on the length.
  def AllLe (n : Word) (s : Slice(Word, n)) (p : Word) : Prop by n := (
    match n {
      Zero => ⊤,
      Succ(m) => match s {
        MkSlice(c) => match c {
          MkC(x, t) => Le(x, p) ∧ AllLe(m, t, p),
        },
      },
    }
  )

  def AllGe (n : Word) (s : Slice(Word, n)) (p : Word) : Prop by n := (
    match n {
      Zero => ⊤,
      Succ(m) => match s {
        MkSlice(c) => match c {
          MkC(x, t) => Le(p, x) ∧ AllGe(m, t, p),
        },
      },
    }
  )

  def Sorted (n : Word) (s : Slice(Word, n)) : Prop by n := (
    match n {
      Zero => ⊤,
      Succ(m) => match s {
        MkSlice(c) => match c {
          MkC(x, t) => AllGe(m, t, x) ∧ Sorted(m, t),
        },
      },
    }
  )

  -- A lower bound can be lowered.
  def AllGeWeaken (n : Word) (s : Slice(Word, n)) (x : Word) (a : Word) (h : AllGe(n, s, x)) (hax : Le(a, x)) :
      AllGe(n, s, a) by n := (
    match n {
      Zero => refl,
      Succ(m) => match s {
        MkSlice(c) => match c {
          MkC(y, t) => (
            let ⟨hy, ht⟩ = h;
            ⟨LeTrans(a, x, y, hax, hy), AllGeWeaken(m, t, x, a, ht, hax)⟩
          ),
        },
      },
    }
  )

  def AllGeJoin (n : Word) (k : Word) (l : Slice(Word, k)) (r : Slice(Word, Sub(n, k))) (h : Le(k, n)) (a : Word)
      (hl : AllGe(k, l, a)) (hr : AllGe(Sub(n, k), r, a)) : AllGe(n, JoinS(Word, n, k, l, r), a) by k := (
    match k {
      Zero => hr,
      Succ(k') => match n {
        Zero => match h {},
        Succ(m) => match l {
          MkSlice(c) => match c {
            MkC(y, t) => (
              let ⟨hy, ht⟩ = hl;
              ⟨hy, AllGeJoin(m, k', t, r, h, a, ht, hr)⟩
            ),
          },
        },
      },
    }
  )

  -- Two sorted views joined, everything on the left at most `x` and on the right at least
  -- `x`, are sorted.
  def SortedJoin (n : Word) (k : Word) (l : Slice(Word, k)) (r : Slice(Word, Sub(n, k))) (h : Le(k, n)) (x : Word)
      (hl : Sorted(k, l)) (hlx : AllLe(k, l, x)) (hr : Sorted(Sub(n, k), r)) (hrx : AllGe(Sub(n, k), r, x)) :
      Sorted(n, JoinS(Word, n, k, l, r)) by k := (
    match k {
      Zero => hr,
      Succ(k') => match n {
        Zero => match h {},
        Succ(m) => match l {
          MkSlice(c) => match c {
            MkC(a, t) => (
              let ⟨hla, hlt⟩ = hl;
              let ⟨hax, htx⟩ = hlx;
              ⟨AllGeJoin(m, k', t, r, h, a, hla, AllGeWeaken(Sub(m, k'), r, x, a, hrx, hax)),
                SortedJoin(m, k', t, r, h, x, hlt, htx, hr, hrx)⟩
            ),
          },
        },
      },
    }
  )

  -- ## Bounds survive a permutation, by counting
  def EqbRefl (x : Word) : Eq Bool (Eqb(x, x)) true by x := (
    match x {
      Zero => refl,
      Succ(x') => EqbRefl(x'),
    }
  )

  -- If q = x (by Eqb), x <= p and p < q is impossible; and the mirror image.
  def EqbLeLt (q : Word) (x : Word) (p : Word) (e : Eq Bool (Eqb(q, x)) true) (h1 : Le(x, p)) (h2 : Lt(p, q)) : False by q := (
    match q {
      Zero => match h2 {},
      Succ(q') => match x {
        Zero => match e {},
        Succ(x') => match p {
          Zero => match h1 {},
          Succ(p') => EqbLeLt(q', x', p', e, h1, h2),
        },
      },
    }
  )

  def EqbGeLt (q : Word) (x : Word) (p : Word) (e : Eq Bool (Eqb(q, x)) true) (h1 : Le(p, x)) (h2 : Lt(q, p)) : False by q := (
    match q {
      Zero => match x {
        Zero => match p {
          Zero => match h2 {},
          Succ(p') => match h1 {},
        },
        Succ(x') => match e {},
      },
      Succ(q') => match x {
        Zero => match e {},
        Succ(x') => match p {
          Zero => match h2 {},
          Succ(p') => EqbGeLt(q', x', p', e, h1, h2),
        },
      },
    }
  )

  -- Every element at most `p`: no value above `p` occurs.
  def CountAboveZero (n : Word) (s : Slice(Word, n)) (p : Word) (h : AllLe(n, s, p)) (q : Word) (hq : Lt(p, q)) :
      Eq Word (Count(q, n, s)) Zero by n := (
    match n {
      Zero => refl,
      Succ(m) => match s {
        MkSlice(c) => match c {
          MkC(x, t) => (
            let ⟨hx, ht⟩ = h;
            let e = Eqb(q, x);
            match e {
              true => (
                let no = EqbLeLt(q, x, p, refl, hx, hq);
                match no {}
              ),
              false => CountAboveZero(m, t, p, ht, q, hq),
            }
          ),
        },
      },
    }
  )

  def CountBelowZero (n : Word) (s : Slice(Word, n)) (p : Word) (h : AllGe(n, s, p)) (q : Word) (hq : Lt(q, p)) :
      Eq Word (Count(q, n, s)) Zero by n := (
    match n {
      Zero => refl,
      Succ(m) => match s {
        MkSlice(c) => match c {
          MkC(x, t) => (
            let ⟨hx, ht⟩ = h;
            let e = Eqb(q, x);
            match e {
              true => (
                let no = EqbGeLt(q, x, p, refl, hx, hq);
                match no {}
              ),
              false => CountBelowZero(m, t, p, ht, q, hq),
            }
          ),
        },
      },
    }
  )

  -- A count of zero for the whole is a count of zero for the rest.
  def CountTailZero (q : Word) (m : Word) (x : Word) (t : Slice(Word, m)) (e0 : Eq Word (Count(q, Succ(m), MkSlice(MkC(x, t)))) Zero) :
      Eq Word (Count(q, m, t)) Zero := (
    let e = Eqb(q, x);
    match e {
      true => match e0 {},
      false => e0,
    }
  )

  -- Conversely: if no value above `p` occurs, every element is at most `p`.
  def AllLeOfCounts (n : Word) (s : Slice(Word, n)) (p : Word)
      (hz : Π(q : Word) (hq : Lt(p, q)). Eq Word (Count(q, n, s)) Zero) : AllLe(n, s, p) by n := (
    match n {
      Zero => refl,
      Succ(m) => match s {
        MkSlice(c) => match c {
          MkC(x, t) => (
            let d = LeDec(x, p);
            match d {
              Yes(hle) => ⟨hle, AllLeOfCounts(m, t, p, λ(q : Word) (hq : Lt(p, q)) : Eq Word (Count(q, m, t)) Zero => CountTailZero(q, m, x, t, hz(q, hq)))⟩,
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

  def AllGeOfCounts (n : Word) (s : Slice(Word, n)) (p : Word)
      (hz : Π(q : Word) (hq : Lt(q, p)). Eq Word (Count(q, n, s)) Zero) : AllGe(n, s, p) by n := (
    match n {
      Zero => refl,
      Succ(m) => match s {
        MkSlice(c) => match c {
          MkC(x, t) => (
            let d = LeDec(p, x);
            match d {
              Yes(hle) => ⟨hle, AllGeOfCounts(m, t, p, λ(q : Word) (hq : Lt(q, p)) : Eq Word (Count(q, m, t)) Zero => CountTailZero(q, m, x, t, hz(q, hq)))⟩,
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
  def AllLePerm (n : Word) (s : Slice(Word, n)) (s2 : Slice(Word, n)) (p : Word) (h : AllLe(n, s, p))
      (perm : Π(q : Word). Eq Word (Count(q, n, s2)) (Count(q, n, s))) : AllLe(n, s2, p) := (
    AllLeOfCounts(n, s2, p, λ(q : Word) (hq : Lt(p, q)) : Eq Word (Count(q, n, s2)) Zero =>
      rewrite ← perm(q) in CountAboveZero(n, s, p, h, q, hq))
  )

  def AllGePerm (n : Word) (s : Slice(Word, n)) (s2 : Slice(Word, n)) (p : Word) (h : AllGe(n, s, p))
      (perm : Π(q : Word). Eq Word (Count(q, n, s2)) (Count(q, n, s))) : AllGe(n, s2, p) := (
    AllGeOfCounts(n, s2, p, λ(q : Word) (hq : Lt(q, p)) : Eq Word (Count(q, n, s2)) Zero =>
      rewrite ← perm(q) in CountBelowZero(n, s, p, h, q, hq))
  )

  def LeSuccFalse (m : Word) (h : Le(Succ(m), m)) : False by m := (
    match m {
      Zero => match h {},
      Succ(m') => LeSuccFalse(m', h),
    }
  )

  -- ## Sorting
  -- The recursive step sorts the view, given the partition's facts about it (the pivot `x`
  -- ends at `k`; everything before is at most `x`, everything after at least `x`) and a
  -- `rec` that sorts and permutes views no longer than `m`.
  def RecurseSorted (m : Word) (rec : Π(n : Word) (s : &Slice(Word, n)). Unit)
      (ihS : Π(n : Word) (s : &Slice(Word, n)) (hn : Le(n, m)). (let c = clone(*s); rec(n, &c); Sorted(n, c)))
      (ihP : Π(n : Word) (s : &Slice(Word, n)) (q : Word). (let old = clone(*s); Eq Word (Count(q, n, (rec(n, &*s); clone(*s)))) (Count(q, n, old))))
      (k : Word) (hk : Le(k, m)) (x : Word) (s : &Slice(Word, Succ(m)))
      (hL : AllLe(k, TakeS(Word, Succ(m), k, clone(*s), LeStep(k, m, hk)), x))
      (hP : Eq (Slice(Word, Succ(Zero))) (MkSlice(MkC(x, MkSlice(End)))) (TakeS(Word, Sub(Succ(m), k), Succ(Zero), DropS(Word, Succ(m), k, clone(*s)), SubPos(m, k, hk))))
      (hR : AllGe(Sub(Sub(Succ(m), k), Succ(Zero)), DropS(Word, Sub(Succ(m), k), Succ(Zero), DropS(Word, Succ(m), k, clone(*s))), x)) :
      (let c = clone(*s); Recurse(rec, m, k, &c); Sorted(Succ(m), c)) := (
    let d = LeDec(k, m);
    match d {
      Yes(hk3) => (
        let hk2 = LeStep(k, m, hk);
        let h1 = SubPos(m, k, hk);
        let tk = TakeS(Word, Succ(m), k, clone(*s), hk2);
        let r0 = DropS(Word, Succ(m), k, clone(*s));
        let pv = TakeS(Word, Sub(Succ(m), k), Succ(Zero), clone(r0), h1);
        let rr = DropS(Word, Sub(Succ(m), k), Succ(Zero), clone(r0));
        let l2 = (let c = clone(tk); rec(k, &c); c);
        let rr2 = (let c = clone(rr); rec(Sub(Sub(Succ(m), k), Succ(Zero)), &c); c);
        let x2 = JoinS(Word, Sub(Succ(m), k), Succ(Zero), clone(pv), clone(rr2));
        -- the left part: sorted by `rec`, and still at most `x` because `rec` permutes
        let sl2 : Sorted(k, l2) = (let c = clone(tk); ihS(k, &c, hk));
        let bl2 : AllLe(k, l2, x) = AllLePerm(k, tk, l2, x, hL,
          λ(q : Word) : Eq Word (Count(q, k, l2)) (Count(q, k, tk)) => (let c = clone(tk); ihP(k, &c, q)));
        -- the right part: likewise, at least `x`
        let srr2 : Sorted(Sub(Sub(Succ(m), k), Succ(Zero)), rr2) = (let c = clone(rr); ihS(Sub(Sub(Succ(m), k), Succ(Zero)), &c, SubOneLe(m, k)));
        let brr2 : AllGe(Sub(Sub(Succ(m), k), Succ(Zero)), rr2, x) = AllGePerm(Sub(Sub(Succ(m), k), Succ(Zero)), rr, rr2, x, hR,
          λ(q : Word) : Eq Word (Count(q, Sub(Sub(Succ(m), k), Succ(Zero)), rr2)) (Count(q, Sub(Sub(Succ(m), k), Succ(Zero)), rr)) =>
            (let c = clone(rr); ihP(Sub(Sub(Succ(m), k), Succ(Zero)), &c, q)));
        -- the pivot piece is `[x]`
        let spv : Sorted(Succ(Zero), pv) = (rewrite hP in refl);
        let lpv : AllLe(Succ(Zero), pv, x) = (rewrite hP in ⟨LeRefl(x), refl⟩);
        let gpv : AllGe(Succ(Zero), pv, x) = (rewrite hP in ⟨LeRefl(x), refl⟩);
        -- glue: pivot and right part, then left part and the rest
        let sx2 : Sorted(Sub(Succ(m), k), x2) = SortedJoin(Sub(Succ(m), k), Succ(Zero), pv, rr2, h1, x, spv, lpv, srr2, brr2);
        let gx2 : AllGe(Sub(Succ(m), k), x2, x) = AllGeJoin(Sub(Succ(m), k), Succ(Zero), pv, rr2, h1, x, gpv, brr2);
        SortedJoin(Succ(m), k, l2, x2, hk2, x, sl2, bl2, sx2, gx2)
      ),
      No(nk) => (
        let no = LeSuccFalse(m, LeTrans(Succ(m), k, m, nk, hk));
        match no {}
      ),
    }
  )

  -- ## The partition's contract
  -- Run on a copy of its input `v`, the partition returns `k` and leaves `PartV(m, v)`. Its
  -- contract: the pivot `x` (the first element of `v`) ends at `k <= m`, everything before
  -- it is at most `x`, and everything after it at least `x`.
  def PartK (m : Word) (v : Slice(Word, Succ(m))) : Word := (
    let c = v;
    Partition(m, &c)
  )

  def PartV (m : Word) (v : Slice(Word, Succ(m))) : Slice(Word, Succ(m)) := (
    let c = v;
    Partition(m, &c);
    c
  )

  def PartLe (m : Word) (v : Slice(Word, Succ(m))) : Prop := Le(PartK(m, v), m)

  def PartLeft (m : Word) (v : Slice(Word, Succ(m))) (hk : PartLe(m, v)) : Prop := (
    AllLe(PartK(m, v), TakeS(Word, Succ(m), PartK(m, clone(v)), PartV(m, clone(v)), LeStep(PartK(m, v), m, hk)), Nth(Word, Succ(m), v, Zero, refl))
  )

  def PartPivot (m : Word) (v : Slice(Word, Succ(m))) (hk : PartLe(m, v)) : Prop := (
    Eq (Slice(Word, Succ(Zero))) (MkSlice(MkC(Nth(Word, Succ(m), v, Zero, refl), MkSlice(End))))
      (TakeS(Word, Sub(Succ(m), PartK(m, clone(v))), Succ(Zero), DropS(Word, Succ(m), PartK(m, clone(v)), PartV(m, clone(v))), SubPos(m, PartK(m, v), hk)))
  )

  def PartRight (m : Word) (v : Slice(Word, Succ(m))) (hk : PartLe(m, v)) : Prop := (
    AllGe(Sub(Sub(Succ(m), PartK(m, v)), Succ(Zero)), DropS(Word, Sub(Succ(m), PartK(m, clone(v))), Succ(Zero), DropS(Word, Succ(m), PartK(m, clone(v)), PartV(m, v))),
      Nth(Word, Succ(m), v, Zero, refl))
  )

  -- Quicksort sorts, for fuel at least the length, given the partition's contract.
  def QSSorted (specLe : Π(m : Word) (v : Slice(Word, Succ(m))). PartLe(m, v))
      (specL : Π(m : Word) (v : Slice(Word, Succ(m))) (hk : PartLe(m, v)). PartLeft(m, v, hk))
      (specP : Π(m : Word) (v : Slice(Word, Succ(m))) (hk : PartLe(m, v)). PartPivot(m, v, hk))
      (specR : Π(m : Word) (v : Slice(Word, Succ(m))) (hk : PartLe(m, v)). PartRight(m, v, hk))
      (fuel : Word) (n : Word) (s : &Slice(Word, n)) (hf : Le(n, fuel)) :
      (let c = clone(*s); QS(fuel, n, &c); Sorted(n, c)) by fuel := (
    match fuel {
      Zero => match n {
        Zero => refl,
        Succ(m) => match hf {},
      },
      Succ(f) => match n {
        Zero => refl,
        Succ(m) => (
          let rec = RecWith(QS, fuel);
          let v = clone(*s);
          let hk = specLe(m, v);
          let c = clone(*s);
          let k = Partition(m, &c);
          RecurseSorted(m, rec,
            λ(n2 : Word) (s2 : &Slice(Word, n2)) (hn : Le(n2, m)) : (let c2 = clone(*s2); QS(f, n2, &c2); Sorted(n2, c2)) =>
              QSSorted(specLe, specL, specP, specR, f, n2, s2, LeTrans(n2, m, f, hn, hf)),
            λ(n2 : Word) (s2 : &Slice(Word, n2)) (q2 : Word) :
                (let old = clone(*s2); Eq Word (Count(q2, n2, (QS(f, n2, &*s2); clone(*s2)))) (Count(q2, n2, old))) =>
              QSPerm(f, n2, s2, q2),
            k, hk, Nth(Word, Succ(m), v, Zero, refl), &c, specL(m, v, hk), specP(m, v, hk), specR(m, v, hk))
        ),
      },
    }
  )

  -- The contract on examples (proved for every input below).
  def ContractRun1 : PartLe(W(4), MkSlice(MkC(W(3), MkSlice(MkC(Succ(Zero), MkSlice(MkC(W(4), MkSlice(MkC(Succ(Zero), MkSlice(MkC(W(2), MkSlice(End)))))))))))) ∧ PartLeft(W(4), MkSlice(MkC(W(3), MkSlice(MkC(Succ(Zero), MkSlice(MkC(W(4), MkSlice(MkC(Succ(Zero), MkSlice(MkC(W(2), MkSlice(End))))))))))), refl) ∧ PartPivot(W(4), MkSlice(MkC(W(3), MkSlice(MkC(Succ(Zero), MkSlice(MkC(W(4), MkSlice(MkC(Succ(Zero), MkSlice(MkC(W(2), MkSlice(End))))))))))), refl) ∧ PartRight(W(4), MkSlice(MkC(W(3), MkSlice(MkC(Succ(Zero), MkSlice(MkC(W(4), MkSlice(MkC(Succ(Zero), MkSlice(MkC(W(2), MkSlice(End))))))))))), refl) := refl
  def ContractRun2 : PartLe(W(5), MkSlice(MkC(W(2), MkSlice(MkC(W(5), MkSlice(MkC(Succ(Zero), MkSlice(MkC(W(5), MkSlice(MkC(Zero, MkSlice(MkC(W(2), MkSlice(End)))))))))))))) ∧ PartLeft(W(5), MkSlice(MkC(W(2), MkSlice(MkC(W(5), MkSlice(MkC(Succ(Zero), MkSlice(MkC(W(5), MkSlice(MkC(Zero, MkSlice(MkC(W(2), MkSlice(End))))))))))))), refl) ∧ PartPivot(W(5), MkSlice(MkC(W(2), MkSlice(MkC(W(5), MkSlice(MkC(Succ(Zero), MkSlice(MkC(W(5), MkSlice(MkC(Zero, MkSlice(MkC(W(2), MkSlice(End))))))))))))), refl) ∧ PartRight(W(5), MkSlice(MkC(W(2), MkSlice(MkC(W(5), MkSlice(MkC(Succ(Zero), MkSlice(MkC(W(5), MkSlice(MkC(Zero, MkSlice(MkC(W(2), MkSlice(End))))))))))))), refl) := refl
  -- A wrong pivot position is not.
  reject def ContractWrong : PartPivot(W(4), MkSlice(MkC(W(3), MkSlice(MkC(Succ(Zero), MkSlice(MkC(W(4), MkSlice(MkC(Succ(Zero), MkSlice(MkC(W(2), MkSlice(End))))))))))), refl) ∧ Eq Word (PartK(W(4), MkSlice(MkC(W(3), MkSlice(MkC(Succ(Zero), MkSlice(MkC(W(4), MkSlice(MkC(Succ(Zero), MkSlice(MkC(W(2), MkSlice(End))))))))))))) W(2) := refl
  -- ## The partition meets its contract: Lomuto's invariant
  -- More order facts.
  def LeOfLt (a : Word) (b : Word) (h : Lt(a, b)) : Le(a, b) by a := (
    match a {
      Zero => refl,
      Succ(a') => match b {
        Zero => match h {},
        Succ(b') => LeOfLt(a', b', h),
      },
    }
  )

  def LtTrans (a : Word) (b : Word) (c : Word) (h1 : Lt(a, b)) (h2 : Lt(b, c)) : Lt(a, c) := (
    LeTrans(Succ(a), b, c, h1, LeOfLt(b, c, h2))
  )

  def LtLeTrans (a : Word) (b : Word) (c : Word) (h1 : Lt(a, b)) (h2 : Le(b, c)) : Lt(a, c) := LeTrans(Succ(a), b, c, h1, h2)

  -- What a comparison said, as a proof.
  def LebLe (a : Word) (b : Word) (e : Eq Bool (Leb(a, b)) true) : Le(a, b) by a := (
    match a {
      Zero => refl,
      Succ(a') => match b {
        Zero => match e {},
        Succ(b') => LebLe(a', b', e),
      },
    }
  )

  def LebGt (a : Word) (b : Word) (e : Eq Bool (Leb(a, b)) false) : Lt(b, a) by a := (
    match a {
      Zero => match e {},
      Succ(a') => match b {
        Zero => refl,
        Succ(b') => LebGt(a', b', e),
      },
    }
  )

  -- ## Reading a swapped view
  def NthSwapB (n : Word) (c : Slice(Word, n)) (a : Word) (b : Word) (ha : Lt(a, n)) (hb : Lt(b, n)) :
      Eq Word (Nth(Word, n, SwapS(Word, n, c, a, b, ha, hb), b, hb)) (Nth(Word, n, c, a, ha)) := (
    NthSetSame(Word, n, SetS(Word, n, clone(c), a, Nth(Word, n, c, b, hb)), b, Nth(Word, n, c, a, ha), hb)
  )

  def NthSwapA (n : Word) (c : Slice(Word, n)) (a : Word) (b : Word) (ha : Lt(a, n)) (hb : Lt(b, n)) :
      Eq Word (Nth(Word, n, SwapS(Word, n, c, a, b, ha, hb), a, ha)) (Nth(Word, n, c, b, hb)) by a := (
    match n {
      Zero => match ha {},
      Succ(m) => match c {
        MkSlice(cc) => match cc {
          MkC(y, t) => match a {
            Zero => match b {
              Zero => refl,
              Succ(b') => refl,
            },
            Succ(a') => match b {
              Zero => NthSetSame(Word, m, t, a', y, ha),
              Succ(b') => NthSwapA(m, t, a', b', ha, hb),
            },
          },
        },
      },
    }
  )

  def NthSwapOther (n : Word) (c : Slice(Word, n)) (a : Word) (b : Word) (t : Word) (ha : Lt(a, n)) (hb : Lt(b, n))
      (ht : Lt(t, n)) (na : Π(e : Eq Word a t). False) (nb : Π(e : Eq Word b t). False) :
      Eq Word (Nth(Word, n, SwapS(Word, n, c, a, b, ha, hb), t, ht)) (Nth(Word, n, c, t, ht)) := (
    rewrite ← NthSetOther(Word, n, SetS(Word, n, clone(c), a, Nth(Word, n, c, b, hb)), b, t, Nth(Word, n, c, a, ha), hb, ht, nb) in
      NthSetOther(Word, n, c, a, t, Nth(Word, n, c, b, hb), ha, ht, na)
  )

  -- ## From facts about positions to facts about pieces
  def AllLeTakeOf (n : Word) (k : Word) (c : Slice(Word, n)) (p : Word) (hk : Le(k, n))
      (h : Π(t : Word) (ht : Lt(t, k)) (htn : Lt(t, n)). Le(Nth(Word, n, c, t, htn), p)) :
      AllLe(k, TakeS(Word, n, k, c, hk), p) by k := (
    match k {
      Zero => refl,
      Succ(k') => match n {
        Zero => match hk {},
        Succ(m) => match c {
          MkSlice(cc) => match cc {
            MkC(x, t0) => ⟨h(Zero, refl, refl),
              AllLeTakeOf(m, k', t0, p, hk,
                λ(t : Word) (ht : Lt(t, k')) (htn : Lt(t, m)) : Le(Nth(Word, m, t0, t, htn), p) => h(Succ(t), ht, htn))⟩,
          },
        },
      },
    }
  )

  def AllGeAllOf (n : Word) (c : Slice(Word, n)) (p : Word)
      (h : Π(t : Word) (ht : Lt(t, n)). Le(p, Nth(Word, n, c, t, ht))) : AllGe(n, c, p) by n := (
    match n {
      Zero => refl,
      Succ(m) => match c {
        MkSlice(cc) => match cc {
          MkC(x, t0) => ⟨h(Zero, refl),
            AllGeAllOf(m, t0, p, λ(t : Word) (ht : Lt(t, m)) : Le(p, Nth(Word, m, t0, t, ht)) => h(Succ(t), ht))⟩,
        },
      },
    }
  )

  def AllGeDropOf (n : Word) (k : Word) (c : Slice(Word, n)) (p : Word)
      (h : Π(t : Word) (ht : Lt(t, n)) (hkt : Lt(k, t)). Le(p, Nth(Word, n, c, t, ht))) :
      AllGe(Sub(Sub(n, k), Succ(Zero)), DropS(Word, Sub(n, k), Succ(Zero), DropS(Word, n, k, c)), p) by k := (
    match k {
      Zero => match n {
        Zero => refl,
        Succ(m) => match c {
          MkSlice(cc) => match cc {
            MkC(x, t0) => AllGeAllOf(m, t0, p, λ(t : Word) (ht : Lt(t, m)) : Le(p, Nth(Word, m, t0, t, ht)) => h(Succ(t), ht, refl)),
          },
        },
      },
      Succ(k') => match n {
        Zero => refl,
        Succ(m) => match c {
          MkSlice(cc) => match cc {
            MkC(x, t0) => AllGeDropOf(m, k', t0, p,
              λ(t : Word) (ht : Lt(t, m)) (hkt : Lt(k', t)) : Le(p, Nth(Word, m, t0, t, ht)) => h(Succ(t), ht, hkt)),
          },
        },
      },
    }
  )

  def TakeOneDrop (n : Word) (k : Word) (c : Slice(Word, n)) (hk : Lt(k, n)) :
      Eq (Slice(Word, Succ(Zero))) (MkSlice(MkC(Nth(Word, n, c, k, hk), MkSlice(End))))
        (TakeS(Word, Sub(n, k), Succ(Zero), DropS(Word, n, k, c), SubPosLt(n, k, hk))) by k := (
    match k {
      Zero => match n {
        Zero => match hk {},
        Succ(m) => match c {
          MkSlice(cc) => match cc {
            MkC(x, t0) => refl,
          },
        },
      },
      Succ(k') => match n {
        Zero => match hk {},
        Succ(m) => match c {
          MkSlice(cc) => match cc {
            MkC(x, t0) => TakeOneDrop(m, k', t0, hk),
          },
        },
      },
    }
  )

  -- ## The scan's last step: the pivot is swapped to `i`
  def EndLeft (n : Word) (s0 : Slice(Word, n)) (p : Word) (i : Word) (hin : Lt(i, n)) (h0 : Lt(Zero, n))
      (j1 : Π(t : Word) (ht : Lt(t, n)) (a : Lt(Zero, t)) (b : Le(t, i)). Le(Nth(Word, n, s0, t, ht), p))
      (t : Word) (ht : Lt(t, i)) (htn : Lt(t, n)) : Le(Nth(Word, n, SwapS(Word, n, s0, Zero, i, h0, hin), t, htn), p) := (
    match t {
      Zero => rewrite ← NthSwapA(n, s0, Zero, i, h0, hin) in j1(i, hin, ht, LeRefl(i)),
      Succ(t') => rewrite ← NthSwapOther(n, s0, Zero, i, Succ(t'), h0, hin, htn, λ(e : Eq Word Zero (Succ(t'))) : False => match e {},
          λ(e : Eq Word i (Succ(t'))) : False => LtNe(Succ(t'), i, ht, rewrite e in refl)) in
        j1(Succ(t'), htn, refl, LeOfLt(Succ(t'), i, ht)),
    }
  )

  def EndRight (n : Word) (s0 : Slice(Word, n)) (p : Word) (i : Word) (j : Word) (hin : Lt(i, n)) (h0 : Lt(Zero, n))
      (hjn : Eq Word j n)
      (j2 : Π(t : Word) (ht : Lt(t, n)) (a : Lt(i, t)) (b : Lt(t, j)). Lt(p, Nth(Word, n, s0, t, ht)))
      (t : Word) (ht : Lt(t, n)) (hkt : Lt(i, t)) : Lt(p, Nth(Word, n, SwapS(Word, n, s0, Zero, i, h0, hin), t, ht)) := (
    rewrite ← NthSwapOther(n, s0, Zero, i, t, h0, hin, ht, λ(e : Eq Word Zero t) : False => LtNe(Zero, t, LeTrans(Succ(Zero), Succ(i), t, refl, hkt), e),
        λ(e : Eq Word i t) : False => LtNe(i, t, hkt, e)) in
      j2(t, ht, hkt, rewrite ← hjn in ht)
  )

  -- ## One step of the scan keeps the invariant
  -- After swapping `i + 1` with `j` (the element at `j` was at most `p`): the pivot is still at
  -- 0, cells `1 … i + 1` are at most `p`, cells `i + 2 … j` are greater.
  def StepJ0 (n : Word) (s0 : Slice(Word, n)) (p : Word) (i : Word) (j : Word) (hsi : Lt(Succ(i), n)) (hjn : Lt(j, n))
      (hij : Lt(i, j)) (j0 : Π(h0 : Lt(Zero, n)). Eq Word (Nth(Word, n, s0, Zero, h0)) p) (h0 : Lt(Zero, n)) :
      Eq Word (Nth(Word, n, SwapS(Word, n, s0, Succ(i), j, hsi, hjn), Zero, h0)) p := (
    rewrite ← NthSwapOther(n, s0, Succ(i), j, Zero, hsi, hjn, h0, λ(e : Eq Word (Succ(i)) Zero) : False => match e {},
        λ(e : Eq Word j Zero) : False => LtNe(Zero, j, LeTrans(Succ(Zero), Succ(i), j, refl, hij), rewrite e in refl)) in
      j0(h0)
  )

  def StepJ1 (n : Word) (s0 : Slice(Word, n)) (p : Word) (i : Word) (j : Word) (hsi : Lt(Succ(i), n)) (hjn : Lt(j, n))
      (hij : Lt(i, j)) (j1 : Π(t : Word) (ht : Lt(t, n)) (a : Lt(Zero, t)) (b : Le(t, i)). Le(Nth(Word, n, s0, t, ht), p))
      (hx : Le(Nth(Word, n, s0, j, hjn), p)) (t : Word) (ht : Lt(t, n)) (a : Lt(Zero, t)) (b : Le(t, Succ(i))) :
      Le(Nth(Word, n, SwapS(Word, n, s0, Succ(i), j, hsi, hjn), t, ht), p) := (
    let d = LeDec(t, i);
    match d {
      Yes(hti) => rewrite ← NthSwapOther(n, s0, Succ(i), j, t, hsi, hjn, ht,
          λ(e : Eq Word (Succ(i)) t) : False => LtNe(t, Succ(i), hti, rewrite e in refl),
          λ(e : Eq Word j t) : False => LtNe(t, j, LeTrans(Succ(t), Succ(i), j, hti, hij), rewrite e in refl)) in
        j1(t, ht, a, hti),
      No(nti) => rewrite ← LeAntisym(t, Succ(i), b, nti) in rewrite ← NthSwapA(n, s0, Succ(i), j, hsi, hjn) in hx,
    }
  )

  def StepJ2 (n : Word) (s0 : Slice(Word, n)) (p : Word) (i : Word) (j : Word) (hsi : Lt(Succ(i), n)) (hjn : Lt(j, n))
      (hij : Lt(i, j)) (j2 : Π(t : Word) (ht : Lt(t, n)) (a : Lt(i, t)) (b : Lt(t, j)). Lt(p, Nth(Word, n, s0, t, ht)))
      (t : Word) (ht : Lt(t, n)) (a : Lt(Succ(i), t)) (b : Lt(t, Succ(j))) : Lt(p, Nth(Word, n, SwapS(Word, n, s0, Succ(i), j, hsi, hjn), t, ht)) := (
    let d = LeDec(Succ(t), j);
    match d {
      Yes(htj) => rewrite ← NthSwapOther(n, s0, Succ(i), j, t, hsi, hjn, ht, λ(e : Eq Word (Succ(i)) t) : False => LtNe(Succ(i), t, a, e),
          λ(e : Eq Word j t) : False => LtNe(t, j, htj, rewrite e in refl)) in
        j2(t, ht, LtTrans(i, Succ(i), t, LeRefl(Succ(i)), a), htj),
      No(ntj) => (
        let e = LeAntisym(t, j, b, ntj);
        rewrite ← e in rewrite ← NthSwapB(n, s0, Succ(i), j, hsi, hjn) in j2(Succ(i), hsi, LeRefl(Succ(i)), rewrite e in a)
      ),
    }
  )

  -- Without a swap (the element at `j` was greater than `p`): cells `i + 1 … j` are greater.
  def StepJ2F (n : Word) (s0 : Slice(Word, n)) (p : Word) (i : Word) (j : Word) (hjn : Lt(j, n))
      (j2 : Π(t : Word) (ht : Lt(t, n)) (a : Lt(i, t)) (b : Lt(t, j)). Lt(p, Nth(Word, n, s0, t, ht)))
      (hx : Lt(p, Nth(Word, n, s0, j, hjn))) (t : Word) (ht : Lt(t, n)) (a : Lt(i, t)) (b : Lt(t, Succ(j))) :
      Lt(p, Nth(Word, n, s0, t, ht)) := (
    let d = LeDec(Succ(t), j);
    match d {
      Yes(htj) => j2(t, ht, a, htj),
      No(ntj) => rewrite ← LeAntisym(t, j, b, ntj) in hx,
    }
  )

  -- ## What the scan leaves, fact by fact
  -- [checker] Stated pointwise, one lemma per fact, rather than as one proposition with
  -- `Π`s inside: a `Π`-type's captured values are not re-normalised after a case split, so a
  -- goal holding the scan's result inside a `Π` stays stale.
  -- The scan's result and final view, run on a copy of `v`.
  def ScanK (n : Word) (v : Slice(Word, n)) (p : Word) (i : Word) (j : Word) (rem : Word) (hij : Lt(i, j))
      (hr : Eq Word (WAdd(rem, j)) n) : Word := (
    let c = v;
    Scan(n, &c, p, i, j, rem, hij, hr)
  )

  def ScanV (n : Word) (v : Slice(Word, n)) (p : Word) (i : Word) (j : Word) (rem : Word) (hij : Lt(i, j))
      (hr : Eq Word (WAdd(rem, j)) n) : Slice(Word, n) := (
    let c = v;
    Scan(n, &c, p, i, j, rem, hij, hr);
    c
  )

  def ScanLt (n : Word) (v : Slice(Word, n)) (p : Word) (i : Word) (j : Word) (rem : Word) (hij : Lt(i, j))
      (hr : Eq Word (WAdd(rem, j)) n) : Lt(ScanK(n, v, p, i, j, rem, hij, hr), n) by rem := (
    match rem {
      Zero => rewrite hr in hij,
      Succ(r) => (
        let hjn : Lt(j, n) = (rewrite hr in LeAddL(r, j));
        let hr2 : Eq Word (WAdd(r, Succ(j))) n = (rewrite AddRS(r, j) in hr);
        -- element `j`, read through its borrow, and the view `w` the read leaves
        let x = (let c = clone(v); *GetMut(Word, n, &c, j, hjn));
        let w = (let c = clone(v); let y = *GetMut(Word, n, &c, j, hjn); c);
        let b = Leb(x, p);
        match b {
          true => (
            let hsi : Lt(Succ(i), n) = LeTrans(Succ(Succ(i)), Succ(j), n, hij, hjn);
            ScanLt(n, (let c1 = clone(w); Swap(Word, n, &c1, Succ(i), j, hsi, hjn); c1), p, Succ(i), Succ(j), r, hij, hr2)
          ),
          false => ScanLt(n, w, p, i, Succ(j), r, LeStep(Succ(i), j, hij), hr2),
        }
      ),
    }
  )

  def ScanPivot (n : Word) (v : Slice(Word, n)) (p : Word) (i : Word) (j : Word) (rem : Word) (hij : Lt(i, j))
      (hr : Eq Word (WAdd(rem, j)) n) (j0 : Π(h0 : Lt(Zero, n)). Eq Word (Nth(Word, n, v, Zero, h0)) p)
      (hk : Lt(ScanK(n, v, p, i, j, rem, hij, hr), n)) :
      Eq Word (Nth(Word, n, ScanV(n, clone(v), p, i, j, rem, hij, hr), ScanK(n, v, p, i, j, rem, hij, hr), hk)) p by rem := (
    match rem {
      Zero => (
        let hin : Lt(i, n) = (rewrite hr in hij);
        let h0 : Lt(Zero, n) = LeTrans(Succ(Zero), Succ(i), n, refl, hin);
        rewrite ← SwapIsSwapSV(Word, n, v, Zero, i, h0, hin) in rewrite ← NthSwapB(n, v, Zero, i, h0, hk) in j0(h0)
      ),
      Succ(r) => (
        let hjn : Lt(j, n) = (rewrite hr in LeAddL(r, j));
        let hr2 : Eq Word (WAdd(r, Succ(j))) n = (rewrite AddRS(r, j) in hr);
        -- element `j`, read through its borrow, and the view `w` the read leaves
        let x = (let c = clone(v); *GetMut(Word, n, &c, j, hjn));
        let w = (let c = clone(v); let y = *GetMut(Word, n, &c, j, hjn); c);
        let ⟨hxv, hw0⟩ = GetMutReadV(Word, n, v, j, hjn);
        let hw : Eq(Slice(Word, n), w, v) = hw0;
        let j0w : Π(h0 : Lt(Zero, n)). Eq(Word, Nth(Word, n, w, Zero, h0), p) = (
          λ(h0 : Lt(Zero, n)) : Eq(Word, Nth(Word, n, w, Zero, h0), p) => rewrite ← hw in j0(h0));
        let b = Leb(x, p);
        match b {
          true => (
            let hsi : Lt(Succ(i), n) = LeTrans(Succ(Succ(i)), Succ(j), n, hij, hjn);
            let c2 = (let c1 = clone(w); Swap(Word, n, &c1, Succ(i), j, hsi, hjn); c1);
            ScanPivot(n, c2, p, Succ(i), Succ(j), r, hij, hr2,
              λ(h0 : Lt(Zero, n)) : Eq Word (Nth(Word, n, c2, Zero, h0)) p =>
                rewrite ← SwapIsSwapSV(Word, n, w, Succ(i), j, hsi, hjn) in StepJ0(n, w, p, i, j, hsi, hjn, hij, j0w, h0), hk)
          ),
          false => ScanPivot(n, w, p, i, Succ(j), r, LeStep(Succ(i), j, hij), hr2, j0w, hk),
        }
      ),
    }
  )

  def ScanLeft (n : Word) (v : Slice(Word, n)) (p : Word) (i : Word) (j : Word) (rem : Word) (hij : Lt(i, j))
      (hr : Eq Word (WAdd(rem, j)) n)
      (j1 : Π(t : Word) (ht : Lt(t, n)) (a : Lt(Zero, t)) (b : Le(t, i)). Le(Nth(Word, n, v, t, ht), p))
      (t : Word) (ht : Lt(t, ScanK(n, v, p, i, j, rem, hij, hr))) (htn : Lt(t, n)) :
      Le(Nth(Word, n, ScanV(n, v, p, i, j, rem, hij, hr), t, htn), p) by rem := (
    match rem {
      Zero => (
        let hin : Lt(i, n) = (rewrite hr in hij);
        let h0 : Lt(Zero, n) = LeTrans(Succ(Zero), Succ(i), n, refl, hin);
        rewrite ← SwapIsSwapSV(Word, n, v, Zero, i, h0, hin) in EndLeft(n, v, p, i, hin, h0, j1, t, ht, htn)
      ),
      Succ(r) => (
        let hjn : Lt(j, n) = (rewrite hr in LeAddL(r, j));
        let hr2 : Eq Word (WAdd(r, Succ(j))) n = (rewrite AddRS(r, j) in hr);
        -- element `j`, read through its borrow, and the view `w` the read leaves
        let x = (let c = clone(v); *GetMut(Word, n, &c, j, hjn));
        let w = (let c = clone(v); let y = *GetMut(Word, n, &c, j, hjn); c);
        let ⟨hxv, hw0⟩ = GetMutReadV(Word, n, v, j, hjn);
        let hw : Eq(Slice(Word, n), w, v) = hw0;
        let j1w : Π(t2 : Word) (ht2 : Lt(t2, n)) (a : Lt(Zero, t2)) (b2 : Le(t2, i)). Le(Nth(Word, n, w, t2, ht2), p) = (
          λ(t2 : Word) (ht2 : Lt(t2, n)) (a : Lt(Zero, t2)) (b2 : Le(t2, i)) : Le(Nth(Word, n, w, t2, ht2), p) =>
          rewrite ← hw in j1(t2, ht2, a, b2));
        let b = Leb(x, p);
        match b {
          true => (
            let hsi : Lt(Succ(i), n) = LeTrans(Succ(Succ(i)), Succ(j), n, hij, hjn);
            let hx : Le(Nth(Word, n, w, j, hjn), p) = (rewrite ← hw in rewrite hxv in LebLe(x, p, refl));
            let c2 = (let c1 = clone(w); Swap(Word, n, &c1, Succ(i), j, hsi, hjn); c1);
            ScanLeft(n, c2, p, Succ(i), Succ(j), r, hij, hr2,
              λ(t2 : Word) (ht2 : Lt(t2, n)) (a : Lt(Zero, t2)) (b2 : Le(t2, Succ(i))) : Le(Nth(Word, n, c2, t2, ht2), p) =>
                rewrite ← SwapIsSwapSV(Word, n, w, Succ(i), j, hsi, hjn) in StepJ1(n, w, p, i, j, hsi, hjn, hij, j1w, hx, t2, ht2, a, b2),
              t, ht, htn)
          ),
          false => ScanLeft(n, w, p, i, Succ(j), r, LeStep(Succ(i), j, hij), hr2, j1w, t, ht, htn),
        }
      ),
    }
  )

  def ScanRight (n : Word) (v : Slice(Word, n)) (p : Word) (i : Word) (j : Word) (rem : Word) (hij : Lt(i, j))
      (hr : Eq Word (WAdd(rem, j)) n)
      (j2 : Π(t : Word) (ht : Lt(t, n)) (a : Lt(i, t)) (b : Lt(t, j)). Lt(p, Nth(Word, n, v, t, ht)))
      (t : Word) (ht : Lt(t, n)) (hkt : Lt(ScanK(n, v, p, i, j, rem, hij, hr), t)) :
      Lt(p, Nth(Word, n, ScanV(n, v, p, i, j, rem, hij, hr), t, ht)) by rem := (
    match rem {
      Zero => (
        let hin : Lt(i, n) = (rewrite hr in hij);
        let h0 : Lt(Zero, n) = LeTrans(Succ(Zero), Succ(i), n, refl, hin);
        rewrite ← SwapIsSwapSV(Word, n, v, Zero, i, h0, hin) in EndRight(n, v, p, i, j, hin, h0, hr, j2, t, ht, hkt)
      ),
      Succ(r) => (
        let hjn : Lt(j, n) = (rewrite hr in LeAddL(r, j));
        let hr2 : Eq Word (WAdd(r, Succ(j))) n = (rewrite AddRS(r, j) in hr);
        -- element `j`, read through its borrow, and the view `w` the read leaves
        let x = (let c = clone(v); *GetMut(Word, n, &c, j, hjn));
        let w = (let c = clone(v); let y = *GetMut(Word, n, &c, j, hjn); c);
        let ⟨hxv, hw0⟩ = GetMutReadV(Word, n, v, j, hjn);
        let hw : Eq(Slice(Word, n), w, v) = hw0;
        let j2w : Π(t2 : Word) (ht2 : Lt(t2, n)) (a : Lt(i, t2)) (b2 : Lt(t2, j)). Lt(p, Nth(Word, n, w, t2, ht2)) = (
          λ(t2 : Word) (ht2 : Lt(t2, n)) (a : Lt(i, t2)) (b2 : Lt(t2, j)) : Lt(p, Nth(Word, n, w, t2, ht2)) =>
          rewrite ← hw in j2(t2, ht2, a, b2));
        let b = Leb(x, p);
        match b {
          true => (
            let hsi : Lt(Succ(i), n) = LeTrans(Succ(Succ(i)), Succ(j), n, hij, hjn);
            let c2 = (let c1 = clone(w); Swap(Word, n, &c1, Succ(i), j, hsi, hjn); c1);
            ScanRight(n, c2, p, Succ(i), Succ(j), r, hij, hr2,
              λ(t2 : Word) (ht2 : Lt(t2, n)) (a : Lt(Succ(i), t2)) (b2 : Lt(t2, Succ(j))) : Lt(p, Nth(Word, n, c2, t2, ht2)) =>
                rewrite ← SwapIsSwapSV(Word, n, w, Succ(i), j, hsi, hjn) in StepJ2(n, w, p, i, j, hsi, hjn, hij, j2w, t2, ht2, a, b2),
              t, ht, hkt)
          ),
          false => (
            let hx : Lt(p, Nth(Word, n, w, j, hjn)) = (rewrite ← hw in rewrite hxv in LebGt(x, p, refl));
            ScanRight(n, w, p, i, Succ(j), r, LeStep(Succ(i), j, hij), hr2,
              λ(t2 : Word) (ht2 : Lt(t2, n)) (a : Lt(i, t2)) (b2 : Lt(t2, Succ(j))) : Lt(p, Nth(Word, n, w, t2, ht2)) =>
                StepJ2F(n, w, p, i, j, hjn, j2w, hx, t2, ht2, a, b2),
              t, ht, hkt)
          ),
        }
      ),
    }
  )

  -- ## The partition meets its contract
  -- At the start (`i = 0`, `j = 1`) the invariant holds trivially: the pivot is the first
  -- element, and the two ranges are empty.
  def Start0 (m : Word) (v : Slice(Word, Succ(m))) (h0 : Lt(Zero, Succ(m))) :
      Eq Word (Nth(Word, Succ(m), v, Zero, h0)) (Nth(Word, Succ(m), v, Zero, refl)) := refl

  def Start1 (m : Word) (v : Slice(Word, Succ(m))) (t : Word) (ht : Lt(t, Succ(m))) (a : Lt(Zero, t)) (b : Le(t, Zero)) :
      Le(Nth(Word, Succ(m), v, t, ht), Nth(Word, Succ(m), v, Zero, refl)) := (
    let no = LeSuccFalse(Zero, LeTrans(Succ(Zero), t, Zero, a, b));
    match no {}
  )

  def Start2 (m : Word) (v : Slice(Word, Succ(m))) (t : Word) (ht : Lt(t, Succ(m))) (a : Lt(Zero, t)) (b : Lt(t, Succ(Zero))) :
      Lt(Nth(Word, Succ(m), v, Zero, refl), Nth(Word, Succ(m), v, t, ht)) := (
    let no = LeSuccFalse(Zero, LeTrans(Succ(Zero), t, Zero, a, b));
    match no {}
  )

  def PartLeProof (m : Word) (v : Slice(Word, Succ(m))) : PartLe(m, v) := (
    -- the pivot is read at 0: once the first cell is split off, the read computes
    match v {
      MkSlice(c0) => match c0 {
        MkC(y0, t0) => (
          ScanLt(Succ(m), v, Nth(Word, Succ(m), v, Zero, refl), Zero, Succ(Zero), m, refl, AddOneR(m))
        ),
      },
    }
  )

  def PartLeftProof (m : Word) (v : Slice(Word, Succ(m))) (hk : PartLe(m, v)) : PartLeft(m, v, hk) := (
    -- the pivot is read at 0: once the first cell is split off, the read computes
    match v {
      MkSlice(c0) => match c0 {
        MkC(y0, t0) => (
          AllLeTakeOf(Succ(m), PartK(m, v), PartV(m, v), Nth(Word, Succ(m), v, Zero, refl), LeStep(PartK(m, v), m, hk),
            λ(t : Word) (ht : Lt(t, PartK(m, v))) (htn : Lt(t, Succ(m))) : Le(Nth(Word, Succ(m), PartV(m, v), t, htn), Nth(Word, Succ(m), v, Zero, refl)) =>
              ScanLeft(Succ(m), v, Nth(Word, Succ(m), v, Zero, refl), Zero, Succ(Zero), m, refl, AddOneR(m),
                λ(t2 : Word) (ht2 : Lt(t2, Succ(m))) (a : Lt(Zero, t2)) (b : Le(t2, Zero)) : Le(Nth(Word, Succ(m), v, t2, ht2), Nth(Word, Succ(m), v, Zero, refl)) =>
                  Start1(m, v, t2, ht2, a, b),
                t, ht, htn))
        ),
      },
    }
  )

  def PartPivotProof (m : Word) (v : Slice(Word, Succ(m))) (hk : PartLe(m, v)) : PartPivot(m, v, hk) := (
    -- the pivot is read at 0: once the first cell is split off, the read computes
    match v {
      MkSlice(c0) => match c0 {
        MkC(y0, t0) => (
          rewrite TakeOneDrop(Succ(m), PartK(m, v), PartV(m, v), hk) in
          rewrite ← ScanPivot(Succ(m), v, Nth(Word, Succ(m), v, Zero, refl), Zero, Succ(Zero), m, refl, AddOneR(m),
              λ(h0 : Lt(Zero, Succ(m))) : Eq Word (Nth(Word, Succ(m), v, Zero, h0)) (Nth(Word, Succ(m), v, Zero, refl)) => Start0(m, v, h0), hk) in
            refl
        ),
      },
    }
  )

  def PartRightProof (m : Word) (v : Slice(Word, Succ(m))) (hk : PartLe(m, v)) : PartRight(m, v, hk) := (
    -- the pivot is read at 0: once the first cell is split off, the read computes
    match v {
      MkSlice(c0) => match c0 {
        MkC(y0, t0) => (
          AllGeDropOf(Succ(m), PartK(m, v), PartV(m, v), Nth(Word, Succ(m), v, Zero, refl),
            λ(t : Word) (ht : Lt(t, Succ(m))) (hkt : Lt(PartK(m, v), t)) : Le(Nth(Word, Succ(m), v, Zero, refl), Nth(Word, Succ(m), PartV(m, v), t, ht)) =>
              LeOfLt(Nth(Word, Succ(m), v, Zero, refl), Nth(Word, Succ(m), PartV(m, v), t, ht),
                ScanRight(Succ(m), v, Nth(Word, Succ(m), v, Zero, refl), Zero, Succ(Zero), m, refl, AddOneR(m),
                  λ(t2 : Word) (ht2 : Lt(t2, Succ(m))) (a : Lt(Zero, t2)) (b : Lt(t2, Succ(Zero))) : Lt(Nth(Word, Succ(m), v, Zero, refl), Nth(Word, Succ(m), v, t2, ht2)) =>
                    Start2(m, v, t2, ht2, a, b),
                  t, ht, hkt)))
        ),
      },
    }
  )

  -- Quicksort sorts, for fuel at least the length, with no hypotheses.
  def QSSortedFull (fuel : Word) (n : Word) (s : &Slice(Word, n)) (hf : Le(n, fuel)) :
      (let c = *s; QS(fuel, n, &c); Sorted(n, c)) := (
    QSSorted(PartLeProof, PartLeftProof, PartPivotProof, PartRightProof, fuel, n, s, hf)
  )

  -- Quicksort is correct: its result is sorted and a permutation of its input.
  def QSCorrect (n : Word) (s : &Slice(Word, n)) (q : Word) :
      (let c = *s; QS(n, n, &c); Sorted(n, c)) ∧
        (let old = clone(*s); Eq Word (Count(q, n, (QS(n, n, &*s); *s))) (Count(q, n, old))) := (
    ⟨QSSortedFull(n, n, s, LeRefl(n)), QSPerm(n, n, s, q)⟩
  )
}

-- the exact number of declarations (a truncated file changes it)
#guard Quicksort.decls.length == 73
