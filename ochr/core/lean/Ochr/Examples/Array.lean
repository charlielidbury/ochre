import Ochr.Examples.List

/-! # Array: a library over a type-level model

Arrays are not built into Ochr. An array of `n` elements is modelled by `Cells(E, n)`, a type
computed by recursion on the length `n`: `CellsEnd` at zero, and a `Cell` holding an element
and the rest at `Succ(m)`. So the length lives only in the type, and a value of `Cells(E, n)`
has exactly `n` elements. A view `Slice(E, n)` wraps the cells, and an owned array
`Array(E, n)` wraps a view. Proofs reason about this model directly (`Nth`, `SetS`, `TakeS`,
`DropS`, `JoinS`, `Count`, ...). Compiled code uses a flat buffer instead, through six native
functions whose models are the Ochr bodies given here (`implemented by`): `AsSlice`, `GetMut`,
`WithSplit`, `ArrFromFn`, `ArrOfList`. An array never changes its length; an array literal
`[x, y]`, written at its type `Array(E, n)`, has `ArrOfList` as its model (a compiler lowers it
directly, building no list). Elements are read and written through `GetMut`:
`*GetMut(Word, n, s, i, h)` reads a `Word`, `clone(*GetMut(E, n, s, i, h))` copies any element,
and `*GetMut(E, n, s, i, h) := x` writes one. `Swap` is built from `WithSplit` and two
`GetMut`s and copies nothing.

The rules: nothing recurses over an array, only over an index; runtime code never owns part
of an array; a borrow of part of an array is scoped by a continuation (`WithSplit`).

The representation is enforced. `SliceOf` is `unsized abstract`, and `Cell`, `CellsEnd` and
`ArrayOf` are `abstract`. Outside model code (the `implemented by` bodies, and the model
functions, which take or return a view by value and so never run at runtime), runtime code
only borrows a view: it never reads, moves, assigns or matches one, and never builds or takes
apart the representation. Statements and proofs (erased code) are unrestricted.

Reads move (D53); indices, lengths and `Word` elements are copies. At an unknown index, what
is done through an element borrow (or by `Swap`) is a sealed program, not the model's `Nth` or
`SetS`: proofs name it with `GetMutRead`, `GetMutSet` and `SwapIsSwapS` (and their forms
about a view given by value, `GetMutReadV`, `GetMutSetV`, `SwapIsSwapSV`).

This file holds the library blocks `Arrays` (the model and the natives) and `ArrayLemmas`
(the lemma library). Indices use the library `Words`; the chapter that explains the design,
with its benchmarks, is `ArrayBench.lean`, and the quicksort case study `Quicksort.lean`. -/

open Ochr.Test

/-! ## The model

`Cells(E, n)` is `CellsEnd` at zero and a `Cell` at `Succ(m)`. A view `Slice(E, n)` wraps the
cells; a cell holds an element and the rest of the view, so the rest is itself a view. An owned array `Array(E, n)` wraps a view. None of them stores a
length. The functions on the model take their arguments by value and recurse over an index;
proofs use them, and they are the models of the native functions below. -/

ochr Arrays uses Words, Lists, Logic {
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

  -- The view of a list of `n` elements (`Lists`' `LenL` is its length), the model of
  -- `ArrOfList`.
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
      (hr : Eq(Word, WAdd(rem, i), n)) : Unit by rem := (
    match rem {
      Zero => (),
      Succ(r) => (
        let hi : Lt(i, n) = (rewrite hr in LeAddL(r, i));
        let hr2 : Eq(Word, WAdd(r, Succ(i)), n) = (rewrite AddRS(r, i) in hr);
        *GetMut(E, n, &*s, i, hi) := clone(x);
        FillFrom(E, n, s, x, Succ(i), r, hr2)
      ),
    }
  )

  def Fill (E : Type) (n : Word) (s : &Slice(E, n)) (x : E) : Unit := FillFrom(E, n, s, x, Zero, n, AddZeroR(n))
}

/-! ## The lemma library

The facts a user of the library relies on, each by recursion on an index. Three of them are
what a primitive array would give by definition (D57): putting the two halves of a split back
together gives the original view (`JoinTakeDrop`), the halves of a join are what was joined
(`TakeJoin`, `DropJoin`), and reading after a write (`NthSetSame`, `NthSetOther`). Counting
(`Count`) is how permutations are stated. -/

ochr ArrayLemmas uses Arrays {
  def NthSetSame (E : Type) (n : Word) (s : Slice(E, n)) (i : Word) (x : E) (h : Lt(i, n)) :
      Eq(E, Nth(E, n, SetS(E, n, s, i, x), i, h), x) by i := (
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
      (hj : Lt(j, n)) (ne : Π(e : Eq(Word, i, j)). False) :
      Eq(E, Nth(E, n, SetS(E, n, s, i, x), j, hj), Nth(E, n, s, j, hj)) by i := (
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
      Eq(Slice(E, n), JoinS(E, n, k, TakeS(E, n, k, clone(s), h), DropS(E, n, k, s)), s) by k := (
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
      Eq(Slice(E, k), TakeS(E, n, k, JoinS(E, n, k, l, r), h), l) by k := (
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
      Eq(Slice(E, Sub(n, k)), DropS(E, n, k, JoinS(E, n, k, l, r)), r) by k := (
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
            let e = EqB(q, x);
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
    let e = EqB(q, x);
    match e {
      true => Succ(Zero),
      false => Zero,
    }
  )

  def CountJoin (q : Word) (n : Word) (k : Word) (l : Slice(Word, k)) (r : Slice(Word, Sub(n, k))) (h : Le(k, n)) :
      Eq(Word, Count(q, n, JoinS(Word, n, k, l, r)), WAdd(Count(q, k, l), Count(q, Sub(n, k), r))) by k := (
    match k {
      Zero => refl,
      Succ(k') => match n {
        Zero => match h {},
        Succ(m) => match l {
          MkSlice(c) => match c {
            MkC(x, t) => (
              let e = EqB(q, x);
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
      Eq(Word, WAdd(Ind(q, Nth(Word, n, clone(s), i, h)), Count(q, n, SetS(Word, n, s, i, x))), WAdd(Ind(q, x), Count(q, n, s))) by i := (
    match n {
      Zero => match h {},
      Succ(m) => match s {
        MkSlice(c) => match c {
          MkC(y, t) => match i {
            Zero => (
              let ex = EqB(q, x);
              let ey = EqB(q, y);
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
              let ey = EqB(q, y);
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
      Eq(Word, Count(q, Succ(m), MkSlice(MkC(Nth(Word, m, clone(t), i, h), SetS(Word, m, t, i, y)))), Count(q, Succ(m), MkSlice(MkC(y, t)))) := (
    let hs = CountSet(q, m, t, i, y, h);
    let eb = EqB(q, Nth(Word, m, t, i, h));
    let ey = EqB(q, y);
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
      Eq(Word, Count(q, n, SwapS(Word, n, s, i, j, hi, hj)), Count(q, n, s)) by i := (
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
                let ey = EqB(q, y);
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
