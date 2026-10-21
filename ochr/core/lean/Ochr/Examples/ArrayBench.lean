import Ochr.Examples.Array

/-! # ArrayBench: the arrays chapter and its benchmarks

Arrays are not built into Ochr (D57). An array of `n` elements is modelled by `Cells(E, n)`,
a type computed by recursion on `n`: `CellsEnd` at zero, and a cell holding an element and
the rest at `Succ(m)`. So the length lives only in the type, and a value of `Cells(E, n)` has exactly
`n` elements. Proofs reason about this model directly; compiled code will use a flat buffer
instead, through a small set of native functions (marked `[native]` below) whose models are
the Ochr bodies given here.

The rules (D57): nothing recurses over an array, only over an index; runtime code never owns
part of an array; a borrow of part of an array is scoped by a continuation (`WithSplit`).
Indices are `Word`s: the order on them (`Lt(i, n)` is the bounds proof that indexing takes),
the comparisons, the arithmetic and the facts about them are the library `Words`
(`Word.lean`).

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
* `[K4]` (resolved) A field type may call a type function, `Array(E, n)` with `n` an earlier
  field (`DependentFields.lean`): the hash map (`HashMap.lean`) stores its size next to its
  array of buckets.
* `[K6]` Quicksort recurses on fuel; with recursion on a measure it recurses on the length.
* `[checker]` The scan's invariant is stated pointwise, one lemma per fact, where one
  proposition with `Π`s inside went stale after a case split (see there).

The library itself is `Array.lean` (`Arrays`, `ArrayLemmas`); this file explains it and
holds its benchmarks, and `Quicksort.lean` the quicksort case study.

Defined in D57 and notes/arrays-library.md. -/

open Ochr.Test

/-! ## The benchmarks (D57)

B1: borrow the first `k` elements, run anything on them, and the rest is unchanged.
B2: quicksort (`Quicksort.lean`). B3: a hash map over an array, inserting into a key's bucket
in place: the hash map case study (`HashMap.lean`). B4: a bounds proof from a runtime
comparison. Each is stated about the program itself. -/

ochr ArrayBench uses ArrayLemmas {
  -- ## B1
  -- By definition, for any `g`: after the split, the view is `g`'s result on the old first
  -- `k` elements, joined to the old rest.
  def B1Join (E : Type) (n : Word) (k : Word) (g : Π(x : &Slice(E, k)). Unit) (s : &Slice(E, n)) (h : Le(k, n)) :
      Id(Unit, WithSplit(E, Unit, n, k, s, h, λ(l : &Slice(E, k)) (r : &Slice(E, Sub(n, k))) : Unit => g(l)), *s := JoinS(E, n, k, (let c = TakeS(E, n, k, clone(*s), h); g(&c); c), DropS(E, n, k, clone(*s)))) := refl

  -- Stated about the rest alone, it takes one lemma, for any `g`: `g`'s result has length `k`
  -- by its type, so the rest starts where it did.
  def B1 (E : Type) (n : Word) (k : Word) (g : Π(x : &Slice(E, k)). Unit) (s : &Slice(E, n)) (h : Le(k, n)) :
      Eq(Slice(E, Sub(n, k)), let c = *s; WithSplit(E, Unit, n, k, &c, h, λ(l : &Slice(E, k)) (r : &Slice(E, Sub(n, k))) : Unit => g(l)); DropS(E, n, k, c), DropS(E, n, k, *s)) := (
    DropJoin(E, n, k, (let c = TakeS(E, n, k, *s, h); g(&c); c), DropS(E, n, k, *s), h)
  )

  -- A primitive array would give that by definition; here it is not.
  reject def B1Refl (E : Type) (n : Word) (k : Word) (g : Π(x : &Slice(E, k)). Unit) (s : &Slice(E, n)) (h : Le(k, n)) :
      Eq(Slice(E, Sub(n, k)), let c = *s; WithSplit(E, Unit, n, k, &c, h, λ(l : &Slice(E, k)) (r : &Slice(E, Sub(n, k))) : Unit => g(l)); DropS(E, n, k, c), DropS(E, n, k, *s)) := refl

  -- Nor is splitting and doing nothing the identity by definition; it is `JoinTakeDrop`.
  reject def SplitNoopRefl (E : Type) (n : Word) (k : Word) (s : &Slice(E, n)) (h : Le(k, n)) :
      Id(Unit, WithSplit(E, Unit, n, k, s, h, λ(l : &Slice(E, k)) (r : &Slice(E, Sub(n, k))) : Unit => ()), ()) := refl

  def SplitNoop (E : Type) (n : Word) (k : Word) (s : &Slice(E, n)) (h : Le(k, n)) :
      Eq(Slice(E, n), let c = *s; WithSplit(E, Unit, n, k, &c, h, λ(l : &Slice(E, k)) (r : &Slice(E, Sub(n, k))) : Unit => ()); c, *s) := (
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
  reject def NotAPlace (a : Word) (b : Word) : Unit := *LeB(a, b) := true

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

  def GetOrIn : Id(Word, let a = Replicate(Word, W(3), W(7)); GetOr(Word, W(3), AsSlice(Word, W(3), &a), Succ(Zero), Zero), W(7)) := refl
  def GetOrOut : Id(Word, let a = Replicate(Word, W(3), W(7)); GetOr(Word, W(3), AsSlice(Word, W(3), &a), W(5), Zero), Zero) := refl

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

#guard (run "ArrayBench" ArrayBench).rejectedWith [
  ("ReadMove", "[D53] reading *GetMut(…) moves its content out through the borrow GetMut(…) returns, which then ends with it moved out (⊥): copy it with clone(*GetMut(…))"),
  ("NotAPlace", "*LeB(…): LeB(…) does not return a borrow (type Bool), so *LeB(…) is not a place"),
  ("ReadPastEnd", "argument 5 (h) has type ⊤, expected False"),
  ("LitWrongLength", "argument 4 (h) has type ⊤, expected False"),
  ("TwoGetMut", "[Read] a was moved out or its borrow ended")]
