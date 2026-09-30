-- FIXED-BEGIN header
import Ochr.Examples.«16Arrays»

/-! # Verified in-place quicksort, two programs (condition `ochr-2p`)

Read `ASSIGNMENT.md` first. Replace every hole `?` with a definition or a proof, and add any
helper definitions and lemmas you need to the blocks `QuicksortModel` and
`QuicksortSolution`, between their FIXED regions. Everything inside a FIXED region must stay exactly as it is.

Check your work with `lake exe check` (the checker's verdict on every declaration) and
`./grade.sh` (the grade). -/

/-! ## The definitions (FIXED, SPEC §4)

An array of `n` words is a view `Slice(Word, n)` of the arrays library (`ArrayLemmas`,
`checker/Ochr/Examples/16Arrays.lean`); element `i` is `Nth(Word, n, s, i, h)`, where the
proof `h : Lt(i, n)` says the index is in bounds. -/

ochr QuicksortSpec uses ArrayLemmas {
  -- sorted(a) :⟺ ∀ i j. i < j < |a| ⟹ a[i] ≤ a[j]. Reading a[i] needs its bound `hi`, which
  -- `hij` and `hj` imply.
  def Sorted (n : Word) (s : Slice(Word, n)) : Prop := (
    Π(i : Word) (j : Word) (hij : Lt(i, j)) (hi : Lt(i, n)) (hj : Lt(j, n)). Le(Nth(Word, n, s, i, hi), Nth(Word, n, s, j, hj))
  )

  -- count(x, a) is the library's `Count(x, n, a)`: how many elements of `a` equal `x`, by
  -- recursion over the elements. perm(a, b) :⟺ ∀ x. count(x, a) = count(x, b).
  def Perm (n : Word) (a : Slice(Word, n)) (b : Slice(Word, n)) : Prop := (
    Π(x : Word). Eq Word (Count(x, n, a)) (Count(x, n, b))
  )
}

/-! ## From the model to the program (FIXED, provided)

Q1 and Q2 about any in-place sort `qs` follow from two facts: `qs` agrees with a pure model
(running `qs(n, s)` has the effect of `*s := model(n, *s)`), and the model's result is sorted
and a permutation of its input. These two lemmas are that argument, checked; nothing here is
for you to do. At the end of `QuicksortSolution` they are applied to your `QuickSort`, your
model `SortModel`, and your proofs. -/

ochr QuicksortCompose uses QuicksortSpec {
  def SortedFromModel (qs : Π(n : Word) (s : &Slice(Word, n)). Unit)
      (model : Π(n : Word) (v : Slice(Word, n)). Slice(Word, n))
      (agree : Π(n : Word) (s : &Slice(Word, n)). Id Unit (qs(n, s)) (*s := model(n, *s)))
      (msorted : Π(n : Word) (v : Slice(Word, n)). Sorted(n, model(n, v)))
      (n : Word) (s : &Slice(Word, n)) : (let c = *s; qs(n, &c); Sorted(n, c)) := (
    rewrite ← agree(n, s) in msorted(n, *s)
  )

  def PermFromModel (qs : Π(n : Word) (s : &Slice(Word, n)). Unit)
      (model : Π(n : Word) (v : Slice(Word, n)). Slice(Word, n))
      (agree : Π(n : Word) (s : &Slice(Word, n)). Id Unit (qs(n, s)) (*s := model(n, *s)))
      (mperm : Π(n : Word) (v : Slice(Word, n)). Perm(n, model(n, v), v))
      (n : Word) (s : &Slice(Word, n)) : (let c = *s; qs(n, &c); Perm(n, c, *s)) := (
    rewrite ← agree(n, s) in mperm(n, *s)
  )
}

/-! ## Your model

A pure functional model of quicksort, and its properties. Pure means: no borrows (`&`) and no
assignment (`p := t`) anywhere in this block; the model computes on values. -/

ochr QuicksortModel uses QuicksortSpec {
-- FIXED-END header

  -- Your pure helper definitions and lemmas go here, and anywhere else between the FIXED
  -- regions of this block.

  -- FIXED-BEGIN model
  -- The model: `v` sorted, computed without borrows or assignment.
  def SortModel (n : Word) (v : Slice(Word, n)) : Slice(Word, n) :=
  -- FIXED-END model
    ?

  -- FIXED-BEGIN M1
  -- Q1 about the model: its result is sorted.
  def SortModelSorted (n : Word) (v : Slice(Word, n)) : Sorted(n, SortModel(n, v)) :=
  -- FIXED-END M1
    ?

  -- FIXED-BEGIN M2
  -- Q2 about the model: its result is a permutation of its input.
  def SortModelPerm (n : Word) (v : Slice(Word, n)) : Perm(n, SortModel(n, v), v) :=
  -- FIXED-END M2
    ?
-- FIXED-BEGIN solution-header
}

/-! ## Your program

The in-place quicksort and the proof that it agrees with the model. Q1 and Q2 about
`QuickSort` then follow, at the end of this block. -/

ochr QuicksortSolution uses QuicksortModel, QuicksortCompose {
-- FIXED-END solution-header

  -- Your helper definitions and lemmas go here, and anywhere else between the FIXED regions
  -- of this block. Say at your partition function whether it is Lomuto's or Hoare's.

  -- FIXED-BEGIN quicksort
  -- quicksort(a : &mut Array(𝕎)): sort the `n` words of `*s` in place.
  def QuickSort (n : Word) (s : &Slice(Word, n)) : Unit :=
  -- FIXED-END quicksort
    ?

  -- FIXED-BEGIN agree
  -- The agreement: running `QuickSort(n, s)` has the same effect as `*s := SortModel(n, *s)`.
  def QuickSortAgrees (n : Word) (s : &Slice(Word, n)) : Id Unit (QuickSort(n, s)) (*s := SortModel(n, *s)) :=
  -- FIXED-END agree
    ?

  -- FIXED-BEGIN Q1
  -- Q1: sorted(a₁), where a₁ is the contents after `QuickSort` (provided: from the model).
  def QuickSortSorted (n : Word) (s : &Slice(Word, n)) : (let c = *s; QuickSort(n, &c); Sorted(n, c)) :=
    SortedFromModel(QuickSort, SortModel, QuickSortAgrees, SortModelSorted, n, s)
  -- FIXED-END Q1

  -- FIXED-BEGIN Q2
  -- Q2: perm(a₁, a₀), where a₁ is the contents after `QuickSort` and a₀ = `*s` those before
  -- (provided: from the model).
  def QuickSortPerm (n : Word) (s : &Slice(Word, n)) : (let c = *s; QuickSort(n, &c); Perm(n, c, *s)) :=
    PermFromModel(QuickSort, SortModel, QuickSortAgrees, SortModelPerm, n, s)
  -- FIXED-END Q2
-- FIXED-BEGIN tests
}

/-! ## The tests (FIXED, SPEC §6)

Each test sorts an array in place and compares the whole array with the expected one; it is
accepted when the two are equal (`Id` compares the results of the two programs, and `refl`
proves it when they compute to the same value). The last one must be rejected: the expected
array is the unsorted input. -/

ochr QuicksortTests uses QuicksortSolution {
  -- BEGIN GENERATED TESTS
  -- empty: [] ↦ []
  def Test_empty : Id (Array(Word, W(0))) (let a = ArrEmpty(Word); QuickSort(W(0), AsSlice(Word, W(0), &a)); a) (ArrEmpty(Word)) := refl
  -- one: [42] ↦ [42]
  def Test_one : Id (Array(Word, W(1))) (let a = ArrPush(Word, W(0), ArrEmpty(Word), W(42)); QuickSort(W(1), AsSlice(Word, W(1), &a)); a) (ArrPush(Word, W(0), ArrEmpty(Word), W(42))) := refl
  -- two-sorted: [1, 2] ↦ [1, 2]
  def Test_two_sorted : Id (Array(Word, W(2))) (let a = ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(1)), W(2)); QuickSort(W(2), AsSlice(Word, W(2), &a)); a) (ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(1)), W(2))) := refl
  -- two-reversed: [2, 1] ↦ [1, 2]
  def Test_two_reversed : Id (Array(Word, W(2))) (let a = ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(2)), W(1)); QuickSort(W(2), AsSlice(Word, W(2), &a)); a) (ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(1)), W(2))) := refl
  -- duplicates: [3, 1, 3, 2, 1, 3, 0, 2] ↦ [0, 1, 1, 2, 2, 3, 3, 3]
  def Test_duplicates : Id (Array(Word, W(8))) (let a = ArrPush(Word, W(7), ArrPush(Word, W(6), ArrPush(Word, W(5), ArrPush(Word, W(4), ArrPush(Word, W(3), ArrPush(Word, W(2), ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(3)), W(1)), W(3)), W(2)), W(1)), W(3)), W(0)), W(2)); QuickSort(W(8), AsSlice(Word, W(8), &a)); a) (ArrPush(Word, W(7), ArrPush(Word, W(6), ArrPush(Word, W(5), ArrPush(Word, W(4), ArrPush(Word, W(3), ArrPush(Word, W(2), ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(0)), W(1)), W(1)), W(2)), W(2)), W(3)), W(3)), W(3))) := refl
  -- sorted: [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] ↦ [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
  def Test_sorted : Id (Array(Word, W(16))) (let a = ArrPush(Word, W(15), ArrPush(Word, W(14), ArrPush(Word, W(13), ArrPush(Word, W(12), ArrPush(Word, W(11), ArrPush(Word, W(10), ArrPush(Word, W(9), ArrPush(Word, W(8), ArrPush(Word, W(7), ArrPush(Word, W(6), ArrPush(Word, W(5), ArrPush(Word, W(4), ArrPush(Word, W(3), ArrPush(Word, W(2), ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(1)), W(2)), W(3)), W(4)), W(5)), W(6)), W(7)), W(8)), W(9)), W(10)), W(11)), W(12)), W(13)), W(14)), W(15)), W(16)); QuickSort(W(16), AsSlice(Word, W(16), &a)); a) (ArrPush(Word, W(15), ArrPush(Word, W(14), ArrPush(Word, W(13), ArrPush(Word, W(12), ArrPush(Word, W(11), ArrPush(Word, W(10), ArrPush(Word, W(9), ArrPush(Word, W(8), ArrPush(Word, W(7), ArrPush(Word, W(6), ArrPush(Word, W(5), ArrPush(Word, W(4), ArrPush(Word, W(3), ArrPush(Word, W(2), ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(1)), W(2)), W(3)), W(4)), W(5)), W(6)), W(7)), W(8)), W(9)), W(10)), W(11)), W(12)), W(13)), W(14)), W(15)), W(16))) := refl
  -- reverse-sorted: [16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1] ↦ [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
  def Test_reverse_sorted : Id (Array(Word, W(16))) (let a = ArrPush(Word, W(15), ArrPush(Word, W(14), ArrPush(Word, W(13), ArrPush(Word, W(12), ArrPush(Word, W(11), ArrPush(Word, W(10), ArrPush(Word, W(9), ArrPush(Word, W(8), ArrPush(Word, W(7), ArrPush(Word, W(6), ArrPush(Word, W(5), ArrPush(Word, W(4), ArrPush(Word, W(3), ArrPush(Word, W(2), ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(16)), W(15)), W(14)), W(13)), W(12)), W(11)), W(10)), W(9)), W(8)), W(7)), W(6)), W(5)), W(4)), W(3)), W(2)), W(1)); QuickSort(W(16), AsSlice(Word, W(16), &a)); a) (ArrPush(Word, W(15), ArrPush(Word, W(14), ArrPush(Word, W(13), ArrPush(Word, W(12), ArrPush(Word, W(11), ArrPush(Word, W(10), ArrPush(Word, W(9), ArrPush(Word, W(8), ArrPush(Word, W(7), ArrPush(Word, W(6), ArrPush(Word, W(5), ArrPush(Word, W(4), ArrPush(Word, W(3), ArrPush(Word, W(2), ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(1)), W(2)), W(3)), W(4)), W(5)), W(6)), W(7)), W(8)), W(9)), W(10)), W(11)), W(12)), W(13)), W(14)), W(15)), W(16))) := refl
  -- all-equal: [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] ↦ [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7]
  def Test_all_equal : Id (Array(Word, W(12))) (let a = ArrPush(Word, W(11), ArrPush(Word, W(10), ArrPush(Word, W(9), ArrPush(Word, W(8), ArrPush(Word, W(7), ArrPush(Word, W(6), ArrPush(Word, W(5), ArrPush(Word, W(4), ArrPush(Word, W(3), ArrPush(Word, W(2), ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(7)), W(7)), W(7)), W(7)), W(7)), W(7)), W(7)), W(7)), W(7)), W(7)), W(7)), W(7)); QuickSort(W(12), AsSlice(Word, W(12), &a)); a) (ArrPush(Word, W(11), ArrPush(Word, W(10), ArrPush(Word, W(9), ArrPush(Word, W(8), ArrPush(Word, W(7), ArrPush(Word, W(6), ArrPush(Word, W(5), ArrPush(Word, W(4), ArrPush(Word, W(3), ArrPush(Word, W(2), ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(7)), W(7)), W(7)), W(7)), W(7)), W(7)), W(7)), W(7)), W(7)), W(7)), W(7)), W(7))) := refl
  -- mixed: [5, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5, 0, 99] ↦ [0, 1, 1, 2, 3, 4, 5, 5, 5, 5, 6, 9, 99]
  def Test_mixed : Id (Array(Word, W(13))) (let a = ArrPush(Word, W(12), ArrPush(Word, W(11), ArrPush(Word, W(10), ArrPush(Word, W(9), ArrPush(Word, W(8), ArrPush(Word, W(7), ArrPush(Word, W(6), ArrPush(Word, W(5), ArrPush(Word, W(4), ArrPush(Word, W(3), ArrPush(Word, W(2), ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(5)), W(1)), W(4)), W(1)), W(5)), W(9)), W(2)), W(6)), W(5)), W(3)), W(5)), W(0)), W(99)); QuickSort(W(13), AsSlice(Word, W(13), &a)); a) (ArrPush(Word, W(12), ArrPush(Word, W(11), ArrPush(Word, W(10), ArrPush(Word, W(9), ArrPush(Word, W(8), ArrPush(Word, W(7), ArrPush(Word, W(6), ArrPush(Word, W(5), ArrPush(Word, W(4), ArrPush(Word, W(3), ArrPush(Word, W(2), ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(0)), W(1)), W(1)), W(2)), W(3)), W(4)), W(5)), W(5)), W(5)), W(5)), W(6)), W(9)), W(99))) := refl
  -- random-00: [70, 30, 15, 26, 27, 68, 94, 48, 69, 54, 87, 20, 36, 38, 0, 67, 65, 22, 80, 20, 62, 12, 97, 53] ↦ [0, 12, 15, 20, 20, 22, 26, 27, 30, 36, 38, 48, 53, 54, 62, 65, 67, 68, 69, 70, 80, 87, 94, 97]
  def Test_random_00 : Id (Array(Word, W(24))) (let a = ArrPush(Word, W(23), ArrPush(Word, W(22), ArrPush(Word, W(21), ArrPush(Word, W(20), ArrPush(Word, W(19), ArrPush(Word, W(18), ArrPush(Word, W(17), ArrPush(Word, W(16), ArrPush(Word, W(15), ArrPush(Word, W(14), ArrPush(Word, W(13), ArrPush(Word, W(12), ArrPush(Word, W(11), ArrPush(Word, W(10), ArrPush(Word, W(9), ArrPush(Word, W(8), ArrPush(Word, W(7), ArrPush(Word, W(6), ArrPush(Word, W(5), ArrPush(Word, W(4), ArrPush(Word, W(3), ArrPush(Word, W(2), ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(70)), W(30)), W(15)), W(26)), W(27)), W(68)), W(94)), W(48)), W(69)), W(54)), W(87)), W(20)), W(36)), W(38)), W(0)), W(67)), W(65)), W(22)), W(80)), W(20)), W(62)), W(12)), W(97)), W(53)); QuickSort(W(24), AsSlice(Word, W(24), &a)); a) (ArrPush(Word, W(23), ArrPush(Word, W(22), ArrPush(Word, W(21), ArrPush(Word, W(20), ArrPush(Word, W(19), ArrPush(Word, W(18), ArrPush(Word, W(17), ArrPush(Word, W(16), ArrPush(Word, W(15), ArrPush(Word, W(14), ArrPush(Word, W(13), ArrPush(Word, W(12), ArrPush(Word, W(11), ArrPush(Word, W(10), ArrPush(Word, W(9), ArrPush(Word, W(8), ArrPush(Word, W(7), ArrPush(Word, W(6), ArrPush(Word, W(5), ArrPush(Word, W(4), ArrPush(Word, W(3), ArrPush(Word, W(2), ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(0)), W(12)), W(15)), W(20)), W(20)), W(22)), W(26)), W(27)), W(30)), W(36)), W(38)), W(48)), W(53)), W(54)), W(62)), W(65)), W(67)), W(68)), W(69)), W(70)), W(80)), W(87)), W(94)), W(97))) := refl
  -- random-01: [79, 68, 98, 29, 19, 78, 77, 1, 47, 79, 53, 91, 91, 83, 35, 41, 55, 25, 9, 96, 8, 76, 70] ↦ [1, 8, 9, 19, 25, 29, 35, 41, 47, 53, 55, 68, 70, 76, 77, 78, 79, 79, 83, 91, 91, 96, 98]
  def Test_random_01 : Id (Array(Word, W(23))) (let a = ArrPush(Word, W(22), ArrPush(Word, W(21), ArrPush(Word, W(20), ArrPush(Word, W(19), ArrPush(Word, W(18), ArrPush(Word, W(17), ArrPush(Word, W(16), ArrPush(Word, W(15), ArrPush(Word, W(14), ArrPush(Word, W(13), ArrPush(Word, W(12), ArrPush(Word, W(11), ArrPush(Word, W(10), ArrPush(Word, W(9), ArrPush(Word, W(8), ArrPush(Word, W(7), ArrPush(Word, W(6), ArrPush(Word, W(5), ArrPush(Word, W(4), ArrPush(Word, W(3), ArrPush(Word, W(2), ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(79)), W(68)), W(98)), W(29)), W(19)), W(78)), W(77)), W(1)), W(47)), W(79)), W(53)), W(91)), W(91)), W(83)), W(35)), W(41)), W(55)), W(25)), W(9)), W(96)), W(8)), W(76)), W(70)); QuickSort(W(23), AsSlice(Word, W(23), &a)); a) (ArrPush(Word, W(22), ArrPush(Word, W(21), ArrPush(Word, W(20), ArrPush(Word, W(19), ArrPush(Word, W(18), ArrPush(Word, W(17), ArrPush(Word, W(16), ArrPush(Word, W(15), ArrPush(Word, W(14), ArrPush(Word, W(13), ArrPush(Word, W(12), ArrPush(Word, W(11), ArrPush(Word, W(10), ArrPush(Word, W(9), ArrPush(Word, W(8), ArrPush(Word, W(7), ArrPush(Word, W(6), ArrPush(Word, W(5), ArrPush(Word, W(4), ArrPush(Word, W(3), ArrPush(Word, W(2), ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(1)), W(8)), W(9)), W(19)), W(25)), W(29)), W(35)), W(41)), W(47)), W(53)), W(55)), W(68)), W(70)), W(76)), W(77)), W(78)), W(79)), W(79)), W(83)), W(91)), W(91)), W(96)), W(98))) := refl
  -- random-02: [] ↦ []
  def Test_random_02 : Id (Array(Word, W(0))) (let a = ArrEmpty(Word); QuickSort(W(0), AsSlice(Word, W(0), &a)); a) (ArrEmpty(Word)) := refl
  -- random-03: [0, 2, 0, 3, 3, 0, 2, 3, 2, 2, 2, 1, 1, 3, 1, 3, 3, 2] ↦ [0, 0, 0, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3]
  def Test_random_03 : Id (Array(Word, W(18))) (let a = ArrPush(Word, W(17), ArrPush(Word, W(16), ArrPush(Word, W(15), ArrPush(Word, W(14), ArrPush(Word, W(13), ArrPush(Word, W(12), ArrPush(Word, W(11), ArrPush(Word, W(10), ArrPush(Word, W(9), ArrPush(Word, W(8), ArrPush(Word, W(7), ArrPush(Word, W(6), ArrPush(Word, W(5), ArrPush(Word, W(4), ArrPush(Word, W(3), ArrPush(Word, W(2), ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(0)), W(2)), W(0)), W(3)), W(3)), W(0)), W(2)), W(3)), W(2)), W(2)), W(2)), W(1)), W(1)), W(3)), W(1)), W(3)), W(3)), W(2)); QuickSort(W(18), AsSlice(Word, W(18), &a)); a) (ArrPush(Word, W(17), ArrPush(Word, W(16), ArrPush(Word, W(15), ArrPush(Word, W(14), ArrPush(Word, W(13), ArrPush(Word, W(12), ArrPush(Word, W(11), ArrPush(Word, W(10), ArrPush(Word, W(9), ArrPush(Word, W(8), ArrPush(Word, W(7), ArrPush(Word, W(6), ArrPush(Word, W(5), ArrPush(Word, W(4), ArrPush(Word, W(3), ArrPush(Word, W(2), ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(0)), W(0)), W(0)), W(1)), W(1)), W(1)), W(2)), W(2)), W(2)), W(2)), W(2)), W(2)), W(3)), W(3)), W(3)), W(3)), W(3)), W(3))) := refl
  -- random-04: [32, 15, 81, 46, 25, 65, 74, 57, 34, 50, 96, 34] ↦ [15, 25, 32, 34, 34, 46, 50, 57, 65, 74, 81, 96]
  def Test_random_04 : Id (Array(Word, W(12))) (let a = ArrPush(Word, W(11), ArrPush(Word, W(10), ArrPush(Word, W(9), ArrPush(Word, W(8), ArrPush(Word, W(7), ArrPush(Word, W(6), ArrPush(Word, W(5), ArrPush(Word, W(4), ArrPush(Word, W(3), ArrPush(Word, W(2), ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(32)), W(15)), W(81)), W(46)), W(25)), W(65)), W(74)), W(57)), W(34)), W(50)), W(96)), W(34)); QuickSort(W(12), AsSlice(Word, W(12), &a)); a) (ArrPush(Word, W(11), ArrPush(Word, W(10), ArrPush(Word, W(9), ArrPush(Word, W(8), ArrPush(Word, W(7), ArrPush(Word, W(6), ArrPush(Word, W(5), ArrPush(Word, W(4), ArrPush(Word, W(3), ArrPush(Word, W(2), ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(15)), W(25)), W(32)), W(34)), W(34)), W(46)), W(50)), W(57)), W(65)), W(74)), W(81)), W(96))) := refl
  -- random-05: [0, 3, 27, 77, 14, 37, 85, 5, 76, 0, 31, 87, 71, 11, 48, 37, 91, 56, 95, 85, 91, 71, 48] ↦ [0, 0, 3, 5, 11, 14, 27, 31, 37, 37, 48, 48, 56, 71, 71, 76, 77, 85, 85, 87, 91, 91, 95]
  def Test_random_05 : Id (Array(Word, W(23))) (let a = ArrPush(Word, W(22), ArrPush(Word, W(21), ArrPush(Word, W(20), ArrPush(Word, W(19), ArrPush(Word, W(18), ArrPush(Word, W(17), ArrPush(Word, W(16), ArrPush(Word, W(15), ArrPush(Word, W(14), ArrPush(Word, W(13), ArrPush(Word, W(12), ArrPush(Word, W(11), ArrPush(Word, W(10), ArrPush(Word, W(9), ArrPush(Word, W(8), ArrPush(Word, W(7), ArrPush(Word, W(6), ArrPush(Word, W(5), ArrPush(Word, W(4), ArrPush(Word, W(3), ArrPush(Word, W(2), ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(0)), W(3)), W(27)), W(77)), W(14)), W(37)), W(85)), W(5)), W(76)), W(0)), W(31)), W(87)), W(71)), W(11)), W(48)), W(37)), W(91)), W(56)), W(95)), W(85)), W(91)), W(71)), W(48)); QuickSort(W(23), AsSlice(Word, W(23), &a)); a) (ArrPush(Word, W(22), ArrPush(Word, W(21), ArrPush(Word, W(20), ArrPush(Word, W(19), ArrPush(Word, W(18), ArrPush(Word, W(17), ArrPush(Word, W(16), ArrPush(Word, W(15), ArrPush(Word, W(14), ArrPush(Word, W(13), ArrPush(Word, W(12), ArrPush(Word, W(11), ArrPush(Word, W(10), ArrPush(Word, W(9), ArrPush(Word, W(8), ArrPush(Word, W(7), ArrPush(Word, W(6), ArrPush(Word, W(5), ArrPush(Word, W(4), ArrPush(Word, W(3), ArrPush(Word, W(2), ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(0)), W(0)), W(3)), W(5)), W(11)), W(14)), W(27)), W(31)), W(37)), W(37)), W(48)), W(48)), W(56)), W(71)), W(71)), W(76)), W(77)), W(85)), W(85)), W(87)), W(91)), W(91)), W(95))) := refl
  -- random-06: [29] ↦ [29]
  def Test_random_06 : Id (Array(Word, W(1))) (let a = ArrPush(Word, W(0), ArrEmpty(Word), W(29)); QuickSort(W(1), AsSlice(Word, W(1), &a)); a) (ArrPush(Word, W(0), ArrEmpty(Word), W(29))) := refl
  -- random-07: [1, 1, 0, 1, 0, 2, 2, 0, 3, 2, 1, 1, 2, 2, 2] ↦ [0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3]
  def Test_random_07 : Id (Array(Word, W(15))) (let a = ArrPush(Word, W(14), ArrPush(Word, W(13), ArrPush(Word, W(12), ArrPush(Word, W(11), ArrPush(Word, W(10), ArrPush(Word, W(9), ArrPush(Word, W(8), ArrPush(Word, W(7), ArrPush(Word, W(6), ArrPush(Word, W(5), ArrPush(Word, W(4), ArrPush(Word, W(3), ArrPush(Word, W(2), ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(1)), W(1)), W(0)), W(1)), W(0)), W(2)), W(2)), W(0)), W(3)), W(2)), W(1)), W(1)), W(2)), W(2)), W(2)); QuickSort(W(15), AsSlice(Word, W(15), &a)); a) (ArrPush(Word, W(14), ArrPush(Word, W(13), ArrPush(Word, W(12), ArrPush(Word, W(11), ArrPush(Word, W(10), ArrPush(Word, W(9), ArrPush(Word, W(8), ArrPush(Word, W(7), ArrPush(Word, W(6), ArrPush(Word, W(5), ArrPush(Word, W(4), ArrPush(Word, W(3), ArrPush(Word, W(2), ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(0)), W(0)), W(0)), W(1)), W(1)), W(1)), W(1)), W(1)), W(2)), W(2)), W(2)), W(2)), W(2)), W(2)), W(3))) := refl
  -- random-08: [0] ↦ [0]
  def Test_random_08 : Id (Array(Word, W(1))) (let a = ArrPush(Word, W(0), ArrEmpty(Word), W(0)); QuickSort(W(1), AsSlice(Word, W(1), &a)); a) (ArrPush(Word, W(0), ArrEmpty(Word), W(0))) := refl
  -- random-09: [20, 25, 25, 62, 64, 98, 39, 57, 84, 29, 30] ↦ [20, 25, 25, 29, 30, 39, 57, 62, 64, 84, 98]
  def Test_random_09 : Id (Array(Word, W(11))) (let a = ArrPush(Word, W(10), ArrPush(Word, W(9), ArrPush(Word, W(8), ArrPush(Word, W(7), ArrPush(Word, W(6), ArrPush(Word, W(5), ArrPush(Word, W(4), ArrPush(Word, W(3), ArrPush(Word, W(2), ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(20)), W(25)), W(25)), W(62)), W(64)), W(98)), W(39)), W(57)), W(84)), W(29)), W(30)); QuickSort(W(11), AsSlice(Word, W(11), &a)); a) (ArrPush(Word, W(10), ArrPush(Word, W(9), ArrPush(Word, W(8), ArrPush(Word, W(7), ArrPush(Word, W(6), ArrPush(Word, W(5), ArrPush(Word, W(4), ArrPush(Word, W(3), ArrPush(Word, W(2), ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(20)), W(25)), W(25)), W(29)), W(30)), W(39)), W(57)), W(62)), W(64)), W(84)), W(98))) := refl
  -- random-10: [31, 30, 20, 2, 67, 70, 83, 63, 31, 51, 55, 13, 5, 53, 93, 57, 58, 36, 39, 93, 2, 51, 6] ↦ [2, 2, 5, 6, 13, 20, 30, 31, 31, 36, 39, 51, 51, 53, 55, 57, 58, 63, 67, 70, 83, 93, 93]
  def Test_random_10 : Id (Array(Word, W(23))) (let a = ArrPush(Word, W(22), ArrPush(Word, W(21), ArrPush(Word, W(20), ArrPush(Word, W(19), ArrPush(Word, W(18), ArrPush(Word, W(17), ArrPush(Word, W(16), ArrPush(Word, W(15), ArrPush(Word, W(14), ArrPush(Word, W(13), ArrPush(Word, W(12), ArrPush(Word, W(11), ArrPush(Word, W(10), ArrPush(Word, W(9), ArrPush(Word, W(8), ArrPush(Word, W(7), ArrPush(Word, W(6), ArrPush(Word, W(5), ArrPush(Word, W(4), ArrPush(Word, W(3), ArrPush(Word, W(2), ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(31)), W(30)), W(20)), W(2)), W(67)), W(70)), W(83)), W(63)), W(31)), W(51)), W(55)), W(13)), W(5)), W(53)), W(93)), W(57)), W(58)), W(36)), W(39)), W(93)), W(2)), W(51)), W(6)); QuickSort(W(23), AsSlice(Word, W(23), &a)); a) (ArrPush(Word, W(22), ArrPush(Word, W(21), ArrPush(Word, W(20), ArrPush(Word, W(19), ArrPush(Word, W(18), ArrPush(Word, W(17), ArrPush(Word, W(16), ArrPush(Word, W(15), ArrPush(Word, W(14), ArrPush(Word, W(13), ArrPush(Word, W(12), ArrPush(Word, W(11), ArrPush(Word, W(10), ArrPush(Word, W(9), ArrPush(Word, W(8), ArrPush(Word, W(7), ArrPush(Word, W(6), ArrPush(Word, W(5), ArrPush(Word, W(4), ArrPush(Word, W(3), ArrPush(Word, W(2), ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(2)), W(2)), W(5)), W(6)), W(13)), W(20)), W(30)), W(31)), W(31)), W(36)), W(39)), W(51)), W(51)), W(53)), W(55)), W(57)), W(58)), W(63)), W(67)), W(70)), W(83)), W(93)), W(93))) := refl
  -- random-11: [1, 3, 1, 1, 1, 0] ↦ [0, 1, 1, 1, 1, 3]
  def Test_random_11 : Id (Array(Word, W(6))) (let a = ArrPush(Word, W(5), ArrPush(Word, W(4), ArrPush(Word, W(3), ArrPush(Word, W(2), ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(1)), W(3)), W(1)), W(1)), W(1)), W(0)); QuickSort(W(6), AsSlice(Word, W(6), &a)); a) (ArrPush(Word, W(5), ArrPush(Word, W(4), ArrPush(Word, W(3), ArrPush(Word, W(2), ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(0)), W(1)), W(1)), W(1)), W(1)), W(3))) := refl
  -- random-12: [32, 6, 18, 62, 15, 33, 90] ↦ [6, 15, 18, 32, 33, 62, 90]
  def Test_random_12 : Id (Array(Word, W(7))) (let a = ArrPush(Word, W(6), ArrPush(Word, W(5), ArrPush(Word, W(4), ArrPush(Word, W(3), ArrPush(Word, W(2), ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(32)), W(6)), W(18)), W(62)), W(15)), W(33)), W(90)); QuickSort(W(7), AsSlice(Word, W(7), &a)); a) (ArrPush(Word, W(6), ArrPush(Word, W(5), ArrPush(Word, W(4), ArrPush(Word, W(3), ArrPush(Word, W(2), ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(6)), W(15)), W(18)), W(32)), W(33)), W(62)), W(90))) := refl
  -- random-13: [81, 92, 71, 92, 35, 19, 18, 39, 3, 12, 94, 12, 73, 40, 99, 8, 71] ↦ [3, 8, 12, 12, 18, 19, 35, 39, 40, 71, 71, 73, 81, 92, 92, 94, 99]
  def Test_random_13 : Id (Array(Word, W(17))) (let a = ArrPush(Word, W(16), ArrPush(Word, W(15), ArrPush(Word, W(14), ArrPush(Word, W(13), ArrPush(Word, W(12), ArrPush(Word, W(11), ArrPush(Word, W(10), ArrPush(Word, W(9), ArrPush(Word, W(8), ArrPush(Word, W(7), ArrPush(Word, W(6), ArrPush(Word, W(5), ArrPush(Word, W(4), ArrPush(Word, W(3), ArrPush(Word, W(2), ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(81)), W(92)), W(71)), W(92)), W(35)), W(19)), W(18)), W(39)), W(3)), W(12)), W(94)), W(12)), W(73)), W(40)), W(99)), W(8)), W(71)); QuickSort(W(17), AsSlice(Word, W(17), &a)); a) (ArrPush(Word, W(16), ArrPush(Word, W(15), ArrPush(Word, W(14), ArrPush(Word, W(13), ArrPush(Word, W(12), ArrPush(Word, W(11), ArrPush(Word, W(10), ArrPush(Word, W(9), ArrPush(Word, W(8), ArrPush(Word, W(7), ArrPush(Word, W(6), ArrPush(Word, W(5), ArrPush(Word, W(4), ArrPush(Word, W(3), ArrPush(Word, W(2), ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(3)), W(8)), W(12)), W(12)), W(18)), W(19)), W(35)), W(39)), W(40)), W(71)), W(71)), W(73)), W(81)), W(92)), W(92)), W(94)), W(99))) := refl
  -- random-14: [92, 18, 32] ↦ [18, 32, 92]
  def Test_random_14 : Id (Array(Word, W(3))) (let a = ArrPush(Word, W(2), ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(92)), W(18)), W(32)); QuickSort(W(3), AsSlice(Word, W(3), &a)); a) (ArrPush(Word, W(2), ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(18)), W(32)), W(92))) := refl
  -- random-15: [0, 3, 1, 1, 0, 2] ↦ [0, 0, 1, 1, 2, 3]
  def Test_random_15 : Id (Array(Word, W(6))) (let a = ArrPush(Word, W(5), ArrPush(Word, W(4), ArrPush(Word, W(3), ArrPush(Word, W(2), ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(0)), W(3)), W(1)), W(1)), W(0)), W(2)); QuickSort(W(6), AsSlice(Word, W(6), &a)); a) (ArrPush(Word, W(5), ArrPush(Word, W(4), ArrPush(Word, W(3), ArrPush(Word, W(2), ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(0)), W(0)), W(1)), W(1)), W(2)), W(3))) := refl
  -- random-16: [83, 33] ↦ [33, 83]
  def Test_random_16 : Id (Array(Word, W(2))) (let a = ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(83)), W(33)); QuickSort(W(2), AsSlice(Word, W(2), &a)); a) (ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(33)), W(83))) := refl
  -- random-17: [66, 41, 59, 84, 32, 11, 27, 32, 18, 96, 77, 21, 6, 73, 80, 92, 42, 91, 40, 3, 41] ↦ [3, 6, 11, 18, 21, 27, 32, 32, 40, 41, 41, 42, 59, 66, 73, 77, 80, 84, 91, 92, 96]
  def Test_random_17 : Id (Array(Word, W(21))) (let a = ArrPush(Word, W(20), ArrPush(Word, W(19), ArrPush(Word, W(18), ArrPush(Word, W(17), ArrPush(Word, W(16), ArrPush(Word, W(15), ArrPush(Word, W(14), ArrPush(Word, W(13), ArrPush(Word, W(12), ArrPush(Word, W(11), ArrPush(Word, W(10), ArrPush(Word, W(9), ArrPush(Word, W(8), ArrPush(Word, W(7), ArrPush(Word, W(6), ArrPush(Word, W(5), ArrPush(Word, W(4), ArrPush(Word, W(3), ArrPush(Word, W(2), ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(66)), W(41)), W(59)), W(84)), W(32)), W(11)), W(27)), W(32)), W(18)), W(96)), W(77)), W(21)), W(6)), W(73)), W(80)), W(92)), W(42)), W(91)), W(40)), W(3)), W(41)); QuickSort(W(21), AsSlice(Word, W(21), &a)); a) (ArrPush(Word, W(20), ArrPush(Word, W(19), ArrPush(Word, W(18), ArrPush(Word, W(17), ArrPush(Word, W(16), ArrPush(Word, W(15), ArrPush(Word, W(14), ArrPush(Word, W(13), ArrPush(Word, W(12), ArrPush(Word, W(11), ArrPush(Word, W(10), ArrPush(Word, W(9), ArrPush(Word, W(8), ArrPush(Word, W(7), ArrPush(Word, W(6), ArrPush(Word, W(5), ArrPush(Word, W(4), ArrPush(Word, W(3), ArrPush(Word, W(2), ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(3)), W(6)), W(11)), W(18)), W(21)), W(27)), W(32)), W(32)), W(40)), W(41)), W(41)), W(42)), W(59)), W(66)), W(73)), W(77)), W(80)), W(84)), W(91)), W(92)), W(96))) := refl
  -- random-18: [63, 26, 27, 90, 53, 58, 2, 13, 8, 30, 79, 39, 77, 24, 5, 32] ↦ [2, 5, 8, 13, 24, 26, 27, 30, 32, 39, 53, 58, 63, 77, 79, 90]
  def Test_random_18 : Id (Array(Word, W(16))) (let a = ArrPush(Word, W(15), ArrPush(Word, W(14), ArrPush(Word, W(13), ArrPush(Word, W(12), ArrPush(Word, W(11), ArrPush(Word, W(10), ArrPush(Word, W(9), ArrPush(Word, W(8), ArrPush(Word, W(7), ArrPush(Word, W(6), ArrPush(Word, W(5), ArrPush(Word, W(4), ArrPush(Word, W(3), ArrPush(Word, W(2), ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(63)), W(26)), W(27)), W(90)), W(53)), W(58)), W(2)), W(13)), W(8)), W(30)), W(79)), W(39)), W(77)), W(24)), W(5)), W(32)); QuickSort(W(16), AsSlice(Word, W(16), &a)); a) (ArrPush(Word, W(15), ArrPush(Word, W(14), ArrPush(Word, W(13), ArrPush(Word, W(12), ArrPush(Word, W(11), ArrPush(Word, W(10), ArrPush(Word, W(9), ArrPush(Word, W(8), ArrPush(Word, W(7), ArrPush(Word, W(6), ArrPush(Word, W(5), ArrPush(Word, W(4), ArrPush(Word, W(3), ArrPush(Word, W(2), ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(2)), W(5)), W(8)), W(13)), W(24)), W(26)), W(27)), W(30)), W(32)), W(39)), W(53)), W(58)), W(63)), W(77)), W(79)), W(90))) := refl
  -- random-19: [0, 1, 0, 0, 2, 0, 0, 1, 2, 1, 3, 0, 3, 0, 0] ↦ [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 3, 3]
  def Test_random_19 : Id (Array(Word, W(15))) (let a = ArrPush(Word, W(14), ArrPush(Word, W(13), ArrPush(Word, W(12), ArrPush(Word, W(11), ArrPush(Word, W(10), ArrPush(Word, W(9), ArrPush(Word, W(8), ArrPush(Word, W(7), ArrPush(Word, W(6), ArrPush(Word, W(5), ArrPush(Word, W(4), ArrPush(Word, W(3), ArrPush(Word, W(2), ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(0)), W(1)), W(0)), W(0)), W(2)), W(0)), W(0)), W(1)), W(2)), W(1)), W(3)), W(0)), W(3)), W(0)), W(0)); QuickSort(W(15), AsSlice(Word, W(15), &a)); a) (ArrPush(Word, W(14), ArrPush(Word, W(13), ArrPush(Word, W(12), ArrPush(Word, W(11), ArrPush(Word, W(10), ArrPush(Word, W(9), ArrPush(Word, W(8), ArrPush(Word, W(7), ArrPush(Word, W(6), ArrPush(Word, W(5), ArrPush(Word, W(4), ArrPush(Word, W(3), ArrPush(Word, W(2), ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(0)), W(0)), W(0)), W(0)), W(0)), W(0)), W(0)), W(0)), W(1)), W(1)), W(1)), W(2)), W(2)), W(3)), W(3))) := refl
  -- must be rejected: the expected array is the unsorted input [5, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5, 0, 99]
  reject def TestReject_unsorted : Id (Array(Word, W(13))) (let a = ArrPush(Word, W(12), ArrPush(Word, W(11), ArrPush(Word, W(10), ArrPush(Word, W(9), ArrPush(Word, W(8), ArrPush(Word, W(7), ArrPush(Word, W(6), ArrPush(Word, W(5), ArrPush(Word, W(4), ArrPush(Word, W(3), ArrPush(Word, W(2), ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(5)), W(1)), W(4)), W(1)), W(5)), W(9)), W(2)), W(6)), W(5)), W(3)), W(5)), W(0)), W(99)); QuickSort(W(13), AsSlice(Word, W(13), &a)); a) (ArrPush(Word, W(12), ArrPush(Word, W(11), ArrPush(Word, W(10), ArrPush(Word, W(9), ArrPush(Word, W(8), ArrPush(Word, W(7), ArrPush(Word, W(6), ArrPush(Word, W(5), ArrPush(Word, W(4), ArrPush(Word, W(3), ArrPush(Word, W(2), ArrPush(Word, W(1), ArrPush(Word, W(0), ArrEmpty(Word), W(5)), W(1)), W(4)), W(1)), W(5)), W(9)), W(2)), W(6)), W(5)), W(3)), W(5)), W(0)), W(99))) := refl
  -- END GENERATED TESTS
}
-- FIXED-END tests
