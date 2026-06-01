||| In-place quicksort over a *single linearly-threaded* mutable array.
|||
||| The whole point of this competitor file is the contrast with Rust borrows
||| and Low* separation: in QTT we have exactly ONE live handle to the mutable
||| array at any time (a value of quantity 1). There is no way to form two
||| disjoint `&mut` sub-views the way Rust's `split_at_mut` or Low*'s
||| `gsub`/`disjoint` do. So partition is expressed *by index ranges over the
||| one linear array*, recursing on `[lo, p)` and `(p, hi]` while threading the
||| same unique handle through both calls.
|||
||| Backed by `Data.Linear.Array.LinArray` (contrib), whose `MArray` interface
||| gives `mread`/`write`/`msize`, each consuming the `(1 _ : arr t)` handle and
||| handing back a fresh one inside a linear `Res` pair.
module QuicksortLinear

import Data.Linear.Array

%default total

------------------------------------------------------------------------
-- Helpers that thread the single linear array handle
------------------------------------------------------------------------

||| Read at index `i`. We have proven (informally) every index used is in
||| range, but `mread` is partial in its result (`Maybe`), so we supply a
||| default of 0 for the impossible out-of-range case. The array handle is
||| threaded out linearly.
get : (1 arr : LinArray Int) -> Int -> Res Int (const (LinArray Int))
get arr i = let (mv # arr') = mread arr i in
            case mv of
                 Just v  => (v # arr')
                 Nothing => (0 # arr')

||| Write `v` at index `i`, discarding the success Bool, threading the handle.
||| Returns a `Res () (...)` so callers always destructure with `#`, which keeps
||| the array strictly in linear position (a plain `let arr = ...` binding would
||| be elaborated at unrestricted multiplicity and reject the linear handle).
set : (1 arr : LinArray Int) -> Int -> Int -> Res () (const (LinArray Int))
set arr i v = let (_ # arr') = write arr i v in (() # arr')

||| Swap the contents of indices `i` and `j` on the one linear array.
swapAt : (1 arr : LinArray Int) -> Int -> Int -> Res () (const (LinArray Int))
swapAt arr i j =
  let (vi # arr1) = get arr  i
      (vj # arr2) = get arr1 j
      (() # arr3) = set arr2 i vj
  in  set arr3 j vi

------------------------------------------------------------------------
-- Lomuto partition (in place, indices only)
------------------------------------------------------------------------

-- We fuel the inner loops with a `Nat` bound (`hi - lo` suffices) so the
-- function is structurally total; the bound is never actually exhausted for
-- well-formed calls.

||| Inner scan of Lomuto partition.
|||   pivot       : pivot value (taken from index `hi`)
|||   lo, hi      : range bounds (partition over [lo, hi))
|||   j           : current scan cursor
|||   i           : store cursor (boundary of "<= pivot" region)
||| Returns the final store cursor `i` paired with the threaded array.
partitionLoop : (pivot : Int) -> (hi : Int) ->
                (1 arr : LinArray Int) -> (i : Int) -> (j : Int) ->
                (fuel : Nat) -> Res Int (const (LinArray Int))
partitionLoop pivot hi arr i j Z          = (i # arr)
partitionLoop pivot hi arr i j (S fuel) =
  if j >= hi
     then (i # arr)
     else let (vj # arr1) = get arr j in
          if vj <= pivot
             then let (() # arr2) = swapAt arr1 i j in
                  partitionLoop pivot hi arr2 (i + 1) (j + 1) fuel
             else partitionLoop pivot hi arr1 i (j + 1) fuel

||| Lomuto partition of the sub-range [lo, hi] (inclusive `hi`); pivot is the
||| element at `hi`. Returns the pivot's final resting index.
partition : (lo : Int) -> (hi : Int) ->
            (1 arr : LinArray Int) -> Res Int (const (LinArray Int))
partition lo hi arr =
  let (pivot # arr0) = get arr hi
      bound          = integerToNat (cast (hi - lo))
      (i # arr1)     = partitionLoop pivot hi arr0 lo lo bound
      (() # arr2)    = swapAt arr1 i hi
  in  (i # arr2)

------------------------------------------------------------------------
-- Quicksort driver
------------------------------------------------------------------------

||| Sort the inclusive range [lo, hi] of the single linear array.
|||
||| This is where the "no disjoint sub-views" point bites: the two recursive
||| calls run *sequentially*, each consuming and returning the one unique
||| handle. There is no `(left # right) = split_at_mut arr p` — the closest QTT
||| analogue would need a dependent split with index-disjointness proofs and a
||| recombine, which `Data.Linear.Array` does not provide.
quicksortRange : (lo : Int) -> (hi : Int) ->
                 (1 arr : LinArray Int) -> (fuel : Nat) ->
                 LinArray Int
quicksortRange lo hi arr Z          = arr
quicksortRange lo hi arr (S fuel) =
  if lo >= hi
     then arr
     else let (p # arr1) = partition lo hi arr in
          -- recurse on the left sub-range [lo, p-1], then on the right
          -- sub-range [p+1, hi] threading the SAME unique handle through both.
          -- Nested application keeps the handle in linear position the whole
          -- way (a plain `let arrK = ...` binding would relax it to ω).
          quicksortRange (p + 1) hi (quicksortRange lo (p - 1) arr1 fuel) fuel

||| Public entry point: sort the whole array. `fuel` of `n` recursion levels is
||| always enough (each level shrinks the range), bounded by the size.
quicksort : (1 arr : LinArray Int) -> LinArray Int
quicksort arr =
  let (n # arr1) = msize arr in
  quicksortRange 0 (n - 1) arr1 (integerToNat (cast n))

------------------------------------------------------------------------
-- A tiny self-check that actually runs the sort.
------------------------------------------------------------------------

||| Fill the array from a list. `fuel`/`Nat` length drives structural totality.
fillFrom : (1 arr : LinArray Int) -> Int -> List Int -> LinArray Int
fillFrom arr _ []        = arr
fillFrom arr i (x :: xs) = let (() # arr1) = set arr i x in
                           fillFrom arr1 (i + 1) xs

||| Read indices [i, n) back out of a *frozen immutable* array into a list.
||| `IArray`'s `read`/`size` are non-linear, so no threading is needed here.
||| `fuel` bounds the recursion for structural totality.
readBack : IArray Int -> Int -> Int -> (fuel : Nat) -> List Int
readBack arr i n Z        = []
readBack arr i n (S fuel) =
  if i >= n
     then []
     else let v = case read arr i of { Just x => x; Nothing => 0 } in
          v :: readBack arr (i + 1) n fuel

||| Sort `xs` by filling a fresh linear array, sorting in place, then *freezing*
||| it with `toIArray` (the library's linear consumer for `LinArray`) and
||| reading the immutable result back out.
runSort : List Int -> List Int
runSort xs =
  let len = the Int (cast (length xs)) in
  newArray len $ \arr =>
    let arr1 = fillFrom arr 0 xs
        arr2 = quicksort arr1
    in  toIArray arr2 $ \iarr =>
          readBack iarr 0 len (integerToNat (cast len))

main : IO ()
main = do
  let inp = [5, 2, 9, 1, 5, 6, 3, 8, 7, 0, 4]
  putStrLn $ "input : " ++ show inp
  putStrLn $ "sorted: " ++ show (runSort inp)
