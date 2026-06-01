||| Quicksort on `List Nat`, with a FULL machine-checked proof that the output
||| is sorted AND a permutation of the input. No `sorry`/`believe_me`/`assert`/
||| `idris_crash`/postulate anywhere (grep the file; see NOTES.md).
|||
||| Headline theorems (see bottom of file):
|||
|||   quicksortSorted : (xs : List Nat) -> Sorted (quicksort xs)
|||   quicksortPerm   : (xs : List Nat) -> Perm xs (quicksort xs)
|||
||| where `Sorted` is ascending-ness and `Perm xs ys` means xs and ys are
||| multiset-equal (every value occurs equally often — i.e. a permutation).
|||
||| REPRESENTATION CHOICE (full rationale in NOTES.md): the linear
||| `Data.Linear.Array.LinArray` route (preserved in `QuicksortLinear.idr`)
||| cannot carry this proof. That type has no length and no invariants in its
||| type, and its reads return `Maybe`, so neither `Sorted` nor `Perm` can even
||| be *stated* about it. We prove correctness over an inductive `List Nat`,
||| where every operation reduces predictably for the proofs. The divide step
||| still partitions into a "<= pivot" half and a "> pivot" half that are sorted
||| independently and concatenated around the pivot — same shape as the in-place
||| version, expressed as passes over one list.
module Quicksort

import Data.Nat
import Data.List.Quantifiers
import Decidable.Equality

%default total

------------------------------------------------------------------------
-- Boolean comparison <-> propositional LTE reflection (Nat)
------------------------------------------------------------------------

||| Reflexivity of `LTE` on Nat.
lteRefl : (n : Nat) -> LTE n n
lteRefl Z     = LTEZero
lteRefl (S k) = LTESucc (lteRefl k)

||| Transitivity of `LTE` on Nat.
lteTrans : LTE a b -> LTE b c -> LTE a c
lteTrans LTEZero     _           = LTEZero
lteTrans (LTESucc p) (LTESucc q) = LTESucc (lteTrans p q)

falseNotTrue : False = True -> Void
falseNotTrue Refl impossible

trueNotFalse : True = False -> Void
trueNotFalse Refl impossible

||| `x <= y` (Bool, from Prelude `Ord Nat`) implies `LTE x y` (the proposition).
lteTrue : (x, y : Nat) -> (x <= y) = True -> LTE x y
lteTrue Z     y     _  = LTEZero
lteTrue (S k) (S j) eq = LTESucc (lteTrue k j eq)
lteTrue (S k) Z     eq = absurd (falseNotTrue eq)

||| `x <= y` is False implies `LTE y x`. (`0 <= y` is always True, so those
||| cases have a contradictory hypothesis.)
lteFalse : (x, y : Nat) -> (x <= y) = False -> LTE y x
lteFalse Z     Z     eq = absurd (trueNotFalse eq)
lteFalse Z     (S j) eq = absurd (trueNotFalse eq)
lteFalse (S k) Z     _  = LTEZero
lteFalse (S k) (S j) eq = LTESucc (lteFalse k j eq)

||| `n == n` is True for Nat.
eqNatRefl : (n : Nat) -> (n == n) = True
eqNatRefl Z     = Refl
eqNatRefl (S k) = eqNatRefl k

||| `a == b` True implies `a = b` for Nat.
eqNatSound : (a, b : Nat) -> (a == b) = True -> a = b
eqNatSound Z     Z     _  = Refl
eqNatSound (S k) (S j) eq = cong S (eqNatSound k j eq)
eqNatSound Z     (S _) eq = absurd (falseNotTrue eq)
eqNatSound (S _) Z     eq = absurd (falseNotTrue eq)

------------------------------------------------------------------------
-- Sortedness
------------------------------------------------------------------------

||| `Sorted xs`: `xs` is ascending. The head is `<=` every later element, and
||| the tail is itself sorted.
public export
data Sorted : List Nat -> Type where
  SNil  : Sorted []
  SCons : All (\y => LTE x y) xs -> Sorted xs -> Sorted (x :: xs)

------------------------------------------------------------------------
-- Permutation via multiset counts
------------------------------------------------------------------------

||| Number of occurrences of `v` in `xs`.
public export
cnt : Nat -> List Nat -> Nat
cnt v []        = 0
cnt v (y :: ys) = (if v == y then 1 else 0) + cnt v ys

||| `Perm xs ys`: xs and ys are multiset-equal. This is precisely the statement
||| that ys is a permutation of xs.
public export
Perm : List Nat -> List Nat -> Type
Perm xs ys = (v : Nat) -> cnt v xs = cnt v ys

-- NB: `Perm xs ys` is a *reducible* function type, so Idris cannot recover the
-- list arguments from a `Perm`-typed value by unification. We therefore make
-- the lists explicit arguments to every combinator below.

permRefl : (xs : List Nat) -> Perm xs xs
permRefl xs = \_ => Refl

permTrans : (xs, ys, zs : List Nat) -> Perm xs ys -> Perm ys zs -> Perm xs zs
permTrans _ _ _ p q = \v => trans (p v) (q v)

permSym : (xs, ys : List Nat) -> Perm xs ys -> Perm ys xs
permSym _ _ p = \v => sym (p v)

||| cnt distributes over append.
countAppend : (v : Nat) -> (xs, ys : List Nat) ->
              cnt v (xs ++ ys) = cnt v xs + cnt v ys
countAppend v []        ys = Refl
countAppend v (x :: xs) ys =
  rewrite countAppend v xs ys in
  plusAssociative (if v == x then 1 else 0) (cnt v xs) (cnt v ys)

||| `cnt x (x :: xs) = S (cnt x xs)`: the matching head contributes exactly one.
cntConsSame : (x : Nat) -> (xs : List Nat) -> cnt x (x :: xs) = S (cnt x xs)
cntConsSame x xs = rewrite eqNatRefl x in Refl

||| Congruence: cons the same head onto a permutation.
permCons : (x : Nat) -> (xs, ys : List Nat) ->
           Perm xs ys -> Perm (x :: xs) (x :: ys)
permCons x _ _ p = \v => cong (\k => (if v == x then 1 else 0) + k) (p v)

||| Append respects Perm on both sides.
permAppend : (as, bs, cs, ds : List Nat) ->
             Perm as bs -> Perm cs ds -> Perm (as ++ cs) (bs ++ ds)
permAppend as bs cs ds p q = \v =>
  rewrite countAppend v as cs in
  rewrite countAppend v bs ds in
  rewrite p v in
  rewrite q v in Refl

------------------------------------------------------------------------
-- Partition: split into (<= p) and (> p)
------------------------------------------------------------------------

le : Nat -> List Nat -> List Nat
le p []        = []
le p (x :: xs) = if x <= p then x :: le p xs else le p xs

gt : Nat -> List Nat -> List Nat
gt p []        = []
gt p (x :: xs) = if x <= p then gt p xs else x :: gt p xs

------------------------------------------------------------------------
-- Termination metric: le/gt never grow the list
------------------------------------------------------------------------

leLength : (p : Nat) -> (xs : List Nat) -> LTE (length (le p xs)) (length xs)
leLength p []        = LTEZero
leLength p (x :: xs) with (x <= p)
  _ | True  = LTESucc (leLength p xs)
  _ | False = lteSuccRight (leLength p xs)

gtLength : (p : Nat) -> (xs : List Nat) -> LTE (length (gt p xs)) (length xs)
gtLength p []        = LTEZero
gtLength p (x :: xs) with (x <= p)
  _ | True  = lteSuccRight (gtLength p xs)
  _ | False = LTESucc (gtLength p xs)

------------------------------------------------------------------------
-- Partition preserves the multiset
------------------------------------------------------------------------

||| a + (b + c) = b + (a + c)
shuffle : (a, b, c : Nat) -> a + (b + c) = b + (a + c)
shuffle a b c =
  rewrite plusAssociative a b c in
  rewrite plusCommutative a b in
  sym (plusAssociative b a c)

||| Every occurrence is accounted for exactly once across the two halves.
countSplit : (v, p : Nat) -> (xs : List Nat) ->
             cnt v xs = cnt v (le p xs) + cnt v (gt p xs)
countSplit v p []        = Refl
countSplit v p (x :: xs) with (x <= p)
  _ | True  =
       rewrite countSplit v p xs in
       plusAssociative (if v == x then 1 else 0)
                       (cnt v (le p xs)) (cnt v (gt p xs))
  _ | False =
       rewrite countSplit v p xs in
       shuffle (if v == x then 1 else 0)
               (cnt v (le p xs)) (cnt v (gt p xs))

||| `Perm xs (le p xs ++ gt p xs)` — partition is a permutation of the input.
partitionPerm : (p : Nat) -> (xs : List Nat) ->
                Perm xs (le p xs ++ gt p xs)
partitionPerm p xs = \v =>
  rewrite countAppend v (le p xs) (gt p xs) in
  countSplit v p xs

------------------------------------------------------------------------
-- Bounds: "every value occurring in xs satisfies P"
------------------------------------------------------------------------

||| `BoundedBy p xs`: every value that actually occurs in `xs` satisfies `p`.
||| This formulation (in terms of `cnt`) is what makes bounds transport
||| cleanly across a `Perm` — see `boundedPerm`.
BoundedBy : (Nat -> Type) -> List Nat -> Type
BoundedBy p xs = (v : Nat) -> Not (cnt v xs = 0) -> p v

||| Bounds transport across a permutation: same multiset => same occurring
||| values => same bound.
boundedPerm : Perm xs ys -> BoundedBy p xs -> BoundedBy p ys
boundedPerm perm b = \v, nz => b v (\cz => nz (trans (sym (perm v)) cz))

||| A `BoundedBy` fact reifies into a full `All` proof over the same list.
boundedToAll : (xs : List Nat) -> BoundedBy p xs -> All p xs
boundedToAll []        _ = []
boundedToAll (x :: xs) b =
  b x headNZ :: boundedToAll xs (\v, nz => b v (tailNZ v nz))
  where
    headNZ : Not (cnt x (x :: xs) = 0)
    headNZ prf = absurd (trans (sym (cntConsSame x xs)) prf)
    tailNZ : (v : Nat) -> Not (cnt v xs = 0) -> Not (cnt v (x :: xs) = 0)
    tailNZ v nz prf with (v == x)
      _ | True  = absurd prf
      _ | False = nz prf

||| Everything in `le p xs` is `<= p`.
leBounded : (p : Nat) -> (xs : List Nat) -> BoundedBy (\y => LTE y p) (le p xs)
leBounded p []        = \v, nz => absurd (nz Refl)
leBounded p (x :: xs) with (x <= p) proof prf
  _ | True  = \v, nz => case decEq (cnt v (le p xs)) 0 of
                             No  ne  => leBounded p xs v ne
                             Yes pz  =>
                               -- v occurs only as the kept head x, so v = x
                               rewrite eqHead v nz pz in lteTrue x p prf
    where
      eqHead : (v : Nat) -> Not (cnt v (x :: le p xs) = 0) ->
               cnt v (le p xs) = 0 -> v = x
      eqHead v nz pz with (v == x) proof e
        _ | True  = eqNatSound v x e
        _ | False = absurd (nz (rewrite pz in Refl))
  _ | False = leBounded p xs

||| Everything in `gt p xs` is `>= p` (i.e. `p <= y`).
gtBounded : (p : Nat) -> (xs : List Nat) -> BoundedBy (\y => LTE p y) (gt p xs)
gtBounded p []        = \v, nz => absurd (nz Refl)
gtBounded p (x :: xs) with (x <= p) proof prf
  _ | True  = gtBounded p xs
  _ | False = \v, nz => case decEq (cnt v (gt p xs)) 0 of
                             No  ne  => gtBounded p xs v ne
                             Yes pz  =>
                               rewrite eqHead v nz pz in lteFalse x p prf
    where
      eqHead : (v : Nat) -> Not (cnt v (x :: gt p xs) = 0) ->
               cnt v (gt p xs) = 0 -> v = x
      eqHead v nz pz with (v == x) proof e
        _ | True  = eqNatSound v x e
        _ | False = absurd (nz (rewrite pz in Refl))

------------------------------------------------------------------------
-- Sortedness of an append (the recombination step)
------------------------------------------------------------------------

||| `All` distributes over append.
allAppend : All p xs -> All p ys -> All p (xs ++ ys)
allAppend []          pys = pys
allAppend (px :: pxs) pys = px :: allAppend pxs pys

||| If `x <= b` and every element of `ys` is `>= b`, then `x <=` every element
||| of `ys` (transitivity, lifted over `All`).
allLteVia : (x, b : Nat) -> (ys : List Nat) ->
            LTE x b -> All (\y => LTE b y) ys -> All (\y => LTE x y) ys
allLteVia x b []        _  _            = []
allLteVia x b (z :: zs) xb (py :: pys) =
  lteTrans xb py :: allLteVia x b zs xb pys

||| If `xs` is sorted with every element `<= b`, `ys` is sorted with every
||| element `>= b`, then `xs ++ (b :: ys)` is sorted.
||| (`b` is the pivot; `xs` the sorted `<=` half, `ys` the sorted `>` half.)
sortedJoin : (b : Nat) -> (xs, ys : List Nat) ->
             Sorted xs -> Sorted ys ->
             All (\y => LTE y b) xs -> All (\y => LTE b y) ys ->
             Sorted (xs ++ (b :: ys))
sortedJoin b []        ys SNil          sy []          gy =
  SCons gy sy
sortedJoin b (x :: xs) ys (SCons ax sx) sy (lx :: lxs) gy =
  let xLeYs   : All (\y => LTE x y) ys
      xLeYs   = allLteVia x b ys lx gy
      headAll : All (\y => LTE x y) (xs ++ (b :: ys))
      headAll = allAppend ax (lx :: xLeYs)
      rest    : Sorted (xs ++ (b :: ys))
      rest    = sortedJoin b xs ys sx sy lxs gy
  in SCons headAll rest

||| `q :: (lo ++ hi)` is a permutation of `lo ++ (q :: hi)`: the pivot moves
||| from the front to between the two halves.
consShift : (q : Nat) -> (lo, hi : List Nat) ->
            Perm (q :: (lo ++ hi)) (lo ++ (q :: hi))
consShift q lo hi = \v =>
  rewrite countAppend v lo (q :: hi) in
  rewrite countAppend v lo hi in
  -- LHS: (if v==q then 1 else 0) + (cnt v lo + cnt v hi)
  -- RHS: cnt v lo + ((if v==q then 1 else 0) + cnt v hi)
  shuffle (if v == q then 1 else 0) (cnt v lo) (cnt v hi)

------------------------------------------------------------------------
-- Quicksort (structural on a Nat fuel = length; always sufficient)
------------------------------------------------------------------------

||| Worker: sorts `xs` given `fuel >= length xs`. Returns the sorted list
||| together with the proofs that it is sorted and a permutation of `xs`.
||| Bundling the proofs lets each recursive call hand its caller exactly the
||| evidence the recombination needs.
qsAux : (fuel : Nat) -> (xs : List Nat) -> LTE (length xs) fuel ->
        (out : List Nat ** (Sorted out, Perm xs out))
qsAux fuel [] _ = ([] ** (SNil, permRefl []))
qsAux Z (x :: xs) lenPf = absurd lenPf  -- length (x::xs) = S _ </= Z
qsAux (S fuel) (p :: xs) (LTESucc lenPf) =
  let -- partition the tail around pivot p
      loFuel : LTE (length (le p xs)) fuel
      loFuel = lteTrans (leLength p xs) lenPf
      hiFuel : LTE (length (gt p xs)) fuel
      hiFuel = lteTrans (gtLength p xs) lenPf
  in
  -- recursively sort each half (dependent-pair scrutinees)
  case qsAux fuel (le p xs) loFuel of
    (lo ** (loSorted, loPerm)) =>
     case qsAux fuel (gt p xs) hiFuel of
      (hi ** (hiSorted, hiPerm)) =>
       let
      -- bounds on the halves, transported to the sorted results
      loBnd : BoundedBy (\y => LTE y p) lo
      loBnd = boundedPerm loPerm (leBounded p xs)
      hiBnd : BoundedBy (\y => LTE p y) hi
      hiBnd = boundedPerm hiPerm (gtBounded p xs)

      loAll : All (\y => LTE y p) lo
      loAll = boundedToAll lo loBnd
      hiAll : All (\y => LTE p y) hi
      hiAll = boundedToAll hi hiBnd

      -- recombine: sorted lo ++ p :: sorted hi
      outSorted : Sorted (lo ++ (p :: hi))
      outSorted = sortedJoin p lo hi loSorted hiSorted loAll hiAll

      -- permutation:  p :: xs
      --   ~ p :: (le p xs ++ gt p xs)        (partitionPerm)
      --   ~ p :: (lo ++ hi)                  (loPerm, hiPerm)
      --   ~ lo ++ (p :: hi)                  (consShift)
      step1 : Perm (p :: xs) (p :: (le p xs ++ gt p xs))
      step1 = permCons p xs (le p xs ++ gt p xs) (partitionPerm p xs)
      step2 : Perm (p :: (le p xs ++ gt p xs)) (p :: (lo ++ hi))
      step2 = permCons p (le p xs ++ gt p xs) (lo ++ hi)
                (permAppend (le p xs) lo (gt p xs) hi loPerm hiPerm)
      step3 : Perm (p :: (lo ++ hi)) (lo ++ (p :: hi))
      step3 = consShift p lo hi
      step23 : Perm (p :: (le p xs ++ gt p xs)) (lo ++ (p :: hi))
      step23 = permTrans (p :: (le p xs ++ gt p xs)) (p :: (lo ++ hi))
                         (lo ++ (p :: hi)) step2 step3
      outPerm : Perm (p :: xs) (lo ++ (p :: hi))
      outPerm = permTrans (p :: xs) (p :: (le p xs ++ gt p xs))
                          (lo ++ (p :: hi)) step1 step23
       in (lo ++ (p :: hi) ** (outSorted, outPerm))

||| The sorting function.
public export
quicksort : List Nat -> List Nat
quicksort xs = fst (qsAux (length xs) xs (lteRefl (length xs)))

------------------------------------------------------------------------
-- HEADLINE THEOREMS
------------------------------------------------------------------------

||| The output of `quicksort` is sorted (ascending).
export
quicksortSorted : (xs : List Nat) -> Sorted (quicksort xs)
quicksortSorted xs = fst (snd (qsAux (length xs) xs (lteRefl (length xs))))

||| The output of `quicksort` is a permutation (multiset-equal) of the input.
export
quicksortPerm : (xs : List Nat) -> Perm xs (quicksort xs)
quicksortPerm xs = snd (snd (qsAux (length xs) xs (lteRefl (length xs))))

------------------------------------------------------------------------
-- Runnable demo
------------------------------------------------------------------------

main : IO ()
main = do
  let inp = [5, 2, 9, 1, 5, 6, 3, 8, 7, 0, 4]
  putStrLn $ "input : " ++ show inp
  putStrLn $ "sorted: " ++ show (quicksort inp)
