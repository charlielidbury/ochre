module Main

-- properties we care about:
-- 1. permutation preservation
-- 2. output sorted

-- how do we represent permutation?
-- in verus it was multiset equality, but here it might be something lower level

Perm : List Int -> List Int -> Type
Perm xs xs' = (t : Int) -> count (== t) xs = count (== t) xs'

splitAt : (Int -> Bool) -> (xs : List Int) -> (ts : List Int ** fs : List Int ** ((t : Int) -> count (==t) xs = (count (==t) ts + count (==t) fs)))
splitAt p [] = ([] ** [] ** (\t => Refl))
splitAt p (x :: xs) = case splitAt p xs of
    (ts ** fs ** sumEq) => case (p x) of
        True => (x :: ts ** fs ** ?h1)
        False => (ts ** x :: fs ** ?h2)

quicksort : (xs : List Int) -> (ys : List Int ** Perm xs ys)
quicksort [] = ([] ** \t => Refl)
quicksort (p :: xs) = case splitAt (<p) xs of -- partition
    (lo ** hi ** sumEq) => case (quicksort lo, quicksort hi) of -- sort both halves 
        ((lo' ** _), (hi' ** _)) => (lo' ++ [p] ++ hi' ** ?h3) -- put together

xs : List Int
xs = [3, 1, 2]

ys : List Int
ys = [1, 2, 3]

eqTrans : a = b -> b = c -> a = c
eqTrans Refl Refl = Refl

eqSym : a = b -> b = a
eqSym Refl = Refl

concatEmptyIsIdentity : (xs : List Int) -> (xs ++ []) = xs
concatEmptyIsIdentity [] = Refl
concatEmptyIsIdentity (x :: xs) = cong (x ::) (concatEmptyIsIdentity xs)


concatEmptyIsIdentity' : (xs : List Int) -> xs = (xs ++ [])
concatEmptyIsIdentity' [] = Refl
concatEmptyIsIdentity' (x :: xs) = cong (x ::) (concatEmptyIsIdentity' xs)


countAppend : (xs : List Int) -> (ys: List Int) -> (n : Int)
    -> (count (== n) xs + count (== n) ys) = count (== n) (xs ++ ys)
countAppend [] ys n = Refl
countAppend (x :: xs) ys n = ?one


-- GOAL: (count (== n) (x::xs) + count (== n) ys)          = count (== n) ((x::xs) ++ ys)
-- reduce: ((if x==n ...) + count (== n) xs) + count (== n) ys = (if x==n ...) + count (== n) (xs ++ ys)
-- +assoc: (if x==n ...) + (count (== n) xs + count (== n) ys) = (if x==n ...) + count (== n) (xs ++ ys)
-- cong (if x==n ...): 


-- count 0 ys = count 0 (ys ++ [])
-- cong breaks this down into ys = ys ++ []
-- which is concatEmptyIsIdentity

concatPreservesPerm : (xs : List Int) -> (ys : List Int)
    -> Perm (xs ++ ys) (ys ++ xs)
concatPreservesPerm [] ys n = cong (count (== n)) $ eqSym $ concatEmptyIsIdentity ys
concatPreservesPerm xs [] n = cong (count (== n)) $ concatEmptyIsIdentity xs
concatPreservesPerm (x :: xs) (y :: ys) n = ?other


-- What is the argument here?
-- if both are cons, then we can bring the first element out front 
-- we can induct on {(x::xs, ys), (xs, ys), (xs, y::ys)}

-- GOAL: For both xs++ys and ys++xs, every number going to give us the same count
-- 

sortWork : quicksort [4, 1, 3, 2] = [1, 2, 3, 4]
sortWork = Refl

main : IO ()
main = do
    let xs = [4,1,3,2]
    putStrLn $ show $ xs
    putStrLn $ show $ quicksort xs
    
