module Main

quicksort : List Nat -> List Nat
quicksort [] = []
quicksort (p :: xs) = quicksort (filter (< p) xs) ++ [p] ++ quicksort (filter (>= p) xs)

main : IO ()
main = do
    let xs = [20, 3, 1, 2, 13]
    putStrLn $ show xs
    putStrLn $ show $ quicksort xs
    
