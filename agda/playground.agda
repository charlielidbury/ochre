module playground where

-- Now it doesn't but it's weirdly not generic
-- Need some kind of inductive principal?
-- Or I could just sidestep this and have ADTs be primitive
ℕ = (a : Set) → a → (a → a) → a

-- Or should the user just define their types in terms of other types?
-- The whole lot would be non-nominal typing
s
