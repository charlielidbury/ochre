foo :: (Const a ~ Const b) => a -> b
foo = id

type family Const a b where
  Const a b = a


type A = Maybe Int
type B = Maybe b


