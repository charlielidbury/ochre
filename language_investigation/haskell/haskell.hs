{-# LANGUAGE KindSignatures #-}

import Data.Map
import Control.Monad.State.Lazy
import Data.Kind (Constraint)


data Primitive
  = PInt Int
  | PBool Bool
  | PUnit ()
  | PFunc (Primitive -> Primitive)

instance Show Primitive where
  show (PInt i) = show i
  show (PBool b) = show b
  show (PUnit ()) = "()"
  show (PFunc _) = "<function>"

pAdd :: Primitive
pAdd = PFunc (\l -> PFunc (\r -> case (l, r) of
  (PInt l', PInt r') -> PInt (l' + r')
  _ -> error "'Add' applied to non-integers"))

pSeq :: Primitive
-- pSeq = PFunc (\_ -> PFunc (\r -> r))
pSeq = PFunc (const (PFunc id))

pNot :: Primitive
pNot = PFunc (\b -> case b of
  PBool b' -> PBool (not b')
  _ -> error "'Not' applied to non-boolean")

data Expr
  = Declare Expr Expr
  | Assign Expr Expr
  | Mut Expr
  | Ident String
  | Prim Primitive
  | App Expr Expr
  | Ref Expr
  | Lam Expr Expr
  deriving (Show)

type Scope = Map String Primitive

eval :: Expr -> State Scope Primitive
eval (Declare (Ident x) r) = do
  r' <- eval r
  modify (insert x r')
  return (PUnit ())
eval (Assign (Ident x) r) = do
  r' <- eval r
  modify (insert x r')
  return (PUnit ())
eval (Ident x) = do
  scope <- get
  return (scope ! x)
eval (Prim l) = return l
eval (App f x) = do
  lhs <- eval f
  case lhs of
    PFunc f' -> do
      x' <- eval x
      return (f' x')
    _ -> error (show lhs ++ "is not a function")
eval (Lam args body) = do
  scope <- get
  return $ PFunc
    (\x -> evalState (eval (Prim pSeq `App` (Declare args (Prim x)) `App` body))
    scope)
eval e = error ("No evaluation rule for " ++ show e)

evalProgram :: Expr -> Primitive
evalProgram e = evalState (eval e) empty

chain :: [Expr] -> Expr
chain [] = error "Empty chain"
chain [x] = x
chain (x:xs) = Prim pSeq `App` x `App` chain xs

data Foo (a :: Constraint) = Foo

x = evalProgram $ chain [
  -- x = 1
  Ident "x" `Declare` Prim (PInt 1),
  -- y = 2
  Ident "y" `Declare` Prim (PInt 2),
  -- y := y + x
  Ident "y" `Assign` (Prim pAdd `App` Ident "y" `App` Ident "x"),
  -- y
  Ident "y"]

main = do
  print "Hello World"

