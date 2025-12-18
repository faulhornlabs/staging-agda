
-- evaluation with fixpoint (in IO) exercise

{-# LANGUAGE BlockArguments #-}
module EvalPure where

--------------------------------------------------------------------------------

import qualified Data.Sequence as Seq
import Data.Sequence ( Seq , (|>) )

import System.IO.Unsafe

import Term

--------------------------------------------------------------------------------

data Val
  = Nat Nat
  | Fun (Val -> Val)

instance Show Val where
  show (Nat k) = show k
  show (Fun _) = "<<lambda>>"

----------------------------------------

appVal :: Val -> Val -> Val
appVal (Fun f) x = f x

plusVal :: Val -> Val -> Val
plusVal (Nat a) (Nat b) = Nat (a + b)

minusVal :: Val -> Val -> Val
minusVal (Nat a) (Nat b) = Nat (a - b)

--------------------------------------------------------------------------------

type Env = Seq Val

emptyEnv :: Env
emptyEnv = Seq.empty

eval :: Tm -> Val
eval = eval' Seq.empty

--------------------------------------------------------------------------------

eval' :: Env -> Tm -> Val
eval' = go where

  go :: Env -> Tm -> Val
  go env tm = case tm of

    Var level -> Seq.index env level
    Lit k     -> Nat k

    App f x -> appVal (go env f) (go env x)

    Lam body -> Fun \x -> go (env |> x) body

    Let rhs body -> 
      let rhs' = go env rhs
      in  go (env |> rhs') body

    Fix body -> let f = go (env |> f) body in f

    Add x y -> plusVal  (go env x) (go env y)
    Sub x y -> minusVal (go env x) (go env y)

    IfZ z t f -> case (go env z) of
      Nat 0 -> go env t
      _     -> go env f

    Print s x kont -> unsafePerformIO $ do
      let x' = go env x
      putStrLn $ s ++ " ~> " ++ show x'
      return (go env kont)

--------------------------------------------------------------------------------
