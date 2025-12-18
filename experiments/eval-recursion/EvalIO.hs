
-- evaluation with fixpoint (in IO) exercise

{-# LANGUAGE BlockArguments #-}
module EvalIO where

--------------------------------------------------------------------------------

import qualified Data.Sequence as Seq
import Data.Sequence ( Seq , (|>) )

import Term

--------------------------------------------------------------------------------

data Val
  = Nat Nat
  | Fun (Val -> IO Val)
  | Thk (IO Val)

instance Show Val where
  show (Nat k) = show k
  show (Fun _) = "<<lambda>>"
  show (Thk _) = "<<thunk>>"

force :: Val -> IO Val
force (Thk delayed) = delayed >>= force
force val = return val

----------------------------------------

appVal :: Val -> Val -> IO Val
appVal (Fun f) x = f x

plusVal :: Val -> Val -> Val
plusVal (Nat a) (Nat b) = Nat (a + b)

minusVal :: Val -> Val -> Val
minusVal (Nat a) (Nat b) = Nat (a - b)

--------------------------------------------------------------------------------

type Env = Seq Val

emptyEnv :: Env
emptyEnv = Seq.empty

eval :: Tm -> IO Val
eval = eval' Seq.empty

--------------------------------------------------------------------------------

eval' :: Env -> Tm -> IO Val
eval' = go where

  go :: Env -> Tm -> IO Val
  go env tm = do
    val <- go' env tm
    force val

  go' :: Env -> Tm -> IO Val
  go' env tm = case tm of

    Var level -> return (Seq.index env level)
    Lit k     -> return (Nat k)

    App f x -> do
      f' <- go env f
      x' <- go env x
      appVal f' x'

    Lam body -> return $ Fun \x -> go (env |> x) body

    Let rhs body -> do
      rhs' <- go env rhs
      go (env |> rhs') body

    Fix body -> let f = go (env |> Thk f) body in f

    Add x y -> do
      x' <- go env x
      y' <- go env y
      return (plusVal x' y')

    Sub x y -> do
      x' <- go env x
      y' <- go env y
      return (minusVal x' y')

    IfZ z t f -> do
      z' <- go env z
      case z' of
        Nat 0 -> go env t
        _     -> go env f

    Print s x kont -> do
      x' <- go env x
      putStrLn $ s ++ " ~> " ++ show x'
      go env kont

--------------------------------------------------------------------------------

