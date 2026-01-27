
{-# LANGUAGE GADTSyntax, StandaloneDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module Lift where

--------------------------------------------------------------------------------

import Control.Monad
import Control.Monad.State.Strict

import Seq
import Term

--------------------------------------------------------------------------------

data Prg = MkPrg 
  { top  :: Seq (Fun Exp) 
  , main :: Exp 
  }
  deriving Show
 
data Exp where
  VarE :: Level            -> Exp
  AppE :: Top -> [Exp]     -> Exp
  LetE :: Ty -> Exp -> Exp -> Exp
  LitE :: Integer          -> Exp
  PriE :: PrimOp Exp       -> Exp

deriving instance Show Exp

--------------------------------------------------------------------------------

type LiftM a = State (Seq Fun) a

newTopLevel :: (Top -> Fun) -> LiftM Top
newTopLevel what = do
  old <- get
  let n = Seq.length old
  put (old |> what n)
  return n

--------------------------------------------------------------------------------

lambdaLift :: Tm' -> Prg
lambdaLift lambdaTerm = prg where

  prg = case runState (go empty lambdaTerm) Seq.empty of 
    (main,tops) -> MkPrg tops main 
  
  go :: Ctx -> Tm -> LiftM Exp
  go ctx term = case term of

    Lam s body -> let t = inferTy (ctx |> s) body 
                  let j = Seq.length ctx
                  let term' = Let (Arrow s t) (Lam s body) (Var j)
                  in  go ctx term'

    Lit x  -> Lit' x
    
    Pri op -> Pri' <$> mapM (go ctx) op

    App {} -> case isApp term' of
      MkApp h xs -> do
        h'  <- go ctx h 
        xs' <- mapM (go ctx) xs
        case h' of
          Var' j -> 

    Let s rhs body -> case isLambda rhs of
      Nothing -> do
        rhs'  <- go  ctx       rhs
        body' <- go (ctx |> s) body'
        return (Let' s rhs' body')
      Just lam -> do
        top <- goLam ctx lam


--------------------------------------------------------------------------------
