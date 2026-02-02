
{-# LANGUAGE BlockArguments, GADTSyntax, StandaloneDeriving, PatternSynonyms #-}
module Term where

--------------------------------------------------------------------------------

import Seq
import Common
import Val

--------------------------------------------------------------------------------
-- *** source terms

data Tm where
  Var :: Level          -> Tm      -- ^ variable
  App :: Tm -> Tm       -> Tm      -- ^ application
  Lam :: Ty -> Tm       -> Tm      -- ^ lambda
  Let :: Ty -> Tm -> Tm -> Tm      -- ^ let binding
  Rec :: Ty -> Tm -> Tm -> Tm      -- ^ recursive let
  Pri :: PrimOp Tm      -> Tm
  Lit :: Literal        -> Tm

deriving instance Show Tm

--------------------------------------------------------------------------------
-- *** simple type inference

inferTy_ :: Tm -> Ty
inferTy_ = inferTy emptyCtx

inferTy :: Ctx -> Tm -> Ty
inferTy = go where

  go :: Ctx -> Tm -> Ty
  go ctx term = case term of

    Var j -> seqIndex ctx j

    App fun arg -> case go ctx fun of
      Arrow s t   -> 
        let s' = go ctx arg in 
          if s == s' then t else error "inferTy/App" 

    Lam s body -> let t = go (ctx |> s) body in Arrow s t

    Let s rhs body -> let s' = go ctx rhs in 
      if s == s' then go (ctx |> s) body else error "inferTy/Let"

    Rec s rhs body -> let s' = go (ctx |> s) rhs in
      if s == s' then go (ctx |> s) body else error "inferTy/Rec"

    Lit lit -> litTy lit

    Pri op  -> primOpTy (fmap (go ctx) op)

--------------------------------------------------------------------------------
-- *** recognize multi-lam and multi-app

isLambda :: Ctx -> Tm -> Maybe (Fun Tm)
isLambda ctx term = case term of
  Lam {} -> Just (isLambda_ ctx term)
  _      -> Nothing

isLambda_ :: Ctx -> Tm -> Fun Tm
isLambda_ = go where
  go ctx (Lam t body) = case go (ctx |> t) body of { Fun_ args ret body -> Fun_ (t <| args) ret body }
  go ctx term         = Fun_ emptySeq (inferTy ctx term) term

----------------------------------------

isApp :: Tm -> Maybe (Apply Tm Tm)
isApp term = case term of
  App {} -> Just (isApp_ term)
  _      -> Nothing 

isApp_ :: Tm -> Apply Tm Tm
isApp_ = go where
  go (App f x) = case go f of { MkApp h xs -> MkApp h (xs |> x) }
  go term      = MkApp term emptySeq

--------------------------------------------------------------------------------
-- *** evaluate

evalTm :: Tm -> Val
evalTm = go emptySeq where

  go :: Env -> Tm -> Val
  go env term = case term of
    Var j          -> seqIndex env j
    App f x        -> valApp (go env f) (go env x)
    Lam t body     -> VLam t \x -> go (env |> x) body
    Let s rhs body -> let x = go  env       rhs in go (env |> x) body
    Rec s rhs body -> let f = go (env |> f) rhs in go (env |> f) body
    Pri op         -> evalPrimOp $ fmap (go env) op
    Lit y          -> litToVal y

--------------------------------------------------------------------------------
