
{-# LANGUAGE GADTSyntax, StandaloneDeriving, PatternSynonyms #-}
module Term where

--------------------------------------------------------------------------------

import Seq
import Common

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
-- *** terms after some preprocessing

data Tm' where
  Var' :: Level                -> Tm'      -- ^ variable
  App' :: Apply Level Tm'      -> Tm'      -- ^ application to a variable
  Let' :: Ty -> Tm'     -> Tm' -> Tm'      -- ^ let binding an expression
  Fun' :: Ty -> Fun Tm' -> Tm' -> Tm'      -- ^ let binding a function
  Rec' :: Ty -> Fun Tm' -> Tm' -> Tm'      -- ^ recursive let binding
  Pri' :: PrimOp Tm'           -> Tm'
  Lit' :: Literal              -> Tm'

deriving instance Show Tm'

preprocess :: Tm -> Tm'
preprocess = go emptyCtx where
 
  go :: Ctx -> Tm -> Tm'
  go ctx term = case term of

    Var j  -> Var' j

    App {} -> case isApp_ term of
      MkApp fun args -> case go ctx fun of
        Var'        j     -> App' (MkApp j $       fmap (go ctx) args)
        App' (MkApp j xs) -> App' (MkApp j $ xs <> fmap (go ctx) args)

    Lam {} -> case isLambda_ ctx term of
      fun@(Fun_ ts ret body) -> 
        let body' = go (ctx <> ts) body
        in Fun' (funTy fun) (Fun_ ts ret body') (Var' (ctxLevel ctx))

    Let t rhs letbody -> if not (isArrow t)
      then Let' t (go ctx rhs) (go (ctx |> t) letbody)
      else case isLambda_ ctx rhs of
        fun@(Fun_ ts ret funbody) -> 
          let funbody' = go (ctx <> ts) funbody
              letbody' = go (ctx |> t ) letbody 
          in  Fun' (funTy fun) (Fun_ ts ret funbody') letbody'

    Rec t rhs letbody -> case isLambda_ (ctx |> t) rhs of
      fun@(Fun_ ts ret funbody) -> 
        let funbody' = go ((ctx |> t) <> ts) funbody
            letbody' = go ( ctx |> t       ) letbody 
        in  Rec' (funTy fun) (Fun_ ts ret funbody') letbody'

    Lit y  -> Lit' y

    Pri op -> Pri' (fmap (go ctx) op)

--------------------------------------------------------------------------------
