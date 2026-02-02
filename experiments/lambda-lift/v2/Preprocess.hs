
{-# LANGUAGE BlockArguments, GADTSyntax, PatternSynonyms, StandaloneDeriving, DeriveFunctor #-}
module Preprocess where

--------------------------------------------------------------------------------

import Control.Monad
import Control.Monad.State.Strict

import qualified Data.Set as Set ; import Data.Set ( Set )
import qualified Data.Map as Map ; import Data.Map ( Map )

import Seq
import Common
import Term
import Val

--------------------------------------------------------------------------------
-- *** terms after some preprocessing

data Tm' v where
  Var' :: v                          -> Tm' v      -- ^ variable
  App' :: v -> Seq (Tm' v)           -> Tm' v      -- ^ application to a variable
  Let' :: Ty ->      Tm' v  -> Tm' v -> Tm' v      -- ^ let binding of an expression
  Fun' :: Ty -> Fun (Tm' v) -> Tm' v -> Tm' v      -- ^ let binding of a function
  Rec' :: Ty -> Fun (Tm' v) -> Tm' v -> Tm' v      -- ^ recursive let binding
  Pri' :: PrimOp (Tm' v)             -> Tm' v
  Lit' :: Literal                    -> Tm' v

deriving instance Show v => Show (Tm' v)
deriving instance Functor Tm'

type Tm1 = Tm' Level

translateTm :: (u -> v) -> Tm' u -> Tm' v
translateTm = fmap

--------------------------------------------------------------------------------

-- | float `let`-s outside of application head:
--
-- > (let x = e' in f) a b c   ~~>    let x = e' in (f a b c)    
--
-- as we use de Bruij *levels*, variables referred in `a`, `b`, `c`... remain unchanged
--
letFloatApp :: Tm' v -> Seq (Tm' v) -> Tm' v
letFloatApp = float where

  float :: Tm' v -> Seq (Tm' v) -> Tm' v
  float appHead args = case appHead of
    Var' j            -> App' j        args 
    App' j xs         -> App' j (xs <> args)
    Let' t rhs body   -> Let' t rhs (float body args)
    Fun' t fun body   -> Fun' t fun (float body args)
    Rec' t fun body   -> Rec' t fun (float body args)
    Pri' {}           -> error "preprocess/letFloat: application to a primitive"
    Lit' {}           -> error "preprocess/letFloat: application to a literal"

--------------------------------------------------------------------------------

-- | This AST preprocessing step simplifies future step by:
--
-- * enfore that application heads are variables
--
-- * eliminate naked lambdas
--
-- * separate let-binding of expressions and functions (and recursive functions)
--
preprocess :: Tm -> Tm1
preprocess = go emptyCtx where

  go :: Ctx -> Tm -> Tm1
  go ctx term = case term of

    Var j  -> Var' j

    App {} -> case isApp_ term of
      MkApp fun args -> letFloatApp (go ctx fun) (fmap (go ctx) args) 

    Lam {} -> case isLambda_ ctx term of
      fun@(Fun_ ts ret body) -> 
        let body' = go (ctx <> ts) body
        in Fun' (funTy fun) (Fun_ ts ret body') (Var' (ctxLevel ctx))

    Let t rhs letbody -> case t of
      Arrow _ _ -> case isLambda_ ctx rhs of
        fun@(Fun_ ts ret funbody) -> 
          let funbody' = go (ctx <> ts) funbody
              letbody' = go (ctx |> t ) letbody 
          in  Fun' (funTy fun) (Fun_ ts ret funbody') letbody'
      _ -> Let' t (go ctx rhs) (go (ctx |> t) letbody)

    Rec t@(Arrow _ _) rhs letbody -> case isLambda_ (ctx |> t) rhs of
      fun@(Fun_ ts ret funbody) -> 
        let funbody' = go ((ctx |> t) <> ts) funbody
            letbody' = go ( ctx |> t       ) letbody 
        in  Rec' (funTy fun) (Fun_ ts ret funbody') letbody'
    Rec _ _ _ -> error "preprocess: recursive lets must bind functions!"

    Lit y  -> Lit' y

    Pri op -> Pri' (fmap (go ctx) op)

--------------------------------------------------------------------------------
-- *** find free variables

type FreeM a = State (Set (Level,Ty)) a

type Ignore = Set Level

-- find free variables (those with level less than the threshold)
freeVarSet :: Level -> Ignore -> Ctx -> Tm1 -> Set (Level,Ty)
freeVarSet threshold ignore ctx expr = execState (go ctx expr) Set.empty where

  goVar :: Ctx -> Level -> FreeM ()
  goVar ctx j = if j < threshold && not (Set.member j ignore)
    then modify (Set.insert (j, seqIndex ctx j))
    else return ()

  go :: Ctx -> Tm1 -> State (Set (Level,Ty)) ()
  go ctx expr = case expr of
    Var' j                              -> goVar ctx j
    App' fun args                       -> goVar ctx fun >> mapM_ (go ctx) args
    Let' ty rhs                 letbody -> go  ctx                rhs     >> go (ctx |> ty) letbody
    Fun' ty (MkFun sig funbody) letbody -> go (ctx       |>> sig) funbody >> go (ctx |> ty) letbody
    Rec' ty (MkFun sig recbody) letbody -> go (ctx |> ty |>> sig) recbody >> go (ctx |> ty) letbody
    Pri' prim                           -> mapM_ (go ctx) prim
    Lit' k                              -> return ()

freeVarMap :: Level -> Ignore ->  Ctx -> Tm1 -> (Map Level Level, Seq Ty)
freeVarMap threshold ignore ctx expr = (tbl, tys) where
  set = freeVarSet threshold ignore ctx expr
  lts = Set.toList set :: [(Level,Ty)]
  tbl = Map.fromList $ zip (map fst lts) [0..]
  tys = seqFromList  $ map snd lts

--------------------------------------------------------------------------------
-- *** evaluation

evalTm1 :: Tm1 -> Val
evalTm1 = go emptySeq where

  go :: Env -> Tm1 -> Val
  go env term = case term of
    Var' j           -> seqIndex env j
    App' j xs        -> valApps (go env (Var' j)) (map (go env) (seqToList xs))
    Let' _ rhs body  -> let x = go     env       rhs in go (env |> x) body
    Fun' _ fun body  -> let f = goFun  env       fun in go (env |> f) body
    Rec' _ fun body  -> let f = goFun (env |> f) fun in go (env |> f) body
    Pri' op          -> evalPrimOp $ fmap (go env) op
    Lit' y           -> litToVal y

  goFun :: Env -> Fun Tm1 -> Val
  goFun env (Fun_ args ret body) = worker env (seqToList args) where
    worker env []     = go env body
    worker env (t:ts) = VLam t \x -> worker (env |> x) ts

