
-- | A simple \"preprocessing\" step which ensures that
--
-- * application is always on variables
-- 
-- * @let@-s are separated into value, function and recursive function
--
-- * there are no \"naked\" lambdas (only let-bound ones)
--


{-# LANGUAGE BlockArguments, GADTSyntax, PatternSynonyms, StandaloneDeriving, DeriveFunctor #-}
module CodeGen.Preprocess where

--------------------------------------------------------------------------------

import Control.Monad
import Control.Monad.State.Strict

import qualified Data.Set as Set ; import Data.Set ( Set )
import qualified Data.Map as Map ; import Data.Map ( Map )

import qualified Data.Sequence as Seq ; import Data.Sequence ( Seq , (|>) , (><) )

import AST.Ty
import AST.Term
import AST.Val

import Aux.Misc

--------------------------------------------------------------------------------
-- *** terms after some preprocessing

{-
data Fun expr = MkFun 
  { funSig  :: FunTy 
  , funBody :: expr
  }
  deriving (Eq,Show,Functor)
-}

type    Sig                = FunTy
type    Fun expr           = Lams FunTy expr
pattern MkFun sig body     = MkLams sig body
pattern Fun_ args ret body = MkFun (MkFunTy args ret) body

infixl 5 ><|
(><|) :: Ctx -> [Ty] -> Ctx
(><|) ctx ts = ctx >< Seq.fromList ts

infixl 5 |>>
(|>>) :: Ctx -> FunTy -> Ctx
(|>>) ctx (MkFunTy args _ret) = ctx ><| args

ctxLevel :: Ctx -> Level
ctxLevel = Seq.length

--------------------------------------------------------------------------------

data Tm' where
  Var' :: Level             -> Tm'      -- ^ variable
  Let' :: Ty -> Tm' -> Tm'  -> Tm'      -- ^ let binding of an expression
  Fun' :: Fun Tm'   -> Tm'  -> Tm'      -- ^ let binding of a function
  Rec' :: Fun Tm'   -> Tm'  -> Tm'      -- ^ recursive let binding
  App' :: Level   -> [Tm']  -> Tm'      -- ^ application to a variable
  Pri' :: RawPrim -> [Tm']  -> Tm'
  Lit' :: Literal           -> Tm'
  -- hacks:
  Log' :: String -> Tm'     -> Tm'    -- ^ give name to things for debugging etc
--  Dbg' :: String -> Ty -> Tm' -> Tm' -> Tm'    -- ^ printf debugging support hack

deriving instance Show Tm'

--------------------------------------------------------------------------------

-- | float `let`-s outside of application head:
--
-- > (let x = e' in f) a b c   ~~>    let x = e' in (f a b c)    
--
-- as we use de Bruij *levels*, variables referred in `a`, `b`, `c`... remain unchanged
--
letFloatApp :: Tm' -> [Tm'] -> Tm'
letFloatApp = float where

  float :: Tm' -> [Tm'] -> Tm' 
  float appHead args = case appHead of
    Var' j            -> App' j        args 
    App' j xs         -> App' j (xs ++ args)
    Let' t rhs body   -> Let' t rhs (float body args)
    Fun'   fun body   -> Fun'   fun (float body args)
    Rec'   fun body   -> Rec'   fun (float body args)
    Pri' {}           -> error "preprocess/letFloat: application to a primitive"
    Lit' {}           -> error "preprocess/letFloat: application to a literal"
    Log' n tm         -> Log' n (float tm args)
--    Dbg' n t s tm     -> Dbg' n t (float s args) (float tm args)

--------------------------------------------------------------------------------

-- | This AST preprocessing step simplifies future step by:
--
-- * enfore that application heads are variables
--
-- * eliminate naked lambdas
--
-- * separate let-binding of expressions and functions (and recursive functions)
--
preprocess :: Raw -> Tm'
preprocess = go emptyCtx where

  go :: Ctx -> Raw -> Tm'
  go ctx term = case term of

    Var j  -> Var' j

    App {} -> case isApp_ term of
      MkApps fun args -> letFloatApp (go ctx fun) (map (go ctx) args) 

    Lam {} -> case isLambda_ ctx term of
      fun@(Fun_ ts ret body) -> 
        let body' = go (ctx ><| ts) body
        in Fun' {- (lamsTy fun) -} (Fun_ ts ret body') (Var' (ctxLevel ctx))

    Let t rhs letbody -> case t of
      Arrow _ _ -> case isLambda_ ctx rhs of
        fun@(Fun_ ts ret funbody) -> 
          let funbody' = go (ctx ><| ts) funbody
              letbody' = go (ctx |>  t ) letbody 
          in  Fun' {- (lamsTy fun) -} (Fun_ ts ret funbody') letbody'
      _ -> Let' t (go ctx rhs) (go (ctx |> t) letbody)

    Rec t@(Arrow _ _) rhs letbody -> case isLambda_ (ctx |> t) rhs of
      fun@(Fun_ ts ret funbody) -> 
        let funbody' = go ((ctx |> t) ><| ts) funbody
            letbody' = go ( ctx |> t        ) letbody 
        in  Rec' {- (lamsTy fun) -} (Fun_ ts ret funbody') letbody'
    Rec _ _ _ -> error "preprocess: recursive lets must bind functions!"

    Lit y  -> Lit' y

    Pri rawprim args -> Pri' rawprim (map (go ctx) args)

    Log nam     tm       -> Log' nam               (go ctx tm)
--    Dbg nam t s tm       -> Dbg' nam t (go ctx s ) (go ctx tm)

--------------------------------------------------------------------------------
-- *** find free variables

type FreeM a = State (Set (Level,Ty)) a

type Ignore = Set Level

-- find free variables (those with level less than the threshold)
freeVarSet :: Level -> Ignore -> Ctx -> Tm' -> Set (Level,Ty)
freeVarSet threshold ignore ctx expr = execState (go ctx expr) Set.empty where

  goVar :: Ctx -> Level -> FreeM ()
  goVar ctx j = if j < threshold && not (Set.member j ignore)
    then modify (Set.insert (j, Seq.index ctx j))
    else return ()

  go :: Ctx -> Tm' -> State (Set (Level,Ty)) ()
  go ctx expr = case expr of
    Var' j                              -> goVar ctx j
    App' fun args                       -> goVar ctx fun >> mapM_ (go ctx) args
    Let' ty rhs              letbody    ->                           go  ctx                rhs     >> go (ctx |> ty) letbody
    Fun' (MkFun sig funbody) letbody    -> let ty = fromFunTy sig in go (ctx       |>> sig) funbody >> go (ctx |> ty) letbody
    Rec' (MkFun sig recbody) letbody    -> let ty = fromFunTy sig in go (ctx |> ty |>> sig) recbody >> go (ctx |> ty) letbody
    Pri' rawprim args                   -> mapM_ (go ctx) args
    Lit' k                              -> return ()
    Log' nam tm                         -> go ctx tm
--    Dbg' nam t s tm                     -> go ctx tm

freeVarMap :: Level -> Ignore ->  Ctx -> Tm' -> (Map Level Level, Seq Ty)
freeVarMap threshold ignore ctx expr = (tbl, tys) where
  set = freeVarSet threshold ignore ctx expr
  lts = Set.toList set :: [(Level,Ty)]
  tbl = Map.fromList $ zip (map fst lts) [0..]
  tys = Seq.fromList  $ map snd lts

--------------------------------------------------------------------------------
-- *** evaluation

{-

evalTm' :: Tm1 -> Val
evalTm' = go emptySeq where

  go :: Env -> Tm1 -> Val
  go env term = case term of
    Var' j           -> seqIndex env j
    App' j xs        -> valApps (go env (Var' j)) (map (go env) (seqToList xs))
    Let' _ rhs body  -> let x = go     env       rhs in go (env |> x) body
    Fun'   fun body  -> let f = goFun  env       fun in go (env |> f) body
    Rec'   fun body  -> let f = goFun (env |> f) fun in go (env |> f) body
    Pri' op          -> evalPrimOp $ fmap (go env) op
    Lit' y           -> litToVal y

  goFun :: Env -> Fun Tm1 -> Val
  goFun env (Fun_ args ret body) = worker env (seqToList args) where
    worker env []     = go env body
    worker env (t:ts) = VLam t \x -> worker (env |> x) ts

-}
