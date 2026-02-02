
{-# LANGUAGE BlockArguments, GADTSyntax, PatternSynonyms, 
      StandaloneDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable 
#-}

module Lift where

--------------------------------------------------------------------------------

import Control.Monad
import Control.Monad.State.Strict

import qualified Data.Set as Set ; import Data.Set ( Set )
import qualified Data.Map as Map ; import Data.Map ( Map )

import Seq
import Common
import Preprocess 
import Val

--------------------------------------------------------------------------------

data Def 
  = MkDef TopIdx (Fun Exp)
  deriving Show

data Prg = MkPrg 
  { topDefs :: Seq Def
  , mainExp :: Exp 
  }
  deriving Show

data Call 
  = TopC TopIdx     -- calling a top-level function
  | VarC Level      -- calling a lambda-bound variable (in a higher-order function)
  deriving Show
 
data Exp where
  VarE :: Level              -> Exp
  AppE :: Apply Call Exp     -> Exp
  LetE :: Ty -> Exp -> Exp   -> Exp
  PriE :: PrimOp Exp         -> Exp
  LitE :: Literal            -> Exp

deriving instance Show Exp

pattern AppE_ top args = AppE (MkApp top args)

--------------------------------------------------------------------------------

{-
-- find free variables (those with level less than the threshold)
freeVarSet :: Level -> Ctx -> Exp -> Set (Level,Ty)
freeVarSet threshold ctx expr = execState (go ctx expr) Set.empty where

  go :: Ctx -> Exp -> State (Set (Level,Ty)) ()
  go ctx expr = case expr of
    VarE j -> if j < threshold 
                then modify (Set.insert (j, seqIndex ctx j))
                else return ()
    LetE  ty rhs body -> go ctx rhs >> go (ctx |> ty) body
    AppE_ top args    -> mapM_ (go ctx) args
    PriE  prim        -> mapM_ (go ctx) prim
    LitE  k           -> return ()

freeVarMap :: Level -> Ctx -> Exp -> (Map Level Level, Seq Ty)
freeVarMap threshold ctx expr = (tbl, tys) where
  set = freeVarSet threshold ctx expr
  lts = Set.toList set :: [(Level,Ty)]
  tbl = Map.fromList $ zip (map fst lts) [0..]
  tys = seqFromList  $ map snd lts
-}

--------------------------------------------------------------------------------

type Capture = Apply TopIdx Level

fromApps :: Capture -> Exp
fromApps (MkApp k captured) = AppE (MkApp (TopC k) (fmap VarE captured))

reApply :: Apply fun arg -> Seq arg -> Apply fun arg
reApply (MkApp f xs) ys = MkApp f (xs <> ys)

reApplyRepl :: Replacement -> Seq Exp -> Exp
reApplyRepl repl ys = case repl of
  VarR  j      -> AppE_ (VarC j  )                  ys
  AppR_ top xs -> AppE_ (TopC top) (fmap VarE xs <> ys)

data Replace a b 
  = a :~> b
  deriving Show

data Replacement
  = VarR Level
  | AppR (Apply TopIdx Level)
  deriving Show

pattern AppR_ fun arg = AppR (MkApp fun arg)

captureToReplacement :: Capture -> Replacement
captureToReplacement (MkApp top js) = AppR (MkApp top js)

fromReplacement :: Replacement -> Exp
fromReplacement = go where
  go (VarR  j)      = VarE j
  go (AppR_ top xs) = AppE_ (TopC top) (fmap VarE xs)

replaceVar' :: (Level -> Replacement) -> Exp -> Exp
replaceVar' replace = go where

  goVar :: Level -> Exp
  goVar j = fromReplacement (replace j)

  go :: Exp -> Exp
  go (VarE  j    ) = goVar j
  go (AppE_ f ys ) = case f of
    TopC _ -> AppE_ f (fmap go ys)
    VarC j -> case replace j of
      VarR  j      -> AppE_ (VarC j) (fmap go ys)
      AppR_ top xs -> AppE $ reApply (MkApp (TopC top) (fmap goVar xs)) (fmap go ys)

  go (LetE  s r b) = LetE s (go r) (go b)
  go (PriE  op   ) = PriE (fmap go op)
  go (LitE  k    ) = LitE k

replaceVar :: Replace Level Replacement -> Exp -> Exp
replaceVar (old :~> new) = replaceVar' (\j -> if j == old then new else VarR j)

--------------------------------------------------------------------------------

-- REVERSE ORDER!
type TopIdx = [Int]

type Stack a 
  = Seq (Node a)

data Node a 
  = Leaf a 
  | Node a (Stack a)
  deriving Show

-- NOTE! sub-stacks come _before_ the entry!
flattenStack :: Stack a -> Seq a
flattenStack = goSeq where

  goSeq xs = seqJoin (fmap goNode xs)

  goNode node = case node of
    Leaf a     -> seqSingleton a
    Node a sub -> goSeq sub |> a

type LiftM a = StateT [Stack Def] IO a

initialState :: [Stack Def]
initialState = [emptySeq]

addTopLevel :: (TopIdx -> LiftM (Def,a)) -> LiftM a
addTopLevel user = do
  stack@(this:rest) <- get
  let ks = map seqLength stack
  (new, out) <- user ks
  let this' = this |> Leaf new
  put (this':rest)
  return out

enter :: (TopIdx -> LiftM (Def,a)) -> LiftM a
enter user = do
  stack@(this:rest) <- get
  let ks = map seqLength stack
  put (emptySeq:stack)
  (new, out) <- user ks
  (inner:this:rest) <- get
  let this' = this |> Node new inner
  put (this':rest)
  return out

--------------------------------------------------------------------------------

type Translation = Map Level Replacement

-- translate :: Translation -> Tm1 -> Tm' 
-- translate

data Info = MkInfo 
  { _nfree    :: Arity
  , _freeMap  :: Map Level Level
  , _table    :: Translation
  , _newSig   :: Sig
  , _innerCtx :: Ctx
  , _replace  :: Replacement
  }
  deriving Show

lambdaLift :: Tm1 -> IO Prg
lambdaLift lambdaTerm = prg where

  prg :: IO Prg
  prg = do
    (main,topstack) <- runStateT (go emptySeq Map.empty lambdaTerm) initialState
    case topstack of
      [stack] -> return $ MkPrg (flattenStack stack) main 
      _       -> error "lambdaLift: fatal: expecting a single final stack"

  goFunBody :: (Ctx, Seq Ty, Seq Ty) -> Translation -> TopIdx -> Ty -> Tm1 -> Info
  goFunBody (ctx, ctxRec, ctxArgs) table idx ret funbody = info where
    level  = seqLength ctx
    ctx'   = ctx <> ctxRec <> ctxArgs
    ignore = Map.keysSet table 
    (free, freeTys) = freeVarMap level ignore ctx' funbody
    nfree  = seqLength freeTys
    args'  = freeTys <> ctxArgs
    this   = MkApp idx (seqFromList $ Map.keys free)
    repl   = captureToReplacement this
    table' = Map.insert level repl table
    sig'   = MkSig args' ret
    info   = MkInfo nfree free table' sig' ctx' repl

  goLam :: Ctx -> Translation -> Fun Tm1 -> LiftM Translation
  goLam ctx table (Fun_ args ret body) = addTopLevel $ \topIdx -> do

    let ctxTriple = (ctx, emptySeq, args)
    let MkInfo nfree free table' sig' ctx' _repl = goFunBody ctxTriple table topIdx ret body 

    body' <- go ctx' table' body

    let level = seqLength ctx

    let replace :: Level -> Replacement
        replace j = case Map.lookup j free of
          Just new  -> VarR new
          Nothing   -> if j >= level
            then VarR (j - level + nfree)
            else error "lambdaLift/goLam: undetected free variable (shouldn't happen)"

    let fun = MkFun sig' (replaceVar' replace body')
    return (MkDef topIdx fun, table')

  -- this is like `goLam`, but more tricky. We must remove the recursive argument
  -- and replace its occurences with the new top-level variable, applied to 
  -- the local names of the captured variables
  goRec :: Ctx -> Ty -> Translation -> Fun Tm1 -> LiftM Translation
  goRec ctx recurseTy table (Fun_ args ret body) = enter $ \recIdx -> do

    let ctxTriple = (ctx, seqSingleton recurseTy, args)
    let MkInfo nfree free table' sig' ctx' repl = goFunBody ctxTriple table recIdx ret body 

    body' <- go ctx' table' body

    let level = seqLength ctx

    let replace :: Level -> Replacement
        replace = go where
          go :: Level -> Replacement
          go j = case Map.lookup j free of
            Just new             -> VarR new
            Nothing | j >  level -> VarR (j - 1 - level + nfree)
            Nothing | j == level -> repl -- AppR_ top (fmap translate args)           -- !!!! 
            Nothing | j <  level -> error $ "lambdaLift/goRec: undetected free variable (shouldn't happen)"

    let fun = MkFun sig' (replaceVar' replace body')
    return (MkDef recIdx fun, table')

  goVar' :: Ctx -> Translation -> Level -> Replacement
  goVar' ctx table j = case Map.lookup j table of
    Nothing   -> VarR j
    Just repl -> repl

  goVar :: Ctx -> Translation -> Level -> Exp
  goVar ctx table j = fromReplacement (goVar' ctx table j)

  go :: Ctx -> Translation -> Tm1 -> LiftM Exp
  go ctx table term = let level = seqLength ctx in case term of

    Var' j -> return $ goVar ctx table j

    App' j args -> do
      let fun' = goVar'   ctx table  j
      args'   <- mapM (go ctx table) args
      return $ reApplyRepl fun' args' 

    Let' s rhs body -> do
      rhs'  <- go  ctx       table rhs
      body' <- go (ctx |> s) table body
      return (LetE s rhs' body')

    Fun' s fun body -> do
      table' <- goLam  ctx       table  fun  
      body'  <- go    (ctx |> s) table' body
      return body'

    Rec' s fun body -> do
      table' <- goRec  ctx    s  table  fun  
      body'  <- go    (ctx |> s) table' body
      return body'

    Pri' op -> PriE <$> mapM (go ctx table) op

    Lit' x  -> return $ LitE x
  
--------------------------------------------------------------------------------
-- *** evaluation

evalPrg :: Prg -> Val
evalPrg (MkPrg defins mainExp) = evalExp topEnv mainExp where
  topEnv = Map.fromList [ (idx,fun) | MkDef idx fun <- seqToList defins ]

type TopEnv = Map TopIdx (Fun Exp)

evalExp :: TopEnv -> Exp -> Val
evalExp topEnv = go emptySeq where

  goFun :: Fun Exp -> Val
  goFun (Fun_ args ret body) = worker emptySeq (seqToList args) where
    worker env []     = go env body
    worker env (t:ts) = VLam t \x -> worker (env |> x) ts

  go :: Env -> Exp -> Val
  go locEnv expr = case expr of

    VarE j -> seqIndex locEnv j

    AppE_ f args -> 
      let fun = case f of
            Lift.VarC j -> seqIndex locEnv j
            Lift.TopC i -> goFun ((Map.!) topEnv i)
      in valApps fun (map (go locEnv) $ seqToList args) 

    LetE _ rhs body -> let x = go locEnv rhs in go (locEnv |> x) body

    PriE op -> evalPrimOp $ fmap (go locEnv) op
    LitE y  -> litToVal y

--------------------------------------------------------------------------------
