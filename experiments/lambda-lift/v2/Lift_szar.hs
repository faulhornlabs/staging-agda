
{-# LANGUAGE GADTSyntax, PatternSynonyms, StandaloneDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module Lift where

--------------------------------------------------------------------------------

import Control.Monad
import Control.Monad.State.Strict

import qualified Data.Set as Set ; import Data.Set ( Set )
import qualified Data.Map as Map ; import Data.Map ( Map )

import System.IO.Unsafe

import Seq
import Common
import Preprocess ( Tm'(..) )

--------------------------------------------------------------------------------

data Prg = MkPrg 
  { topDefs :: Seq (Fun Exp) 
  , mainExp :: Exp 
  }
  deriving Show

--
-- we need this for two reasons:
--
-- * higher order function can call their arguments (out of scope for lambda lifting)
-- * during lambda-lifting recursive function, there is a temporary state where
--   the recursive argment is not yet replaced
--

data Call 
  = TopC Top      -- calling a top-level function
  | VarC Level    -- calling a lambda-bound thing
  | RecC Level    -- calling a recursive function which isn't yet lifted
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

-- find free variables (those with level less than the threshold)
freeVarSet :: Level -> LiftCtx -> Exp -> Set (Level,Ty)
freeVarSet threshold ctx expr = execState (go ctx expr) Set.empty where

  go :: LiftCtx -> Exp -> State (Set (Level,Ty)) ()
  go ctx expr = case expr of
    VarE j -> if j < threshold 
                then modify (Set.insert (j, entryTy (seqIndex ctx j))) 
                else return ()
    LetE  ty rhs body -> go ctx rhs >> go (ctx |> LetEntry ty) body
    AppE_ top args    -> mapM_ (go ctx) args
    PriE  prim        -> mapM_ (go ctx) prim
    LitE  k           -> return ()

freeVarMap :: Level -> LiftCtx -> Exp -> (Map Level Level, Seq Ty)
freeVarMap threshold ctx expr = (tbl, tys) where
  set = freeVarSet threshold ctx expr
  lts = Set.toList set :: [(Level,Ty)]
  tbl = Map.fromList $ zip (map fst lts) [0..]
  tys = seqFromList  $ map snd lts

--------------------------------------------------------------------------------

type Capture = Apply Top Level

fromApps :: Capture -> Exp
fromApps (MkApp k captured) = AppE (MkApp (TopC k) (fmap VarE captured))

reApply :: Apply fun arg -> Seq arg -> Apply fun arg
reApply (MkApp f xs) ys = MkApp f (xs <> ys)

data Replace a b 
  = a :~> b
  deriving Show

data Replacement
  = VarR Level
  | RecR Level
  | AppR (Apply Top Level)
  deriving Show

pattern AppR_ fun arg = AppR (MkApp fun arg)

captureToReplacement :: Capture -> Replacement
captureToReplacement (MkApp top js) = AppR (MkApp top js)

fromReplacement :: Replacement -> Exp
fromReplacement = go where
  go (VarR  j)      = VarE j
  go (RecR  j)      = AppE_ (RecC j  ) emptySeq
  go (AppR_ top xs) = AppE_ (TopC top) (fmap VarE xs)

replaceVar' :: (Level -> Replacement) -> Exp -> Exp
replaceVar' replace = go where
  goLev :: Level -> Exp
  goLev j = fromReplacement (replace j)

  go :: Exp -> Exp
  go (VarE  j    ) = fromReplacement (replace j) 
  go (AppE_ f ys ) = case f of
    TopC _ -> AppE_ f (fmap go ys)
    RecC _ -> AppE_ f (fmap go ys)
    VarC j -> case replace j of
      VarR j       -> AppE_ (VarC j) (fmap go ys)
      AppR_ top xs -> AppE $ reApply (MkApp (TopC top) (fmap goLev xs)) (fmap go ys)

  go (LetE  s r b) = LetE s (go r) (go b)
  go (PriE  op   ) = PriE (fmap go op)
  go (LitE  k    ) = LitE k

replaceVar :: Replace Level Replacement -> Exp -> Exp
replaceVar (old :~> new) = replaceVar' (\j -> if j == old then new else VarR j)

-- hackety hack
replaceRec :: Level -> Apply Top Level -> Exp -> Exp
replaceRec origRecLevel (MkApp top args) = go where

  go :: Exp -> Exp
  go (VarE  j    ) = VarE j
  go (AppE_ f ys ) = case f of
    TopC _ -> AppE_ f (fmap go ys)
    VarC _ -> AppE_ f (fmap go ys)
    RecC r -> if r == origRecLevel
      then AppE_ (TopC top) (fmap VarE args <> fmap go ys)
      else AppE_ f (fmap go ys)
 
  go (LetE  s r b) = LetE s (go r) (go b)
  go (PriE  op   ) = PriE (fmap go op)
  go (LitE  k    ) = LitE k

--------------------------------------------------------------------------------

type LiftM a = StateT (Seq (Fun Exp)) IO a

newTopLevel :: (Top -> Fun Exp) -> LiftM Top
newTopLevel what = do
  old <- get
  let n = seqLength old
  put (old |> what n)
  return n

--------------------------------------------------------------------------------

-- debugging
checkHigherOrder :: Seq Ty -> LiftM () 
checkHigherOrder argSeq = do
  let args = seqToList argSeq
  forM_ (zip [0..] args) $ \(i,ty) -> if isArrow ty 
    then error $ "checkHigherOrder: higher order argument in:\n" ++ unlines (map ("  " ++) $ map showTy args)
    else return () 

--------------------------------------------------------------------------------

data CtxEntry 
  = TopEntry Ty Capture     -- top-level
  | LetEntry Ty             -- let-bound
  | ArgEntry Ty             -- bound by a lambda
  | RecEntry Ty             -- recursive call
  deriving Show

entryTy :: CtxEntry -> Ty
entryTy (TopEntry ty _) = ty
entryTy (LetEntry ty  ) = ty
entryTy (ArgEntry ty  ) = ty
entryTy (RecEntry ty  ) = ty

type LiftCtx = Seq CtxEntry

lambdaLift :: Tm' -> IO Prg
lambdaLift lambdaTerm = prg where

  prg = do
    (main,tops) <- runStateT (go emptySeq lambdaTerm) emptySeq  
    return $ MkPrg tops main 
  
  goLam :: LiftCtx -> Fun Tm' -> LiftM Capture
  goLam ctx (Fun_ args ret body) = do
    checkHigherOrder args
    let ctx' = ctx <> (fmap ArgEntry args)
    body' <- go ctx' body
    let level = seqLength ctx
    let (free, freeTys) = freeVarMap level ctx' body'
    let nfree = seqLength freeTys
    let args' = freeTys <> args

    let replace :: Level -> Replacement
        replace j = case Map.lookup j free of
          Just new  -> VarR new
          Nothing   -> if j >= level
            then VarR (j - level + nfree)
            else error "lambdaLift/goLam: undetected free variable (shouldn't happen)"

    i <- newTopLevel $ \i -> 
        let sig'   = MkSig args' ret
            body'' = replaceVar' replace body'
        in  MkFun sig' body''

    return (MkApp i (seqFromList $ Map.keys free))

  -- this is like `goLam`, but more tricky. We must remove the recursive argument
  -- and replace its occurences with the new top-level variable, applied to 
  -- the local names of the captured variables
  goRec :: LiftCtx -> Ty -> Fun Tm' -> LiftM Capture
  goRec ctx recurseTy (Fun_ args ret body) = do
    checkHigherOrder args
    let level = seqLength ctx
    let ctx'  = ctx <> (RecEntry recurseTy <| fmap ArgEntry args)
    body' <- go ctx' body
    let (free, freeTys) = freeVarMap level ctx' body'
    let nfree = seqLength freeTys
    let args' = freeTys <> args

    let translate j = (Map.!) free j 

    let replace :: Capture -> Level -> Replacement
        replace (MkApp top args) = go where
          go :: Level -> Replacement
          go j = case Map.lookup j free of
            Just new             -> VarR  new
            Nothing | j >  level -> VarR  (j - 1 - level + nfree)
            Nothing | j == level -> AppR_ top (fmap translate args)           -- !!!! 
            Nothing | j <  level -> RecR j  -- cannot be anything else??
{-            
              let debugMsg = unlines
                    [ "- ctx    = " ++ show ctx 
                    , "- level  = " ++ show level
                    , "- rec ty = " ++ showTy recurseTy
                    , "- j      = " ++ show j
                    ]
              in  error $ "lambdaLift/goRec: undetected free variable (shouldn't happen)\n" ++ debugMsg
-}

    let thisApps i = MkApp i (seqFromList $ Map.keys free)
    i <- newTopLevel $ \i -> 
      let sig'   = MkSig args' ret
          body'' = replaceRec level (thisApps i) $ replaceVar' (replace (thisApps i)) body'
      in  MkFun sig' body''

    return (thisApps i)

  go :: LiftCtx -> Tm' -> LiftM Exp
  go ctx term = do
   liftIO $ print ctx
   liftIO $ print term
   case term of

    Var' j -> return $ case seqIndex ctx j of
--      TopEntry _ty apps -> fromApps apps
--      RecEntry _ty      -> AppE_ (VarC j) emptySeq
      LetEntry _ty      -> VarE j
      ArgEntry _ty      -> VarE j

    App' (MkApp j args) -> do
      args' <- mapM (go ctx) args
      return $ case seqIndex ctx j of
        TopEntry _ty (MkApp top js) -> AppE $ reApply (MkApp (TopC top) (fmap VarE js)) args'
        ArgEntry _ -> AppE_ (VarC j) args'
        RecEntry _ -> AppE_ (RecC j) args'
        LetEntry s -> error $ "lambdaLift/go: application to something which is not a function\n > " ++ show j ++ " : " ++ showTy s

    Let' s rhs body -> do
      liftIO $ print (showTy s) 
      rhs'  <- go  ctx                rhs
      body' <- go (ctx |> LetEntry s) body
      return (LetE s rhs' body')

    Fun' s fun body -> do
      apps  <- goLam  ctx                     fun
      body' <- go    (ctx |> TopEntry s apps) body
      let level = seqLength ctx
      return $ replaceVar (level :~> captureToReplacement apps) body'

    Rec' s fun body -> do
      apps  <- goRec  ctx             s       fun
      body' <- go    (ctx |> TopEntry s apps) body
      let level = seqLength ctx
      return $ replaceVar (level :~> captureToReplacement apps) body'

    Pri' op -> PriE <$> mapM (go ctx) op

    Lit' x  -> return $ LitE x
    

--------------------------------------------------------------------------------
