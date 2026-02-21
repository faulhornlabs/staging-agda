
-- lambda lifting

{-# LANGUAGE PatternSynonyms, BlockArguments, RecordWildCards, StrictData, DeriveFunctor #-}
module CodeGen.Lifting where

--------------------------------------------------------------------------------

import Data.List
import Data.Maybe

import Control.Applicative
import Control.Monad
import Control.Monad.State.Strict
import System.IO.Unsafe

import qualified Data.Set      as Set ; import Data.Set      ( Set )
import qualified Data.Map      as Map ; import Data.Map      ( Map )
import qualified Data.Sequence as Seq ; import Data.Sequence ( Seq , (<|) , (|>) , (><) )
import qualified Data.Foldable as F

import Text.Show.Pretty ( ppShow , pPrint )

import AST.Ty
import AST.Val
import AST.PrimOp
import AST.IO
import AST.Literal

-- import AST.Term hiding ( Top )
-- import qualified AST.Term
import CodeGen.Preprocess ( Tm'(..) , freeVarMap )

import Aux.Misc

--------------------------------------------------------------------------------

seqToList :: Seq a -> [a]
seqToList = F.toList

seqConcat :: Seq (Seq a) -> Seq a
seqConcat = mconcat . seqToList

--------------------------------------------------------------------------------

type TopIdx = Int

data Variable top
  = Loc Level     -- local variable
  | Top top       -- top-level variable
  deriving (Eq,Show,Functor)

-- After the lifting transformation, @lambda@-s, @letrec@-s and even @let@-s 
-- where the defined value is a function are all eliminated. 
--
-- To simplify things we also eliminate @Log@ and @Dbg@ (which are ugly hacks anyway)
data RawExp' top  where
  VarE :: Variable top                     -> RawExp' top     -- better pretty-printing this way...
  AppE :: Variable top -> [RawExp' top]    -> RawExp' top
  LetE :: Ty -> RawExp' top -> RawExp' top -> RawExp' top
  PriE :: RawPrim -> [RawExp' top]         -> RawExp' top
  LitE :: Literal                          -> RawExp' top
  -- hacks...
--  LogE :: String ->                 RawExp' -> RawExp' -- ^ give name to things for debugging etc
--  DbgE :: String -> Ty -> RawExp' -> RawExp' -> RawExp'  -- ^ printf debugging support
  deriving (Show,Functor)

type RawExp = RawExp' TopIdx

-- pattern VarE v = AppE v []
pattern LocE j = VarE (Loc j)
pattern TopE k = VarE (Top k)

appsE :: Apps (Variable top) (RawExp' top) -> [RawExp' top] -> RawExp' top
appsE (MkApps variable args1) args2 = case (args1 ++ args2) of
  []   -> VarE variable
  args -> AppE variable args

--------------------------------------------------------------------------------

inferTyRawExp :: TopCtx -> Ctx -> RawExp -> Ty
inferTyRawExp topEnv = go where

  goVar :: Ctx -> Variable TopIdx -> Ty
  goVar localEnv var = case var of

    Loc j -> case Seq.lookup j localEnv of 
      Just ty -> ty 
      Nothing -> error $ "inferTyRawExp': local variable " ++ show j ++ " not found in local context"

    Top k -> case Seq.lookup k topEnv of 
      Just ty -> ty 
      Nothing -> error $ "inferTyRawExp': top level variable " ++ show k ++ " not found in top level context"

  go :: Ctx -> RawExp  -> Ty
  go localEnv term = case term of

    VarE v -> goVar localEnv v
    
    LetE t rhs body -> 
      let t' = go localEnv rhs 
      in  if t' == t 
            then go (localEnv |> t) body
            else error $ "inferTyRawExp': inconsistent let binding type: " ++ show t' ++ " vs. " ++ show t

    AppE fun []   -> goVar localEnv fun
    AppE fun args -> case isFunctionTy (goVar localEnv fun) of
      Just (MkFunTy argTys retTy) -> if map (go localEnv) args == argTys 
        then retTy 
        else error "inferTyRawExp': incompatible function (multi-)application"
      _ -> error "inferTyRawExp': application to a non-lambda"

    PriE op args -> primOpTy op (map (go localEnv) args)

    LitE lit -> literalTy lit

--------------------------------------------------------------------------------

{-
instance Pretty Variable where
  pretty (Loc j) = "v" ++ show j
  pretty (Top k) = "f" ++ show k

instance Pretty Raw' where
  prettyPrec d = prettyExp 0 d
-}

{-
prettyRaw' :: Level -> Prec -> Raw' -> ShowS
prettyRaw' = go where

  go :: Level -> Prec -> Raw' -> ShowS
  go level d expr = case expr of

    Lit' k         -> shows k     
    Var' var       -> prettyS var
    App' fun args  -> prettyPrec d (MkApps fun args)
    Pri' op        -> prettyPrec d op

    Let' rhs body  -> showParen (d > let_prec) 
                    $ showString "let "
                    . prettyS (Loc level)
                    . showString " = "
                    . go  level    (let_prec+1) rhs
                    . showString " in "
                    . go (level+1) (let_prec+1) body 
                    
instance Pretty (TopLev, FunDef) where
  pretty (k, MkFunDef n body) = 
    let args = intercalate " " [ "v" ++ show j | j<-[0..n-1] ]
    in  pretty (Top k) ++ " " ++ args ++ " = " ++ pretty body
-}

--------------------------------------------------------------------------------

data FunDef' top expr = MkFunDef
  { _funIdx  :: top                  -- ^ top-level index of the function 
  , _funName :: String               -- ^ name of the function
  , _funBody :: (Lams FunTy expr)    -- ^ function body
  }
  deriving (Show,Functor)

type FunDef = FunDef' TopIdx

-- | type signature of the function
_funType :: FunDef' top expr -> FunTy      
_funType def = case _funBody def of
  MkLams funty _ -> funty

funDefTy :: FunDef' top expr -> Ty
funDefTy = fromFunTy . _funType

data Program' def main
  = MkProgram (Seq def) main
  deriving Show
  
type Program expr = Program' (FunDef expr) expr

{-
instance Pretty (Prog FunDef Exp) where
  pretty (MkProg topEnv main) = unlines (defs ++ [body]) where
    defs = map pretty $ zip [(0::TopLev)..] (seqToList topEnv)
    body = "main = " ++ pretty main
-}

printFunDefWith :: (idx -> String) -> (a -> String) -> FunDef' idx a -> IO ()
printFunDefWith userShowIdx userShow (MkFunDef idx name (MkLams (MkFunTy argsTy retTy) body)) = do
  putStrLn $ "\n" ++ userShowIdx idx ++ ": def " ++ show name
  putStrLn $ " :: " ++ show argsTy ++ " -> " ++ show retTy
  putStrLn $ " = "
  putStrLn (userShow body)

printFunDef :: (Show idx, Show a) => FunDef' idx a -> IO ()
printFunDef = printFunDefWith show show

printProgramWith :: (a -> String) -> Program a -> IO ()
printProgramWith userShow (MkProgram tops main) = do
  mapM_ (printFunDefWith show userShow) (F.toList tops)
  putStrLn ""
  putStrLn (userShow main)

printProgram :: Show a => Program a -> IO ()
printProgram = printProgramWith ppShow -- show

--------------------------------------------------------------------------------
-- ** naming convention matching...

type Tm      = Tm'
type Exp     = RawExp'  TreeIdx
type FunDef_ = FunDef' TreeIdx Exp
type Ignore  = Set Level
type Fun a   = Lams FunTy a

pattern MkFun sig body = MkLams sig body

--------------------------------------------------------------------------------
-- * replace tree indexing with flat array indexing

type FunDefRaw top = FunDef' top (RawExp' top)
type Prog'     top = Program' (FunDefRaw top) (RawExp' top)

replaceTreeIdxs :: Prog' TreeIdx -> Prog' TopIdx
replaceTreeIdxs (MkProgram oldSeq oldMain) = MkProgram newSeq newMain where

  oldIdxs = [ _funIdx funDef | funDef <- seqToList oldSeq ]
  table   = Map.fromList $ zip oldIdxs [0..]

  newSeq  = fmap mapFunDef oldSeq
  newMain = fmap h oldMain
 
  mapFunDef (MkFunDef    idx  name (MkLams sig         body )) = 
             MkFunDef (h idx) name (MkLams sig (fmap h body))

  h :: TreeIdx -> TopIdx
  h old = case Map.lookup old table of
    Just new -> new
    Nothing  -> error "replaceTreeIdxs: should not happen"

--------------------------------------------------------------------------------
-- ** replacing variables

data Replacement
  = VarR Level
  | AppR (Apps TreeIdx Level)
  deriving Show

pattern AppR_ idx args = AppR (MkApps idx args)

replaceVars :: (Level -> Replacement) -> Exp -> Exp
replaceVars replace = go where

  goVar :: Variable TreeIdx -> Replacement
  goVar var = case var of 
    Loc j -> replace j
    Top k -> AppR_ k []

  go :: Exp -> Exp
  go (LetE t r b) = LetE t (go r) (go b)
  go (PriE op as) = PriE op (map go as)
  go (LitE k    ) = LitE k
  go (AppE f xs ) = case goVar f of
    VarR  j           -> AppE  (Loc j)                  (map go xs)
    AppR_ k args      -> AppE  (Top k) (map LocE args ++ map go xs)
  go (VarE v    ) = case goVar v of
    VarR  j           -> VarE  (Loc j) 
    AppR_ k args      -> AppE  (Top k) (map LocE args)

fromCapture :: Capture -> Exp
fromCapture (MkApps k captured) = AppE (Top k) (map LocE captured)

{-
data Replace a b 
  = a :~> b
  deriving Show

replaceVar :: Replace Level Exp -> Exp -> Exp
replaceVar (old :~> new) = replaceVar' (\j -> if j == old then new else Loc' j)

replaceVarFunDef :: Replace Level Exp -> FunDef_ -> FunDef_
replaceVarFunDef replace (MkFunDef i n (MkLams fty body)) = 
                          MkFunDef i n (MkLams fty $ replaceVar replace body)
-}

--------------------------------------------------------------------------------
-- *** lambda-lift monad

-- REVERSE ORDER!
type TreeIdx = [Int]

treeIdxToIdentPostfix :: TreeIdx -> String
treeIdxToIdentPostfix treeidx = intercalate "_" (map show $ reverse treeidx)

type Stack a 
  = Seq (Node a)

data Node a 
  = Leaf a 
  | Node a (Stack a)
  deriving Show

-- NOTE! sub-stacks come _before_ the entry!
flattenStack :: Stack a -> Seq a
flattenStack = goSeq where

  goSeq :: Seq (Node a) -> Seq a
  goSeq xs = seqConcat (fmap goNode xs)

  goNode :: Node a -> Seq a
  goNode node = case node of
    Leaf a     -> Seq.singleton a
    Node a sub -> goSeq sub |> a

type Def = FunDef_

type LiftM a = StateT [Stack Def] IO a
-- type LiftM a = State [Stack Def] a

emptySeq  = Seq.empty
seqLength = Seq.length

initialState :: [Stack Def]
initialState = [emptySeq]

{-
addTopLevel :: (TreeIdx -> LiftM (Def,a)) -> LiftM a
addTopLevel user = do
  stack@(this:rest) <- get
  let ks = map seqLength stack
  (new, out) <- user ks
  let this' = this |> Leaf new
  put (this':rest)
  return out
-}

-- State monad is not MonadFail, hence this hackety hack
getHeadTail :: LiftM (Stack Def, [Stack Def])
getHeadTail = do
  list <- get
  case list of
    []          -> error "LiftM/getHeadTail: empty"
    (this:rest) -> return (this, rest)

enter :: (TreeIdx -> LiftM (Def,a)) -> LiftM a
enter user = do
  (this,rest) <- getHeadTail
  let stack = (this:rest)
  let ks = map seqLength stack
  put (emptySeq:stack)
  (new, out) <- user ks
  (inner, outer) <- getHeadTail
  case outer of 
    []          -> error "LiftM/enter: fatal: should not happen"
    (this:rest) -> do
      let this' = this |> Node new inner
      put (this':rest)
      return out

----------------------------------------

-- when we lift something to top-level, when we call it later, 
-- we also need to apply the captured variables from the environment
type Capture = Apps TreeIdx Level

type TopCtx = Ctx 

-- is it true that `ignore` is always the keys of `table` ?
data LiftCtx = MkLiftCtx
  { ctx    :: Ctx                  -- ^ the usual context
  , table  :: Map Level Capture    -- ^ we replace a let-bound function by a top-level partial application
  }
  deriving Show

emptyLiftCtx :: LiftCtx
emptyLiftCtx = MkLiftCtx
  { ctx    = emptyCtx
  , table  = Map.empty 
  }

----------------------------------------

-- information when dealing with function bodies 
data FunInfo = MkFunInfo 
  { _level    :: Level
  , _nfree    :: Arity
  , _freeMap  :: Map Level Level
  , _table    :: Map Level Capture
  , _newSig   :: FunTy
  , _innerCtx :: Ctx
  , _replace  :: Replacement
  }
  deriving Show

funBodyInfo :: LiftCtx -> Maybe Ty -> FunTy -> TreeIdx -> Tm -> FunInfo
funBodyInfo liftCtx@(MkLiftCtx{..}) mbRecTy (MkFunTy ctxArgs ret) topidx funbody = info where
  level  = Seq.length ctx
  middle = case mbRecTy of { Nothing -> Seq.empty ; Just ty -> Seq.singleton ty }
  ctx'   = ctx <> middle <> (Seq.fromList ctxArgs)
  ignore = Map.keysSet table 
  (free, freeTys) = freeVarMap level ignore ctx' funbody
  nfree  = Seq.length freeTys
  args'  = seqToList freeTys ++ ctxArgs
  this   = MkApps topidx (Map.keys free)
  repl   = AppR this
  table' = Map.insert level this table
  sig'   = MkFunTy args' ret
  info   = MkFunInfo level nfree free table' sig' ctx' repl

----------------------------------------

{-# NOINLINE lambdaLift #-}
lambdaLift :: Tm -> Prog' TopIdx
-- lambdaLift = replaceTreeIdxs . lambdaLift' 
lambdaLift tm = unsafePerformIO (replaceTreeIdxs <$> lambdaLift' tm)

{-# NOINLINE lambdaLift' #-}
lambdaLift' :: Tm -> IO (Prog' TreeIdx)
lambdaLift' lambdaTerm = program where

  program :: IO (Prog' TreeIdx) 
  program = do
    (main,topstack) <- runStateT (go emptyLiftCtx lambdaTerm) initialState
    case topstack of
      [stack] -> return $ MkProgram (flattenStack stack) main 
      _       -> error "lambdaLift: fatal: expecting a single final stack"

  goVar :: LiftCtx -> Level -> Apps (Variable TreeIdx) Exp
  goVar liftCtx@(MkLiftCtx{..}) j = 
   case Map.lookup j table of
      Nothing               -> MkApps (Loc j ) []
      Just (MkApps ks args) -> MkApps (Top ks) (map LocE args)

  fromApps :: Apps (Variable TreeIdx) Exp -> Exp
  fromApps (MkApps var args) = case args of
    [] -> VarE var
    _  -> AppE var args

  go :: LiftCtx -> Tm -> LiftM Exp
  go = go' Nothing

  go' :: Maybe String -> LiftCtx -> Tm -> LiftM Exp
  go' mbName liftCtx@(MkLiftCtx{..}) term = case term of

    Var' j -> return $ fromApps (goVar liftCtx j)

    Let' ty rhs body -> do
      let liftCtx' = MkLiftCtx (ctx |> ty) table
      rhs'  <- go liftCtx  rhs        
      body' <- go liftCtx' body
      return (LetE ty rhs' body')

    Fun' fun body -> do
      let name = maybe "fun" id mbName
      liftCtx' <- goLam name liftCtx  fun    
      body'    <- go         liftCtx' body
      return body'

    Rec' fun body -> do
      let name = maybe "rec" id mbName
      liftCtx' <- goRec name liftCtx  fun  
      body'    <- go         liftCtx' body
      return body'

    App' j args -> do
      let fun' = goVar liftCtx j
      args' <- mapM (go liftCtx) args
      return $ appsE fun' args'

    Pri' op args -> PriE op <$> mapM (go liftCtx) args

    Lit' k  -> return (LitE k)

    Log' n y -> go' (Just n) liftCtx y
--    Dbg' n t x y -> go liftCtx y


  --
  -- given something like
  --
  --   ... let a = ... in let b = ... in \x y z -> (... a ... b ...)
  --                                     |
  --                                     ^ we are here
  --
  -- we want to lift that tha lambda into toplevel:
  --
  --   top a' b' x y z = (... a' ... b' ... ) 
  --
  -- and wherever this lambda appeared needs to be replaced by `top a b`
  --
  goLam :: String -> LiftCtx -> Fun Tm -> LiftM LiftCtx
  goLam name liftCtx@(MkLiftCtx{..}) (MkFun funsig funbody) = enter $ \idx -> do

    let name'  = name ++ "_" ++ treeIdxToIdentPostfix idx
    let funTy  = fromFunTy funsig
    let info@(MkFunInfo{..}) = funBodyInfo liftCtx Nothing funsig idx funbody
    body' <- go (MkLiftCtx _innerCtx table) funbody     -- NOTE!!! we NEED the OLD table here!!!

    let replace :: Level -> Replacement
        replace j = case Map.lookup j _freeMap of
          Just new  -> VarR new
          Nothing   -> if j >= _level
            then VarR (j - _level + _nfree)
            else error "lambdaLift/goLam: undetected free variable (shouldn't happen)"

    let liftCtx' = MkLiftCtx (ctx |> funTy) _table
    let fun'     = MkLams _newSig (replaceVars replace body')
    let def      = MkFunDef idx name' fun'
    return (def, liftCtx')

  -- this is like `goLam`, but more tricky. We must remove the recursive argument
  -- and replace its occurences (in the body of the recursive function) with the new 
  -- top-level variable, applied to the captured variables, also in the function nody
  -- 
  goRec :: String -> LiftCtx -> Fun Tm -> LiftM LiftCtx
  goRec name liftCtx@(MkLiftCtx{..}) (MkFun funsig funbody) = enter $ \idx -> do

    let name'  = name ++ "_" ++ treeIdxToIdentPostfix idx
    let recTy  = fromFunTy funsig
    let MkFunInfo{..} = funBodyInfo liftCtx (Just recTy) funsig idx funbody
    body' <- go (MkLiftCtx _innerCtx _table) funbody

    let replace :: Level -> Replacement
        replace = go where
          
          shift :: Level -> Level
          shift j = j - 1 - _level + _nfree

          go :: Level -> Replacement
          go j = case Map.lookup j _freeMap of
            Just new              -> VarR new
            Nothing | j >  _level -> VarR (shift j)
            Nothing | j == _level -> case _replace of { AppR_ top args -> AppR_ top (map shift args) }   -- !!!!
            Nothing | j <  _level -> error "lambdaLift/goRec: undetected free variable (shouldn't happen)"

    let liftCtx' = MkLiftCtx (ctx |> recTy) _table
    let fun'     = MkLams _newSig (replaceVars replace body')
    let def      = MkFunDef idx name' fun'
    return (def, liftCtx')

--------------------------------------------------------------------------------

