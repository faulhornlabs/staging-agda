
-- lambda-lifting

{-# LANGUAGE PatternSynonyms, BlockArguments #-}
module Lift where

--------------------------------------------------------------------------------

import Data.Kind
import Data.List

import Text.Show

import Control.Applicative
import Control.Monad
import Control.Monad.State

-- debugging
import System.IO.Unsafe      

import qualified Data.Set      as Set ; import Data.Set      ( Set )
import qualified Data.Map      as Map ; import Data.Map      ( Map )
import qualified Data.Sequence as Seq ; import Data.Sequence ( Seq , (|>) )
import qualified Data.Foldable

import Shared
import Term

--------------------------------------------------------------------------------

seqToList :: Seq a -> [a]
seqToList = Data.Foldable.toList

--------------------------------------------------------------------------------

data Variable
  = Loc Level     -- local variable
  | Top TopLev    -- top-level variable
  deriving (Eq,Show)

data Exp where
  Var' :: Variable      -> Exp
  App' :: Exp -> [Exp]  -> Exp
  Let' :: Exp -> Exp    -> Exp
  Pri' :: PrimOp Exp    -> Exp
  Lit' :: Int           -> Exp
  deriving Show

pattern Loc' j = Var' (Loc j)
pattern Top' k = Var' (Top k)

--------------------------------------------------------------------------------

instance Pretty Variable where
  pretty (Loc j) = "v" ++ show j
  pretty (Top k) = "f" ++ show k

instance Pretty Exp where
  prettyPrec d = prettyExp 0 d

prettyExp :: Level -> Prec -> Exp -> ShowS
prettyExp = go where

  go :: Level -> Prec -> Exp -> ShowS
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

--------------------------------------------------------------------------------

data Prog def main
  = MkProg (Seq def) main
  deriving Show

type FunDef = Lams Exp
pattern MkFunDef n body = MkLams n body

instance Pretty (Prog FunDef Exp) where
  pretty (MkProg topEnv main) = unlines (defs ++ [body]) where
    defs = map pretty $ zip [(0::TopLev)..] (seqToList topEnv)
    body = "main = " ++ pretty main

--------------------------------------------------------------------------------
-- ** free variables

freeVarSet' :: Level -> Level -> Exp -> Set Level
freeVarSet' threshold curLevel expr = execState (go curLevel expr) Set.empty where
  go :: Level -> Exp -> State (Set Level) ()
  go level expr = case expr of
    Loc' j         -> if j < threshold then modify (Set.insert j) else return ()
    Top' k         -> return ()
    App' fun args  -> go  level   fun  >> mapM_ (go level) args
    Let' rhs body  -> go  level    rhs  >> go (level+1) body
    Pri' op        -> mapM_ (go level) op
    Lit' k         -> return ()

freeVarMap' :: Level -> Level -> Exp -> (Map Level Level, Int)
freeVarMap' threshold level expr = (tbl, n) where
  set = freeVarSet' threshold level expr
  tbl = Map.fromList $ zip (Set.toList set) [0..]
  n   = Set.size set

freeVarSet :: Level -> Exp -> Set Level
freeVarSet level = freeVarSet' level level

freeVarMap :: Level -> Exp -> (Map Level Level, Int)
freeVarMap level = freeVarMap' level level

--------------------------------------------------------------------------------

data Replace a b 
  = a :~> b
  deriving Show

replaceVar' :: (Level -> Exp) -> Exp -> Exp
replaceVar' replace = go where
  go :: Exp -> Exp
  go (Var' var ) = case var of { Top k -> Top' k ; Loc j -> replace j }
  go (App' f xs) = App' (go f) (map go xs)
  go (Let' r b ) = Let' (go r) (go b)
  go (Pri' op  ) = Pri' (fmap go op)
  go (Lit' k   ) = Lit' k

replaceVar :: Replace Level Exp -> Exp -> Exp
replaceVar (old :~> new) = replaceVar' (\j -> if j == old then new else Loc' j)

-- replaceVarFunDef :: Replace Level Exp -> FunDef -> FunDef
-- replaceVarFunDef replace (MkFunDef n body) = MkFunDef n (replaceVar replace body)

--------------------------------------------------------------------------------
-- *** lambda-lift monad

type LiftM a = State (Seq FunDef) a

addNew' :: (TopLev -> FunDef) -> LiftM TopLev
addNew' what = do
  old <- get
  let n = Seq.length old
  put (old |> what n)
  return n

addNew :: FunDef -> LiftM TopLev
addNew what = addNew' (\_ -> what)

applyAt :: TopLev -> (FunDef -> FunDef) -> LiftM ()
applyAt idx f = modify (Seq.adjust' f idx)

----------------------------------------
-- debugging hacks...

{-# NOINLINE debugPrint #-}
debugPrint :: Show a => String -> a -> IO () 
debugPrint name y = putStrLn (">>> " ++ name ++ " = " ++ show y)

{-# NOINLINE discard #-}
discard :: a -> b -> b
discard !x y = x `seq` y

debug :: Show a => String -> a -> LiftM ()
debug name s = do
  let !none = unsafePerformIO $ debugPrint name s
  return (discard none ())

----------------------------------------

-- when we lift something to top-level, when we call it later, 
-- we also need to apply the captured variables from the environment
type Capture = Apps TopLev Level

lambdaLift :: Tm -> Prog FunDef Exp
lambdaLift orig = case runState (go_ 0 orig) Seq.empty of { (main,tops) -> MkProg tops main } where

  go_ :: Level -> Tm -> LiftM Exp
  go_ level term = fromEither <$> goEither level term

  fromEither :: Either Capture Exp -> Exp
  fromEither ei = case ei of
    Left  apps -> fromApps apps
    Right expr -> expr

  goEither :: Level -> Tm -> LiftM (Either Capture Exp)
  goEither level term = case term of
    Lam {} -> Left  <$> goLam    level term
    _      -> Right <$> goNotLam level term

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
  goLam :: Level -> Tm -> LiftM Capture
  goLam level term = case term of
    Lam {} -> case isLambda' term of
      MkLams nargs body -> do
        body' <- go_ (level + nargs) body
        let (free, nfree) = freeVarMap' level (level + nargs) body'
            nargs' = nfree + nargs 
        let replace :: Level -> Exp
            replace j = case Map.lookup j free of
              Just new -> Loc' new
              Nothing  -> if j >= level
                then Loc' (j - level + nfree)
                else error "lambdaLift/goLam: undetected free variable (shouldn't happen)"
        i <- addNew $ MkFunDef nargs' (replaceVar' replace body')
        return (MkApps i (Map.keys free))
    _ -> error "lambdaLift/goLam: not Lam (shouldn't happen)"

  -- this is like `goLam`, but more tricky. We must remove the recursive argument
  -- and replace its occurences with the new top-level variable, applied to 
  -- the local names of the captured variables
  goFix :: Level -> Tm -> LiftM Capture
  goFix level term = case term of
    Lam {} -> case isLambda' term of
      MkLams nargs body -> do
        -- the +1 is the recursive function itself
        body' <- go_ (level + 1 + nargs) body
        let (free, nfree) = freeVarMap' level (level + 1 + nargs) body'
            nargs' = nfree + nargs
            thisApps i = MkApps i (Map.keys free)
        let replace :: Capture -> Level -> Exp
            replace (MkApps top args) = go where
              go :: Level -> Exp
              go j = case Map.lookup j free of
                Just new             -> Loc' new
                Nothing | j >  level -> Loc' (j - 1 - level + nfree)
                Nothing | j == level -> app' (Top' top) (map go args)           -- !!!!
                Nothing | j <  level -> error "lambdaLift/goFix: undetected free variable (shouldn't happen)"
        i <- addNew' $ \k -> MkFunDef nargs' (replaceVar' (replace (thisApps k)) body')
        return (MkApps i (Map.keys free))
    _ -> error "lambdaLift/goFix: not Lam (shouldn't happen)"

  app' :: Exp -> [Exp] -> Exp
  app' fun []   = fun
  app' fun args = App' fun args

  fromApps :: Capture -> Exp
  fromApps (MkApps k captured) = app' (Top' k) (map Loc' captured)

  goNotLam :: Level -> Tm -> LiftM Exp
  goNotLam level term = case term of

    Var j -> return (Loc' j)

    -- if this was of the form `let f = \x y z -> ... a ... b ... in ... f ...` 
    -- then appearances of `f` in the body needs to be replaced by `top a b`
    Let rhs body -> do
      rhsEi <- goEither  level    rhs
      body' <- go_      (level+1) body
      return $ case rhsEi of 
        Left  apps -> replaceVar (level :~> fromApps apps) body'
        Right rhs' -> Let' rhs' body'
      
    -- if this was of the form `let f = \x y z -> ... f ... a ... b ... in ... f ...` 
    -- then appearances of `f` in the body needs to be replaced by `top a b`
    Rec rhs body -> case rhs of
      Lam {} -> do
        apps  <- goFix  level    rhs
        body' <- go_   (level+1) body
        return $ replaceVar (level :~> fromApps apps) body'
      _ -> error "recursive definitions must be functions"

    App {} -> case isApp' term of
      MkApps fun args -> do
        fun'  <-       go_ level  fun
        args' <- mapM (go_ level) args
        return (App' fun' args')

    Pri op -> Pri' <$> traverse (go_ level) op

    Lit k  -> return (Lit' k)

    Lam {} -> error "lambdaLift/goNotLam: shouldn't happen (Lam)"

--------------------------------------------------------------------------------
-- *** evaluation

type TopEnv = Seq FunDef

evalProg :: Prog FunDef Exp -> Val
evalProg (MkProg topEnv main) = eval Seq.empty main where

  eval :: Env -> Exp -> Val
  eval env expr = case expr of
    Var' var       -> case var of
      Loc j          ->          Seq.index env    j
      Top k          -> evalFun (Seq.index topEnv k)
    App' fun arg   -> valApps (eval env fun) (map (eval env) arg)
    Let' rhs body  -> let x = eval  env       rhs in eval (env |> x) body
    Pri' op        -> evalPrimOp $ fmap (eval env) op
    Lit' k         -> VInt k

  evalFun :: FunDef -> Val
  evalFun (MkFunDef n body) = go n emptyEnv where
    go 0 env = eval env body
    go n env = VLam \x -> go (n-1) (env |> x) 

--------------------------------------------------------------------------------
