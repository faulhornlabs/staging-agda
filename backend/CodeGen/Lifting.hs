
-- lambda lifting

{-# LANGUAGE PatternSynonyms, BlockArguments #-}
module CodeGen.Lifting where

--------------------------------------------------------------------------------

import Data.List

import Control.Applicative
import Control.Monad
import Control.Monad.State.Strict

import Data.Maybe

import qualified Data.Set      as Set ; import Data.Set      ( Set )
import qualified Data.Map      as Map ; import Data.Map      ( Map )
import qualified Data.Sequence as Seq ; import Data.Sequence ( Seq , (<|) , (|>) , (><) )
import qualified Data.Foldable as F

import Text.Show.Pretty ( ppShow )

import AST.Ty
import AST.Val
import AST.PrimOp
import AST.IO

import AST.Term hiding ( Top )
import qualified AST.Term

import Aux.Misc

--------------------------------------------------------------------------------

seqToList :: Seq a -> [a]
seqToList = F.toList

--------------------------------------------------------------------------------

data Variable
  = Loc Level     -- local variable
  | Top TopLev    -- top-level variable
  deriving (Eq,Show)

-- After the lifting transformation, @lambda@-s, @letrec@-s and even @let@-s 
-- where the defined value is a function are all eliminated. 
--
-- To simplify things we also eliminate @Log@ and @Dbg@ (which are ugly hacks anyway)
data Raw' where
  Var' :: Variable               -> Raw'
  App' :: Raw' -> [Raw']         -> Raw'
  Let' :: Ty -> Raw' -> Raw'     -> Raw'
  Pri' :: RawPrim -> [Raw']      -> Raw'
  Lit' :: Literal                -> Raw'
  -- hacks...
--  Log' :: String -> Raw' -> Raw'                -- ^ give name to things for debugging etc
--  Dbg' :: String -> Ty -> Raw' -> Raw' -> Raw'  -- ^ printf debugging support
  deriving Show

pattern Loc' j = Var' (Loc j)
pattern Top' k = Var' (Top k)

{-
quoteRaw' :: Raw' -> Raw
quoteRaw' = go where
  go (Loc' j)           = Var j
  go (Top' k)           = AST.Term.Top k
  go (App' f xs)        = appList (go f) (map go xs)
  go (Lit' l)           = Lit l
  go (Let' ty rhs body) = Let ty (go rhs) (go body)
  go (Pri' op args    ) = Pri op (map go args)

funDefToLam :: FunDef Raw' -> Raw
funDefToLam (MkFunDef _ _ (MkLams (MkFunTy args _) body)) = go args
  where
    go []     = quoteRaw' body
    go (t:ts) = Lam t (go ts)
-}

--------------------------------------------------------------------------------

inferTyRaw' :: Ctx -> Ctx -> Raw' -> Ty
inferTyRaw' topEnv = go where

  go :: Ctx -> Raw' -> Ty
  go localEnv term = case term of

    Loc' j -> case Seq.lookup j localEnv of 
      Just ty -> ty 
      Nothing -> error $ "inferTyRaw': local variable " ++ show j ++ " not found in local context"

    Top' k -> case Seq.lookup k topEnv of 
      Just ty -> ty 
      Nothing -> error $ "inferTyRaw': top level variable " ++ show k ++ " not found in top level context"

    Let' t rhs body -> 
      let t' = go localEnv rhs 
      in  if t' == t 
            then go (localEnv |> t) body
            else error $ "inferTyRaw': inconsistent let binding type: " ++ show t' ++ " vs. " ++ show t

    App' fun []   -> go localEnv fun
    App' fun args -> case isFunctionTy (go localEnv fun) of
      Just (MkFunTy argTys retTy) -> if map (go localEnv) args == argTys 
        then retTy 
        else error "inferTyRaw': incompatible function (multi-)application"
      _ -> error "inferTyRaw': application to a non-lambda"

    Pri' op args -> primOpTy op (map (go localEnv) args)

    Lit' lit -> literalTy lit

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

data FunDef expr = MkFunDef
  { _funIdx  :: !TopLev               -- ^ top-level index of the function 
  , _funName :: !String               -- ^ name of the function
  , _funBody :: !(Lams FunTy expr)    -- ^ function body
  }
  deriving Show

-- | type signature of the function
_funType :: FunDef expr -> FunTy      
_funType def = case _funBody def of
  MkLams funty _ -> funty

funDefTy :: FunDef expr -> Ty
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

printFunDefWith :: (a -> String) -> FunDef a -> IO ()
printFunDefWith userShow (MkFunDef idx name (MkLams (MkFunTy argsTy retTy) body)) = do
  putStrLn $ "\n" ++ show idx ++ ": def " ++ show name
  putStrLn $ " :: " ++ show argsTy ++ " -> " ++ show retTy
  putStrLn $ " = "
  putStrLn (userShow body)

printFunDef :: Show a => FunDef a -> IO ()
printFunDef = printFunDefWith show 

printProgramWith :: (a -> String) -> Program a -> IO ()
printProgramWith userShow (MkProgram tops main) = do
  mapM_ (printFunDefWith userShow) (F.toList tops)
  putStrLn ""
  putStrLn (userShow main)

printProgram :: Show a => Program a -> IO ()
printProgram = printProgramWith ppShow -- show

--------------------------------------------------------------------------------
-- ** free variables

type Tm  = Raw
type Exp = Raw'

type FunDef_ = FunDef Exp

freeVarSet' :: Level -> Ctx -> Exp -> Set (Level,Ty)
freeVarSet' threshold ctx expr = execState (go ctx expr) Set.empty where
  go :: Ctx -> Exp -> State (Set (Level,Ty)) ()
  go ctx expr = case expr of
    Loc' j            -> if j < threshold 
                           then modify (Set.insert (j, ctxLkp ctx j)) 
                           else return ()
    Top' k            -> return ()
    App' fun args     -> go  ctx        fun  >> mapM_ (go ctx) args
    Let' ty rhs body  -> go  ctx        rhs  >> go (ctx |> ty) body
    Pri' op args      -> mapM_ (go ctx) args
    Lit' k            -> return ()
    --
--    Log' n x          -> go ctx x
--    Dbg' n t x y      -> go ctx x >> go ctx y 

freeVarMap' :: Level -> Ctx -> Exp -> (Map Level Level, Seq Ty)
freeVarMap' threshold level expr = (tbl, tys) where
  set = freeVarSet' threshold level expr
  lts = Set.toList set :: [(Level,Ty)]
  tbl = Map.fromList $ zip (map fst lts) [0..]
  tys = Seq.fromList $ map snd lts

freeVarSet :: Ctx -> Exp -> Set (Level,Ty)
freeVarSet ctx = freeVarSet' (ctxToLevel ctx) ctx

freeVarMap :: Ctx -> Exp -> (Map Level Level, Seq Ty)
freeVarMap ctx = freeVarMap' (ctxToLevel ctx) ctx

--------------------------------------------------------------------------------

data Replace a b 
  = a :~> b
  deriving Show

replaceVar' :: (Level -> Exp) -> Exp -> Exp
replaceVar' replace = go where
  go :: Exp -> Exp
  go (Var' var  ) = case var of { Top k -> Top' k ; Loc j -> replace j }
  go (App' f xs ) = App' (go f) (map go xs)
  go (Let' t r b) = Let' t (go r) (go b)
  go (Pri' op as) = Pri' op (map go as)
  go (Lit' k    ) = Lit' k
  --
--  go (Log' n x    ) =  Log' n   (go x)
--  go (Dbg' n t x y) =  Dbg' n t (go x) (go y)

replaceVar :: Replace Level Exp -> Exp -> Exp
replaceVar (old :~> new) = replaceVar' (\j -> if j == old then new else Loc' j)

replaceVarFunDef :: Replace Level Exp -> FunDef_ -> FunDef_
replaceVarFunDef replace (MkFunDef i n (MkLams fty body)) = 
                          MkFunDef i n (MkLams fty $ replaceVar replace body)

--------------------------------------------------------------------------------
-- *** lambda-lift monad

type LiftM a = State (Seq FunDef_) a

addNew' :: (TopLev -> FunDef_) -> LiftM TopLev
addNew' what = do
  old <- get
  let n = Seq.length old
  put (old |> what n)
  return n

-- addNew :: FunDef_ -> LiftM TopLev
-- addNew what = addNew' (\i -> what { _funIdx = i})     

applyAt :: TopLev -> (FunDef_ -> FunDef_) -> LiftM ()
applyAt idx f = modify (Seq.adjust' f idx)

----------------------------------------

-- when we lift something to top-level, when we call it later, 
-- we also need to apply the captured variables from the environment
type Capture = Apps TopLev Level

lambdaLift :: Tm -> Program Exp
lambdaLift orig = case runState (go_ emptyCtx orig) Seq.empty of { (main,tops) -> MkProgram tops main } where

  go_ :: Ctx -> Tm -> LiftM Exp
  go_ ctx term = fromEither <$> goEither Nothing ctx term

  fromEither :: Either Capture Exp -> Exp
  fromEither ei = case ei of
    Left  apps -> fromApps apps
    Right expr -> expr

  goEither :: Maybe String -> Ctx -> Tm -> LiftM (Either Capture Exp)
  goEither mbName ctx term = case term of
    Lam {}                   -> let name = maybe "lam" id mbName in
                                Left  <$> goLam    name ctx term
    Log name term'@(Lam {})  -> Left  <$> goLam    name ctx term'
    _                        -> Right <$> goNotLam      ctx term

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
  goLam :: String -> Ctx -> Tm -> LiftM Capture
  goLam name ctx term = case term of
    Lam {} -> {- debugNice "Lam/isLambda" (ctx,term) $ -} case isLambda' ctx term of
      MkLams (MkFunTy argTys retTy) body -> do
        let ctx' = ctx >< Seq.fromList argTys
        body' <- go_ ctx' body
        let level = ctxToLevel ctx
            nargs = length argTys
        let (free, freeTys) = freeVarMap' level ctx' body'
            nfree = Seq.length freeTys
            argTys' = F.toList freeTys ++ argTys
            nargs'  = nfree + nargs 

        let replace :: Level -> Exp
            replace j = case Map.lookup j free of
              Just new -> Loc' new
              Nothing  -> if j >= level
                then Loc' (j - level + nfree)
                else error "lambdaLift/goLam: undetected free variable (shouldn't happen)"
        i <- addNew' $ \i -> 
            let name'  = name ++ show i
                funTy' = MkFunTy argTys' retTy
                body'' = (replaceVar' replace body')
            in  MkFunDef i name' (MkLams funTy' body'')
  
        return (MkApps i (Map.keys free))
  
    _ -> error "lambdaLift/goLam: not Lam (shouldn't happen)"

{-
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
-}

  -- this is like `goLam`, but more tricky. We must remove the recursive argument
  -- and replace its occurences with the new top-level variable, applied to 
  -- the local names of the captured variables
  --
  -- in the typed world: we had something like
  --
  -- letrec f :: s -> t
  --        f x = if cond x then x else f (x-1) + 1
  --
  goFix :: String -> Ctx -> Ty -> Tm -> LiftM Capture
  goFix name ctx recTy term = case term of
    Log name' term'@(Lam {}) -> goFix name' ctx recTy term'      -- naming hack
    Lam {} -> {- debugNice "Rec(Fix)/isLambda" (ctx,recTy,term) $ -} case isLambda' (ctx |> recTy) term of
      MkLams funTy@(MkFunTy argTys retTy) body -> do
        -- let recTy = fromFunTy funTy                        -- type of the recursive call (eg. s -> t)
        let ctx'  = ctx >< (recTy <| Seq.fromList argTys)
        body' <- {- debug "type of rec" recTy $ -} go_ ctx' body
        let level = ctxToLevel ctx
            nargs = length argTys
        let (free, freeTys) = freeVarMap' level ctx' body'
            nfree = Seq.length freeTys
            argTys' = F.toList freeTys ++ argTys
            nargs'  = nfree + nargs 

        let thisApps i = MkApps i (Map.keys free)
        let replace :: Capture -> Level -> Exp
            replace (MkApps top args) = go where
              go :: Level -> Exp
              go j = case Map.lookup j free of
                Just new             -> Loc' new
                Nothing | j >  level -> Loc' (j - 1 - level + nfree)
                Nothing | j == level -> app' (Top' top) (map go args)           -- !!!!
                Nothing | j <  level -> error "lambdaLift/goFix: undetected free variable (shouldn't happen)"
        i <- addNew' $ \i -> 
              let name'  = name ++ show i
                  funTy' = MkFunTy argTys' retTy
                  body'' = replaceVar' (replace (thisApps i)) body'
              in  MkFunDef i name' (MkLams funTy' body'')

        return (MkApps i (Map.keys free))

    _ -> error "lambdaLift/goFix: not Lam (shouldn't happen)"

  app' :: Exp -> [Exp] -> Exp
  app' fun []   = fun
  app' fun args = App' fun args

  fromApps :: Capture -> Exp
  fromApps (MkApps k captured) = app' (Top' k) (map Loc' captured)

  goNotLam :: Ctx -> Tm -> LiftM Exp
  goNotLam ctx term = case term of

    Var j -> return (Loc' j)

    -- if this was of the form `let f = \x y z -> ... a ... b ... in ... f ...` 
    -- then appearances of `f` in the body needs to be replaced by `top a b`
    Let ty rhs body -> do
      rhsEi <- goEither (Just "fun")  ctx        rhs
      body' <- go_                   (ctx |> ty) body
      let level = ctxToLevel ctx
      return $ case rhsEi of 
        Left  apps -> replaceVar (level :~> fromApps apps) body'
        Right rhs' -> Let' ty rhs' body'
      
    -- if this was of the form `let f = \x y z -> ... f ... a ... b ... in ... f ...` 
    -- then appearances of `f` in the body needs to be replaced by `top a b`
    Rec ty rhs body -> case rhs of
      Lam {} -> do
        apps  <- goFix "rec"  ctx    ty  rhs
        body' <- go_         (ctx |> ty) body
        let level = ctxToLevel ctx
        return $ replaceVar (level :~> fromApps apps) body'
      _ -> error "recursive definitions must be functions"

    App {} -> case isApp' term of
      MkApps fun args -> do
        fun'  <-       go_ ctx  fun
        args' <- mapM (go_ ctx) args
        return (App' fun' args')

    Pri op args -> Pri' op <$> mapM (go_ ctx) args

    Lit k  -> return (Lit' k)

    Lam {} -> error "lambdaLift/goNotLam: shouldn't happen (Lam)"

    Dbg n t x y -> go_ ctx y
    Log n     y -> go_ ctx y

--------------------------------------------------------------------------------


