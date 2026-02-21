
{-# LANGUAGE BangPatterns, GADTSyntax, GeneralizedNewtypeDeriving, PatternSynonyms #-}

module AST.Term
  ( AST 
  , Raw(..) 
  , pattern NamedLam , pattern NamedVar
  , appList , lamList
  , shiftVars , mapVars -- , shiftVars'
  , module AST.Ty
  , module AST.Literal
  , module AST.PrimOp
--  , Ctx , TyEnv , emptyCtx , ctxLkp , ctxToLevel
  , inferTy , inferTy_
  , isLambda_ , isLambda , isApp_ , isApp
  )
  where

--------------------------------------------------------------------------------

import Data.Sequence ( Seq , (|>) )
import qualified Data.Sequence as Seq

-- import Data.IntMap ( IntMap )
-- import qualified Data.IntMap as IntMap

import AST.Ty
import AST.Literal
import AST.PrimOp
import AST.IO

import Aux.Misc

--------------------------------------------------------------------------------

type AST = Raw

data Raw where
  Lam :: Ty -> Raw -> Raw
  Let :: Ty -> Raw -> Raw -> Raw
  Rec :: Ty -> Raw -> Raw -> Raw
  App :: Raw -> Raw -> Raw
  Pri :: RawPrim -> [Raw] -> Raw
  Lit :: Literal -> Raw
  Var :: Level  -> Raw
  -- hacks...
  Log :: String -> Raw -> Raw                  -- ^ give name to things for debugging etc
  -- Top :: TopLev -> Raw                         -- ^ top level variable. This is only used when evaluating of lambda-lifted expressions
  -- Dbg :: String -> Ty -> Raw -> Raw -> Raw     -- ^ printf debugging support hack

pattern NamedVar name j    = Log name (Var j)
pattern NamedLam name ty f = Log name (Lam ty f)
-- pattern NamedTop name k    = Log name (Top k)

deriving instance Eq   Raw
deriving instance Show Raw
deriving instance Read Raw

app2 :: Raw -> Raw -> Raw -> Raw
app2 f x y = App (App f x) y

appList :: Raw -> [Raw] -> Raw
appList = go where
  go fun []     = fun
  go fun (x:xs) = go (App fun x) xs

lamList :: [Ty] -> Raw -> Raw
lamList = go where
  go []     body = body
  go (t:ts) body = Lam t (go ts body)

--------------------------------------------------------------------------------

shiftVars :: (Level -> Level) -> Raw -> Raw
shiftVars f = shiftVars' (\_ j -> f j)

-- | @f = \level var -> var'@
shiftVars' :: (Level -> Level -> Level) -> Raw -> Raw
shiftVars' f = go 0 where

  go :: Level -> Raw -> Raw
  go level term = case term of

    Lit v -> Lit v
    Var j -> Var (f level j)
    -- Top k -> Top k

    App fun args -> App (go level fun) (go level args)
    Pri op  args -> Pri op (map (go level) args)

    Lam t body     -> Lam t (go (level+1) body)

    Let t rhs body -> Let t (go level rhs) (go (level+1) body)
    Rec t rhs body -> Rec t (go level rhs) (go (level+1) body)

    Log n body     -> Log n (go level body)
    -- Dbg n t x y    -> Dbg n t (go level x) (go level y)

mapVars :: (Level -> Raw) -> Raw -> Raw
mapVars f = go 0 where

  go :: Level -> Raw -> Raw
  go level term = case term of

    Lit v -> Lit v
    Var j -> f j
    -- Top k -> Top k

    App fun args -> App (go level fun) (go level args)
    Pri op  args -> Pri op (map (go level) args)

    Lam t body     -> Lam t (go (level+1) body)

    Let t rhs body -> Let t (go level rhs) (go (level+1) body)
    Rec t rhs body -> Rec t (go level rhs) (go (level+1) body)

    Log n body     -> Log n (go level body)
    -- Dbg n t x y    -> Dbg n t (go level x) (go level y)

--------------------------------------------------------------------------------

inferTy_ :: Raw -> Ty
inferTy_ = inferTy Seq.empty Seq.empty

inferTy :: Ctx -> Ctx -> Raw -> Ty
inferTy topEnv = go where

  go :: Ctx -> Raw -> Ty
  go localEnv term = case term of

    Var j -> case Seq.lookup j localEnv of 
      Just ty -> ty 
      Nothing -> error $ "inferTy: local variable " ++ show j ++ " not found in local context"

{-    
    Top k -> case Seq.lookup k topEnv of 
      Just ty -> ty 
      Nothing -> error $ "inferTy: top level variable " ++ show k ++ " not found in top level context"
-}

    Lam t body     -> Arrow t (go (localEnv |> t) body)

    Let t rhs body -> 
      let t' = go localEnv rhs 
      in  if t' == t 
            then go (localEnv |> t) body
            else error $ "inferTy: inconsistent let binding type: " ++ show t' ++ " vs. " ++ show t

    Rec t rhs body -> if go (localEnv |> t) rhs == t 
      then go (localEnv |> t) body
      else error "inferTy: inconsistent letrec binding type"

    App fun arg -> case go localEnv fun of
      Arrow s t   -> if go localEnv arg == s 
        then t
        else error "inferTy: incompatible function application"
      _ -> error "inferTy: application to a non-lambda"

    Pri op args -> primOpTy op (map (go localEnv) args)

    Lit lit -> literalTy lit

    Log _ body  -> go localEnv body
    -- Dbg _ _ _ y -> go localEnv y

--------------------------------------------------------------------------------

isLambda_ :: Ctx -> Raw -> Lams FunTy Raw
isLambda_ = go where
  go :: Ctx -> Raw -> Lams FunTy Raw
  go ctx tm = case tm of
    Lam ty body -> case go (ctx |> ty) body of 
                     MkLams (MkFunTy args ret) body' -> MkLams (MkFunTy (ty:args) ret) body' 
    _           -> let t = inferTy emptyCtx ctx tm in MkLams (MkFunTy [] t) tm

isApp_ :: Raw -> Apps Raw Raw
isApp_ = go where
  go tm = case tm of
    App f x -> case go f of { MkApps f xs -> MkApps f (xs ++ [x]) }
    _       -> MkApps tm []

isLambda :: Ctx -> Raw -> Maybe (Lams FunTy Raw)
isLambda ctx tm = case isLambda_ ctx tm of
  MkLams funty body -> case funty of
    MkFunTy [] ret -> Nothing
    _              -> Just (MkLams funty body)

isApp :: Raw -> Maybe (Apps Raw Raw)
isApp tm = case isApp_ tm of
  MkApps f xs -> case xs of
    [] -> Nothing
    _  -> Just (MkApps f xs)

--------------------------------------------------------------------------------
