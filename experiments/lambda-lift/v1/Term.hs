
-- standard first-order syntax

{-# LANGUAGE BlockArguments #-}
module Term where

--------------------------------------------------------------------------------

import Data.Kind

import Control.Applicative
import Control.Monad
import Control.Monad.State

import qualified Data.Set      as Set ; import Data.Set ( Set )
import qualified Data.Map      as Map ; import Data.Map ( Map )
import qualified Data.Sequence as Seq ; import Data.Sequence ( Seq , (|>) )

import Shared

--------------------------------------------------------------------------------
-- *** first-order terms

data Tm where
  Var :: Level     -> Tm 
  App :: Tm -> Tm  -> Tm       -- Tm ctx (s => t) -> Tm ctx s       -> Tm ctx t
  Lam :: Tm        -> Tm       -- Tm (ctx |> s) t                   -> Tm ctx (s => t)
  Let :: Tm -> Tm  -> Tm       -- Tm ctx s        -> Tm (ctx |>s) t -> Tm ctx t
  Rec :: Tm -> Tm  -> Tm       -- Tm (ctx |> s) s -> Tm (ctx |>s) t -> Tm ctx t
  Pri :: PrimOp Tm -> Tm
  Lit :: Int       -> Tm
  deriving Show

--------------------------------------------------------------------------------

isLambda' :: Tm -> Lams Tm
isLambda' = go where
  go tm = case tm of
    Lam body -> case go body of { MkLams n body' -> MkLams (n+1) body' }
    _        -> MkLams 0 tm

isApp' :: Tm -> Apps Tm Tm
isApp' = go where
  go tm = case tm of
    App f x -> case go f of { MkApps f xs -> MkApps f (xs ++ [x]) }
    _       -> MkApps tm []

isLambda :: Tm -> Maybe (Lams Tm)
isLambda tm = case isLambda' tm of
  MkLams n body -> case n of
    0 -> Nothing
    _ -> Just (MkLams n body)

isApp :: Tm -> Maybe (Apps Tm Tm)
isApp tm = case isApp' tm of
  MkApps f xs -> case xs of
    [] -> Nothing
    _  -> Just (MkApps f xs)

--------------------------------------------------------------------------------
-- ** free variables

{-
freeVarSet' :: Level -> Level -> Tm -> Set Level
freeVarSet' threshold curLevel term = execState (go curLevel term) Set.empty where
  go :: Level -> Tm -> State (Set Level) ()
  go level tm = case tm of
    Var j         -> if j < threshold then modify (Set.insert j) else return ()
    App fun arg   -> go  level    fun  >> go  level    arg
    Lam body      ->                      go (level+1) body
    Let rhs body  -> go  level    rhs  >> go (level+1) body
    Rec rhs body  -> go (level+1) rhs  >> go (level+1) body
    Pri op        -> mapM_ (go level) op
    Lit k         -> return ()

freeVarMap' :: Level -> Level -> Tm -> (Map Level Level, Int)
freeVarMap' threshold level tm = (tbl, n) where
  set = freeVarSet' threshold level tm
  tbl = Map.fromList $ zip (Set.toList set) [0..]
  n   = Set.size set

freeVarSet :: Level -> Tm -> Set Level
freeVarSet level = freeVarSet' level level

freeVarMap :: Level -> Tm -> (Map Level Level, Int)
freeVarMap level = freeVarMap' level level
-}

--------------------------------------------------------------------------------
-- *** evaluation

evalTm :: Tm -> Val
evalTm = evalTm' Seq.empty

evalTm' :: Env -> Tm -> Val
evalTm' = go where
  go env tm = case tm of
    Var j         -> Seq.index env j
    App fun arg   -> valApp (go env fun) (go env arg)
    Lam body      -> VLam \x -> go (env |> x) body
    Let rhs body  -> let x = go  env       rhs in go (env |> x) body
    Rec rhs body  -> let f = go (env |> f) rhs in go (env |> f) body
    Pri op        -> evalPrimOp $ fmap (go env) op
    Lit k         -> VInt k

--------------------------------------------------------------------------------

instance Pretty Tm where
  prettyPrec = prettyTm

prettyTm :: Prec -> Tm -> (String -> String)
prettyTm d = go d 0 where
  go d level term = case term of
    Var j        -> showChar 'v' . shows j
    App f x      -> showParen (d > app_prec) $ go (app_prec) level f . showChar ' ' . go (app_prec+1) level x
    Lam body     -> showParen (d > lam_prec) $ showChar '\\' . showVar level . showString " -> " . go (lam_prec) (level+1) body
    Let rhs body -> showParen (d > let_prec) $ showString "let "    . showVar level . showString " = " . go (let_prec+1)  level    rhs . showString " in " . go (in_prec) (level+1) body
    Rec rhs body -> showParen (d > let_prec) $ showString "letrec " . showVar level . showString " = " . go (let_prec+1) (level+1) rhs . showString " in " . go (in_prec) (level+1) body
    Pri op       -> prettyPrec d op
    Lit n        -> shows n
  showVar level = showString "v" . shows level

--------------------------------------------------------------------------------
