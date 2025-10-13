
{-# LANGUAGE PatternSynonyms #-}
module Run.Eval.Pure where

--------------------------------------------------------------------------------

import Data.Word
import Data.Bits

import qualified Data.Map      as Map ; import Data.Map      ( Map )
import qualified Data.Sequence as Seq ; import Data.Sequence ( Seq , (|>) , (><) )
import qualified Data.Foldable as F

import Control.Monad
import Control.Monad.Identity

import Debug.Trace

import AST.Ty
import AST.Val
import AST.PrimOp
import AST.Term

import CodeGen.Lifting
import CodeGen.ANF

import Run.Input
import Run.Prim

import Aux.Misc

--------------------------------------------------------------------------------

eval :: Raw -> Val
eval = evalInEnv Seq.empty emptyEnv

runF :: (Val -> Identity Val) -> Val -> Val
runF f x = runIdentity (f x)

mkF :: (Val -> Val) -> (Val -> Identity Val)
mkF f x = return (f x)

--------------------------------------------------------------------------------

pattern Fun f = FunV (MkFun f)

evalInEnv :: Seq (FunDef Raw) -> Env -> Raw -> Val
evalInEnv topEnv = go where

  go ::  Env -> Raw -> Val
  go env term = case term of
    Lam _ty body      -> Fun $ mkF (\x -> go (env |> x) body)
    Let _ty rhs body  -> go (env |> go env rhs) body
    App fun arg       -> case (go env fun) of
                           Fun f -> runF f (go env arg)
                           _     -> error "evalInEnv: application to a non-lambda"
    Fix fun           -> case (go env fun) of
                           Fun f -> evalFix (runF f)
                           _     -> error "evalInEnv: fixpoint of a non-lambda"
    Pri op args       -> let ys = map (go env) args in evalPrimOpPure (MkPrim op ys)
    Lit val           -> val
    Var j             -> Seq.index env j
    Top k             -> go Seq.empty $ funDefToLam (Seq.index topEnv k)
    Log _ body        -> go env body
    Dbg n _ x body    -> 
      let s = ">>> " ++ n ++ " = " ++ show (go env x)
      in  trace s $ go env body

evalFix :: (Val -> Val) -> Val
evalFix f = f (evalFix f) 

runProgram :: Program Raw -> Val
runProgram (MkProgram tops main) = evalInEnv tops Seq.empty main

--------------------------------------------------------------------------------

{-

data Atom 
  = VarA !Level        -- ^ local variable (de Bruijn levels)
  | TopA !TopLev       -- ^ top-level variable
  | KstA !Val          -- ^ literal constant
  --  | ExtA !Int          -- ^ external input
  deriving (Eq,Show)

-- expressions
data ExpA
  = AtmE !Atom
  | AppE !TopLev  [Atom]
  | PriE !RawPrim [Atom] 
  | IftE !Atom !ANFE !ANFE
  deriving (Eq,Show)
 
data ANF hole = MkANF 
  { _lets :: !(Seq (Typed ExpA))
  , _in   :: !hole
  }
  deriving (Eq,Show)

type ANFE = ANF (Typed ExpA)

 { _funIdx  :: Int         -- ^ top level index
  , _funName :: String
  , _funType :: FunTy
  , _funBody :: a 
  }
-}

evalAnfInEnv :: Seq (FunDef ANFE) -> Env -> ANFE -> Val
evalAnfInEnv topEnv = goANF where

  goAtom :: Env -> Atom -> Val
  goAtom locEnv atom = case atom of
    VarA j -> Seq.index locEnv j
    TopA k -> error "evalANF: trying to evaluate top-level lambda"
    KstA v -> v

  goTyExp ::  Env -> Typed ExpA -> Val
  goTyExp env (MkTyped ty expr) = goExp env expr

  goApp :: Env -> FunDef ANFE -> [Val] -> Val
  goApp env (MkFunDef _idx _name funTy body _fix) args = 
    goANF (Seq.fromList args) body
    
  goExp :: Env -> ExpA -> Val
  goExp env expr = case expr of
    AtmE atom            -> goAtom env atom
    AppE topIdx args     -> goApp env (Seq.index topEnv topIdx) (map (goAtom env) args)
    PriE op args         -> evalPrimOpPure (MkPrim op $ map (goAtom env) args)
    IftE cond tbr fbr    -> goIfte env (goAtom env cond) tbr fbr

  goIfte :: Env -> Val -> ANFE -> ANFE -> Val
  goIfte env cond tbr fbr = case cond of 
    BitV True  -> goANF env tbr
    BitV False -> goANF env fbr
    _          -> error "evalANF: IFTE: condition is not a boolean"
    
  goANF :: Env -> ANFE -> Val
  goANF env0 (MkANF lets expr) = worker env0 (F.toList lets) where
    worker env []     = goTyExp env expr
    worker env (u:us) = let v = goTyExp env u 
                        in  worker (env |> v) us

runANFProgram :: Program ANFE -> Val
runANFProgram (MkProgram tops main) = evalAnfInEnv tops Seq.empty main

--------------------------------------------------------------------------------

