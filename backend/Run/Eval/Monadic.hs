
{-# LANGUAGE PatternSynonyms, ScopedTypeVariables #-}
module Run.Eval.Monadic where

--------------------------------------------------------------------------------

import Data.Word
import Data.Bits

import qualified Data.Map      as Map ; import Data.Map      ( Map )
import qualified Data.Sequence as Seq ; import Data.Sequence ( Seq , (|>) , (><) )
import qualified Data.Foldable as F

import Control.Monad
import Control.Monad.Fix
import Control.Monad.State.Strict

import AST.Ty
import AST.Val
import AST.PrimOp
import AST.Term

import CodeGen.Lifting
import CodeGen.ANF

import Run.Monad
import Run.Input
import Run.Prim

import Aux.Misc

--------------------------------------------------------------------------------

runWithInputs :: (a -> EvalM b) -> Inputs -> a -> (Outputs, b)
runWithInputs action inputs x = 
  case runState (action x) iniState of
    (result, outState) -> (_outputs outState , result)
  where
    iniState = emptyEvalState { _inputs = inputs }

evalWithInputs :: Inputs -> Raw -> (Outputs, ValM)
evalWithInputs = runWithInputs evalM

evalM :: EvalMonad m => Raw -> m (Val' m)
evalM = evalInEnvM Seq.empty emptyEnv

evalIO :: Raw -> IO ValIO
evalIO = evalM

--------------------------------------------------------------------------------

pattern Fun f = FunV (MkFun f)

evalInEnvM :: forall m. EvalMonad m => Seq (FunDef Raw) -> Env' m -> Raw -> m (Val' m)
evalInEnvM topEnv = go where

  go ::  Env' m -> Raw -> m (Val' m)
  go env term = case term of

    Lam _ty body -> return $ Fun (\x -> go (env |> x) body)

    Let _ty rhs body -> do
      rhs' <- go env rhs
      go (env |> rhs') body

    App fun arg -> do
      fun' <- go env fun
      case fun' of
        Fun f -> f =<< (go env arg)
        _     -> error "evalInEnvM: application to a non-lambda"

    Fix fun -> do
      fun' <- go env fun
      case fun' of
        Fun f -> mfix f -- evalFixM f
        _     -> error "evalInEnvM: fixpoint of a non-lambda"

    Pri op args  -> do
      ys <- mapM (go env) args 
      evalPrimOpMonadic (MkPrim op ys)

    Lit val -> return (castVal val)

    Var j -> return (Seq.index env j)

    Top k -> go Seq.empty $ funDefToLam (Seq.index topEnv k)

    Log _ body -> go env body

    Dbg name ty x y -> do
      x' <- go env x
      debugPrint name x'
      go env y

{-
evalFixM :: EvalMonad m => (Val' m -> m (Val' m)) -> m (Val' m)
evalFixM f = mfix f
-- evalFixM f = f =<< (evalFixM f) 
-}

runProgramM :: EvalMonad m => Program Raw -> m (Val' m)
runProgramM (MkProgram tops main) = evalInEnvM tops Seq.empty main

runProgramWithInputs :: Inputs -> Program Raw -> (Outputs, ValM)
runProgramWithInputs = runWithInputs runProgramM

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

evalAnfInEnvM :: forall m. EvalMonad m => Seq (FunDef ANFE) -> Env' m -> ANFE -> m (Val' m)
evalAnfInEnvM topEnv = goANF where

  goAtom :: Env' m -> Atom -> m (Val' m)
  goAtom locEnv atom = case atom of
    VarA j -> return $ Seq.index locEnv j
    KstA v -> return $ castVal v
    TopA k -> error "evalANF: trying to evaluate top-level lambda"

  goTyExp ::  Env' m -> Typed ExpA -> m (Val' m)
  goTyExp env (MkTyped ty expr) = goExp env expr

  goApp :: Env' m -> FunDef ANFE -> [Val' m] -> m (Val' m)
  goApp env (MkFunDef _idx _name funTy body _fix) args = 
    goANF (Seq.fromList args) body
    
  goExp :: Env' m -> ExpA -> m (Val' m)
  goExp env expr = case expr of

    AtmE atom -> goAtom env atom

    AppE topIdx args     -> do
      args' <- mapM (goAtom env) args
      goApp env (Seq.index topEnv topIdx) args'

    PriE op args         -> do
      args' <- mapM (goAtom env) args
      evalPrimOpMonadic (MkPrim op args')

    IftE cond tbr fbr    -> do
      cond' <- goAtom env cond
      goIfte env cond' tbr fbr

  goIfte :: Env' m -> Val' m -> ANFE -> ANFE -> m (Val' m)
  goIfte env cond tbr fbr = case cond of 
    BitV True  -> goANF env tbr
    BitV False -> goANF env fbr
    _          -> error "evalANF: IFTE: condition is not a boolean"
    
  goANF :: Env' m -> ANFE -> m (Val' m)
  goANF env0 (MkANF lets expr) = worker env0 (F.toList lets) where
    worker env []     = goTyExp env expr
    worker env (u:us) = do
      v <- goTyExp env u 
      worker (env |> v) us

runANFProgramM :: EvalMonad m => Program ANFE -> m (Val' m)
runANFProgramM (MkProgram tops main) = evalAnfInEnvM tops Seq.empty main

runANFProgramWithInputs :: Inputs -> Program ANFE -> (Outputs, ValM)
runANFProgramWithInputs = runWithInputs runANFProgramM

--------------------------------------------------------------------------------

