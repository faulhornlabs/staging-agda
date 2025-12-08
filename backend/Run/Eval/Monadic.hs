
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
import AST.IO
import AST.Term

import CodeGen.Lifting
import CodeGen.ANF

import Run.Input
import Run.Prim

import Aux.Misc

--------------------------------------------------------------------------------

eval :: Raw -> IO Val
eval orig = do
  let ty = inferTy_ orig 
  case ty of
    Arrow Token pair -> do
      putStrLn "eval: input is IO action"
      let rwt_in = Lit (TokenV 0)
      out <- eval' (App orig rwt_in)
      case out of 
        PairV result (TokenV _) -> return result
        _ -> fail "eval/IO: expecting a (result,Token) pair"
    _ -> do
      putStrLn "eval: input is pure"
      eval' orig

eval' :: Raw -> IO Val
eval' = evalInEnv Seq.empty emptyEnv

--------------------------------------------------------------------------------

debugPutStrLn :: String -> IO ()
debugPutStrLn = putStrLn

debugPrint :: Show a => String -> a -> IO ()
debugPrint name x = debugPutStrLn $ ">>> " ++ name ++ " = " ++ show x

--------------------------------------------------------------------------------

pattern Fun f = FunV (MkRunTimeFun f)

evalInEnv :: Seq (FunDef Raw) -> Env -> Raw -> IO Val
evalInEnv topEnv = go where

  go ::  Env -> Raw -> IO Val
  go env term = case term of

    App fun arg -> do
      fun' <- go env fun
      case fun' of
        Fun f -> f =<< (go env arg)
        _     -> error "evalInEnvM: application to a non-lambda"

    Lam _ty body -> return $ Fun (\x -> go (env |> x) body)

    Let _ty rhs body -> do
      rhs' <- go env rhs
      go (env |> rhs') body

    -- ????
    Rec _ty rhs body -> do
      rhs' <- mfix (\rec -> go (env |> rec) rhs)
      go (env |> rhs') body

{-
    Fix fun -> do
      fun' <- go env fun
      case fun' of
        Fun f -> mfix f -- evalFixM f
        _     -> error "evalInEnvM: fixpoint of a non-lambda"
-}

    Pri op args  -> do
      ys <- mapM (go env) args 
      evalPrimOpMonadic (MkPrim op ys)

    Lit val -> return val

    Var j -> return (Seq.index env j)

    Top k -> go Seq.empty $ funDefToLam (Seq.index topEnv k)

    Log _ body -> go env body

    Dbg name ty x y -> do
      x' <- go env x
      debugPrint name x'
      go env y

--------------------------------------------------------------------------------

runProgram :: Program Raw -> IO Val
runProgram (MkProgram tops main) = evalInEnv tops Seq.empty main

runProgramWithInputs :: Inputs -> Program Raw -> IO (Outputs, Val)
runProgramWithInputs inputs prg = runWithInputs inputs $ runProgram prg


--------------------------------------------------------------------------------
-- *** ANF

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

evalAnfInEnv :: Seq (FunDef ANFE) -> Env -> ANFE -> IO Val
evalAnfInEnv topEnv = goANF where

  goAtom :: Env -> Atom -> IO Val
  goAtom locEnv atom = case atom of
    VarA j -> return $ Seq.index locEnv j
    KstA v -> return $ v
    TopA k -> fail "evalANFInEnv: trying to evaluate top-level lambda"

  goTyExp ::  Env -> Typed ExpA -> IO Val
  goTyExp env (MkTyped ty expr) = goExp env expr

  goApp :: Env -> FunDef ANFE -> [Val] -> IO Val
  goApp env (MkFunDef _idx _name funTy body _isFix) args = 
    goANF (Seq.fromList args) body
    
  goExp :: Env -> ExpA -> IO Val
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

  goIfte :: Env -> Val -> ANFE -> ANFE -> IO Val
  goIfte env cond tbr fbr = case cond of 
    BitV True  -> goANF env tbr
    BitV False -> goANF env fbr
    _          -> fail "evalANF: IFTE: condition is not a boolean"
    
  goANF :: Env -> ANFE -> IO Val
  goANF env0 (MkANF lets expr) = worker env0 (F.toList lets) where
    worker env []     = goTyExp env expr
    worker env (u:us) = do
      v <- goTyExp env u 
      worker (env |> v) us

runANFProgram :: Program ANFE -> IO Val
runANFProgram (MkProgram tops main) = evalAnfInEnv tops Seq.empty main

runANFProgramWithInputs :: Inputs -> Program ANFE -> IO (Outputs, Val)
runANFProgramWithInputs inputs prg = runWithInputs inputs $ runANFProgram prg

--------------------------------------------------------------------------------

