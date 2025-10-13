
module Run.Monad where

--------------------------------------------------------------------------------

import Control.Monad
import Control.Monad.Fix
import Control.Monad.State.Strict

import qualified Data.Map as Map 
import Data.Map ( Map )

import Debug.Trace

import AST.Val

--------------------------------------------------------------------------------

class MonadFix m => EvalMonad m where
  evalInput     :: String -> m Integer
  evalOutput    :: String -> Integer -> m ()
  debugPutStrLn :: String -> m ()

debugPrint :: (EvalMonad m, Show a) => String -> a -> m ()
debugPrint name x = debugPutStrLn $ ">>> " ++ name ++ " = " ++ show x

instance EvalMonad IO where
  evalInput         = error "IO/evalInput"
  evalOutput name x = putStrLn $ name ++ " = " ++ show x
  debugPutStrLn     = putStrLn

-- EvalM = State EvalState
instance EvalMonad (State EvalState) where 
  evalInput       = evalGetInput
  evalOutput      = evalPutOutput
  debugPutStrLn s = trace s $! return ()

--------------------------------------------------------------------------------

data EvalState = MkEvalS 
  { _inputs   :: !(Map String Integer)
  , _outputs  :: !(Map String Integer)
  }
  deriving (Eq,Show)

emptyEvalState :: EvalState
emptyEvalState = MkEvalS
  { _inputs  = Map.empty
  , _outputs = Map.empty
  }

type EvalM a = State EvalState a

type ValM = Val' (State EvalState)
type EnvM = Env' (State EvalState)

type ValIO = Val' IO
type EnvIO = Env' IO

runEvalM :: EvalM a -> (a, EvalState)
runEvalM action = runState action emptyEvalState

runEvalM_ :: EvalM a -> a
runEvalM_ action = fst (runEvalM action)

evalGetInput :: String -> EvalM Integer
evalGetInput name = do
  state <- get
  case Map.lookup name (_inputs state) of
    Nothing  -> error $ "evalGetInput: name `" ++ name ++ "` not found in inputs"
    Just y   -> return y

evalPutOutput :: String -> Integer -> EvalM ()
evalPutOutput name value = do
  old <- get
  let outputs' = Map.insert name value (_outputs old)
  let new = old { _outputs = outputs' }
  put new

--------------------------------------------------------------------------------
