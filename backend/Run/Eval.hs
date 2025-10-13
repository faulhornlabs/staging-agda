
module Run.Eval 
  ( module Run.Eval.Pure
  , module Run.Eval.Monadic
--  , module Run.Monad
  , EvalState(..) , emptyEvalState 
  , EvalM , ValM , EnvM
  ) 
  where

--------------------------------------------------------------------------------

import Run.Eval.Pure    hiding ( Fun )
import Run.Eval.Monadic hiding ( Fun )
import Run.Prim
import Run.Monad

--------------------------------------------------------------------------------

