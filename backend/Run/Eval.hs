
module Run.Eval 
  ( module Run.Eval.Monadic
  , Val , Env
  ) 
  where

--------------------------------------------------------------------------------

import AST.Val
import Run.Eval.Monadic hiding ( Fun )
import Run.Prim

--------------------------------------------------------------------------------

