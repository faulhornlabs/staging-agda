
{-# LANGUAGE BlockArguments, PatternSynonyms #-}
module Eval 
  ( module Val
  , evalHOAS
  , evalTm
  , evalTm1
  , evalPrg , evalExp
  )
  where

--------------------------------------------------------------------------------

-- import qualified Data.Map as Map ; import Data.Map ( Map )

import Seq
import Common
import Val

import HOAS       ( evalHOAS )
import Term       ( evalTm   )
import Preprocess ( evalTm1  )
import Lift       ( evalPrg , evalExp )

--------------------------------------------------------------------------------
