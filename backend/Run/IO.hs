{-# LANGUAGE PatternSynonyms #-}
module Run.IO where

--------------------------------------------------------------------------------

import Data.Word
import Data.Bits

import Control.Monad

import AST.Ty
import AST.Val
import AST.PrimOp
import AST.IO

import Run.Input
import Run.Semantics

import Aux.Misc

--------------------------------------------------------------------------------

evalPrimIO  :: RawPrimIO -> [Val] -> IO Val
evalPrimIO  prim args = case (prim , args) of

  ( RawPrimGet name ty , [TokenV k] ) -> do 
    int <- getInputIO_ name 
    case marshalInto ty int of
      Nothing  -> fail $ "evalPrimIO: cannot marshal input `" ++ name ++ "` into " ++ show ty
      Just val -> return $ PairV val (TokenV (k+1))

  ( RawPrimPut name, [value, TokenV k]  ) -> do
    -- putStrLn $ "> " ++ name ++ " = " ++ show value
    case marshalFrom value of
      Nothing  -> fail $ "evalPrimIO: cannot marshal output `" ++ name ++ "` into integer"
      Just int -> do
        putOutputIO name int 
        return $ PairV TtV (TokenV (k+1))

  ( RawPrimAlloc  ty , _ ) -> fail "evalPrimIO: RawPrimAlloc: not implemented"
  ( RawPrimRead   ty , _ ) -> fail "evalPrimIO: RawPrimRead:  not implemented" 
  ( RawPrimFree      , _ ) -> fail "evalPrimIO: RawPrimFree:  not implemented"
  ( RawPrimWrite     , _ ) -> fail "evalPrimIO: RawPrimWrite: not implemented"
 
  _ -> fail $ "evalPrimIO: invalid primitive IO / argument combination: " ++ show prim ++ " " ++ show args

--------------------------------------------------------------------------------
