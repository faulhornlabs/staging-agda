
{-# LANGUAGE PatternSynonyms #-}
module Run.Prim where

--------------------------------------------------------------------------------

import Data.Word
import Data.Bits

import qualified Data.Map as Map ; import Data.Map ( Map )

import Control.Monad
import Control.Monad.State.Strict

import AST.Ty
import AST.Val
import AST.PrimOp

import Run.Input
import Run.Semantics
import Run.IO

import Aux.Misc

--------------------------------------------------------------------------------

data Prim a 
  = MkPrim RawPrim [a]
  deriving (Eq,Show)

evalPrimOpMonadic :: Prim Val -> IO Val
evalPrimOpMonadic primArgs = case primArgs of

  MkPrim (MkRawPrimIO pio    ) args          -> evalPrimIO pio args
  MkPrim (MkRawPrim   prim   ) args          -> return $ evalNormalPrim (prim, args)
  MkPrim (RawProj     j      ) [StructV xs]  -> return $ xs !! j
  MkPrim (RawWrap     name   ) [x]           -> return $ WrapV name x

--  _ -> error $ "evalPrimOp: invalid combination\n  " ++ show primArgs

--------------------------------------------------------------------------------

evalGet :: String -> Ty -> IO Val
evalGet name ty = do
  x <- getInputIO_ name
  case marshalInto ty x of
    Nothing -> fail $ "cannot marshal input `" ++ name ++ "` from an integer"
    Just y  -> return y

evalPut :: String -> Val -> IO Val
evalPut name what = do
  case marshalFrom what of
    Nothing -> fail $ "cannot marshal output `" ++ name ++ "` into an integer"
    Just i  -> do
      putStrLn $ name ++ " == " ++ show i
      return TtV

--------------------------------------------------------------------------------

-- just sugar for nicer patterns below
pattern name :@@ args = (name, args)

evalNormalPrim :: (String , [Val]) -> Val
evalNormalPrim primArgs = 

  case primArgs of

    "AddU64"        :@@ [ U64V x , U64V y ]             -> U64V (x + y)
    "SubU64"        :@@ [ U64V x , U64V y ]             -> U64V (x - y)
    "AddCarryU64"   :@@ [ BitV cin , U64V x , U64V y ]  -> pairBitU64 (addCarry64 cin x y)
    "SubCarryU64"   :@@ [ BitV cin , U64V x , U64V y ]  -> pairBitU64 (subCarry64 cin x y)
    "MulTruncU64"   :@@ [ U64V x , U64V y ]             -> U64V (x * y)
    "MulExtU64"     :@@ [            U64V x , U64V y ]  -> pairU64U64 (mulExtU64   x y)
    "MulAddU64"     :@@ [ U64V a   , U64V x , U64V y ]  -> pairU64U64 (mulAddU64 a x y)
    "BitComplement" :@@ [ U64V x ]                      -> U64V (complement x)
    "BitOr"         :@@ [ U64V x , U64V y ]             -> U64V (x .|. y)
    "BitAnd"        :@@ [ U64V x , U64V y ]             -> U64V (x .&. y)
    "BitXor"        :@@ [ U64V x , U64V y ]             -> U64V (x `xor` y)
    "RotLeftU64"    :@@ [ BitV cin , U64V x ]           -> pairBitU64 (rotLeftU64  cin x)    
    "RotRightU64"   :@@ [ BitV cin , U64V x ]           -> pairBitU64 (rotRightU64 cin x)
    "EqU64"         :@@ [ U64V x   , U64V y ]           -> BitV (primEqU64 x y) 
    "LtU64"         :@@ [ U64V x   , U64V y ]           -> BitV (primLtU64 x y)  
    "LeU64"         :@@ [ U64V x   , U64V y ]           -> BitV (primLeU64 x y) 
    "CastBitU64"    :@@ [ BitV b ]                      -> U64V (primCastBitU64 b)
    "Not"           :@@ [ BitV b ]                      -> BitV (not b)
    "And"           :@@ [ BitV a , BitV b ]             -> BitV (a && b)
    "Or"            :@@ [ BitV a , BitV b ]             -> BitV (a || b)
    "IFTE"          :@@ [ BitV b , x , y ]              -> if b then x else y
    "MkStruct"      :@@ xs                              -> StructV xs
    "Unwrap"        :@@ [ WrapV _ x ]                   -> x
    "Zero"          :@@ []                              -> NatV 0
    "Succ"          :@@ [ NatV n ]                      -> NatV (n + 1)
    "IsZero"        :@@ [ NatV n ]                      -> BitV (n == 0)
    "NatAdd"        :@@ [ NatV x , NatV y ]             -> NatV (x + y)
    "NatMul"        :@@ [ NatV x , NatV y ]             -> NatV (x * y)
    "NatSubTrunc"   :@@ [ NatV x , NatV y ]             -> NatV (max 0 (x - y))

    _ -> error $ "evalNormalPrim: either unimplement or invalid: `" ++ show (fst primArgs) ++ "`  \n" ++ show primArgs

  where 

    pairBitU64 :: (Bit, Word64) -> Val
    pairBitU64 (bit,word) = PairV (BitV bit) (U64V word)

    pairU64U64 :: (Word64, Word64) -> Val
    pairU64U64 (w1,w2) = PairV (U64V w1) (U64V w2)

--------------------------------------------------------------------------------
