
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

import Run.Monad
import Run.Input
import Run.Semantics

import Aux.Misc

--------------------------------------------------------------------------------

data Prim a 
  = MkPrim RawPrim [a]
  deriving (Eq,Show)

-- we keep the old pure version, but it doesn't support input/output
evalPrimOpPure :: Prim Val -> Val
evalPrimOpPure primArgs = case primArgs of

  MkPrim (MkRawPrim prim   ) args          -> evalNormalPrim (prim, args)
  MkPrim (RawProj   j      ) [StructV xs]  -> xs !! j
  MkPrim (RawWrap   name   ) [x]           -> WrapV name x
{-
  MkPrim (RawInput  name ty) []            -> error "evalPrimOp: input"
  MkPrim (RawOutput name   ) [x]           -> error "evalPrimOp: output"
-}

  _ -> error "evalPrimOp: invalid combination"

--------------------

evalPrimOpMonadic :: EvalMonad m => Prim (Val' m) -> m (Val' m)
evalPrimOpMonadic primArgs = case primArgs of

  MkPrim (MkRawPrim prim   ) args          -> return $ evalNormalPrim (prim, args)
  MkPrim (RawProj   j      ) [StructV xs]  -> return $ xs !! j
  MkPrim (RawWrap   name   ) [x]           -> return $ WrapV name x

{-
  MkPrim (RawInput  name ty) []  -> do
    inputs <- _inputs <$> get
    case Map.lookup name inputs of
      Nothing  -> error $ "evalPrimOp/Input: name `" ++ name ++ "` not found in inputs"
      Just y   -> case marshalInto ty y of
        Nothing  -> error $ "evalPrimOp/Input: cannot marshal input `" ++ name ++ "` into type " ++ show ty
        Just val -> return val

  MkPrim (RawOutput name) [x] -> do
    case marshalFrom x of
      Nothing  -> error $ "evalPrimOp/Output: value for name `" ++ name ++ "` cannot be marshalled into an integer"
      Just int -> do
        old <- get
        let outputs' = Map.insert name int (_outputs old)
        let new = old { _outputs = outputs' }
        put new
        return TtV
-}

  _ -> error "evalPrimOp: invalid combination"

--------------------------------------------------------------------------------

-- just sugar for nicer patterns below
pattern name :@@ args = (name, args)

evalNormalPrim :: (String , [Val' m]) -> Val' m
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

    _ -> error $ "evalNormalPrim: either unimplement or invalid: `" ++ show (fst primArgs) ++ "`"

  where 

    pairBitU64 :: (Bit, Word64) -> Val' m
    pairBitU64 (bit,word) = PairV (BitV bit) (U64V word)

    pairU64U64 :: (Word64, Word64) -> Val' m
    pairU64U64 (w1,w2) = PairV (U64V w1) (U64V w2)

--------------------------------------------------------------------------------
