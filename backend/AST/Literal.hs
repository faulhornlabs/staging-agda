
{-# LANGUAGE StandaloneDeriving #-}
module AST.Literal where

--------------------------------------------------------------------------------

import Data.Word

import AST.Ty

--------------------------------------------------------------------------------

data Literal where
  TtL      ::                      Literal
  BitL     :: Bool              -> Literal
  U64L     :: Word64            -> Literal
  NatL     :: Integer           -> Literal
  StructL  :: [Literal]         -> Literal
  WrapL    :: String -> Literal -> Literal

deriving instance Eq   Literal
deriving instance Show Literal
deriving instance Read Literal

--------------------------------------------------------------------------------

literalTy :: Literal -> Ty
literalTy = go where
  go :: Literal -> Ty
  go lit = case lit of
    TtL          -> Unit
    BitL _       -> Bit
    U64L _       -> U64
    NatL _       -> Nat
    StructL xs   -> Struct (map go xs)
    WrapL   n x  -> Named n (go x)
    
--------------------------------------------------------------------------------

isAtomicLiteral :: Literal -> Bool
isAtomicLiteral lit = case lit of
  TtL         -> True
  BitL {}     -> True
  U64L {}     -> True
  NatL {}     -> True
  StructL _   -> False
  WrapL   _ x -> isAtomicLiteral x

mbAtomicLiteral :: Literal -> Maybe Literal
mbAtomicLiteral lit = if isAtomicLiteral lit
  then Just lit
  else Nothing

--------------------------------------------------------------------------------
