
{-# LANGUAGE GADTSyntax, GeneralizedNewtypeDeriving #-}
module AST.PrimOp where

--------------------------------------------------------------------------------

import AST.Ty

--------------------------------------------------------------------------------

data RawPrim where
  MkRawPrim :: String       -> RawPrim
  RawProj   :: Int          -> RawPrim
  RawWrap   :: String       -> RawPrim
{-
  RawInput  :: String -> Ty -> RawPrim
  RawOutput :: String       -> RawPrim
-}

deriving instance Eq   RawPrim
deriving instance Show RawPrim
deriving instance Read RawPrim

--------------------------------------------------------------------------------

primOpTy :: RawPrim -> [Ty] -> Ty
primOpTy rawprim args = case rawprim of

  MkRawPrim name  -> simplePrimOpTy name args

  RawProj j -> case args of
    [Struct ts] -> ts !! j
    _           -> error "primOpTy: projection from a non-struct"

  RawWrap name -> case args of
    [ty] -> Named name ty
    _    -> error "primOpTy: wrapping applied to more than 1 arguments"

{-
  RawInput  _ ty  -> ty
  RawOutput _     -> Unit
-}

--------------------------------------------------------------------------------

simplePrimOpTy :: String -> [Ty] -> Ty
simplePrimOpTy prim args = case prim of

  "AddU64"        -> U64
  "SubU64"        -> U64
  "AddCarryU64"   -> Pair Bit U64
  "SubCarryU64"   -> Pair Bit U64
  "MulTruncU64"   -> U64
  "MulExtU64"     -> Pair U64 U64
  "MulAddU64"     -> Pair U64 U64
  "BitComplement" -> U64
  "BitOr"         -> U64
  "BitAnd"        -> U64
  "BitXor"        -> U64
  "RotLeftU64"    -> Pair Bit U64
  "RotRightU64"   -> Pair Bit U64
  "EqU64"         -> Bit
  "LtU64"         -> Bit
  "LeU64"         -> Bit
  "CastBitU64"    -> U64
  "Not"           -> Bit
  "And"           -> Bit
  "Or"            -> Bit
  "IFTE"          -> case args of 
                       [ Bit , u , v ] -> if u == v then u else error "IFTE: incompatible branch types"
                       _ -> error "IFTE: invalid arguments"
  "MkStruct"      -> Struct args
  "Unwrap"        -> case args of
                       [ Named _ ty ] -> ty
                       _ -> error "Unwrap: expecting a struct"
  "Zero"          -> Nat
  "Succ"          -> Nat
  "IsZero"        -> Bit
  "NatSplit"      -> case args of
                       [ Nat , s , Arrow Nat t ] -> if s == t then s else error "NatSplit: incompatible branch types"
                       _ -> error "NatSplit: invalid arguments"
  "NatAdd"        -> Nat
  "NatSubTrunc"   -> Nat
  "NatMul"        -> Nat

  _ -> error $ "simplePrimOpTy: unrecognized / unhandled primop: `" ++ prim ++ "`"

--------------------------------------------------------------------------------
