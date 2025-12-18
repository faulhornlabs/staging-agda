
{-# LANGUAGE GADTSyntax, GeneralizedNewtypeDeriving #-}
module AST.IO where

--------------------------------------------------------------------------------

import AST.Ty

--------------------------------------------------------------------------------

data RawPrimIO where
  RawPrimGet    :: String -> Ty  -> RawPrimIO     -- input name and type
  RawPrimPut    :: String        -> RawPrimIO     -- output name (type is implicit)
  RawPrimPrint  :: String        -> RawPrimIO     -- output descriptor (type is implicit)
  RawPrimAlloc  :: Ty            -> RawPrimIO     -- type of the elements of the array what we allocate
  RawPrimFree   ::                  RawPrimIO
  RawPrimRead   :: Ty            -> RawPrimIO     -- type of the element we read
  RawPrimWrite  :: Ty            -> RawPrimIO     -- type of the element we write
  RawPrimLen    ::                  RawPrimIO
  RawPrimLoop   ::                  RawPrimIO

deriving instance Eq   RawPrimIO
deriving instance Show RawPrimIO
deriving instance Read RawPrimIO

--------------------------------------------------------------------------------

{- recall:

data PrimIO (tm : Ty -> Set) : Ty -> Set where
  -- basic input/output
  PrimGet   : String -> (ty : Ty)                 -> PrimIO tm ty
  PrimPut   : String -> tm ty                     -> PrimIO tm Unit
  -- memory allocation
  PrimAlloc : tm U64 -> (vty : VTy)               -> PrimIO tm (Ptr vty)
  PrimFree  : tm (Ptr vty)                        -> PrimIO tm Unit     
  -- reading/writing arrays
  PrimRead  : {eq : vtyToTy vty ≡ ty} -> tm (Ptr vty) -> tm Idx          -> PrimIO tm ty  
  PrimWrite : {eq : vtyToTy vty ≡ ty} -> tm (Ptr vty) -> tm Idx -> tm ty -> PrimIO tm Unit

data PrimOp (tm : Ty -> Set) : Ty -> Set where
  ...
  WrapPrimIO : PrimIO tm t -> tm Token -> PrimOp tm (Pair t Token)

-}

rawPrimIOTy  :: RawPrimIO -> [Ty] -> Ty
rawPrimIOTy  prim args = case args of
  []                      -> error "rawPrimIOTy: no argument (at least a token is expected)"
  _ | last args /= Token  -> error "rawPrimIOTy: the last argument is expected to be a token" 
  otherwise               -> case prim of

    RawPrimGet    name ty -> io__ ty
    RawPrimPut    name    -> io__ Unit
    RawPrimPrint  name    -> io__ Unit

    RawPrimAlloc  ty      -> io__ (Ptr_ ty)
    RawPrimFree           -> io__ Unit
  
    RawPrimRead   ty      -> io__ ty
    RawPrimWrite  ty      -> io__ Unit

    RawPrimLen            -> io__ U64
    RawPrimLoop           -> io__ Unit


  where

    -- NOTE: the input token becomes an argument!
    io__ ty = Pair ty Token


 --------------------------------------------------------------------------------
