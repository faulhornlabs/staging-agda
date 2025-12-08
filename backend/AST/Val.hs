
{-# LANGUAGE GADTSyntax, GeneralizedNewtypeDeriving, PatternSynonyms #-}
module AST.Val where

--------------------------------------------------------------------------------

import Data.Word
import Text.Read

import Data.Sequence ( Seq , empty )

import Control.Monad.Identity

import AST.Ty

--------------------------------------------------------------------------------

 -- used only for the evaluator
data RunTimeFun 
  = MkRunTimeFun (Val -> IO Val)

instance Eq   RunTimeFun where (==)     = error "RunTimeFun/Eq"
instance Read RunTimeFun where readPrec = error "RunTimeFun/Read"
instance Show RunTimeFun where show _   = "<<runtime function>>"

runRunTimeFun :: RunTimeFun -> Val -> IO Val
runRunTimeFun (MkRunTimeFun f) x = f x

--------------------------------------------------------------------------------

data Val where
  TtV      ::                  Val
  BitV     :: Bool          -> Val
  U64V     :: Word64        -> Val
  NatV     :: Integer       -> Val
  StructV  :: [Val]         -> Val
  WrapV    :: String -> Val -> Val
  FunV     :: RunTimeFun    -> Val      -- ^ used only for the evaluator
  TokenV   :: Int           -> Val      -- ^ used only for token-passing IO
  -- PtrV     ::  ???

pattern PairV x y = StructV [x,y]

deriving instance Eq   Val
deriving instance Show Val
deriving instance Read Val

isAtomicValue :: Val -> Bool
isAtomicValue value = case value of
  TtV         -> True
  BitV {}     -> True
  U64V {}     -> True
  NatV {}     -> True
  StructV _   -> False
  WrapV   _ x -> isAtomicValue x
  FunV {}     -> error "isAtomicValue: called on function"
  TokenV {}   -> True

mbAtomicValue :: Val -> Maybe Val
mbAtomicValue value = if isAtomicValue value 
  then Just value
  else Nothing
  
--------------------------------------------------------------------------------

type Env = Seq Val

emptyEnv :: Env
emptyEnv = Data.Sequence.empty

--------------------------------------------------------------------------------

valTy :: Val -> Ty
valTy val = case val of
  TtV         -> Unit
  TokenV _    -> Token
  BitV _      -> Bit
  U64V _      -> U64
  NatV _      -> Nat
  StructV xs  -> Struct (map valTy xs)
  WrapV   n x -> Named n (valTy x)
  FunV {}     -> error "valTy: FunV"

--------------------------------------------------------------------------------
