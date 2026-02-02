
{-# LANGUAGE BlockArguments, PatternSynonyms #-}
module Val where

--------------------------------------------------------------------------------

import Data.Map ( Map )
import qualified Data.Map as Map 

import Seq
import Common

-- import qualified HOAS       as HOAS
-- import qualified Term       as Term
-- import qualified Preprocess as Pre
-- import qualified Lift       as Lift

--------------------------------------------------------------------------------
-- * values

data Val
  = VBool Bool
  | VNat  Integer
  | VLam  Ty (Val -> Val)

instance Show Val where
  show (VBool b  ) = show b
  show (VNat  n  ) = show n
  show (VLam  t _) = "< \\(_:" ++ showTy t ++ ") -> ... >"

{-
-- doesn't work out...
valTy :: Val -> Ty
valTy = go where
  go VBool = BoolT
  go VNat  = NatT
  go (VLam s f) = Arrow s $ go (f undefined)
-}

litToVal :: Literal -> Val
litToVal lit = case lit of
  BoolL b -> VBool b
  NatL  n -> VNat  n

valApp :: Val -> Val -> Val
valApp fun arg = case fun of
  VLam t f -> f arg
  _        -> error "valApp: application to a non-lambda value"

valApps :: Val -> [Val] -> Val
valApps fun []     = fun
valApps fun (a:as) = valApps (valApp fun a) as

type Env = Seq Val

--------------------------------------------------------------------------------

evalPrimOp :: PrimOp Val -> Val
evalPrimOp op = case op of
  -- arithmetic
  Add  (VNat x)  (VNat y)  -> VNat (x + y)
  Sub  (VNat x)  (VNat y)  -> VNat (x - y)
  Mul  (VNat x)  (VNat y)  -> VNat (x * y)
  Div  (VNat x)  (VNat y)  -> VNat (x `div` y)
  Mod  (VNat x)  (VNat y)  -> VNat (x `mod` y)
  -- comparison
  Equ  (VBool x) (VBool y) -> VBool (x == y)
  Equ  (VNat  x) (VNat  y) -> VBool (x == y)
  IFTE (VBool c) x y       -> if c then x else y

--------------------------------------------------------------------------------

