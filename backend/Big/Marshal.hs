
-- marshalling to/from bigint values (useful for debugging)

module Big.Marshal where

--------------------------------------------------------------------------------

import AST.Val
import Big.Limbs

--------------------------------------------------------------------------------

limbsToBigIntVal' :: Limbs -> Val
limbsToBigIntVal' limbs = StructV (map U64V limbs)

limbsToBigIntVal :: Limbs -> Val
limbsToBigIntVal limbs = WrapV name (limbsToBigIntVal' limbs) where
  name = "BigInt" ++ show (length limbs)

mbLimbsFromU64Vals_ :: [Val] -> Maybe Limbs
mbLimbsFromU64Vals_ = go where
  go []              = Just []
  go (U64V w : rest) = (w:) <$> go rest
  go _               = Nothing

limbsFromU64Vals_ :: [Val] -> Limbs
limbsFromU64Vals_ what = case mbLimbsFromU64Vals_ what of
  Just limbs -> limbs
  Nothing    -> error "limbsFromU64Vals: expecting a list of U64 values"

mbLimbsFromBigIntVal' :: Val -> Maybe Limbs
mbLimbsFromBigIntVal' (StructV vals) = mbLimbsFromU64Vals_ vals
mbLimbsFromBigIntVal' _              = Nothing

limbsFromBigIntVal' :: Val -> Limbs
limbsFromBigIntVal' val = case mbLimbsFromBigIntVal' val of
  Just limbs -> limbs
  Nothing    -> error "limbsFromBigInt: expecting a struct encoding a bigint"

limbsFromBigIntVal :: Val -> Limbs
limbsFromBigIntVal value = case value of
  WrapV name (StructV vals) -> 
    let ref_name = "BigInt" ++ show (length vals)
    in  if name == ref_name 
           then limbsFromU64Vals_ vals 
           else error "limbsFromBigIntVal: wrong newtype"
  _ -> error "limbsFromBigIntVal: expecting a newtype over a struct"

--------------------------------------------------------------------------------

integerToBigIntVal' :: NLimbs -> Integer -> Val
integerToBigIntVal' nlimbs n = limbsToBigIntVal' (integerToLimbs nlimbs n)

integerToBigIntVal :: NLimbs -> Integer -> Val
integerToBigIntVal nlimbs n = limbsToBigIntVal (integerToLimbs nlimbs n)

mbIntegerFromBigIntVal' :: Val -> Maybe Integer
mbIntegerFromBigIntVal' val = integerFromLimbs <$> mbLimbsFromBigIntVal' val

integerFromBigIntVal' :: Val -> Integer
integerFromBigIntVal' = integerFromLimbs . limbsFromBigIntVal'

integerFromBigIntVal :: Val -> Integer
integerFromBigIntVal = integerFromLimbs . limbsFromBigIntVal

--------------------------------------------------------------------------------

showBigIntVal :: Val -> String
showBigIntVal = show . integerFromBigIntVal

printBigIntVal :: Val -> IO ()
printBigIntVal = putStrLn . showBigIntVal

--------------------------------------------------------------------------------
