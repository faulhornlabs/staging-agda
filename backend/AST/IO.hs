
{-# LANGUAGE GADTSyntax, GeneralizedNewtypeDeriving #-}
module AST.IO where

--------------------------------------------------------------------------------

import AST.Ty

--------------------------------------------------------------------------------

data RawIO raw where
  RawHalt   :: RawIO raw
  RawGet    :: String -> Ty  -> raw -> RawIO raw
  RawPut    :: String -> raw -> raw -> RawIO raw

deriving instance Eq   raw => Eq   (RawIO raw)
deriving instance Show raw => Show (RawIO raw)
deriving instance Read raw => Read (RawIO raw)

--------------------------------------------------------------------------------

