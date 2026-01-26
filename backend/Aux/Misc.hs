
module Aux.Misc where

--------------------------------------------------------------------------------

import Data.Word

import Debug.Trace
import Text.Show.Pretty

--------------------------------------------------------------------------------

type Level  = Int
type TopLev = Int
type NArgs  = Int

--------------------------------------------------------------------------------
-- multi-lambdas and multi-applications

data Lams ty body
  = MkLams ty body
  deriving Show

data Apps f arg
  = MkApps f [arg]
  deriving Show

--------------------------------------------------------------------------------

debug' :: Show a => Bool -> String -> a -> b -> b
debug' lf s x y = trace (newline ++ ">>> " ++ s ++ " = " ++ show x) y where
  newline = if lf then "\n" else ""

debug, debugLn :: Show a => String -> a -> b -> b
debug   = debug' False
debugLn = debug' True

debugNice' :: Show a => Bool -> String -> a -> b -> b
debugNice' lf s x y = trace (newline ++ ">>> " ++ s ++ " = " ++ ppShow x) y where
  newline = if lf then "\n" else ""

debugNice, debugNiceLn :: Show a => String -> a -> b -> b
debugNice   = debugNice' False
debugNiceLn = debugNice' True

--------------------------------------------------------------------------------

type Bit = Bool

zeroBit = False
oneBit  = True

bitToWord64 :: Bit -> Word64
bitToWord64 False = 0
bitToWord64 True  = 1

--------------------------------------------------------------------------------

safeZip :: [a] -> [b] -> [(a,b)]
safeZip = safeZipWith (,)

safeZipWith :: (a -> b -> c) -> [a] -> [b] -> [c] 
safeZipWith f = go where
  go []     []     = []
  go (x:xs) (y:ys) = f x y : go xs ys
  go _      _      = error "safeZipWith: inputs have different lengths"

--------------------------------------------------------------------------------

pairs :: [a] -> [(a,a)]
pairs []  = []
pairs [_] = []
pairs (x:y:rest) = (x,y) : pairs (y:rest)

--------------------------------------------------------------------------------
