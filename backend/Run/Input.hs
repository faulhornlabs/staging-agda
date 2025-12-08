
-- Input / Output

module Run.Input where

--------------------------------------------------------------------------------

import Control.Monad
import Control.Applicative

import Data.IORef
import System.IO.Unsafe

import Data.Char
import Data.List.Split
import Data.Maybe
import Text.Read

import qualified Data.Map.Strict as Map

import AST.Ty
import AST.Val

import Big.Marshal

--------------------------------------------------------------------------------

-- TMP for testing
fakeInputs = 
  [ ("x" , 11   )
  , ("y" , 202  )
  , ("z" , 3003 )
  ]

--------------------------------------------------------------------------------

type Inputs  = Map.Map String Integer
type Outputs = Map.Map String Integer

emptyInputs :: Inputs
emptyInputs  = Map.fromList fakeInputs -- Map.empty

emptyOutputs :: Outputs
emptyOutputs = Map.empty

--------------------------------------------------------------------------------
-- hack for eval in IO 

{-# NOINLINE theInputs  #-}
{-# NOINLINE theOutputs #-}
theInputs, theOutputs :: IORef (Map.Map String Integer)
theInputs  = unsafePerformIO (newIORef emptyInputs )
theOutputs = unsafePerformIO (newIORef emptyOutputs)

runWithInputs :: Inputs -> IO a -> IO (Outputs,a)
runWithInputs inputs action = do
  writeIORef theInputs inputs
  y <- action
  outs <- readIORef theOutputs
  return (outs,y)

getInputIO :: String -> IO (Maybe Integer)
getInputIO name = do
  inputs <- readIORef theInputs
  return (Map.lookup name inputs)

getInputIO_ :: String -> IO Integer
getInputIO_ name = do
  mb <- getInputIO name
  case mb of
    Just y  -> return y
    Nothing -> fail $ "input `" ++ name ++ "` not found"

putOutputIO :: String -> Integer -> IO ()
putOutputIO name x = do
  modifyIORef' theOutputs (Map.insert name x)
  putStrLn $ name ++ " = " ++ show x

--------------------------------------------------------------------------------

-- | We use a trivial format:
--
-- > myinput = 123456789
--
-- TODO: maybe support some limited form of structures, eg. giving an elliptic
-- curve points as 
--
-- > ecpoint = ( 1234 , 5678 )
--
-- letting the automatic marshalling solve the internal bigints (field elements)
--
parseInputLine :: String -> Maybe (String,Integer)
parseInputLine ln = case splitOn "=" (filter (not . isSpace) ln) of
  [name,value] -> case readMaybe value of
    Just k  -> Just (name,k)
    Nothing -> Nothing
  _ -> Nothing

parseInputs :: String -> Map.Map String Integer
parseInputs = Map.fromList . mapMaybe parseInputLine . lines

printOutputs :: Map.Map String Integer -> IO ()
printOutputs table = forM_ (Map.toList table) $ \(name,value) -> do
  putStrLn $ name ++ " = " ++ show value

--------------------------------------------------------------------------------

marshalInto :: Ty -> Integer -> Maybe Val
marshalInto ty what = case ty of

  Unit       -> Just $ TtV
  Bit        -> Just $ BitV (what /= 0)
  U64        -> Just $ U64V (fromInteger what)
  Nat        -> Just $ NatV (fromInteger what)

  Named n t  -> WrapV n <$> marshalInto t what

  Struct tys -> if all (==U64) tys
    then Just $ integerToBigIntVal' (length tys) what
    else Nothing

  _ -> Nothing

--------------------------------------------------------------------------------

marshalFrom :: Val -> Maybe Integer
marshalFrom value = case value of

  TtV        -> Just $ 0
  BitV b     -> Just $ if b then 1 else 0
  U64V x     -> Just $ fromIntegral x
  NatV k     -> Just $ fromIntegral k

  WrapV _ x  -> marshalFrom x

  StructV _  -> mbIntegerFromBigIntVal' value

  _ -> Nothing

--------------------------------------------------------------------------------
