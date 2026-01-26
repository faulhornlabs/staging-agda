
{-# LANGUAGE GADTSyntax, BlockArguments, GeneralizedNewtypeDeriving, PatternSynonyms #-}
module AST.Val where

--------------------------------------------------------------------------------

import Data.Word
import Text.Read

import Data.Sequence ( Seq , empty , (|>) )
import qualified Data.Sequence as Seq

import Control.Monad.Identity

import Foreign.ForeignPtr

import AST.Ty
import AST.Literal
import Aux.Misc

--------------------------------------------------------------------------------

-- used only for the evaluator
newtype RunTimeFun 
  = MkRunTimeFun (Val -> IO Val)

mkMultiFunVal :: NArgs -> (Seq Val -> IO Val) -> IO Val
mkMultiFunVal nargs eval = go nargs Seq.empty where
  go :: NArgs -> Seq Val -> IO Val
  go 0 args = eval args
  go n args = return $ FunV $ MkRunTimeFun \x -> go (n-1) (args |> x)

-- also used only for the evaluator (needed because it's monadic??)
newtype Thunk 
  = MkThunk (IO Val)

pattern Fun f = FunV   (MkRunTimeFun f)
pattern Thk g = ThunkV (MkThunk      g)

-- hackety hack hack
instance Eq   RunTimeFun where (==)     = error "RunTimeFun/Eq"
instance Read RunTimeFun where readPrec = error "RunTimeFun/Read"
instance Show RunTimeFun where show _   = "<<runtime function>>"

instance Eq   Thunk where (==)     = error "Thunk/Eq"
instance Read Thunk where readPrec = error "Thunk/Read"
instance Show Thunk where show _   = "<<thunk>>"

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
  --
  TokenV   :: Int           -> Val                       -- ^ used only for token-passing IO
  PtrV     :: FlatTy -> ForeignPtr Word8 -> Int -> Val   -- ^ used only in the interperter
  FunV     :: RunTimeFun    -> Val                       -- ^ used only for the interpreter
  ThunkV   :: Thunk         -> Val                       -- ^ used only for interpretation (??)

forceVal :: Val -> IO Val
forceVal (Thk delayed) = delayed >>= forceVal
forceVal value         = return value

pattern PairV x y = StructV [x,y]

valApp :: Val -> Val -> IO Val
valApp fun arg = do
  fun' <- forceVal fun 
  case fun' of
    FunV (MkRunTimeFun f) -> do { arg' <- forceVal arg ; f arg }
    _ -> error "valApp: application to a non-function"

valApps :: Val -> [Val] -> IO Val
valApps fun []     = return fun
valApps fun (a:as) = do 
  fun' <- valApp fun a
  valApps fun' as

deriving instance Eq   Val
deriving instance Show Val
deriving instance Read Val

-- hackety hack hack
instance Read (ForeignPtr a) where readPrec = error "ForeignPtr/Read"

{-
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
  PtrV {}     -> False
  ThunkV {}   -> False

mbAtomicValue :: Val -> Maybe Val
mbAtomicValue value = if isAtomicValue value 
  then Just value
  else Nothing
-}

--------------------------------------------------------------------------------

literalToVal :: Literal -> Val
literalToVal = go where
  go :: Literal -> Val
  go lit = case lit of
    TtL        -> TtV         
    BitL b     -> BitV b      
    U64L x     -> U64V x      
    NatL n     -> NatV n      
    StructL ls -> StructV (map go ls)  
    WrapL n l  -> WrapV n (go l)

--------------------------------------------------------------------------------

type Env = Seq Val

emptyEnv :: Env
emptyEnv = Data.Sequence.empty

--------------------------------------------------------------------------------

valTy :: Val -> Ty
valTy val = case val of
  TtV          -> Unit
  TokenV _     -> Token
  BitV _       -> Bit
  U64V _       -> U64
  NatV _       -> Nat
  StructV xs   -> Struct (map valTy xs)
  WrapV   n x  -> Named n (valTy x)
  PtrV fty _ _ -> Ptr_ (fromFlatTy fty)
  FunV {}      -> error "valTy: FunV"
  ThunkV {}    -> error "valTy: Thunk"

--------------------------------------------------------------------------------
