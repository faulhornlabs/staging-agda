
{-# LANGUAGE ScopedTypeVariables, StrictData, GADTSyntax, StandaloneDeriving, PatternSynonyms #-}
module AST.Ty where

--------------------------------------------------------------------------------

import Data.Map (Map)
import qualified Data.Map as Map

--------------------------------------------------------------------------------

{-
-- value types
data VTy : Set where
  Unit_   :: VTy
  Token_  :: VTy
  Bit_    :: VTy
  U64_    :: VTy
  Nat_    :: VTy
  Struct_ :: [VTy] -> VTy
  Named_  :: String -> VTy -> VTy

deriving instance Eq   VTy
deriving instance Ord  VTy
deriving instance Show VTy
deriving instance Read VTy
-}

-- all types
data Ty where
  Unit    :: Ty
  Arrow   :: Ty -> Ty -> Ty
  Bit     :: Ty
  U64     :: Ty
  Nat     :: Ty
  Struct  :: [Ty] -> Ty
  Named   :: String -> Ty -> Ty
  Token   :: Ty                           -- used after translating IO to token passing?
  Ptr_    :: Ty -> Ty

deriving instance Eq   Ty
deriving instance Ord  Ty
deriving instance Show Ty
deriving instance Read Ty

pattern Pair x y = Struct [x,y]

infixr 1 ~>
(~>) :: Ty -> Ty -> Ty
(~>) = Arrow

io_ :: Ty -> Ty
io_ ty = Token ~> Pair ty Token

isArrowTy :: Ty -> Bool
isArrowTy (Arrow _ _) = True
isArrowTy _           = False

isAtomicBuiltInTy :: Ty -> Bool
isAtomicBuiltInTy ty = case ty of
  Unit -> True
  Bit  -> True
  U64  -> True
  Nat  -> True
  _    -> False

{-
isIOTy_ :: Ty -> Bool
isIOTy_ (IO_ t) = True
isIOTy_ _       = False

isIOTy :: Ty -> Maybe Ty
isIOTy (IO_ t) = Just t
isIOTy _       = Nothing
-}

--------------------------------------------------------------------------------

bigIntTy' :: Int -> Ty
bigIntTy' nlimbs = Struct $ replicate nlimbs U64

bigIntTy :: Int -> Ty
bigIntTy nlimbs = Named ("BigInt" ++ show nlimbs) $ bigIntTy' nlimbs

--------------------------------------------------------------------------------

data Typed a 
  = MkTyped !Ty !a
  deriving (Eq,Show)

typeOf :: Typed a -> Ty
typeOf (MkTyped t _) = t

forgetTy :: Typed a -> a
forgetTy (MkTyped _ x) = x

unzipTy :: [Typed a] -> ([Ty] , [a])
unzipTy = go where
  go []                   = ([] , [])
  go (MkTyped t y : rest) = case go rest of { (ts,ys) -> (t:ts, y:ys) }

--------------------------------------------------------------------------------

tyApp :: Ty -> [Ty] -> Maybe Ty
tyApp = go where
  go :: Ty -> [Ty] -> Maybe Ty
  go funTy []     = Just funTy
  go funTy (a:as) = case funTy of
    Arrow s t -> if a == s then go t as else Nothing
    _         -> Nothing

--------------------------------------------------------------------------------

data FunTy = MkFunTy 
  { _argTys   :: [Ty] 
  , _returnTy :: Ty
  }
  deriving (Eq,Show)

isFunctionTy :: Ty -> Maybe FunTy
isFunctionTy what =
  case go what of
    ([],_) -> Nothing
    (as,t) -> Just (MkFunTy as t)
  where
    go (Arrow s t) = case go t of (us,v) -> (s:us,v) 
    go t           = ([],t)

isFunctionTy_ :: Ty -> Bool
isFunctionTy_ (Arrow _ _) = True
isFunctionTy_ _           = False

fromFunTy :: FunTy -> Ty
fromFunTy (MkFunTy args ret) = go args where
  go []     = ret
  go (u:us) = Arrow u (go us)

toFunTy :: Ty -> FunTy
toFunTy ty = case isFunctionTy ty of
  Just funty -> funty
  Nothing    -> error "toFunTy: was not lambda"

--------------------------------------------------------------------------------
 
