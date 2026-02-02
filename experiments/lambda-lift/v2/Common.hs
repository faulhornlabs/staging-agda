
{-# LANGUAGE GADTSyntax, StandaloneDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, PatternSynonyms #-}
module Common where

--------------------------------------------------------------------------------

import Seq

--------------------------------------------------------------------------------

type Level = Int
type Top   = Int
type Arity = Int

--------------------------------------------------------------------------------
-- *** types

data Ty 
  = Arrow Ty Ty 
  | NatT
  | BoolT
  deriving (Eq,Ord,Show)

infixr 1 ~>
(~>) :: Ty -> Ty -> Ty
(~>) = Arrow

isArrow :: Ty -> Bool
isArrow (Arrow _ _) = True
isArrow _           = False

showTy :: Ty -> String 
showTy = go 0 where
  
  go d NatT  = "Nat"
  go d BoolT = "Bool"
  go d (Arrow s t) = inParens (d > arr_prec) $ go (arr_prec+1) s ++ " -> " ++ go arr_prec t
 
  arr_prec = 0

inParens :: Bool -> String -> String
inParens False s = s
inParens True  s = "(" ++ s ++ ")"

----------------------------------------
-- *** function signatures

data Sig 
  = MkSig (Seq Ty) Ty
  deriving (Eq,Show)

sigArity :: Sig -> Arity
sigArity (MkSig args _ret) = seqLength args

sigToTy :: Sig -> Ty
sigToTy (MkSig args ret) = go (seqToList args) where
  go []     = ret
  go (t:ts) = Arrow t (go ts)

--------------------------------------------------------------------------------
-- *** contexts

type Ctx = Seq Ty

emptyCtx :: Ctx
emptyCtx = emptySeq

ctxLevel :: Ctx -> Level
ctxLevel = seqLength

ctxToList :: Ctx -> [Ty]
ctxToList = seqToList

infixl 5 |>>
(|>>) :: Ctx -> Sig -> Ctx
(|>>) ctx (MkSig args _ret) = ctx <> args

--------------------------------------------------------------------------------
-- *** literals

data Literal
  = NatL  Integer
  | BoolL Bool
  deriving (Eq,Show)

litTy :: Literal -> Ty
litTy lit = case lit of
  NatL  _ -> NatT
  BoolL _ -> BoolT

--------------------------------------------------------------------------------
-- *** primops

data PrimOp a where
  -- arithmetic
  Add  :: a -> a -> PrimOp a 
  Sub  :: a -> a -> PrimOp a 
  Mul  :: a -> a -> PrimOp a 
  Div  :: a -> a -> PrimOp a
  Mod  :: a -> a -> PrimOp a
  -- comparison
  Equ  :: a -> a -> PrimOp a
  IFTE :: a -> a -> a -> PrimOp a

deriving instance Functor     PrimOp
deriving instance Foldable    PrimOp
deriving instance Traversable PrimOp

deriving instance Show a => Show (PrimOp a)

primOpTy :: PrimOp Ty -> Ty
primOpTy op = case op of
  Add  NatT NatT           -> NatT
  Sub  NatT NatT           -> NatT
  Mul  NatT NatT           -> NatT
  Div  NatT NatT           -> NatT
  Mod  NatT NatT           -> NatT
  Equ        s t | s == t  -> BoolT
  IFTE BoolT s t | s == t  -> s
  _ -> error "primOpTy: invalid primop application"

--------------------------------------------------------------------------------
-- *** multi-argument functions

-- a (top-level) function can have several arguments
data Fun exp = MkFun 
  { funSig  :: Sig
  , funBody :: exp 
  }
  deriving (Show,Functor)

pattern Fun_ args ret body = MkFun (MkSig args ret) body

funArity :: Fun a -> Arity
funArity (MkFun sig _body) = sigArity sig

funTy :: Fun a -> Ty
funTy (MkFun sig _body) = sigToTy sig

--------------------------------------------------------------------------------
-- *** multi-application

data Apply fun arg = MkApp
  { appFunc :: fun
  , appArgs :: Seq arg
  }
  deriving Show

--------------------------------------------------------------------------------

