
module Shared where

--------------------------------------------------------------------------------

import Text.Show

import qualified Data.Sequence as Seq 
import Data.Sequence ( Seq , (|>) )

--------------------------------------------------------------------------------

type Level  = Int
type TopLev = Int
type NArgs  = Int

--------------------------------------------------------------------------------
-- *** values

data Val 
  = VInt Int
  | VLam (Val -> Val)

instance Eq Val where
  (==) (VInt a) (VInt b) = a == b
  (==) _        _        = False

instance Show Val where
  show (VInt k) = show k
  show (VLam _) = "<<lambda>>"

valApp :: Val -> Val -> Val
valApp fun arg = case fun of
  VLam f -> f arg
  _      -> error "valApp: application to a non-lambda value"

valApps :: Val -> [Val] -> Val
valApps fun []     = fun
valApps fun (a:as) = valApps (valApp fun a) as

--------------------------------------------------------------------------------
-- *** environment

type Env = Seq Val

emptyEnv :: Env
emptyEnv = Seq.empty

--------------------------------------------------------------------------------
-- *** primops

data PrimOp tm where
  Add :: tm -> tm       -> PrimOp tm
  Sub :: tm -> tm       -> PrimOp tm
  Mul :: tm -> tm       -> PrimOp tm
  Div :: tm -> tm       -> PrimOp tm
  Mod :: tm -> tm       -> PrimOp tm
  IfZ :: tm -> tm -> tm -> PrimOp tm
  deriving (Show,Functor,Foldable,Traversable)

evalPrimOp :: PrimOp Val -> Val
evalPrimOp op = case op of
  Add (VInt x) (VInt y)  -> VInt (x + y)
  Sub (VInt x) (VInt y)  -> VInt (x - y)
  Mul (VInt x) (VInt y)  -> VInt (x * y)
  Div (VInt x) (VInt y)  -> VInt (x `div` y)
  Mod (VInt x) (VInt y)  -> VInt (x `mod` y)
  IfZ (VInt c) x y       -> if (c == 0) then x else y
  _ -> error $ "evalPrimOp: illegal combination: " ++ pretty op

--------------------------------------------------------------------------------
-- *** multi-lambdas and multi-applications

data Lams body
  = MkLams NArgs body
  deriving Show

data Apps f arg
  = MkApps f [arg]
  deriving Show

--------------------

-- used for pretty-printing
data App1 f arg 
  = Fun1 f
  | App1 (App1 f arg) arg
  deriving Show

toApp1 :: Apps f arg -> App1 f arg
toApp1 (MkApps f args) = go (Fun1 f) args where
  go fun []     = fun
  go fun (a:as) = go (App1 fun a) as

fromApp1 :: App1 f arg -> Apps f arg
fromApp1 = go where
  go (Fun1 f)   = MkApps f []
  go (App1 f x) = case go f of 
    MkApps f xs -> MkApps f (xs ++ [x])

--------------------------------------------------------------------------------
-- *** pretty-printing

type Prec = Int

class Pretty a where
  prettyPrec :: Prec -> a -> ShowS
  pretty     :: a -> String
  prettyPrec _ x s = pretty x ++ s
  pretty      x    = prettyPrec 0 x ""

prettyS :: Pretty a => a -> ShowS
prettyS = prettyPrec 0

pp :: Pretty a => a -> IO ()
pp = putStrLn . pretty

-- ???
let_prec = 1  :: Prec
in_prec  = 1  :: Prec
lam_prec = 2  :: Prec
ifz_prec = 3  :: Prec
add_prec = 6  :: Prec 
mul_prec = 7  :: Prec 
app_prec = 10 :: Prec

instance Pretty Val where pretty = show

instance (Pretty f, Pretty arg) => Pretty (App1 f arg) where
  prettyPrec d (Fun1 fun    ) = prettyPrec d fun
  prettyPrec d (App1 fun arg) = showParen (d > app_prec) 
                              $ prettyPrec app_prec fun . showChar ' ' . prettyPrec (app_prec+1) arg

instance (Pretty f, Pretty arg) => Pretty (Apps f arg) where
  prettyPrec d apps = prettyPrec d (toApp1 apps)

instance Pretty tm => Pretty (PrimOp tm) where
  prettyPrec d op = case op of
    Add x y   -> showParen (d > add_prec) $ prettyPrec add_prec x . showString " + " . prettyPrec (add_prec+1) y
    Sub x y   -> showParen (d > add_prec) $ prettyPrec add_prec x . showString " - " . prettyPrec (add_prec+1) y
    Mul x y   -> showParen (d > mul_prec) $ prettyPrec mul_prec x . showString " * " . prettyPrec (mul_prec+1) y
    Div x y   -> showParen (d > mul_prec) $ prettyPrec mul_prec x . showString " / " . prettyPrec (mul_prec+1) y
    Mod x y   -> showParen (d > mul_prec) $ prettyPrec mul_prec x . showString " % " . prettyPrec (mul_prec+1) y
    IfZ c x y -> showParen (d > ifz_prec) $ showString "ifZero " 
                                          . prettyS c
                                          . showString " then "
                                          . prettyS x
                                          . showString " else "
                                          . prettyS y

--------------------------------------------------------------------------------
