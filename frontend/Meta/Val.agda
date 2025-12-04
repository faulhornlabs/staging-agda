
{-# OPTIONS --type-in-type #-}
module Meta.Val where

--------------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality

open import Data.Empty
open import Data.Nat
open import Data.Bool
open import Data.Word64
open import Data.String
open import Data.List
open import Data.Vec
open import Data.Product

open import Meta.Ty 
open import Meta.HList

--------------------------------------------------------------------------------

private variable
  s t : Ty
  ty : Ty
  n m : ℕ
  ts  : Vec Ty m
  nam : String

--------------------------------------------------------------------------------

{-# NO_POSITIVITY_CHECK #-}
data Literal : Ty -> Set where
  TtL     :                     Literal Unit
  BitL    : Bool             -> Literal Bit
  U64L    : Word64           -> Literal U64
  NatL    : ℕ                -> Literal Nat
  StructL : HList Literal ts -> Literal (Struct ts)
  WrapL   : Literal t        -> Literal (Named nam t)

litVec : Vec (Literal t) n -> Literal (Meta.Ty.Vect n t)
litVec v = StructL (vecToHList Literal v) 

--------------------------------------------------------------------------------

{-# NO_POSITIVITY_CHECK #-}
data Val : Ty -> Set where
  TtV     :                     Val Unit
  BitV    : Bool             -> Val Bit
  U64V    : Word64           -> Val U64
  NatV    : ℕ                -> Val Nat
  StructV : HList Val ts     -> Val (Struct ts)
  WrapV   : Val t            -> Val (Named nam t)
  FunV    : (Val s -> Val t) -> Val (s ⇒ t)
  -- ArrayV  : Vec (Val t) n    -> Val (Array n t)

valVec : Vec (Val t) n -> Val (Meta.Ty.Vect n t)
valVec v = StructV (vecToHList Val v) 

--------------------------------------------------------------------------------

valApp : Val (s ⇒ t) -> Val s -> Val t
valApp (FunV f) x = f x

-- valIO : Val (IO t) -> ⊥
-- valIO ()

--------------------------------------------------------------------------------

{-# TERMINATING #-}
literalToVal : Literal ty -> Val ty
literalToVal = go where
  go : {ty : Ty} -> Literal ty -> Val ty
  go TtL          = TtV
  go (BitL b)     = BitV b
  go (U64L x)     = U64V x 
  go (NatL n)     = NatV n
  go (StructL xs) = StructV (Meta.HList.transform go xs)
  go (WrapL what) = WrapV (go what)

--------------------------------------------------------------------------------
