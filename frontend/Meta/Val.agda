
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
  n m : ℕ
  ts  : Vec Ty m
  nam : String

  s′ t′ : VTy
  ts′   : Vec VTy m

{-# NO_POSITIVITY_CHECK #-}
data Val′ : VTy -> Set where
  TtV′     :                     Val′ Unit′
  BitV′    : Bool             -> Val′ Bit′
  U64V′    : Word64           -> Val′ U64′
  NatV′    : ℕ                -> Val′ Nat′
  StructV′ : HList Val′ ts′   -> Val′ (Struct′ ts′)
  WrapV′   : Val′ t′          -> Val′ (Named′ nam t′)

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

{-# TERMINATING #-}
Val′-to-Val : Val′ t′ -> Val (vtyToTy t′)
Val′-to-Val = go where
  go : {ty′ : VTy} -> Val′ ty′ -> Val (vtyToTy ty′)
  go  TtV′     = TtV
  go (BitV′ b) = BitV b
  go (U64V′ x) = U64V x
  go (NatV′ n) = NatV n
  go (StructV′ xs) = StructV (mapHList′ {F = Val′} {G = Val} vtyToTy go xs)
  go (WrapV′   x ) = WrapV (go x)

{-# TERMINATING #-}
unsafe-Val-to-Val′ : Val t -> Val′ (unsafeTyToVTy t)
unsafe-Val-to-Val′ = go where
  {-# NON_COVERING #-}
  go : {ty : Ty} -> Val ty -> Val′ (unsafeTyToVTy ty)
  go TtV     = TtV′
  go (BitV b) = BitV′ b
  go (U64V x) = U64V′ x
  go (NatV n) = NatV′ n
  go (StructV xs) = StructV′ (mapHList′ {F = Val} {G = Val′} unsafeTyToVTy go xs)
  go (WrapV   x ) = WrapV′ (go x)

--------------------------------------------------------------------------------

valVec : Vec (Val t) n -> Val (Meta.Ty.Vect n t)
valVec v = StructV (vecToHList Val v) 

valVec′ : {t : VTy} -> Vec (Val′ t) n -> Val′ (Meta.Ty.Vect′ n t)
valVec′ v = StructV′ (vecToHList Val′ v) 

--------------------------------------------------------------------------------

valApp : Val (s ⇒ t) -> Val s -> Val t
valApp (FunV f) x = f x

valIO : Val (IO t) -> ⊥
valIO ()

--------------------------------------------------------------------------------
