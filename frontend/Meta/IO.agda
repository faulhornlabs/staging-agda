

{-# OPTIONS --type-in-type --show-implicit #-}

module Meta.IO where

--------------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality

open import Data.Nat
open import Data.Vec using ( _∷_ )
open import Data.String
open import Data.Maybe
open import Data.List using ( List ; _∷_ ; [] )
open import Data.Product using ( _×_ ; _,_ )

open import Effect.Applicative
open import Effect.Monad.Identity
  using    ( Identity ; mkIdentity ; runIdentity )
  renaming ( applicative to identityApplicative )

open import Meta.Ty 
open import Meta.Val
open import Meta.Ctx
open import Meta.Show

--------------------------------------------------------------------------------
-- HOAS version

private variable
  ty  : Ty
  s t : Ty
  vty : VTy

--------------------------------------------------------------------------------
-- primop-level, token-passing IO primitives
--
-- but the token-passing is added at the definition of PrimOp:
--
-- > WrapPrimIO    : PrimIO tm t -> tm Token -> PrimOp tm (Pair t Token)
--

data PrimIO (tm : Ty -> Set) : Ty -> Set where
  -- basic input/output
  PrimGet   : String -> (ty : Ty)                 -> PrimIO tm ty
  PrimPut   : String -> tm ty                     -> PrimIO tm Unit
  PrimPrint : String -> tm ty                     -> PrimIO tm Unit
  -- memory allocation
  PrimAlloc : (vty : VTy) -> tm U64               -> PrimIO tm (Ptr vty)
  PrimFree  : tm (Ptr vty)                        -> PrimIO tm Unit     
  -- reading/writing arrays
  PrimRead  : {eq : vtyToTy vty ≡ ty} -> tm (Ptr vty) -> tm Idx          -> PrimIO tm ty  
  PrimWrite : {eq : vtyToTy vty ≡ ty} -> tm (Ptr vty) -> tm Idx -> tm ty -> PrimIO tm Unit
  -- for loop (from 0..n-1)
  PrimLen   : tm (Ptr vty)                        -> PrimIO tm U64           -- could be pure iguess...
  PrimLoop  : tm U64 -> tm (U64 ⇒ IO Unit)        -> PrimIO tm Unit
  
traversePrimIO : {F : Set -> Set} -> {tm₁ tm₂ : Ty -> Set} -> RawApplicative F -> ({s : Ty} -> tm₁ s -> F (tm₂ s)) -> {t : Ty} -> PrimIO tm₁ t -> F (PrimIO tm₂ t)
traversePrimIO {F = F} {tm₁ = tm₁} {tm₂ = tm₂} applicative f what = go what where

  pure  = RawApplicative.pure  applicative
  _<*>_ = RawApplicative._<*>_ applicative
  _<$>_ = RawApplicative._<$>_ applicative

  infixl 4 _<*>_
  
  go : {t : Ty} -> PrimIO tm₁ t -> F (PrimIO tm₂ t)
  go (PrimGet   name ty           ) = pure (PrimGet   name  ty)
  go (PrimPut   name what         ) = (| PrimPut   (pure name) (f what)            |)
  go (PrimPrint name what         ) = (| PrimPrint (pure name) (f what)            |)
  go (PrimAlloc vty size          ) =  (PrimAlloc vty) <$> (f size)  -- (| PrimAlloc (pure vty ) (f size)            |) 
  go (PrimFree  ptr               ) = (| PrimFree  (f ptr)                         |)
  go (PrimRead  {eq = eq} ptr j   ) = (| (PrimRead  {eq = eq}) (f ptr) (f j)       |)
  go (PrimWrite {eq = eq} ptr j y ) = (| (PrimWrite {eq = eq}) (f ptr) (f j) (f y) |)
  go (PrimLen   ptr               ) = (| PrimLen    (f ptr)                        |)
  go (PrimLoop  len body          ) = (| PrimLoop   (f len) (f body)               |)

mapPrimIO : {tm₁ tm₂ : Ty -> Set} -> ({s : Ty} -> tm₁ s -> tm₂ s) -> {t : Ty} -> PrimIO tm₁ t -> PrimIO tm₂ t
mapPrimIO {tm₁} {tm₂} f what = runIdentity (traversePrimIO {F = Identity} identityApplicative h′ what) where
  h′ : ∀ {t} -> tm₁ t -> Identity (tm₂ t)
  h′ tm = mkIdentity (f tm)

----------------------------------------
-- Raw version

-- Note: the actual arguments are passed as separate lists
data RawPrimIO : Set where
  RawPrimGet    : String -> Ty  -> RawPrimIO
  RawPrimPut    : String        -> RawPrimIO
  RawPrimPrint  : String        -> RawPrimIO
  RawPrimAlloc  : VTy           -> RawPrimIO
  RawPrimFree   :                  RawPrimIO
  RawPrimRead   : VTy           -> RawPrimIO 
  RawPrimWrite  : VTy           -> RawPrimIO
  RawPrimLen    :                  RawPrimIO
  RawPrimLoop   :                  RawPrimIO

showRawPrimIOPrec : ℕ -> RawPrimIO -> String
showRawPrimIOPrec  = go where
  go : ℕ -> RawPrimIO  -> String
  go d (RawPrimGet name ty ) = showParen (d >ᵇ appPrec) ("RawPrimGet "   ++ showString name ++ " " ++ showTyPrec appPrec₊₁ ty  )
  go d (RawPrimPut name    ) = showParen (d >ᵇ appPrec) ("RawPrimPut "   ++ showString name)
  go d (RawPrimPrint name  ) = showParen (d >ᵇ appPrec) ("RawPrimPrint " ++ showString name)
  go d (RawPrimRead  vty   ) = showParen (d >ᵇ appPrec) ("RawPrimRead "  ++ showTyPrec appPrec₊₁ (vtyToTy vty))
  go d (RawPrimWrite vty   ) = showParen (d >ᵇ appPrec) ("RawPrimWrite " ++ showTyPrec appPrec₊₁ (vtyToTy vty))
  go d (RawPrimAlloc vty   ) = showParen (d >ᵇ appPrec) ("RawPrimAlloc " ++ showTyPrec appPrec₊₁ (vtyToTy vty))
  go d (RawPrimFree        ) =                           "RawPrimFree"
  go d (RawPrimLen         ) =                           "RawPrimLen"
  go d (RawPrimLoop        ) =                           "RawPrimLoop"

primIOForget : {tm : Ty -> Set} -> {A : Set} -> {t : Ty} -> ({t : Ty} -> tm t -> A) -> PrimIO tm t -> RawPrimIO × List A
primIOForget {tm} {A} f = go where
  go : {ty : Ty} -> PrimIO tm ty -> RawPrimIO × List A
  go (PrimGet   name ty             ) = RawPrimGet name ty , []
  go (PrimPut   name what           ) = RawPrimPut name    , (f what)                 ∷ []
  go (PrimPrint name what           ) = RawPrimPrint name  , (f what)                 ∷ []
  go (PrimAlloc vty size            ) = RawPrimAlloc vty   , (f size)                 ∷ []
  go (PrimFree  ptr                 ) = RawPrimFree        , (f ptr )                 ∷ []
  go (PrimRead  {vty = vty} ptr j   ) = RawPrimRead  vty   , (f ptr ) ∷ (f j)         ∷ []
  go (PrimWrite {vty = vty} ptr j y ) = RawPrimWrite vty   , (f ptr ) ∷ (f j) ∷ (f y) ∷ []
  go (PrimLen   ptr                 ) = RawPrimLen         , (f ptr )                 ∷ []
  go (PrimLoop  len body            ) = RawPrimLoop        , (f len ) ∷ (f body)      ∷ []

--------------------------------------------------------------------------------

