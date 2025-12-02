

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
  -- memory allocation
  PrimAlloc : tm U64 -> (vty : VTy)               -> PrimIO tm (Ptr vty)
  PrimFree  : tm (Ptr vty)                        -> PrimIO tm Unit     
  -- reading/writing arrays
  PrimRead  : {eq : vtyToTy vty ≡ ty} -> tm (Ptr vty) -> tm Idx          -> PrimIO tm ty  
  PrimWrite : {eq : vtyToTy vty ≡ ty} -> tm (Ptr vty) -> tm Idx -> tm ty -> PrimIO tm Unit

traversePrimIO : {F : Set -> Set} -> {tm₁ tm₂ : Ty -> Set} -> RawApplicative F -> ({s : Ty} -> tm₁ s -> F (tm₂ s)) -> {t : Ty} -> PrimIO tm₁ t -> F (PrimIO tm₂ t)
traversePrimIO {F = F} {tm₁ = tm₁} {tm₂ = tm₂} applicative f what = go what where

  pure  = RawApplicative.pure  applicative
  _<*>_ = RawApplicative._<*>_ applicative

  infixl 4 _<*>_
  
  go : {t : Ty} -> PrimIO tm₁ t -> F (PrimIO tm₂ t)
  go (PrimGet   name ty          ) = pure (PrimGet   name  ty)
  go (PrimAlloc size vty         ) = pure (\size′ -> PrimAlloc size′ vty) <*> (f size)
  go (PrimPut   name what        ) = (| PrimPut   (pure name) (f what)            |)
  go (PrimFree  ptr              ) = (| PrimFree  (f ptr)                         |)
  go (PrimRead  {eq = eq} ptr j  ) = (| (PrimRead  {eq = eq}) (f ptr) (f j)       |)
  go (PrimWrite {eq = eq} ptr j y) = (| (PrimWrite {eq = eq}) (f ptr) (f j) (f y) |)

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
  RawPrimAlloc  : VTy           -> RawPrimIO
  RawPrimFree   :                  RawPrimIO
  RawPrimRead   : VTy           -> RawPrimIO 
  RawPrimWrite  :                  RawPrimIO

showRawPrimIOPrec : ℕ -> RawPrimIO -> String
showRawPrimIOPrec  = go where
  go : ℕ -> RawPrimIO  -> String
  go d (RawPrimGet name ty ) = showParen (d >ᵇ appPrec) ("RawPrimGet "   ++ showString name ++ " " ++ showTyPrec appPrec₊₁ ty  )
  go d (RawPrimPut name    ) = showParen (d >ᵇ appPrec) ("RawPrimPut "   ++ showString name)
  go d (RawPrimAlloc vty   ) = showParen (d >ᵇ appPrec) ("RawPrimAlloc " ++ showTyPrec appPrec₊₁ (vtyToTy vty))
  go d (RawPrimRead  vty   ) = showParen (d >ᵇ appPrec) ("RawPrimRead "  ++ showTyPrec appPrec₊₁ (vtyToTy vty))
  go d (RawPrimFree        ) =                           "RawPrimFree"
  go d (RawPrimWrite       ) =                           "RawPrimWrite"

primIOForget : {tm : Ty -> Set} -> {A : Set} -> {t : Ty} -> ({t : Ty} -> tm t -> A) -> PrimIO tm t -> RawPrimIO × List A
primIOForget {tm} {A} f = go where
  go : {ty : Ty} -> PrimIO tm ty -> RawPrimIO × List A
  go (PrimGet   name ty         ) = RawPrimGet name ty , []
  go (PrimPut   name what       ) = RawPrimPut name    , (f what)                 ∷ []
  go (PrimAlloc size vty        ) = RawPrimAlloc vty   , (f size)                 ∷ []
  go (PrimFree  ptr             ) = RawPrimFree        , (f ptr )                 ∷ []
  go (PrimRead {vty = vty} ptr j) = RawPrimRead  vty   , (f ptr ) ∷ (f j)         ∷ []
  go (PrimWrite ptr j y         ) = RawPrimWrite       , (f ptr ) ∷ (f j) ∷ (f y) ∷ []

--------------------------------------------------------------------------------



{-
--------------------------------------------------------------------------------
-- primop-level, token-passing IO primitives

data PrimIO (tm : Ty -> Set) : Ty -> Set where
  -- basic input/output
  PrimGet   : String -> (ty : Ty)                 -> tm Token -> PrimIO tm (Pair ty   Token)
  PrimPut   : String -> tm ty                     -> tm Token -> PrimIO tm (Pair Unit Token)
  -- memory allocation
  PrimAlloc : tm U64 -> (vty : VTy)               -> tm Token -> PrimIO tm (Pair (Ptr vty) Token)
  PrimFree  : tm (Ptr vty)                        -> tm Token -> PrimIO tm (Pair Unit      Token)
  -- reading/writing arrays
  PrimRead  : {eq : vtyToTy vty ≡ ty} -> tm (Ptr vty) -> tm Idx          -> tm Token -> PrimIO tm (Pair ty   Token)
  PrimWrite : {eq : vtyToTy vty ≡ ty} -> tm (Ptr vty) -> tm Idx -> tm ty -> tm Token -> PrimIO tm (Pair Unit Token)

traversePrimIO : {F : Set -> Set} -> {tm₁ tm₂ : Ty -> Set} -> RawApplicative F -> ({s : Ty} -> tm₁ s -> F (tm₂ s)) -> {t : Ty} -> PrimIO tm₁ t -> F (PrimIO tm₂ t)
traversePrimIO {F = F} {tm₁ = tm₁} {tm₂ = tm₂} applicative f what = go what where

  pure  = RawApplicative.pure  applicative
  _<*>_ = RawApplicative._<*>_ applicative

  infixl 4 _<*>_
  
  go : {t : Ty} -> PrimIO tm₁ t -> F (PrimIO tm₂ t)
  go (PrimGet   name ty            rwt) = pure (\rwt′       -> PrimGet   name  ty  rwt′ ) <*>              (f rwt)    -- Agda huh??
  go (PrimAlloc size vty           rwt) = pure (\size′ rwt′ -> PrimAlloc size′ vty rwt′ ) <*> (f size) <*> (f rwt)    -- ....
  go (PrimPut   name what          rwt) = (| PrimPut   (pure name) (f what)  (f rwt) |)
  go (PrimFree  ptr                rwt) = (| PrimFree  (f ptr)               (f rwt) |)
  go (PrimRead  {eq = eq} ptr j    rwt) = (| (PrimRead  {eq = eq}) (f ptr) (f j)        (f rwt) |)
  go (PrimWrite {eq = eq} ptr j y  rwt) = (| (PrimWrite {eq = eq}) (f ptr) (f j) (f y)  (f rwt) |)

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
  RawPrimAlloc  : VTy           -> RawPrimIO
  RawPrimFree   :                  RawPrimIO
  RawPrimRead   : VTy           -> RawPrimIO 
  RawPrimWrite  :                  RawPrimIO

showRawPrimIOPrec : ℕ -> RawPrimIO -> String
showRawPrimIOPrec  = go where
  go : ℕ -> RawPrimIO  -> String
  go d (RawPrimGet name ty ) = showParen (d >ᵇ appPrec) ("RawPrimGet "   ++ showString name ++ " " ++ showTyPrec appPrec₊₁ ty  )
  go d (RawPrimPut name    ) = showParen (d >ᵇ appPrec) ("RawPrimPut "   ++ showString name)
  go d (RawPrimAlloc vty   ) = showParen (d >ᵇ appPrec) ("RawPrimAlloc " ++ showTyPrec appPrec₊₁ (vtyToTy vty))
  go d (RawPrimRead  vty   ) = showParen (d >ᵇ appPrec) ("RawPrimRead "  ++ showTyPrec appPrec₊₁ (vtyToTy vty))
  go d (RawPrimFree        ) =                           "RawPrimFree"
  go d (RawPrimWrite       ) =                           "RawPrimWrite"

primIOForget : {tm : Ty -> Set} -> {A : Set} -> {t : Ty} -> ({t : Ty} -> tm t -> A) -> PrimIO tm t -> RawPrimIO × List A
primIOForget {tm} {A} f = go where
  go : {ty : Ty} -> PrimIO tm ty -> RawPrimIO × List A
  go (PrimGet   name ty          rwt) = RawPrimGet name ty , (f rwt ) ∷ []
  go (PrimPut   name what        rwt) = RawPrimPut name    , (f what)                 ∷ (f rwt) ∷ []
  go (PrimAlloc size vty         rwt) = RawPrimAlloc vty   , (f size)                 ∷ (f rwt) ∷ []
  go (PrimFree  ptr              rwt) = RawPrimFree        , (f ptr )                 ∷ (f rwt) ∷ []
  go (PrimRead {vty = vty} ptr j rwt) = RawPrimRead  vty   , (f ptr ) ∷ (f j)         ∷ (f rwt) ∷ []
  go (PrimWrite ptr j y          rwt) = RawPrimWrite       , (f ptr ) ∷ (f j) ∷ (f y) ∷ (f rwt) ∷ []

--------------------------------------------------------------------------------
-}

