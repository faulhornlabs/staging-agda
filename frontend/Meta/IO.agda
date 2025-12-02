

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

data InOut (tm : Ty -> Set) : Ty -> Set where
  -- monad
  Pure : tm ty                            -> InOut tm ty
  Bind : tm (IO s) -> tm (s ⇒ IO t)       -> InOut tm t
  -- input / output
  Get  : String -> (ty : Ty)              -> InOut tm ty
  Put  : String -> tm ty                  -> InOut tm Unit
  -- allocation
  Alloc : tm U64 -> (vty : VTy)           -> InOut tm (Ptr vty)
  Free  : tm (Ptr vty)                    -> InOut tm Unit
  -- memory indexing
  Read  : {eq : vtyToTy vty ≡ ty} -> tm (Ptr vty) -> tm Idx          -> InOut tm ty
  Write : {eq : vtyToTy vty ≡ ty} -> tm (Ptr vty) -> tm Idx -> tm ty -> InOut tm Unit

mapInOut : {tm₁ tm₂ : Ty -> Set} -> ({s : Ty} -> tm₁ s -> tm₂ s) -> {t : Ty} -> InOut tm₁ t -> InOut tm₂ t
mapInOut {tm₁ = tm₁} {tm₂ = tm₂} f what = go what where
  go : {t : Ty} -> InOut tm₁ t -> InOut tm₂ t
  go (Pure x  )      = Pure (f x)
  go (Bind u h)      = Bind (f u) (f h)
  go (Get name ty  ) = Get name ty
  go (Put name what) = Put name (f what)
  go (Alloc size vty  ) = Alloc (f size) vty
  go (Free  ptr       ) = Free  (f ptr)
  go (Read  {eq = eq} ptr j  ) = Read  {eq = eq} (f ptr) (f j)
  go (Write {eq = eq} ptr j y) = Write {eq = eq} (f ptr) (f j) (f y)

mapMaybeInOut : {tm₁ tm₂ : Ty -> Set} -> ({s : Ty} -> tm₁ s -> Maybe (tm₂ s)) -> {t : Ty} -> InOut tm₁ t -> Maybe (InOut tm₂ t)
mapMaybeInOut {tm₁ = tm₁} {tm₂ = tm₂} f what = go what where

  go : {t : Ty} -> InOut tm₁ t -> Maybe (InOut tm₂ t)

  go (Pure x) = do
    x' <- f x
    just (Pure x')
    
  go (Bind u h) = do
    u' <- f u
    h' <- f h
    just (Bind u' h')
    
  go (Get name ty) =
    just (Get name ty)
 
  go (Put name what) = do
    what' <- f what
    just (Put name what')

  go (Alloc size vty) = do
    size' <- f size
    just (Alloc size' vty)

  go (Free ptr) = do
    ptr' <- f ptr
    just (Free ptr')

  go (Read {eq = eq} ptr j) = do
    ptr' <- f ptr
    j'   <- f j
    just (Read {eq = eq} ptr' j')

  go (Write {eq = eq} ptr j y) = do
    ptr' <- f ptr
    j'   <- f j
    y'   <- f y
    just (Write {eq = eq} ptr' j' y')

----------------------------------------
-- STLC version

{-
private variable
  m   : ℕ
  ctx : Ctx m

data InOut′ (lc : {n : ℕ} -> Ctx n -> Ty -> Set) : Ctx m -> Ty -> Set where
  Pure′ : lc ctx ty                            -> InOut′ lc ctx ty
  Bind′ : lc ctx (IO s) -> lc (s ∷ ctx) (IO t) -> InOut′ lc ctx t
  Get′  : String -> (ty : Ty)                  -> InOut′ lc ctx ty
  Put′  : String -> lc ctx ty                  -> InOut′ lc ctx Unit
-}

--------------------------------------------------------------------------------
-- primop-level, token-passing IO primitives

data PrimIO (tm : Ty -> Set) : Ty -> Set where
  -- basic input/output
  PrimGet   : tm Token -> String -> (ty : Ty)                        -> PrimIO tm (Pair Token ty       )
  PrimPut   : tm Token -> String -> tm ty                            -> PrimIO tm (Pair Token Unit     )
  -- memory allocation
  PrimAlloc : tm Token -> tm U64 -> (vty : VTy)                      -> PrimIO tm (Pair Token (Ptr vty))
  PrimFree  : tm Token -> tm (Ptr vty)                               -> PrimIO tm (Pair Token Unit     )
  -- reading/writing arrays
  PrimRead  : {eq : vtyToTy vty ≡ ty} -> tm Token -> tm (Ptr vty) -> tm Idx          -> PrimIO tm (Pair Token ty  )
  PrimWrite : {eq : vtyToTy vty ≡ ty} -> tm Token -> tm (Ptr vty) -> tm Idx -> tm ty -> PrimIO tm (Pair Token Unit)

mapPrimIO : {tm₁ tm₂ : Ty -> Set} -> ({s : Ty} -> tm₁ s -> tm₂ s) -> {t : Ty} -> PrimIO tm₁ t -> PrimIO tm₂ t
mapPrimIO {tm₁} {tm₂} f what = go what where
  go : {t : Ty} -> PrimIO tm₁ t -> PrimIO tm₂ t
  go (PrimGet   rwt name ty  ) = PrimGet   (f rwt) name ty
  go (PrimPut   rwt name what) = PrimPut   (f rwt) name (f what)
  go (PrimAlloc rwt size vty ) = PrimAlloc (f rwt) (f size) vty
  go (PrimFree  rwt ptr      ) = PrimFree  (f rwt) (f ptr)
  go (PrimRead  {eq = eq} rwt ptr j    ) = PrimRead  {eq = eq} (f rwt) (f ptr) (f j)
  go (PrimWrite {eq = eq} rwt ptr j y  ) = PrimWrite {eq = eq} (f rwt) (f ptr) (f j) (f y)

traversePrimIO : {F : Set -> Set} -> {tm₁ tm₂ : Ty -> Set} -> RawApplicative F -> ({s : Ty} -> tm₁ s -> F (tm₂ s)) -> {t : Ty} -> PrimIO tm₁ t -> F (PrimIO tm₂ t)
traversePrimIO {F = F} {tm₁ = tm₁} {tm₂ = tm₂} applicative f what = go what where

  pure  = RawApplicative.pure  applicative
  _<*>_ = RawApplicative._<*>_ applicative

  infixl 4 _<*>_
  
  go : {t : Ty} -> PrimIO tm₁ t -> F (PrimIO tm₂ t)
  go (PrimGet   rwt name ty  ) = pure (\rwt′       -> PrimGet   rwt′ name  ty ) <*> (f rwt)                -- Agda huh??
  go (PrimAlloc rwt size vty ) = pure (\rwt′ size′ -> PrimAlloc rwt′ size′ vty) <*> (f rwt) <*> (f size)   -- ....
  go (PrimPut   rwt name what) = (| PrimPut   (f rwt) (pure name) (f what) |)
  go (PrimFree  rwt ptr      ) = (| PrimFree  (f rwt) (f ptr)              |)
  go (PrimRead  {eq = eq} rwt ptr j    ) = (| (PrimRead  {eq = eq}) (f rwt) (f ptr) (f j)        |)
  go (PrimWrite {eq = eq} rwt ptr j y  ) = (| (PrimWrite {eq = eq}) (f rwt) (f ptr) (f j) (f y)  |)

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
  go (PrimGet   rwt name ty         ) = RawPrimGet name ty , (f rwt) ∷ []
  go (PrimPut   rwt name what       ) = RawPrimPut name    , (f rwt) ∷ (f what) ∷ []
  go (PrimAlloc rwt size vty        ) = RawPrimAlloc vty   , (f rwt) ∷ (f size) ∷ []
  go (PrimFree  rwt ptr             ) = RawPrimFree        , (f rwt) ∷ (f ptr ) ∷ []
  go (PrimRead {vty = vty} rwt ptr j) = RawPrimRead  vty   , (f rwt) ∷ (f ptr ) ∷ (f j) ∷ []
  go (PrimWrite rwt ptr j y         ) = RawPrimWrite       , (f rwt) ∷ (f ptr ) ∷ (f j) ∷ (f y) ∷ []

--------------------------------------------------------------------------------

