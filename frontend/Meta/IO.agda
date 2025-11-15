

{-# OPTIONS --type-in-type --show-implicit #-}

module Meta.IO where

--------------------------------------------------------------------------------

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

data InOut (tm : Ty -> Set) : Ty -> Set where
  Pure : tm ty                       -> InOut tm ty
  Bind : tm (IO s) -> tm (s ⇒ IO t)  -> InOut tm t
  Get  : String -> (ty : Ty)         -> InOut tm ty
  Put  : String -> tm ty             -> InOut tm Unit

  -- Alloc
  -- Free

-- withAlloc ...

mapInOut : {tm₁ tm₂ : Ty -> Set} -> ({s : Ty} -> tm₁ s -> tm₂ s) -> {t : Ty} -> InOut tm₁ t -> InOut tm₂ t
mapInOut {tm₁ = tm₁} {tm₂ = tm₂} f what = go what where
  go : {t : Ty} -> InOut tm₁ t -> InOut tm₂ t
  go (Pure x  )      = Pure (f x)
  go (Bind u h)      = Bind (f u) (f h)
  go (Get name ty  ) = Get name ty
  go (Put name what) = Put name (f what)

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

----------------------------------------
-- STLC version

private variable
  m   : ℕ
  ctx : Ctx m

data InOut′ (lc : {n : ℕ} -> Ctx n -> Ty -> Set) : Ctx m -> Ty -> Set where
  Pure′ : lc ctx ty                            -> InOut′ lc ctx ty
  Bind′ : lc ctx (IO s) -> lc (s ∷ ctx) (IO t) -> InOut′ lc ctx t
  Get′  : String -> (ty : Ty)                  -> InOut′ lc ctx ty
  Put′  : String -> lc ctx ty                  -> InOut′ lc ctx Unit

--------------------------------------------------------------------------------
-- primop-level, token-passing IO primitives

data PrimIO (tm : Ty -> Set) : Ty -> Set where
  PrimGet : tm Token -> String -> (ty : Ty) -> PrimIO tm (Pair Token ty  )
  PrimPut : tm Token -> String -> tm ty     -> PrimIO tm (Pair Token Unit) 

mapPrimIO : {tm₁ tm₂ : Ty -> Set} -> ({s : Ty} -> tm₁ s -> tm₂ s) -> {t : Ty} -> PrimIO tm₁ t -> PrimIO tm₂ t
mapPrimIO {tm₁} {tm₂} f what = go what where
  go : {t : Ty} -> PrimIO tm₁ t -> PrimIO tm₂ t
  go (PrimGet rwt name ty  ) = PrimGet (f rwt) name ty
  go (PrimPut rwt name what) = PrimPut (f rwt) name (f what)

traversePrimIO : {F : Set -> Set} -> {tm₁ tm₂ : Ty -> Set} -> RawApplicative F -> ({s : Ty} -> tm₁ s -> F (tm₂ s)) -> {t : Ty} -> PrimIO tm₁ t -> F (PrimIO tm₂ t)
traversePrimIO {F = F} {tm₁ = tm₁} {tm₂ = tm₂} applicative f what = go what where

  pure  = RawApplicative.pure  applicative
  _<*>_ = RawApplicative._<*>_ applicative

  infixl 4 _<*>_
  
  go : {t : Ty} -> PrimIO tm₁ t -> F (PrimIO tm₂ t)
  go (PrimGet rwt name ty  ) = pure (\rwt′ -> PrimGet rwt′ name ty) <*> (f rwt)
  go (PrimPut rwt name what) = pure PrimPut <*> (f rwt) <*> (pure name) <*> (f what) 

----------------------------------------
-- Raw version

-- Note: the actual arguments are passed as separate lists
data RawPrimIO : Set where
  RawPrimGet    : String -> Ty  -> RawPrimIO
  RawPrimPut    : String        -> RawPrimIO

{-
showRawPrimIOPrec : {raw : Set} -> (ℕ -> raw -> String) -> ℕ -> RawPrimIO raw -> String
showRawPrimIOPrec {raw} showRawPrec = go where
  go : ℕ -> RawPrimIO raw -> String
  go d (RawPrimGet rwt name ty     ) = showParen (d >ᵇ appPrec) ("RawPrimGet " ++ showRawPrec appPrec₊₁ rwt ++ " " ++ showString name ++ " " ++ showTyPrec  appPrec₊₁ ty  )
  go d (RawPrimPut rwt name what   ) = showParen (d >ᵇ appPrec) ("RawPrimPut " ++ showRawPrec appPrec₊₁ rwt ++ " " ++ showString name ++ " " ++ showRawPrec appPrec₊₁ what)
-}

showRawPrimIOPrec : ℕ -> RawPrimIO -> String
showRawPrimIOPrec  = go where
  go : ℕ -> RawPrimIO  -> String
  go d (RawPrimGet name ty ) = showParen (d >ᵇ appPrec) ("RawPrimGet " ++ showString name ++ " " ++ showTyPrec  appPrec₊₁ ty  )
  go d (RawPrimPut name    ) = showParen (d >ᵇ appPrec) ("RawPrimPut " ++ showString name)

{-
primIOForget : {lc : {n : ℕ} -> Ctx n -> Ty -> Set} ->
           {k : ℕ} -> {ctx : Ctx k} -> {ty : Ty} ->
           {A : Set} -> ({m : ℕ} -> {ctx : Ctx m} -> {t : Ty} -> lc ctx t -> A) ->
           PrimIO (lc ctx) ty -> RawPrimIO × List A
primIOForget {lc = lc} {k = k} {ctx = ctx} {ty = ty} {A = A} f = go where
  go : PrimIO (lc ctx) t -> RawPrimIO × List A
  go (PrimGet rwt name ty     ) = RawPrimGet name ty , (f rwt) ∷ []
  go (PrimPut rwt name what   ) = RawPrimPut name    , (f rwt) ∷ (f what) ∷ [] 
-}

primIOForget : {tm : Ty -> Set} -> {A : Set} -> {t : Ty} -> ({t : Ty} -> tm t -> A) -> PrimIO tm t -> RawPrimIO × List A
primIOForget {tm} {A} f = go where
  go : {ty : Ty} -> PrimIO tm ty -> RawPrimIO × List A
  go (PrimGet rwt name ty     ) = RawPrimGet name ty , (f rwt) ∷ []
  go (PrimPut rwt name what   ) = RawPrimPut name    , (f rwt) ∷ (f what) ∷ [] 

----------------------------------------
-- a previous Raw version

{-
data RawIO (raw : Set) : Set where
  RawPure   : raw               -> RawIO raw
  RawBind   : raw -> raw        -> RawIO raw
  RawGet    : String -> Ty      -> RawIO raw
  RawPut    : String -> raw     -> RawIO raw

showRawIOPrec : {raw : Set} -> (ℕ -> raw -> String) -> ℕ -> RawIO raw -> String
showRawIOPrec {raw} showRawPrec = go where
  go : ℕ -> RawIO raw -> String
  go d (RawPure what       ) = showParen (d >ᵇ appPrec) ("RawReturn " ++ showRawPrec appPrec₊₁ what)
  go d (RawBind action next) = showParen (d >ᵇ appPrec) ("RawBind "   ++ showRawPrec appPrec₊₁ action ++ " " ++ showRawPrec appPrec₊₁ next)
  go d (RawGet name ty     ) = showParen (d >ᵇ appPrec) ("RawGet " ++ showString name ++ " " ++ showTyPrec appPrec₊₁ ty)
  go d (RawPut name what   ) = showParen (d >ᵇ appPrec) ("RawPut " ++ showString name ++ " " ++ showRawPrec appPrec₊₁ what)

--------------------------------------------------------------------------------

ioForget : {lc : {n : ℕ} -> Ctx n -> Ty -> Set} ->
           {k : ℕ} -> {ctx : Ctx k} -> {ty : Ty} ->
           {A : Set} -> ({m : ℕ} -> {ctx : Ctx m} -> {t : Ty} -> lc ctx t -> A) ->
           InOut′ lc ctx ty -> RawIO A
ioForget {lc = lc} {k = k} {ctx = ctx} {ty = ty} {A = A} f = go where
  go : InOut′ lc ctx t -> RawIO A
  go (Pute′ what       ) = RawPure (f what)
  go (Bind′ action next) = RawBind (f action) (f next)
  go (Get′ name ty     ) = RawGet name ty
  go (Put′ name what   ) = RawPut name (f what) 
-}

--------------------------------------------------------------------------------
