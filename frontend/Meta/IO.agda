

{-# OPTIONS --type-in-type --show-implicit #-}

module Meta.IO where

--------------------------------------------------------------------------------

open import Data.Nat
open import Data.Vec using ( _∷_ )
open import Data.String

open import Meta.Ty 
open import Meta.Val
open import Meta.Ctx
open import Meta.Show


--------------------------------------------------------------------------------
-- HOAS version

private variable
  ty : Ty

data InOut (tm : Ty -> Set) : Set where
  Halt :                               InOut tm 
  Get  : String -> (tm ty -> tm IO) -> InOut tm
  Put  : String ->  tm ty -> tm IO  -> InOut tm
  -- Malloc
  -- Free

-- withAlloc ...

----------------------------------------
-- STLC version

private variable
  m   : ℕ
  ctx : Ctx m

data InOut′ (lc : {n : ℕ} -> Ctx n -> Ty -> Set) : Ctx m -> Set where
  Halt′ :                                      InOut′ lc ctx 
  Get′  : String -> lc (ty ∷ ctx) IO        -> InOut′ lc ctx
  Put′  : String -> lc ctx  ty -> lc ctx IO -> InOut′ lc ctx

----------------------------------------
-- Raw version

data RawIO (raw : Set) : Set where
  RawHalt :                         RawIO raw
  RawGet  : String ->        raw -> RawIO raw
  RawPut  : String -> raw -> raw -> RawIO raw

showRawIOPrec : {raw : Set} -> (ℕ -> raw -> String) -> ℕ -> RawIO raw -> String
showRawIOPrec {raw} showRawPrec = go where
  go : ℕ -> RawIO raw -> String
  go d (RawHalt              ) =                           "RawHalt"
  go d (RawGet name body     ) = showParen (d >ᵇ appPrec) ("RawGet " ++ showString name ++ " " ++ showRawPrec appPrec₊₁ body)
  go d (RawPut name what kont) = showParen (d >ᵇ appPrec) ("RawPut " ++ showString name ++ " " ++ showRawPrec appPrec₊₁ what ++ " " ++ showRawPrec appPrec₊₁ kont)

--------------------------------------------------------------------------------

ioForget : {lc : {n : ℕ} -> Ctx n -> Ty -> Set} -> 
           {A : Set} -> ({m : ℕ} -> {ctx : Ctx m} -> {t : Ty} -> lc ctx t -> A) -> InOut′ lc ctx -> RawIO A
ioForget {k} {ctx} {lc} {A} f = go where
  go : InOut′ lc ctx -> RawIO A
  go (Halt′              ) = RawHalt
  go (Get′ name body     ) = RawGet name (f body)
  go (Put′ name what kont) = RawPut name (f what) (f kont)
