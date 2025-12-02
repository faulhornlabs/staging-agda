
{-# OPTIONS --type-in-type #-}
module Meta.Ty where

--------------------------------------------------------------------------------

open import Data.Nat
open import Data.Vec using ( Vec ; [] ; _∷_ )
open import Data.Bool using ( Bool ; false ; true )
open import Data.String using ( String ; _++_ ; _≟_ )
open import Data.Fin using ( Fin ; zero ; suc ;  opposite ; inject₁ )
open import Data.Maybe

open import Function using ( id )

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable

open import Meta.Show
open import Meta.HList

--------------------------------------------------------------------------------

private variable
  n : ℕ

-- value types
-- a separate type is a BAD IDEA, it makes everything extremely cumbersome
-- better include a proof of being a value type...
data VTy : Set where
  Unit′   : VTy
  Token′  : VTy
  Bit′    : VTy
  U64′    : VTy
  Nat′    : VTy
  Struct′ : {n : ℕ} -> Vec VTy n -> VTy
  Named′  : String -> VTy -> VTy

--------------------------------------------------------------------------------

-- all types
data Ty    : Set
-- data VTy   : Set
-- data IsVTy : Ty -> Set

data Ty where
  -- LC
  Unit  : Ty
  _⇒_   : Ty -> Ty -> Ty
  -- IO
  IO    : Ty -> Ty
  Token : Ty             -- type of the `RealWorld` token
  -- built-in
  Bit    : Ty
  U64    : Ty
  Nat    : Ty            -- we should probably remove this
  -- data structures
  Struct : {n : ℕ} -> Vec Ty n -> Ty
  Named  : String -> Ty -> Ty
  -- arrays
  Ptr    : VTy -> Ty  

infixr 30 _⇒_

{-
-- proof that this is a value type
data IsVTy where
  Unit′   : IsVTy Unit
  Token′  : IsVTy Token
  Bit′    : IsVTy Bit
  U64′    : IsVTy U64
  Nat′    : IsVTy Nat
  Struct′ : {n : ℕ} -> (ts : Vec Ty n) -> HList IsVTy ts -> IsVTy (Struct ts)
  Named′  : (name : String) -> {ty : Ty} -> IsVTy ty -> IsVTy (Named name ty)


data VTy where
  MkVTy : (ty : Ty) -> IsVTy ty -> VTy

isVTy′ : Ty -> Maybe IsVTy

{-# NON_COVERING #-}
isVTy : Ty -> Maybe VTy
isVTy ty with isVTy′ ty
... | just prf = MkVTy ty prf

vtyToTy : VTy -> Ty
vtyToTy (MkVTy ty prf) = ty


-}

----------------------------------------

-- indexing into arrays
Idx : Ty
Idx = U64

Pair : Ty -> Ty -> Ty
Pair s t = Struct (s ∷ t ∷ [])

Vect : ℕ -> Ty -> Ty
Vect n t = Struct (Data.Vec.replicate n t)

U128 : Ty
U128 = Pair U64 U64     -- currently the convention is (hi , lo) but maybe that should be changed???

--------------------------------------------------------------------------------

{-# TERMINATING #-}
vtyToTy : VTy -> Ty
vtyToTy = go where
  go : VTy -> Ty
  go Unit′   = Unit
  go Token′  = Token
  go Bit′    = Bit
  go U64′    = U64
  go Nat′    = Nat
  go (Struct′ ts ) = Struct (Data.Vec.map go ts)
  go (Named′  n t) = Named n (go t)

{-# TERMINATING #-}
unsafeTyToVTy : Ty -> VTy
unsafeTyToVTy = go where
  {-# NON_COVERING #-}
  go : Ty -> VTy
  go Unit   = Unit′
  go Token  = Token′
  go Bit    = Bit′
  go U64    = U64′
  go Nat    = Nat′
  go (Struct ts ) = Struct′ (Data.Vec.map go ts)
  go (Named  n t) = Named′ n (go t)

Pair′ : VTy -> VTy -> VTy
Pair′ s t = Struct′ (s ∷ t ∷ [])

Vect′ : ℕ -> VTy -> VTy
Vect′ n t = Struct′ (Data.Vec.replicate n t)

U128′ : VTy
U128′ = Pair′ U64′ U64′     -- currently the convention is (hi , lo) but maybe that should be changed???

--------------------------------------------------------------------------------

exTy1 : Ty
exTy1 = Named "U128" U128

exTy2 : Ty
exTy2 = Named "Foo" (Struct (Bit ∷ exTy1 ∷ Named "N" Nat ∷ []))

--------------------------------------------------------------------------------

-- TODO: move this to a SemiDec module?
data SemiDec (p : Set) : Set where
  STrue  : p -> SemiDec p
  SFalse : SemiDec p

natEq : (n m : ℕ) -> SemiDec (n ≡ m)
natEq zero     zero     = STrue refl
natEq zero     (suc _)  = SFalse
natEq (suc _ ) zero     = SFalse
natEq (suc n₁) (suc m₁) with (natEq n₁ m₁)
natEq _        _        | SFalse     = SFalse
natEq _        _        | STrue refl = STrue refl

strEq : (s t : String) -> SemiDec (s ≡ t)
strEq s t with dec⇒maybe (Data.String._≟_ s t)
strEq s t | nothing  = SFalse
strEq s t | (just p) = STrue p

----------------------------------------

tyEq     : (s t : Ty      ) -> SemiDec (s ≡ t)
tyVecEq  : (u v : Vec Ty n) -> SemiDec (u ≡ v)

tyEq = go where

  go : (s t : Ty) -> SemiDec (s ≡ t)
  go Unit  Unit = STrue refl
  go Bit   Bit  = STrue refl
  go U64   U64  = STrue refl
  go Nat   Nat  = STrue refl

  go Token Token = STrue refl

  go (IO s₁) (IO t₁) with go s₁ t₁ 
  go (IO s₁) (IO t₁) | SFalse     = SFalse
  go (IO s₁) (IO t₁) | STrue refl = STrue refl

{-
  go (Array n s) (Array m t) with natEq n m
  go (Array n s) (Array m t) | SFalse = SFalse
  go (Array n s) (Array m t) | (STrue refl) with go s t 
  go (Array n s) (Array m t) | (STrue refl) | SFalse     = SFalse
  go (Array n s) (Array m t) | (STrue refl) | STrue refl = STrue refl
-}

  go (Named n s) (Named m t) with strEq n m
  go (Named n s) (Named m t) | SFalse = SFalse
  go (Named n s) (Named m t) | (STrue refl) with go s t
  go (Named n s) (Named m t) | (STrue refl) | SFalse     = SFalse
  go (Named n s) (Named m t) | (STrue refl) | STrue refl = STrue refl
  
  go (s₁ ⇒ s₂) (t₁ ⇒ t₂) with go s₁ t₁
  go (s₁ ⇒ s₂) (t₁ ⇒ t₂) | SFalse = SFalse
  go (s₁ ⇒ s₂) (t₁ ⇒ t₂) | STrue refl with go s₂ t₂
  go (s₁ ⇒ s₂) (t₁ ⇒ t₂) | STrue refl | SFalse     = SFalse
  go (s₁ ⇒ s₂) (t₁ ⇒ t₂) | STrue refl | STrue refl = STrue refl

  go (Struct {n} u) (Struct {m} v) with natEq n m
  go (Struct {n} u) (Struct {m} v) | SFalse = SFalse
  go (Struct {n} u) (Struct {m} v) | STrue refl with tyVecEq u v
  go (Struct {n} u) (Struct {m} v) | STrue refl | SFalse     = SFalse
  go (Struct {n} u) (Struct {m} v) | STrue refl | STrue refl = STrue refl

  go _ _ = SFalse

tyVecEq []       []       = STrue refl
tyVecEq (x ∷ xs) (y ∷ ys) with tyEq x y
tyVecEq (x ∷ xs) (y ∷ ys) | SFalse = SFalse
tyVecEq (x ∷ xs) (y ∷ ys) | STrue refl with tyVecEq xs ys
tyVecEq (x ∷ xs) (y ∷ ys) | STrue refl | SFalse     = SFalse
tyVecEq (x ∷ xs) (y ∷ ys) | STrue refl | STrue refl = STrue refl

--------------------------------------------------------------------------------

{-# TERMINATING #-}
showTyPrec : ℕ -> Ty -> String
showTyPrec = go where

  go : ℕ -> Ty -> String
  go d Unit        = "Unit"
  go d Bit         = "Bit"
  go d U64         = "U64"
  go d Nat         = "Nat"
  go d Token       = "Token"
  go d (IO t)      = showParen (d >ᵇ appPrec) ("IO_ " ++ go appPrec₊₁ t)
  go d (Named n t) = showParen (d >ᵇ appPrec) ("Named "  ++ quoteString n ++ " " ++ go appPrec₊₁ t) 
  go d (s ⇒ t)     = showParen (d >ᵇ appPrec) ("Arrow "  ++ go appPrec₊₁ s ++ " " ++ go appPrec₊₁ t)
  go d (Struct ts) = showParen (d >ᵇ appPrec) ("Struct " ++ showVec (\t -> go 0 t) ts)
  go d (Ptr t)     = showParen (d >ᵇ appPrec) ("Ptr " ++ go appPrec₊₁ (vtyToTy t))

showTy : Ty -> String
showTy = showTyPrec 0

--------------------------------------------------------------------------------

exTyStr2 : String
exTyStr2 = showTy exTy2

--------------------------------------------------------------------------------



