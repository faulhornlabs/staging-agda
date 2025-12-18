
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

open import Effect.Applicative

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable

open import Meta.Show
open import Meta.HList

--------------------------------------------------------------------------------

private variable
  n : ℕ

--------------------------------------------------------------------------------

-- all types
data Ty    : Set
data VTy   : Set
data IsVTy : Ty -> Set

data Ty where
  -- LC
  Unit  : Ty
  _⇒_   : Ty -> Ty -> Ty
  -- IO
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

-- proof that this is a value type (really a Storable type, maybe rename at some point)
data IsVTy where
  -- IsUnit   : IsVTy Unit
  -- IsToken  : IsVTy Token
  IsBit    : IsVTy Bit
  IsU64    : IsVTy U64
  -- IsNat    : IsVTy Nat
  IsStruct : {n : ℕ} -> {ts : Vec Ty n} -> HList IsVTy ts -> IsVTy (Struct ts)
  IsNamed  : (name : String) -> {ty : Ty} -> IsVTy ty -> IsVTy (Named name ty)

data VTy where
  MkVTy : (ty : Ty) -> IsVTy ty -> VTy

BitVTy U64VTy : VTy
BitVTy = MkVTy Bit IsBit
U64VTy = MkVTy U64 IsU64

private

  open import Data.Maybe.Effectful renaming ( applicative to maybeApplicative )

  pure  = RawApplicative.pure  maybeApplicative
  _<*>_ = RawApplicative._<*>_ maybeApplicative

{-# TERMINATING #-}
isVTy′ : (ty : Ty) -> Maybe (IsVTy ty)
isVTy′ = go where
  go : (ty : Ty) -> Maybe (IsVTy ty)
  go Bit             = just IsBit  
  go U64             = just IsU64   
  go (Struct ts)     = (| IsStruct (Meta.HList.traverseTyVec maybeApplicative go ts) |) 
  go (Named name ty) = (| (IsNamed name) (go ty) |)
  go _                = nothing

{-# NON_COVERING #-}
isVTy : Ty -> Maybe VTy
isVTy ty with isVTy′ ty
... | just prf = just (MkVTy ty prf)
... | nothing  = nothing

vtyToTy : VTy -> Ty
vtyToTy (MkVTy ty prf) = ty

----------------------------------------

-- indexing into arrays
Idx : Ty
Idx = U64

Pair : Ty -> Ty -> Ty
Pair s t = Struct (s ∷ t ∷ [])

opaque
  IO : Ty -> Ty
  IO ty = Token ⇒ Pair ty Token

Vect : ℕ -> Ty -> Ty
Vect n t = Struct (Data.Vec.replicate n t)

U128 : Ty
U128 = Pair U64 U64     -- currently the convention is (hi , lo) but maybe that should be changed???

--------------------------------------------------------------------------------

{-# NON_COVERING #-}
unsafeTyToVTy : Ty -> VTy
unsafeTyToVTy ty with isVTy ty
... | just vty = vty

{-
Pair′ : VTy -> VTy -> VTy
Pair′ s t = Struct′ (s ∷ t ∷ [])

Vect′ : ℕ -> VTy -> VTy
Vect′ n t = Struct′ (Data.Vec.replicate n t)

U128′ : VTy
U128′ = Pair′ U64′ U64′     -- currently the convention is (hi , lo) but maybe that should be changed???
-}

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

isVTyEq    : {t : Ty} -> (p q : IsVTy t)           -> SemiDec (p  ≡ q )
isVTyVecEq : {ts : Vec Ty n} -> (ps qs : HList IsVTy ts) -> SemiDec (ps ≡ qs)

isVTyEq IsBit   IsBit  = STrue refl
isVTyEq IsU64   IsU64  = STrue refl
isVTyEq (IsNamed n s) (IsNamed m t) with strEq n m
... | SFalse = SFalse
... | (STrue refl) with isVTyEq s t
...                 | SFalse     = SFalse
...                 | STrue refl = STrue refl
isVTyEq (IsStruct {n} u) (IsStruct {m} v) with natEq n m
... | SFalse = SFalse
... | STrue refl with isVTyVecEq u v
...                    | SFalse     = SFalse
...                    | STrue refl = STrue refl

isVTyVecEq Nil         Nil         = STrue refl
isVTyVecEq (Cons x xs) (Cons y ys) with isVTyEq x y
... | SFalse = SFalse
... | STrue refl with isVTyVecEq xs ys
...              | SFalse     = SFalse
...              | STrue refl = STrue refl

----------------------------------------

tyEq     : (s t : Ty      ) -> SemiDec (s ≡ t)
tyVecEq  : (u v : Vec Ty n) -> SemiDec (u ≡ v)
vtyEq    : (s t : VTy     ) -> SemiDec (s ≡ t)

tyEq = go where

  go : (s t : Ty) -> SemiDec (s ≡ t)
  go Unit  Unit = STrue refl
  go Bit   Bit  = STrue refl
  go U64   U64  = STrue refl
  go Nat   Nat  = STrue refl

  go Token Token = STrue refl

  go (Named n s) (Named m t) with strEq n m
  ... | SFalse = SFalse
  ... | (STrue refl) with go s t
  ...                 | SFalse     = SFalse
  ...                 | STrue refl = STrue refl
  
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

  go (Ptr s) (Ptr t) with vtyEq s t
  ... | SFalse       = SFalse
  ... | (STrue refl) = STrue refl

  go _ _ = SFalse

vtyEq (MkVTy s p) (MkVTy t q) with tyEq s t
... | SFalse  = SFalse
... | STrue refl with isVTyEq p q
...              | SFalse     = SFalse
...              | STrue refl = STrue refl

tyVecEq []       []       = STrue refl
tyVecEq (x ∷ xs) (y ∷ ys) with tyEq x y
tyVecEq (x ∷ xs) (y ∷ ys) | SFalse = SFalse
tyVecEq (x ∷ xs) (y ∷ ys) | STrue refl with tyVecEq xs ys
tyVecEq (x ∷ xs) (y ∷ ys) | STrue refl | SFalse     = SFalse
tyVecEq (x ∷ xs) (y ∷ ys) | STrue refl | STrue refl = STrue refl

--------------------------------------------------------------------------------

-- opaque
--   unfolding IO

{-# TERMINATING #-}
showTyPrec : ℕ -> Ty -> String
showTyPrec = go where

    go : ℕ -> Ty -> String
    go d Unit        = "Unit"
    go d Bit         = "Bit"
    go d U64         = "U64"
    go d Nat         = "Nat"
    go d Token       = "Token"
    go d (Named n t) = showParen (d >ᵇ appPrec) ("Named "  ++ quoteString n ++ " " ++ go appPrec₊₁ t) 
    go d (s ⇒ t)     = showParen (d >ᵇ appPrec) ("Arrow "  ++ go appPrec₊₁ s ++ " " ++ go appPrec₊₁ t)
    go d (Struct ts) = showParen (d >ᵇ appPrec) ("Struct " ++ showVec (\t -> go 0 t) ts)
    go d (Ptr t)     = showParen (d >ᵇ appPrec) ("Ptr_ " ++ go appPrec₊₁ (vtyToTy t))

showTy : Ty -> String
showTy = showTyPrec 0

--------------------------------------------------------------------------------

exTyStr2 : String
exTyStr2 = showTy exTy2

--------------------------------------------------------------------------------



