
{-# OPTIONS --type-in-type #-}

module Meta.PrimOp where

open import Data.Nat
open import Data.Fin
open import Data.Vec    using ( Vec  ; [] ; _∷_ )
open import Data.List   using ( List ; [] ; _∷_ )
open import Data.String using ( String ; _++_ )
open import Data.Maybe
open import Data.Product using ( _×_ ; _,_ )

import Data.Maybe.Effectful
open import Effect.Applicative

--open import Data.Bool
--open import Data.Word64

open import Meta.Ty 
open import Meta.Val
open import Meta.HList using ( HList ; Cons ; Nil ; traverse₂ ; hlistForget )
open import Meta.Show

--------------------------------------------------------------------------------

private variable
  s t : Ty
  n   : ℕ
  ts  : Vec Ty n
  
data PrimOp (tm : Ty -> Set) : Ty -> Set where
  -- 64-bit arithmetic
  AddU64        : tm U64 -> tm U64 -> PrimOp tm U64
  SubU64        : tm U64 -> tm U64 -> PrimOp tm U64
  AddCarryU64   : tm Bit -> tm U64 -> tm U64 -> PrimOp tm (Pair Bit U64)
  SubCarryU64   : tm Bit -> tm U64 -> tm U64 -> PrimOp tm (Pair Bit U64)
  MulTruncU64   : tm U64 -> tm U64 -> PrimOp tm U64
  MulExtU64     :           tm U64 -> tm U64 -> PrimOp tm (Pair U64 U64)
  MulAddU64     : tm U64 -> tm U64 -> tm U64 -> PrimOp tm (Pair U64 U64)
  -- 64 bit bit operations
  BitComplement : tm U64 -> PrimOp tm U64
  BitOr         : tm U64 -> tm U64 -> PrimOp tm U64
  BitAnd        : tm U64 -> tm U64 -> PrimOp tm U64
  BitXor        : tm U64 -> tm U64 -> PrimOp tm U64
  RotLeftU64    : tm Bit -> tm U64 -> PrimOp tm (Pair Bit U64)
  RotRightU64   : tm Bit -> tm U64 -> PrimOp tm (Pair Bit U64)
  -- 64-bit comparisons
  EqU64         : tm U64 -> tm U64 -> PrimOp tm Bit
  LtU64         : tm U64 -> tm U64 -> PrimOp tm Bit
  LeU64         : tm U64 -> tm U64 -> PrimOp tm Bit
  -- bits (boolean)
  CastBitU64    : tm Bit           -> PrimOp tm U64
  Not           : tm Bit           -> PrimOp tm Bit
  And           : tm Bit -> tm Bit -> PrimOp tm Bit
  Or            : tm Bit -> tm Bit -> PrimOp tm Bit
  IFTE          : tm Bit -> tm t -> tm t -> PrimOp tm t
  -- struct
  MkStruct      : HList tm ts -> PrimOp tm (Struct ts)
  Proj          : {n : ℕ} -> {ts : Vec Ty n} ->
                  Fin n -> tm (Struct {n} ts) -> PrimOp tm t
  -- newtype
  Wrap          : (name : String) -> tm t -> PrimOp tm (Named name t)
  Unwrap        : {name : String} -> tm (Named name t) -> PrimOp tm t
  -- nat
  Zero          : PrimOp tm Nat
  Succ          : tm Nat -> PrimOp tm Nat
  IsZero        : tm Nat -> PrimOp tm Bit      
  NatSplit      : tm Nat -> tm s -> tm (Nat ⇒ s) -> PrimOp tm s
  NatAdd        : tm Nat -> tm Nat -> PrimOp tm Nat
  NatSubTrunc   : tm Nat -> tm Nat -> PrimOp tm Nat
  NatMul        : tm Nat -> tm Nat -> PrimOp tm Nat
{-
  -- input / output (the old-style IO hack; it's replaced now by a continuation based IO type)
  Input         : String -> (ty : Ty) -> PrimOp tm ty
  Output        : String -> {ty : Ty} -> tm ty -> PrimOp tm Unit
-}

--------------------------------------------------------------------------------

private variable
  tm  : Ty -> Set
  
MkPair : tm s -> tm t -> PrimOp tm (Pair s t)
MkPair x y = MkStruct (Cons x (Cons y Nil))

Fst : tm (Pair s t) -> PrimOp tm s
Fst = Proj Fin.zero

Snd : tm (Pair s t) -> PrimOp tm t
Snd = Proj (Fin.suc Fin.zero)

----------------------------------------

GtU64 : tm U64 -> tm U64 -> PrimOp tm Bit
GtU64 x y = LtU64 y x

GeU64 : tm U64 -> tm U64 -> PrimOp tm Bit
GeU64 x y = LeU64 y x

--------------------------------------------------------------------------------

mapPrim : {tm₁ tm₂ : Ty -> Set} -> ({s : Ty} -> tm₁ s -> tm₂ s) -> {t : Ty} -> PrimOp tm₁ t -> PrimOp tm₂ t
mapPrim {tm₁} {tm₂} f what = go what where
  go : {t : Ty} -> PrimOp tm₁ t -> PrimOp tm₂ t
  go (AddU64 x y)        = AddU64 (f x) (f y)
  go (SubU64 x y)        = SubU64 (f x) (f y)
  go (AddCarryU64 c x y) = AddCarryU64 (f c) (f x) (f y)
  go (SubCarryU64 c x y) = SubCarryU64 (f c) (f x) (f y)
  go (MulTruncU64 x y)   = MulTruncU64 (f x) (f y)
  go (MulExtU64 x y)     = MulExtU64 (f x) (f y)
  go (MulAddU64 a x y)   = MulAddU64 (f a) (f x) (f y)
  go (BitComplement x)   = BitComplement (f x)
  go (BitOr  x y)        = BitOr  (f x) (f y)
  go (BitAnd x y)        = BitAnd (f x) (f y)
  go (BitXor x y)        = BitXor (f x) (f y)
  go (RotLeftU64   c x)  = RotLeftU64  (f c) (f x)
  go (RotRightU64  c x)  = RotRightU64 (f c) (f x)
  go (EqU64 x y)         = EqU64 (f x) (f y)
  go (LtU64 x y)         = LtU64 (f x) (f y)
  go (LeU64 x y)         = LeU64 (f x) (f y)
  go (CastBitU64 x)      = CastBitU64 (f x)
  go (Not x)             = Not (f x)
  go (And x y)           = And (f x) (f y)
  go (Or  x y)           = Or  (f x) (f y)
  go (IFTE b x y)        = IFTE (f b) (f x) (f y)
  go (MkStruct s)        = MkStruct (Meta.HList.transform f s)
  go (Proj j s)          = Proj j (f s)
  go (Wrap n x)          = Wrap n (f x)
  go (Unwrap y)          = Unwrap (f y)
  go Zero                = Zero
  go (Succ x)            = Succ (f x)
  go (IsZero x)          = IsZero (f x)
  go (NatSplit n z s)    = NatSplit (f n) (f z) (f s)
  go (NatAdd x y)        = NatAdd (f x) (f y)
  go (NatSubTrunc x y)   = NatSubTrunc (f x) (f y)
  go (NatMul x y)        = NatMul (f x) (f y)
{-
  go (Input  n t)        = Input n t
  go (Output n y)        = Output n (f y)
-}

--------------------------------------------------------------------------------

traversePrim : {F : Set -> Set} -> {tm₁ tm₂ : Ty -> Set} -> RawApplicative F -> ({s : Ty} -> tm₁ s -> F (tm₂ s)) -> {t : Ty} -> PrimOp tm₁ t -> F (PrimOp tm₂ t)
traversePrim {F} {tm₁} {tm₂} applicative f what = go what where

  pure  = RawApplicative.pure  applicative
  _<*>_ = RawApplicative._<*>_ applicative

  go : {t : Ty} -> PrimOp tm₁ t -> F (PrimOp tm₂ t)
  go (AddU64 x y)        = (| AddU64 (f x) (f y)             |)
  go (SubU64 x y)        = (| SubU64 (f x) (f y)             |)
  go (MulTruncU64 x y)   = (| MulTruncU64 (f x) (f y)        |)
  go (AddCarryU64 c x y) = (| AddCarryU64 (f c) (f x) (f y)  |)
  go (SubCarryU64 c x y) = (| SubCarryU64 (f c) (f x) (f y)  |)
  go (MulExtU64 x y)     = (| MulExtU64 (f x) (f y)          |)
  go (MulAddU64 a x y)   = (| MulAddU64 (f a) (f x) (f y)    |)
  go (BitComplement x)   = (| BitComplement (f x)            |)
  go (BitOr  x y)        = (| BitOr  (f x) (f y)             |)
  go (BitAnd x y)        = (| BitAnd (f x) (f y)             |)
  go (BitXor x y)        = (| BitXor (f x) (f y)             |)
  go (RotLeftU64   c x)  = (| RotLeftU64  (f c) (f x)        |)
  go (RotRightU64  c x)  = (| RotRightU64 (f c) (f x)        |)
  go (EqU64 x y)         = (| EqU64 (f x) (f y)              |)
  go (LtU64 x y)         = (| LtU64 (f x) (f y)              |)
  go (LeU64 x y)         = (| LeU64 (f x) (f y)              |)
  go (CastBitU64 x)      = (| CastBitU64 (f x)               |)
  go (Not x)             = (| Not (f x)                      |)
  go (And x y)           = (| And (f x) (f y)                |)
  go (Or  x y)           = (| Or  (f x) (f y)                |)
  go (IFTE b x y)        = (| IFTE (f b) (f x) (f y)         |)
  go (MkStruct xs)       = (| MkStruct (Meta.HList.traverse₂ applicative f xs) |) 
  go (Proj j s)          = (| (Proj j) (f s)                 |)
  go (Wrap n x)          = (| (Wrap n) (f x)                 |)
  go (Unwrap y)          = (| Unwrap (f y)                   |)
  go Zero                = (| Zero                           |)
  go (Succ x)            = (| Succ (f x)                     |)
  go (IsZero n)          = (| IsZero (f n)                   |)
  go (NatSplit n z s)    = (| NatSplit (f n) (f z) (f s)     |)
  go (NatAdd x y)        = (| NatAdd (f x) (f y)             |)
  go (NatSubTrunc x y)   = (| NatSubTrunc (f x) (f y)        |)
  go (NatMul x y)        = (| NatMul (f x) (f y)             |)
{-
  go (Input  n t)        = pure (Input n t)                    
  go (Output n y)        = (| (Output n) (f y)               |)
-}

mapMaybePrim
  :  {tm₁ tm₂ : Ty -> Set}
  -> ({s : Ty} -> tm₁ s -> Maybe (tm₂ s))
  -> {t : Ty} -> PrimOp tm₁ t -> Maybe (PrimOp tm₂ t)
mapMaybePrim = traversePrim Data.Maybe.Effectful.applicative

--------------------------------------------------------------------------------

data RawPrim : Set where
  MkRawPrim : String -> RawPrim
  RawProj   : ℕ -> RawPrim
  RawWrap   : String -> RawPrim
{-
  -- the old-style IO hack; it's replaced now by a continuation based IO type
  RawInput  : String -> Ty -> RawPrim
  RawOutput : String -> RawPrim
-}

showRawPrimPrec : ℕ -> RawPrim -> String
showRawPrimPrec = go where
  go : ℕ -> RawPrim -> String
  go d (MkRawPrim name) = showParen (d >ᵇ appPrec) ("MkRawPrim " ++ showString name)
  go d (RawProj   j)    = showParen (d >ᵇ appPrec) ("RawProj "   ++ showNat j)
  go d (RawWrap   n)    = showParen (d >ᵇ appPrec) ("RawWrap "   ++ showString n)
{-
  go d (RawInput  n t)  = showParen (d >ᵇ appPrec) ("RawInput "  ++ showString n ++ " " ++ showTyPrec appPrec₊₁ t)
  go d (RawOutput n  )  = showParen (d >ᵇ appPrec) ("RawOutput " ++ showString n)
-}

primOpForget : {tm : Ty -> Set} -> {A : Set} -> {t : Ty} -> ({t : Ty} -> tm t -> A) -> PrimOp tm t -> RawPrim × List A
primOpForget {tm} {A} f = go where
  go : {ty : Ty} -> PrimOp tm ty -> RawPrim × List A
  go (AddU64 x y)        = MkRawPrim "AddU64"        , (f x ∷ f y ∷ [])
  go (SubU64 x y)        = MkRawPrim "SubU64"        , (f x ∷ f y ∷ [])
  go (AddCarryU64 c x y) = MkRawPrim "AddCarryU64"   , (f c ∷ f x ∷ f y ∷ [])
  go (SubCarryU64 c x y) = MkRawPrim "SubCarryU64"   , (f c ∷ f x ∷ f y ∷ [])
  go (MulTruncU64 x y)   = MkRawPrim "MulTruncU64"   , (f x ∷ f y ∷ [])
  go (MulExtU64 x y)     = MkRawPrim "MulExtU64"     , (f x ∷ f y ∷ []) 
  go (MulAddU64 a x y)   = MkRawPrim "MulAddU64"     , (f a ∷ f x ∷ f y ∷ [])
  go (BitComplement x)   = MkRawPrim "BitComplement" , (f x ∷ [])
  go (BitOr  x y)        = MkRawPrim "BitOr"         , (f x ∷ f y ∷ [])
  go (BitAnd x y)        = MkRawPrim "BitAnd"        , (f x ∷ f y ∷ [])
  go (BitXor x y)        = MkRawPrim "BitXor"        , (f x ∷ f y ∷ [])
  go (RotLeftU64   c x)  = MkRawPrim "RotLeftU64"    , (f c ∷ f x ∷ [])
  go (RotRightU64  c x)  = MkRawPrim "RotRightU64"   , (f c ∷ f x ∷ [])
  go (EqU64 x y)         = MkRawPrim "EqU64"         , (f x ∷ f y ∷ [])
  go (LtU64 x y)         = MkRawPrim "LtU64"         , (f x ∷ f y ∷ [])
  go (LeU64 x y)         = MkRawPrim "LeU64"         , (f x ∷ f y ∷ [])
  go (CastBitU64 x)      = MkRawPrim "CastBitU64"    , (f x ∷ [])
  go (Not x)             = MkRawPrim "Not"           , (f x ∷ [])
  go (And x y)           = MkRawPrim "And"           , (f x ∷ f y ∷ [])
  go (Or  x y)           = MkRawPrim "Or"            , (f x ∷ f y ∷ [])
  go (IFTE b x y)        = MkRawPrim "IFTE"          , (f b ∷ f x ∷ f y ∷ [])
  go (MkStruct s)        = MkRawPrim "MkStruct"      , hlistForget f s
  go (Proj j s)          = RawProj (Data.Fin.toℕ j)  , (f s ∷ [])
  go (Wrap n x)          = RawWrap n                 , (f x ∷ [])
  go (Unwrap y)          = MkRawPrim "Unwrap"        , (f y ∷ [])
  go Zero                = MkRawPrim "Zero"          , []
  go (Succ x)            = MkRawPrim "Succ"          , (f x ∷ [])
  go (IsZero n)          = MkRawPrim "IsZero"        , (f n ∷ [])
  go (NatSplit n z s)    = MkRawPrim "NatSplit"      , (f n ∷ f z ∷ f s ∷ [])
  go (NatAdd x y)        = MkRawPrim "NatAdd"        , (f x ∷ f y ∷ [])
  go (NatSubTrunc x y)   = MkRawPrim "NatSubTrunc"   , (f x ∷ f y ∷ [])
  go (NatMul x y)        = MkRawPrim "NatMul"        , (f x ∷ f y ∷ [])
{-
  go (Input  n t)        = RawInput  n t             , []
  go (Output n y)        = RawOutput n               , (f y ∷ [])
-}

--------------------------------------------------------------------------------
