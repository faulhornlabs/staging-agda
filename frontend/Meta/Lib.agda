
{-# OPTIONS --type-in-type #-}

module Meta.Lib where

--------------------------------------------------------------------------------

open import Data.Bool using ( Bool ) -- ; true ; false )
open import Data.Nat  using ( ℕ ; zero ; suc )
open import Data.Fin  using ( Fin ; cast ; inject₁ )
open import Data.Vec
open import Data.Word64  using ( Word64 ; fromℕ )
open import Data.String  using ( String )
open import Data.Product using ( _×_ ; _,_ )

open import Relation.Binary.PropositionalEquality
open import Data.Vec.Properties using ( lookup-replicate )

open import Meta.Ctx
open import Meta.Val
open import Meta.HList
open import Meta.PrimOp
open import Meta.IO

open import Meta.Ty
open import Meta.HOAS

--------------------------------------------------------------------------------

private variable
  s t : Ty
  n   : ℕ
  ts  : Vec Ty n

--------------------------------------------------------------------------------

tt : Tm Unit
tt = Lit Tt

--------------------------------------------------------------------------------

debug′ : String -> Tm s -> Tm t -> Tm t
debug′ = Dbg

--------------------------------------------------------------------------------

{-
module IOLib where

  input′ : String -> (ty : Ty) -> Tm ty
  input′ n t = Pri (Input n t)

  input : {ty : Ty} -> String -> Tm ty
  input {t} n = Pri (Input n t)
-}

module IOLib where

  halt : Tm IO
  halt = IOp Halt

  get′ : String -> (ty : Ty) -> (Tm ty -> Tm IO) -> Tm IO  
  get′ name ty kont = IOp (Get name kont)

  get : {ty : Ty} -> String -> (Tm ty -> Tm IO) -> Tm IO
  get {ty} name kont = get′ name ty kont

  put : {ty : Ty} -> String -> Tm ty -> Tm IO -> Tm IO
  put {ty} name what kont = IOp (Put name what kont)

  putAndHalt : {ty : Ty} -> String -> Tm ty -> Tm IO
  putAndHalt name what = put name what halt
  
--------------------------------------------------------------------------------

ifte : Tm Bit -> Tm s -> Tm s -> Tm s
ifte b x y = Pri (IFTE b x y)

_&&_ : Tm Bit -> Tm Bit -> Tm Bit
_&&_ b c   = Pri (And b c)

_||_ : Tm Bit -> Tm Bit -> Tm Bit
_||_ b c = Pri (Or  b c)

module BitLib where
 
  kstBit : Bool -> Tm Bit
  kstBit b = Lit (Val.BitV b)

  zeroBit : Tm Bit
  zeroBit = kstBit Data.Bool.false

  oneBit : Tm Bit
  oneBit = kstBit Data.Bool.true

  true : Tm Bit
  true = oneBit

  false : Tm Bit
  false = zeroBit

  and : Tm Bit -> Tm Bit -> Tm Bit
  and b c   = Pri (And b c)

  or : Tm Bit -> Tm Bit -> Tm Bit
  or b c = Pri (Or  b c)

  not : Tm Bit -> Tm Bit 
  not b = Pri (Not b)

  castBitU64 : Tm Bit -> Tm U64
  castBitU64 x = Pri (CastBitU64 x)

  andMany : {n : ℕ} -> Vec (Tm Bit) n -> Tm Bit
  andMany []       = true
  andMany (x ∷ xs) = ifte x (andMany xs) false

  orMany : {n : ℕ} -> Vec (Tm Bit) n -> Tm Bit
  orMany []       = false
  orMany (x ∷ xs) = ifte x true (orMany xs)

  allOf : {ty : Ty} -> {n : ℕ} -> (Tm ty -> Tm Bit) -> Vec (Tm ty) n -> Tm Bit 
  allOf {ty = ty} {n = n} f = go where
    go : {k : ℕ} -> Vec (Tm ty) k -> Tm Bit
    go []       = true
    go (x ∷ xs) = ifte (f x) (go xs) false

  anyOf : {ty : Ty} -> {n : ℕ} -> (Tm ty -> Tm Bit) -> Vec (Tm ty) n -> Tm Bit 
  anyOf {ty = ty} {n = n} f = go where
    go : {k : ℕ} -> Vec (Tm ty) k -> Tm Bit
    go []       = false
    go (x ∷ xs) = ifte (f x) true (go xs) 

--------------------------------------------------------------------------------

module NatLib where

  kstNat : ℕ -> Tm Nat
  kstNat n = Lit (Val.NatV n)

  zeroNat : Tm Nat
  zeroNat = Pri Zero

  succNat : Tm Nat -> Tm Nat
  succNat n = Pri (Succ n)

  isZeroNat : Tm Nat -> Tm Bit
  isZeroNat n = Pri (IsZero n)

  addNat : Tm Nat -> Tm Nat -> Tm Nat
  addNat x y = Pri (NatAdd x y)

  subNat : Tm Nat -> Tm Nat -> Tm Nat
  subNat x y = Pri (NatSubTrunc x y)

  mulNat : Tm Nat -> Tm Nat -> Tm Nat
  mulNat x y = Pri (NatMul x y)

  predNat : Tm Nat -> Tm Nat
  predNat n = subNat n (kstNat 1)

--------------------------------------------------------------------------------

module StructLib where

  mkStruct : HList Tm ts -> Tm (Struct ts) 
  mkStruct xs  = Pri (MkStruct xs)

  mkVect : {n : ℕ} -> Vec (Tm t) n -> Tm (Struct (replicate n t))
  mkVect xs = mkStruct (vecToHList Tm xs)
  
  proj : (k : Fin n) -> Tm (Struct {n} ts) -> Tm (Data.Vec.lookup ts k)
  proj k what = Pri (Proj k what)

  vecproj : {ty : Ty} -> (k : Fin n) -> Tm (Struct {n} (replicate n ty)) -> Tm ty
  vecproj {n} {ty} k what = subst Tm (lookup-replicate k ty) (proj k what)
  
  mkPair : Tm s -> Tm t -> Tm (Pair s t)
  mkPair x y = Pri (MkPair x y)

  fst : Tm (Pair s t) -> Tm s
  fst x  = Pri (Fst x)

  snd : Tm (Pair s t) -> Tm t
  snd x  = Pri (Snd x)

  wrap : {name : String} -> Tm t -> Tm (Named name t)
  wrap {t} {name} x = Pri (Wrap name x)

  unwrap : {name : String} -> Tm (Named name t) -> Tm t
  unwrap y = Pri (Unwrap y)

open StructLib public

--------------------------------------------------------------------------------

module U64Lib where

  kstU64 : Word64 -> Tm U64
  kstU64 x = Lit (Val.U64V x)

  kstU64′ : ℕ -> Tm U64
  kstU64′ k = kstU64 (Data.Word64.fromℕ k)

  zeroU64 : Tm U64
  zeroU64 = kstU64 (Data.Word64.fromℕ 0)

  oneU64 : Tm U64
  oneU64 = kstU64 (Data.Word64.fromℕ 1)

  minusOneU64 : Tm U64
  minusOneU64 = kstU64 (Data.Word64.fromℕ 0xffffffffffffffff)

  ----------------------------------------
 
  hiWordOf : Tm U128 -> Tm U64
  hiWordOf = fst

  loWordOf : Tm U128 -> Tm U64
  loWordOf = snd

  addCarryU64 : Tm Bit -> Tm U64 -> Tm U64 -> Tm (Pair Bit U64)
  addCarryU64 c x y = Pri (AddCarryU64 c x y)

  subCarryU64 : Tm Bit -> Tm U64 -> Tm U64 -> Tm (Pair Bit U64)
  subCarryU64 c x y = Pri (SubCarryU64 c x y)

  negU64 : Tm U64 -> Tm U64
  negU64 y = Pri (SubU64 zeroU64 y)       -- TODO: maybe add NegU64 primop?

  addU64 : Tm U64 -> Tm U64 -> Tm U64
  addU64 x y = Pri (AddU64 x y)

  subU64 : Tm U64 -> Tm U64 -> Tm U64
  subU64 x y = Pri (SubU64 x y)

  mulExtU64 : Tm U64 -> Tm U64 -> Tm U128
  mulExtU64 x y = Pri (MulExtU64 x y)

  sqrExtU64 : Tm U64 -> Tm U128
  sqrExtU64 x = mulExtU64 x x

  mulTruncU64 : Tm U64 -> Tm U64 -> Tm U64
  mulTruncU64 x y = Pri (MulTruncU64 x y)   -- snd (mulExtU64 x y)

  sqrTruncU64 : Tm U64 -> Tm U64
  sqrTruncU64 x = Pri (MulTruncU64 x x)

  mulAddU64 : Tm U64 -> Tm U64 -> Tm U64 -> Tm U128
  mulAddU64 c x y = Pri (MulAddU64 c x y)

  bitComplU64 : Tm U64 -> Tm U64
  bitComplU64 x = Pri (BitComplement x)
  
  bitOrU64 : Tm U64 -> Tm U64 -> Tm U64
  bitOrU64 x y = Pri (BitOr x y)

  bitAndU64 : Tm U64 -> Tm U64 -> Tm U64
  bitAndU64 x y = Pri (BitAnd x y)

  bitXorU64 : Tm U64 -> Tm U64 -> Tm U64
  bitXorU64 x y = Pri (BitXor x y)

  rotLeftU64 : Tm Bit -> Tm U64 -> Tm (Pair Bit U64)
  rotLeftU64 c x = Pri (RotLeftU64 c x)

  rotRightU64 : Tm Bit -> Tm U64 -> Tm (Pair Bit U64)
  rotRightU64 c x = Pri (RotRightU64 c x)

  open BitLib
  
  shiftLeftU64 : Tm U64 -> Tm (Pair Bit U64)
  shiftLeftU64 = rotLeftU64 zeroBit

  shiftRightU64 : Tm U64 -> Tm (Pair Bit U64)
  shiftRightU64 = rotRightU64 zeroBit

  ----------------------------------------

  eqU64 : Tm U64 -> Tm U64 -> Tm Bit
  eqU64 x y = Pri (EqU64 x y)

  ltU64 : Tm U64 -> Tm U64 -> Tm Bit
  ltU64 x y = Pri (LtU64 x y)

  leU64 : Tm U64 -> Tm U64 -> Tm Bit
  leU64 x y = Pri (LeU64 x y)

  gtU64 : Tm U64 -> Tm U64 -> Tm Bit
  gtU64 x y = Pri (GtU64 x y)

  geU64 : Tm U64 -> Tm U64 -> Tm Bit
  geU64 x y = Pri (GeU64 x y)

  isZeroU64 : Tm U64 -> Tm Bit
  isZeroU64 x = eqU64 x zeroU64

  _==_ : Tm U64 -> Tm U64 -> Tm Bit
  _==_ = eqU64

  _!=_ : Tm U64 -> Tm U64 -> Tm Bit
  _!=_ x y = not (eqU64 x y)

  _<=_ : Tm U64 -> Tm U64 -> Tm Bit
  _<=_ = leU64

  _>=_ : Tm U64 -> Tm U64 -> Tm Bit
  _>=_ = geU64

  _<_ : Tm U64 -> Tm U64 -> Tm Bit
  _<_ = ltU64

  _>_ : Tm U64 -> Tm U64 -> Tm Bit
  _>_ = gtU64

  infix 40 _==_
  infix 40 _!=_
  infix 40 _<=_
  infix 40 _>=_
  infix 40 _<_
  infix 40 _>_

--------------------------------------------------------------------------------
