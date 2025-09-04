
module Algebra.Goldilocks where

--------------------------------------------------------------------------------

open import Data.Nat
open import Data.Product

open import Meta.Object

--------------------------------------------------------------------------------

open U64Lib
open BitLib

Goldilocks : Ty
Goldilocks = Named "Goldilocks" U64

-- p = 2^64 - 2^32 + 1
theGoldilocksPrime : ℕ
theGoldilocksPrime = 0xffffffff00000001    

fromℕ : ℕ -> Tm Goldilocks
fromℕ k = wrap (kstU64′ (k % theGoldilocksPrime))

private

  F : Ty
  F = Goldilocks

  with1 : (Tm U64 -> Tm U64) -> Tm F -> Tm F
  with1 f tm = Let (unwrap tm) \x -> wrap (f x)

  with2 : (Tm U64 -> Tm U64 -> Tm U64) -> Tm F -> Tm F -> Tm F
  with2 g tm1 tm2 = Let (unwrap tm1) \x -> Let (unwrap tm2) \y -> wrap (g x y)

  with2′ : {ty : Ty} -> (Tm U64 -> Tm U64 -> Tm ty) -> Tm F -> Tm F -> Tm ty
  with2′ g tm1 tm2 = Let (unwrap tm1) \x -> Let (unwrap tm2) \y -> g x y

isEqual : Tm F -> Tm F -> Tm Bit
isEqual = with2′ eqU64

----------------------------------------

private 

  thePrimeU64 : Tm U64
  thePrimeU64 = kstU64′ theGoldilocksPrime

  neg' : Tm U64 -> Tm U64
  neg' x = ifte (isZeroU64 x) x (subU64 thePrimeU64 x)

  add' : Tm U64 -> Tm U64 -> Tm U64
  add' x y = runGen do
    c , z <- pair⇑ (addCarryU64 zeroBit x y)
    let out = ifte (or c (geU64 z thePrimeU64))
          (subU64 z thePrimeU64)
          z
    return out

  sub' : Tm U64 -> Tm U64 -> Tm U64
  sub' x y = runGen do
    z <- gen (subU64 x y)
    let out = ifte (gtU64 z x)
          (addU64 z thePrimeU64)
          z
    return out  

----------------------------------------

neg : Tm F -> Tm F
neg = with1 neg'

add : Tm F -> Tm F -> Tm F
add = with2 add'

sub : Tm F -> Tm F -> Tm F
sub = with2 sub'

--------------------------------------------------------------------------------

postulate
  shiftLeftByU64  : ℕ -> Tm U64 -> Tm U64
  shiftRightByU64 : ℕ -> Tm U64 -> Tm U64

private
  
  _<<<_ : Tm U64 -> ℕ -> Tm U64
  _<<<_ x k = shiftLeftByU64 k x

  _>>>_ : Tm U64 -> ℕ -> Tm U64
  _>>>_ x k = shiftRightByU64 k x

  loMask : Tm U64
  loMask = kstU64′ 0xffffffff

  hiLoWord32 : Tm U64 -> Gen (Tm U64 × Tm U64)
  hiLoWord32 input = do
    w  <- gen input
    lo <- gen (bitAndU64 w loMask)
    hi <- gen (w >>> 32)
    return (hi , lo)
 
reduceToU64 : Tm U128 -> Gen (Tm U64)
reduceToU64 input = do
  hi , n0 <- pair⇑ input
  n1 , n2 <- hiLoWord32 hi
  mid  <- gen (subU64 (n1 <<< 32) n1)
  tmp  <- gen (addU64 n0 mid)
  tmp′ <- gen (ifte (ltU64 tmp n0) (subU64 tmp thePrimeU64) tmp)
  res  <- gen (subU64 tmp′ n2)
  res′ <- gen (ifte (gtU64 res tmp) (addU64 res thePrimeU64) res)
  return res′

reduce : Tm U128 -> Gen (Tm F)
reduce input = do
  res <- reduceToU64 input
  let out = ifte (geU64 res thePrimeU64) (subU64 res thePrimeU64) res
  return (wrap out)

mul : Tm F -> Tm F -> Tm F
mul fld1 fld2 = runGen do
  x <- gen (unwrap fld1)
  y <- gen (unwrap fld2)
  z <- gen (mulExtU64 x y)
  reduce z

sqr : Tm F -> Tm F
sqr x = mul x x

--------------------------------------------------------------------------------

open import Algebra.API.Field

goldilocksAPI : FieldAPI
goldilocksAPI = record
  { F     = Goldilocks
  ; fromℕ = fromℕ
    -- metadata
  ; name  = "Goldilocks"
  ; size  = theGoldilocksPrime
--    mulGen : Tm F
    -- queries
  ; isEqual  = isEqual
--    isEqualℕ : ℕ    -> Tm F -> Tm Bit
    -- arithmetic
  ; neg   = neg
  ; add   = add
  ; sub   = sub
  ; sqr   = sqr
  ; mul   = mul
--    inv   : Tm F -> Tm F  
--    div   : Tm F -> Tm F -> Tm F
--    divBySmallConst : Tm F -> ℕ -> Tm F
    -- exponentiation
--    staticPow : Tm F -> ℕ -> Tm F
  }

--------------------------------------------------------------------------------
