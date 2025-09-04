
module Examples.IOExample where

--------------------------------------------------------------------------------

open import Data.Empty
open import Data.Nat

open import Function using ( _$_ )

open import Relation.Binary.PropositionalEquality

open import Meta.Object
open import Algebra.FieldLib
open import Algebra.Limbs
open import Algebra.Prime

--------------------------------------------------------------------------------

open import Algebra.BigInt using ( BigInt )

open IOLib

--------------------------------------------------------------------------------
-- *** FIELD PRIME ***

thePrime-ℕ : ℕ
thePrime-ℕ = bigFieldPrime (ScalarField BN254)

thePrime : Prime
thePrime = mkPrime thePrime-ℕ

--------------------------------------------------------------------------------
-- *** MONTGOMERY ***

module Foo where

  import Algebra.Montgomery.Impl as Montgomery
  open module MontP = Montgomery thePrime

  -- x*y + z
  compute1 : Tm (BigInt 4) -> Tm (BigInt 4) -> Tm (BigInt 4) -> Tm (BigInt 4)
  compute1 big1 big2 big3 = runGen do
    x <- gen (MontP.unsafeFromBigInt big1)
    y <- gen (MontP.unsafeFromBigInt big2)
    z <- gen (MontP.unsafeFromBigInt big3)
    tmp₁ <- gen (MontP.mul x y)
    tmp₂ <- gen (MontP.add tmp₁ z)
    out  <- gen (MontP.toBigInt tmp₂)
    Meta.Object.return out

  -- (x-y) * (x-z)
  compute2 : Tm (BigInt 4) -> Tm (BigInt 4) -> Tm (BigInt 4) -> Tm (BigInt 4)
  compute2 big1 big2 big3 = runGen do
    x <- gen (MontP.unsafeFromBigInt big1)
    y <- gen (MontP.unsafeFromBigInt big2)
    z <- gen (MontP.unsafeFromBigInt big3)
    tmp₁ <- gen (MontP.sub x y)
    tmp₂ <- gen (MontP.sub x z)
    tmp₃ <- gen (MontP.mul tmp₁ tmp₂)
    out  <- gen (MontP.toBigInt tmp₃)
    Meta.Object.return out

  test1 : Tm IO
  test1 = 
    get "x" \x -> 
    get "y" \y -> 
    get "z" \z -> 
    put "out1" (compute1 x y z) $
    put "out2" (compute2 x y z) $
    halt

exIO1 : Tm IO
exIO1 = Foo.test1

--------------------------------------------------------------------------------

