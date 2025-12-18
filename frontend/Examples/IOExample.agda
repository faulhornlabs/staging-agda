
module Examples.IOExample where

--------------------------------------------------------------------------------

open import Data.Empty
open import Data.Nat
open import Data.String

-- open import Function using ( _$_ )
open import Relation.Binary.PropositionalEquality using ( refl )

open import Meta.Object hiding ( Gen ; return ; _>>_ ; _>>=_ )

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

open U64Lib using ( kstU64′ )

--------------------------------------------------------------------------------
-- *** MONTGOMERY ***

module Foo where

  open import Meta.Gen
  
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

module MyMain where

  open Foo

  variable
    ty  : Ty
    s t : Ty
    
  private
    _>>=_ : Tm (IO s) -> (Tm s -> Tm (IO t)) -> Tm (IO t)    
    _>>=_ u h = bind u (Lam \x -> h x)

    _>>_ : Tm (IO s) -> Tm (IO t) -> Tm (IO t)
    _>>_ u v = then u v

  open U64Lib

  test0 : Tm (IO Unit)
  test0 = do
    x <- get′ "x" U64 
    put "out" (addU64 x (kstU64′ 101))

  testA : Tm (IO U64)
  testA = do
    put "foo" (kstU64′ 666)
    put "bar" (kstU64′ 777)
    return (kstU64′ 555)

  test0b : Tm (IO Unit)
  test0b = Let testA \action -> do
    x <- get′ "x" U64
    put "x_was" x
    y <- action
    put "out" (addU64 x y)

  test1 : Tm (IO Unit)
  test1 = do
    x <- get "x"
    y <- get "y"
    z <- get "z"
    put "out1" (compute1 x y z) 
    put "out2" (compute2 x y z)
    return tt

  testLoop1 : Tm U64 -> Tm (IO U64)
  testLoop1 n = do
    withTmpArray {vty = U64VTy} n \arr -> do
      for arr \i -> write {eq = refl} arr i (addU64 i (kstU64′ 1))
      print "array" arr
      read {eq = refl} arr (subU64 n (kstU64′ 1))

  exLoop0 : Tm (IO Unit)
  exLoop0 = do
    z <- testLoop1 (kstU64′ 10)
    put "result" z

exIO0 : Tm (IO Unit)
exIO0 = MyMain.test0

exIO0b : Tm (IO Unit)
exIO0b = MyMain.test0b

exIO1 : Tm (IO Unit)
exIO1 = MyMain.test1

exLoop0 : Tm (IO Unit)
exLoop0 = MyMain.exLoop0

{-
exIOWtf : Tm (IO Unit)
exIOWtf = MyMain.exIOWtf --  (kstU64′ 5)
-}

--------------------------------------------------------------------------------

