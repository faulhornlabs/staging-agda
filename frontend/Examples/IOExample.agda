
module Examples.IOExample where

--------------------------------------------------------------------------------

open import Data.Empty
open import Data.Nat
open import Data.String

-- open import Function using ( _$_ )
-- open import Relation.Binary.PropositionalEquality

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
    
  data MIO : Ty -> Set where
    MkMIO : Tm (IO ty) -> MIO ty

  runMIO : MIO ty -> Tm (IO ty)
  runMIO (MkMIO tm) = tm
  
  private
    _>>=_ : MIO s -> (Tm s -> MIO t) -> MIO t    
    _>>=_ (MkMIO u) h = MkMIO (bind u (Lam \x -> runMIO (h x)))

    _>>_ : MIO s -> MIO t -> MIO t
    _>>_ (MkMIO u) (MkMIO v) = MkMIO (then u v)

    mreturn : Tm ty -> MIO ty
    mreturn x = MkMIO (return x)

  mget : {ty : Ty} -> String -> MIO ty
  mget {ty} name = MkMIO (get name ty)

  mput : String -> Tm ty -> MIO Unit
  mput name what = MkMIO (put name what)

  open U64Lib

  test0 : Tm (IO Unit)
  test0 = runMIO do
    x <- mget "x"
    mput "out" (addU64 x (kstU64′ 101))

  testA : Tm (IO U64)
  testA = runMIO do
    mput "foo" (kstU64′ 666)
    mput "bar" (kstU64′ 777)
    mreturn (kstU64′ 555)

  test0b : Tm (IO Unit)
  test0b = Let testA \action -> runMIO do
    x <- mget "x"
    y <- MkMIO (action)
    mput "out" (addU64 x y)

  test1 : Tm (IO Unit)
  test1 = runMIO do
    x <- mget "x"
    y <- mget "y"
    z <- mget "z"
    mput "out1" (compute1 x y z) 
    mput "out2" (compute2 x y z)
    mreturn tt

exIO0 : Tm (IO Unit)
exIO0 = MyMain.test0

exIO0b : Tm (IO Unit)
exIO0b = MyMain.test0b

exIO1 : Tm (IO Unit)
exIO1 = MyMain.test1

--------------------------------------------------------------------------------

