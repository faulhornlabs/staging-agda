
module Examples.Simple where

--------------------------------------------------------------------------------

open import Data.Empty
open import Data.Nat

open import Relation.Binary.PropositionalEquality

open import Meta.Object
open import Algebra.FieldLib
open import Algebra.Limbs
open import Algebra.Prime

--------------------------------------------------------------------------------

-- *** BIGINT ***

open import Algebra.BigInt using ( BigInt )

open IOLib

module Big where

  open import Algebra.BigInt 

  halfP+1 : Tm (BigInt 4)
  halfP+1 = bigIntFromℕ 10944121435919637611123202872628637544274182200208017171849102093287904247809

  big1 big2 big3 : Tm (BigInt 4)
  big1 = bigIntFromℕ 12535032671501493392438659292886563663979619812816639413586309554197071221275
  big2 = bigIntFromℕ 20670156704232560809430694243501641649572216251781105022963497476851362916519
  big3 = bigIntFromℕ 10734482926936635597888852654981536388697257091861152194513442686302125663795
  --         prime = 21888242871839275222246405745257275088548364400416034343698204186575808495617

  small1 small2 : Tm (BigInt 2)
  small1 = bigIntFromℕ 298219370995091515800384725779828479220
  small2 = bigIntFromℕ 45210828018843085130265813626022701902

  verySmall : Tm (BigInt 1)
  verySmall = bigIntFromℕ 45210828018843

  tiny1 tiny2 tiny3 : Tm (BigInt 1)
  tiny1 = bigIntFromℕ 386048
  tiny2 = bigIntFromℕ 713841
  tiny3 = bigIntFromℕ 489020

  exBig0 : Tm (BigInt _)
  exBig0 = snd (Algebra.BigInt.add big1 big2)

  exBig1 : Tm Bit
  exBig1 = isGE big2 big1 

  exBigMul : Tm (BigInt _)
  exBigMul = mulExt big1 big2

  exSmall1 : Tm (BigInt 2)
  exSmall1 = subNC small2 small1
  -- exSmall1 = Algebra.BigInt.addNC small1 small2

  exSmall2 : Tm Bit
  exSmall2 = isGE small1 small2 

  exBinary' : Tm (BigInt 4)
  exBinary' = bitXor (bitOr big1 big2) (bitAnd (bitComplement big1) big3)

{-
  -- this used the old-style IO hack
  exBinary : Tm (BigInt 4)
  exBinary = runGen do
    x <- gen (input "x")
    y <- gen (input "y")
    z <- gen (input "z")
    let out = bitXor (bitOr x y) (bitAnd (bitComplement x) z)
    return out
-}

--------------------------------------------------------------------------------
-- *** FIELD PRIME ***

thePrime-ℕ : ℕ
thePrime-ℕ = bigFieldPrime (ScalarField BN254)

thePrime : Prime
thePrime = mkPrime thePrime-ℕ

tinyPrime : Prime
tinyPrime = mkPrime 1299709

--------------------------------------------------------------------------------
-- *** MODULAR ***

module Baz where

  import Algebra.Modular as Modular

  open module ModuloP = Modular thePrime 

  T : Ty
  T = Mod
  
  mod1 mod2 mod3 : Tm Mod
  mod1 = wrap Big.big1
  mod2 = wrap Big.big2
  mod3 = wrap Big.big3

  exMod1 exMod2 exModInv exModDiv : Tm Mod
  exMod1 = ModuloP.add mod1 mod2
  exMod2 = ModuloP.sub mod1 mod2
  exModInv = ModuloP.inv mod1
  exModDiv = ModuloP.div mod1 mod2

exMod1 exMod2 exModInv exModDiv : Tm Baz.T
exMod1 = Baz.exMod1
exMod2 = Baz.exMod2
exModInv = Baz.exModInv
exModDiv = Baz.exModDiv

--------------------------------------------------------------------------------

module TinyBaz where

  import Algebra.Modular as Modular

  open module ModuloP = Modular tinyPrime

  T : Ty
  T = Mod
  
  mod1 mod2 mod3 : Tm Mod
  mod1 = wrap Big.tiny1
  mod2 = wrap Big.tiny2
  mod3 = wrap Big.tiny3

  exTinyModInv exTinyModDiv : Tm Mod
  exTinyModInv = ModuloP.inv mod1
  exTinyModDiv = ModuloP.div mod1 mod2

exTinyModInv exTinyModDiv : Tm TinyBaz.T
exTinyModInv = TinyBaz.exTinyModInv
exTinyModDiv = TinyBaz.exTinyModDiv

--------------------------------------------------------------------------------

module TinyBazU64 where

  open U64Lib
  
  open import Algebra.API.Word.U64 

  open import Algebra.Euclid ( u64AsWordAPI )

  pr : ℕ
  pr = 1299709 
  
  p x y : Tm U64
  p = kstU64′ pr
  x = kstU64′ 386048
  y = kstU64′ 713841

  prime : Prime
  prime = mkPrime pr

  rx ry : Tm U64
  rx = modularInv′ prime x
  ry = modularInv′ prime y

exInvU64xy : Tm (Pair U64 U64)
exInvU64xy = mkPair TinyBazU64.rx TinyBazU64.ry

exInvU64x exInvU64y : Tm U64
exInvU64x = TinyBazU64.rx
exInvU64y = TinyBazU64.ry

--------------------------------------------------------------------------------

module BabyBaz where

  import Algebra.Modular as Modular

  babyPrime : Prime
  babyPrime = mkPrime 163 -- 61
  
  open module ModuloP = Modular babyPrime

  T : Ty
  T = Mod

  baby1 baby2 : Tm (BigInt 1)
  baby1 = bigIntFromℕ 17
  baby2 = bigIntFromℕ 23

  mod1 mod2  : Tm Mod
  mod1 = wrap baby1
  mod2 = wrap baby2

  exBabyModInv exBabyModDiv : Tm Mod
  exBabyModInv = ModuloP.inv mod1
  exBabyModDiv = ModuloP.div mod1 mod2

exBabyModInv exBabyModDiv : Tm BabyBaz.T
exBabyModInv = BabyBaz.exBabyModInv
exBabyModDiv = BabyBaz.exBabyModDiv

--------------------------------------------------------------------------------
-- *** MONTGOMERY ***

module Bar where

  import Algebra.Montgomery.Impl as Montgomery
  open module MontP = Montgomery thePrime

  mont1 mont2 mont3 : Tm Mont
  mont1 = wrap Big.big1
  mont2 = wrap Big.big2
  mont3 = wrap Big.big3

  exMont1 : Tm Mont
  exMont1 = MontP.mul mont1 mont2

  exMont2 : Tm (BigInt 4)
  exMont2 = runGen do
    x <- gen (MontP.unsafeFromBigInt Big.big1)
    y <- gen (MontP.unsafeFromBigInt Big.big2)
    z <- gen (MontP.unsafeFromBigInt Big.big3)
    tmp₁ <- gen (MontP.mul x y)
    tmp₂ <- gen (MontP.add tmp₁ z)
    tmp₃ <- gen (MontP.toBigInt tmp₂)
    return tmp₃

  exMontDiv : Tm (BigInt 4)
  exMontDiv = runGen do
    x <- gen (MontP.unsafeFromBigInt Big.big1)
    y <- gen (MontP.unsafeFromBigInt Big.big2)
    xpery <- gen (MontP.div x y)
    x′    <- gen (MontP.mul y xpery)
    z     <- gen (MontP.sub x′ x)           -- should be zero
    return (MontP.toBigInt z) 

  exMontInv : Tm (BigInt 4)
  exMontInv = runGen do
    x    <- gen (MontP.unsafeFromBigInt Big.big3)
    invx <- gen (MontP.inv x)
    one  <- gen (MontP.mul invx x)          -- should be one
    return (MontP.toBigInt one) 

exMont2 : Tm (BigInt 4)
exMont2 = Bar.exMont2

exMontInv : Tm (BigInt 4)
exMontInv = Bar.exMontInv

exMontDiv : Tm (BigInt 4)
exMontDiv = Bar.exMontDiv

----------------------------------------

module Foo where

  import Algebra.Montgomery.Instance as Inst

  exMont2b' : Inst.MontgomeryAPI thePrime -> Tm (BigInt 4)
  exMont2b' montAPI = result where

    open Inst.MontgomeryAPI montAPI

    {-# NON_COVERING #-}
    eq4 : #limbs ≡ 4
    eq4 with #limbs
    eq4 | 4 = refl

{-
    big1 big2 big3 : Tm Big
    big1 = bigIntFromℕ 12535032671501493392438659292886563663979619812816639413586309554197071221275
    big2 = bigIntFromℕ 20670156704232560809430694243501641649572216251781105022963497476851362916519
    big3 = bigIntFromℕ 10734482926936635597888852654981536388697257091861152194513442686302125663795
-}

    mont1 mont2 mont3 : Tm Mont
    mont1 = montFromℕ 12535032671501493392438659292886563663979619812816639413586309554197071221275
    mont2 = montFromℕ 20670156704232560809430694243501641649572216251781105022963497476851362916519
    mont3 = montFromℕ 10734482926936635597888852654981536388697257091861152194513442686302125663795

    result : Tm (BigInt 4)
    result = runGen do
      x <- gen mont1 -- (unsafeFromBig big1)
      y <- gen mont2 -- (unsafeFromBig big2)
      z <- gen mont3 -- (unsafeFromBig big3)
      tmp₁ <- gen (mul x y)
      tmp₂ <- gen (add tmp₁ z)
      tmp₃ <- gen (exportMont eq4 tmp₂)
      return tmp₃

  exMont2b : Tm (BigInt 4)
  exMont2b = Inst.withMontgomery thePrime exMont2b'

exMont2b : Tm (BigInt 4)
exMont2b = Foo.exMont2b


--------------------------------------------------------------------------------
-- *** NAT and RECURSION ***

open NatLib

import Examples.Tests as Tests

natEx1 natEx2 : Tm Nat
natEx1 = Tests.natFixPow 7 (kstNat 2)
natEx2 = Tests.natDynPowNaive (kstNat 8) (kstNat 2) 

lamEx0 lamEx2a : Tm Nat
lamEx1 lamEx2  : Tm (Pair Nat Nat)
lamEx0  = App Tests.squarePlus7 (kstNat 10)
lamEx1  = Tests.lamTest2
lamEx2a = Tests.lamTest3
lamEx2  = Tests.lambdaLiftTest

mixedLam1 : Tm (Pair U64 Nat)
mixedLam1 = Tests.mixedTest1

--------------------------------------------------------------------------------
