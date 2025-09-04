
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

  big1 : Tm (BigInt 4)
  big1 = bigIntFromℕ 12535032671501493392438659292886563663979619812816639413586309554197071221275

  big2 : Tm (BigInt 4)
  big2 = bigIntFromℕ 20670156704232560809430694243501641649572216251781105022963497476851362916519
  --         prime = 21888242871839275222246405745257275088548364400416034343698204186575808495617

  big3 : Tm (BigInt 4)
  big3 = bigIntFromℕ 10734482926936635597888852654981536388697257091861152194513442686302125663795

  small1 : Tm (BigInt 2)
  small1 = bigIntFromℕ 298219370995091515800384725779828479220

  small2 : Tm (BigInt 2)
  small2 = bigIntFromℕ 45210828018843085130265813626022701902

  verySmall : Tm (BigInt 1)
  verySmall = bigIntFromℕ 45210828018843

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

--------------------------------------------------------------------------------
-- *** MODULAR ***

module Baz where

  import Algebra.Modular as Modular

  open module ModuloP = Modular thePrime 

  T : Ty
  T = Mod
  
  mod1 : Tm Mod
  mod1 = wrap Big.big1

  mod2 : Tm Mod
  mod2 = wrap Big.big2

  mod3 : Tm Mod
  mod3 = wrap Big.big3

  exMod1 : Tm Mod
  exMod1 = ModuloP.add mod1 mod2

  exMod2 : Tm Mod
  exMod2 = ModuloP.sub mod1 mod2

exMod1 : Tm Baz.T
exMod1 = Baz.exMod1

exMod2 : Tm Baz.T
exMod2 = Baz.exMod2

--------------------------------------------------------------------------------
-- *** MONTGOMERY ***

module Bar where

  import Algebra.Montgomery.Impl as Montgomery
  open module MontP = Montgomery thePrime

  mont1 : Tm Mont
  mont1 = wrap Big.big1

  mont2 : Tm Mont
  mont2 = wrap Big.big2

  mont3 : Tm Mont
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
    Meta.Object.return tmp₃

exMont2 : Tm (BigInt 4)
exMont2 = Bar.exMont2

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
    big1 : Tm Big
    big1 = bigIntFromℕ 12535032671501493392438659292886563663979619812816639413586309554197071221275

    big2 : Tm Big
    big2 = bigIntFromℕ 20670156704232560809430694243501641649572216251781105022963497476851362916519

    big3 : Tm Big
    big3 = bigIntFromℕ 10734482926936635597888852654981536388697257091861152194513442686302125663795
-}

    mont1 : Tm Mont
    mont1 = montFromℕ 12535032671501493392438659292886563663979619812816639413586309554197071221275

    mont2 : Tm Mont
    mont2 = montFromℕ 20670156704232560809430694243501641649572216251781105022963497476851362916519

    mont3 : Tm Mont
    mont3 = montFromℕ 10734482926936635597888852654981536388697257091861152194513442686302125663795

    result : Tm (BigInt 4)
    result = runGen do
      x <- gen mont1 -- (unsafeFromBig big1)
      y <- gen mont2 -- (unsafeFromBig big2)
      z <- gen mont3 -- (unsafeFromBig big3)
      tmp₁ <- gen (mul x y)
      tmp₂ <- gen (add tmp₁ z)
      tmp₃ <- gen (exportMont eq4 tmp₂)
      Meta.Object.return tmp₃

  exMont2b : Tm (BigInt 4)
  exMont2b = Inst.withMontgomery thePrime exMont2b'

exMont2b : Tm (BigInt 4)
exMont2b = Foo.exMont2b


--------------------------------------------------------------------------------
-- *** NAT and RECURSION ***

open NatLib

import Examples.Tests as Tests

natEx1 : Tm Nat
natEx1 = Tests.natFixPow 7 (kstNat 2)

natEx2 : Tm Nat
natEx2 = Tests.natDynPowNaive (kstNat 8) (kstNat 2) 

lamEx0 : Tm Nat
lamEx0 = App Tests.squarePlus7 (kstNat 10)

lamEx1 : Tm (Pair Nat Nat)
lamEx1 = Tests.lamTest2

lamEx2a : Tm Nat
lamEx2a = Tests.lamTest3

lamEx2 : Tm (Pair Nat Nat)
lamEx2 = Tests.lambdaLiftTest

mixedLam1 : Tm (Pair U64 Nat)
mixedLam1 = Tests.mixedTest1

--------------------------------------------------------------------------------
