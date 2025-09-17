
-- extended binary Euclidean algorithm

open import Algebra.API.Word

module Algebra.Euclid (api : WordAPI) where

--------------------------------------------------------------------------------

open import Data.Nat
open import Data.Product

open import Meta.Object

open import Algebra.Prime

--------------------------------------------------------------------------------

open BitLib
open WordAPI api

-- Classic extended binary Euclidean algorithm.
--
-- see eg. Thomas Pornin: Optimized Binary GCD for Modular Inversion
--
-- TODO: maybe implement some optimizations?
--
modularBinaryEuclid : Prime -> Tm Word -> Tm Word -> Tm Word -> Tm Word -> Tm Word 
modularBinaryEuclid prime′ x0 y0 u0 v0 = App worker (mkQuad u0 x0 v0 y0) where 

  prime : Tm Word
  prime = fromℕ (Prime.primeℕ prime′)

  halfPrime : Tm Word
  halfPrime = snd (shiftRightBy1 prime)

  halfPrime₊₁ : Tm Word
  halfPrime₊₁ = add halfPrime (fromℕ 1)

  step : Tm (Pair Word Word ⇒ Pair Word Word)
  step = Fix (Lam recU) where
    recU : Tm (Pair Word Word ⇒ Pair Word Word) -> Tm (Pair Word Word ⇒ Pair Word Word)
    recU rec = Lam \u,x -> runGen do
      (u , x  ) <- pair⇑ u,x
      (c , u′ ) <- pair⇑ (shiftRightBy1 u)
      let kont = runGen do
            (d , x′ ) <- pair⇑ (shiftRightBy1 x)
            x″ <- gen (ifte d (add x′ halfPrime₊₁) x′)
            return (mkPair u′ x″)
      return (ifte c u,x (App rec kont))

  Quad : Ty
  Quad = Pair (Pair Word Word) (Pair Word Word)

  mkQuad : Tm Word -> Tm Word -> Tm Word -> Tm Word -> Tm Quad
  mkQuad u x v y = mkPair (mkPair u x) (mkPair v y)

  subModP : Tm Word -> Tm Word -> Tm Word
  subModP x y = runGen do
    (c , z) <- pair⇑ (subCarry x y)
    let z′ = ifte c (add z prime) z
    return z′
  
  worker : Tm (Quad ⇒ Word)
  worker = Fix (Lam recQ) where
    recQ : Tm (Quad ⇒ Word) -> Tm (Quad ⇒ Word)
    recQ rec = Lam \u,x,v,y -> runGen do
      (u,x , v,y) <- pair⇑ u,x,v,y
      u , x <- pair⇑ u,x
      v , y <- pair⇑ v,y
      -- debug "u" u
      -- debug "x" x
      -- debug "v" v
      -- debug "y" y
      let kont = runGen do
            u′,x′ <- gen (App step u,x)
            v′,y′ <- gen (App step v,y)
            u′ , x′ <- pair⇑ u′,x′
            v′ , y′ <- pair⇑ v′,y′
            return (ifte (isLT u′ v′)
              (mkQuad      u′              x′     (sub v′ u′) (subModP y′ x′))
              (mkQuad (sub u′ v′) (subModP x′ y′)      v′              y′    ))
            
      let out = ifte (isEqualℕ 1 u) x
                  (ifte (isEqualℕ 1 v) y
                    (App rec kont))
      return out
      
--------------------------------------------------------------------------------

modularDiv′ : Prime -> Tm Word -> Tm Word -> Tm Word
modularDiv′ prime a b = modularBinaryEuclid prime x y u v where
  x = a
  y = fromℕ 0
  u = b
  v = fromℕ (Prime.primeℕ prime)

modularInv′ : Prime -> Tm Word -> Tm Word
modularInv′ prime what = modularDiv′ prime (fromℕ 1) what

--------------------------------------------------------------------------------

