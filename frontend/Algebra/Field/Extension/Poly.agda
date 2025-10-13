
-- small (low-degree) polynomials over fields
-- used for implementing field extensions

open import Algebra.API.Field

module Algebra.Field.Extension.Poly ( coeffAPI : FieldAPI ) where

--------------------------------------------------------------------------------

open import Data.Nat
open import Data.Fin using ( Fin )
open import Data.Vec
open import Data.List
open import Data.Product

open import Meta.Object

open BitLib

--------------------------------------------------------------------------------

open FieldAPI coeffAPI

Coeff : Ty
Coeff = F

zeroCoeff oneCoeff : Tm Coeff
zeroCoeff = fromℕ 0
oneCoeff = fromℕ 1

isZero isOne : Tm Coeff -> Tm Bit
isZero = isEqualℕ 0
isOne  = isEqualℕ 1

--------------------------------------------------------------------------------

Poly : ℕ -> Ty
Poly deg =  Vect (suc deg) Coeff

variable
  d e : ℕ
  
constPoly : Tm Coeff -> Tm (Poly d)
constPoly {d = d} c = mkVect (c ∷ Data.Vec.replicate d zeroCoeff)

polyIsEqualConst : Tm Coeff -> Tm (Poly d) -> Tm Bit
polyIsEqualConst c0 poly = runGen do
  (c ∷ rest) <- unVect poly
  return (ifte (isEqual c c0)
    (allOf isZero rest)
    zeroBit)

polyIsZero : Tm (Poly d) -> Tm Bit
polyIsZero = polyIsEqualConst zeroCoeff

polyIsOne : Tm (Poly d) -> Tm Bit
polyIsOne = polyIsEqualConst oneCoeff

--------------------------------------------------------------------------------

negPoly : Tm (Poly d) -> Tm (Poly d)
negPoly = vectMap neg

addPoly : Tm (Poly d) -> Tm (Poly d) -> Tm (Poly d)
addPoly = vectZipWith add

subPoly : Tm (Poly d) -> Tm (Poly d) -> Tm (Poly d)
subPoly = vectZipWith sub

scalePoly : Tm Coeff -> Tm (Poly d) -> Tm (Poly d)
scalePoly s = vectMap (mul s)

import Algebra.Misc
open Algebra.Misc.Diagonal

private

  {-# NON_TERMINATING #-}
  listFoldLeft1 : {t : Ty} -> Tm t -> (Tm t -> Tm t -> Tm t) -> List (Tm t) -> Tm t
  listFoldLeft1 {t = t} ini fun = go where
    go : List (Tm t) -> Tm t
    go []             = ini
    go (x ∷ [])       = x
    go (x ∷ y ∷ rest) = go (fun x y ∷ rest)

  listFoldRight1 : {t : Ty} -> Tm t -> (Tm t -> Tm t -> Tm t) -> List (Tm t) -> Tm t
  listFoldRight1 {t = t} ini fun = go where
    go : List (Tm t) -> Tm t
    go []       = ini
    go (x ∷ []) = x
    go (x ∷ xs) = fun x (go xs)

open Algebra.Misc.MyFin₁

polyMul : Tm (Poly d) -> Tm (Poly e) -> Tm (Poly (d + e))
polyMul {d = d} {e = e} poly1 poly2 = runGen
  do
    xs <- gen poly1
    ys <- gen poly2
    parts <- vecMapM (wrapper xs ys) (vecAllFin₁ (d + e))
    return (mkVect parts)
  where
    wrapper : Tm (Poly d) -> Tm (Poly e) -> Fin₁ (d + e) -> Gen (Tm Coeff)
    wrapper xs ys = worker where
      worker : Fin₁ (d + e) -> Gen (Tm Coeff)
      worker  k = do
        terms <- listMapM (\(i , j) -> return (mul (vecproj i xs) (vecproj j ys))) (Algebra.Misc.Diagonal.diagonal₁ d e k)
        return (listFoldLeft1 zeroCoeff add terms)

-- a monic irredicuble polynomial of degree d
-- note: we don't include the top coefficient 1
MonicIrred₁ : ℕ -> Ty
MonicIrred₁ d = Vect d Coeff

private

  open import Relation.Binary.PropositionalEquality
  open import Relation.Binary.PropositionalEquality.TrustMe

  lemma₁ : suc (suc e + d) ≡ suc (suc (e + d))
  lemma₁ = trustMe
  
  eliminateTopCoeff : Val (MonicIrred₁ d) -> Tm (Poly (suc e + d)) -> Tm (Pair Coeff (Poly (e + d)))
  eliminateTopCoeff {d = d} {e = e} irred input = {!!} where
    topCoeff = vecproj finMax input
  
--polyDivRem
