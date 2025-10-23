
module Algebra.Curve.Params where

--------------------------------------------------------------------------------

open import Meta.Object

open import Algebra.Prime
open import Algebra.FieldLib
open import Algebra.API.Field

--------------------------------------------------------------------------------

record WeierstrassCurve : Set where
  field
    baseFieldAPI : FieldAPI
    coeffA : Val (FieldAPI.F baseFieldAPI)
    coeffB : Val (FieldAPI.F baseFieldAPI)

--------------------------------------------------------------------------------

module ExCurve1 where

  theFieldPrime : Prime
  theFieldPrime = mkPrime (bigFieldPrime (ScalarField BN254))

  open import Algebra.Montgomery.Instance

-- module ExCurve1 where

