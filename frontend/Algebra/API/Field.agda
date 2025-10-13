
module Algebra.API.Field where

--------------------------------------------------------------------------------

open import Data.Nat
open import Data.String

open import Meta.Object

--------------------------------------------------------------------------------

record FieldAPI : Set where
  field
    F     : Ty
    fromℕ : ℕ -> Tm F
    -- metadata
    name   : String
    size   : ℕ
--    mulGen : Tm F
    -- queries
    isEqual  : Tm F -> Tm F -> Tm Bit
    isEqualℕ : ℕ    -> Tm F -> Tm Bit
    -- arithmetic
    neg   : Tm F -> Tm F
    add   : Tm F -> Tm F -> Tm F
    sub   : Tm F -> Tm F -> Tm F
    sqr   : Tm F -> Tm F
    mul   : Tm F -> Tm F -> Tm F
    inv   : Tm F -> Tm F  
    div   : Tm F -> Tm F -> Tm F
--    divBySmallConst : Tm F -> ℕ -> Tm F
    -- exponentiation
--    staticPow : Tm F -> ℕ -> Tm F

--------------------------------------------------------------------------------
