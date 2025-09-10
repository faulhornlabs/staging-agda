
-- Arbitrary sized (n-bit) words

module Algebra.API.Word where

--------------------------------------------------------------------------------

open import Data.Nat

open import Meta.Object

--------------------------------------------------------------------------------

record WordAPI : Set where
  field
    #bits : ℕ
    Word  : Ty
    fromℕ : ℕ -> Tm Word
    -- queries
    isEqualℕ : ℕ       -> Tm Word -> Tm Bit
    isEqual  : Tm Word -> Tm Word -> Tm Bit
    isLT     : Tm Word -> Tm Word -> Tm Bit
    isLE     : Tm Word -> Tm Word -> Tm Bit
    -- arithmetic
    addCarry : Tm Word -> Tm Word -> Tm (Pair Bit Word)
    subCarry : Tm Word -> Tm Word -> Tm (Pair Bit Word)
    neg   : Tm Word -> Tm Word
    add   : Tm Word -> Tm Word -> Tm Word
    sub   : Tm Word -> Tm Word -> Tm Word
    sqr   : Tm Word -> Tm Word
    mul   : Tm Word -> Tm Word -> Tm Word
    powℕ  : Tm Word -> ℕ -> Tm Word
    -- bit operations
    complement : Tm Word -> Tm Word
    bitOr      : Tm Word -> Tm Word -> Tm Word
    bitAnd     : Tm Word -> Tm Word -> Tm Word
    bitXor     : Tm Word -> Tm Word -> Tm Word
    -- shifts
    shiftLeftBy1  : Tm Word -> Tm (Pair Bit Word)
    shiftRightBy1 : Tm Word -> Tm (Pair Bit Word)

--------------------------------------------------------------------------------

