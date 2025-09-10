
module Algebra.API.Word.BigInt where

--------------------------------------------------------------------------------

open import Data.Nat

import Algebra.Limbs  as L     
import Algebra.BigInt as B

open import Algebra.API.Word

import Meta.Lib 
open Meta.Lib.BitLib

--------------------------------------------------------------------------------

bigIntAsWordAPI : ℕ -> WordAPI
bigIntAsWordAPI nlimbs =  record
  { #bits = 64 * nlimbs
  ; Word  = B.BigInt nlimbs
  ; fromℕ = L.bigIntFromℕ
    -- queries
  ; isEqualℕ = \n y -> B.isEqual (L.bigIntFromℕ n) y
  ; isEqual  = B.isEqual
  ; isLT     = B.isLT
  ; isLE     = B.isLE
    -- arithmetic
  ; addCarry = B.addCarry zeroBit
  ; subCarry = B.subCarry zeroBit
  ; neg   = B.neg
  ; add   = B.addNC
  ; sub   = B.subNC
  ; sqr   = B.squareTrunc
  ; mul   = B.mulTrunc
  ; powℕ  = B.powℕ
    -- bit operations
  ; complement = B.bitComplement
  ; bitOr      = B.bitOr
  ; bitAnd     = B.bitAnd
  ; bitXor     = B.bitXor
    -- shifts
  ; shiftLeftBy1  = B.shiftLeftBy1
  ; shiftRightBy1 = B.shiftRightBy1
  }

--------------------------------------------------------------------------------
