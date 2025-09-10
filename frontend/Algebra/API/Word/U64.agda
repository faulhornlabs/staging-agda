
module Algebra.API.Word.U64 where

--------------------------------------------------------------------------------

open import Data.Nat

open import Meta.Object

open import Algebra.API.Word

--------------------------------------------------------------------------------

open U64Lib
open BitLib

private 

  open import Algebra.Misc using ( Half ; Even ; Odd ; halve )
  
  {-# TERMINATING #-}
  powℕ : Tm U64 -> ℕ -> Tm U64
  powℕ base expo = go expo base where
    go : ℕ -> Tm U64 -> Tm U64
    go 0 _ = oneU64
    go 1 x = x
    go n x with halve n 
    go _ x | Even k = Let (go k x) \s ->              sqrTruncU64 s
    go _ x | Odd  k = Let (go k x) \s -> mulTruncU64 (sqrTruncU64 s) x

--------------------------------------------------------------------------------

u64AsWordAPI : WordAPI
u64AsWordAPI = record
  { #bits = 64 
  ; Word  = U64
  ; fromℕ = kstU64′
    -- queries
  ; isEqualℕ = \n y -> eqU64 (kstU64′ n) y
  ; isEqual  = eqU64
  ; isLT     = ltU64
  ; isLE     = leU64
    -- arithmetic
  ; addCarry = addCarryU64 zeroBit
  ; subCarry = subCarryU64 zeroBit
  ; neg   = negU64
  ; add   = addU64
  ; sub   = subU64
  ; sqr   = sqrTruncU64
  ; mul   = mulTruncU64
  ; powℕ  = powℕ
    -- bit operations
  ; complement = bitComplU64
  ; bitOr      = bitOrU64
  ; bitAnd     = bitAndU64
  ; bitXor     = bitXorU64
    -- shifts
  ; shiftLeftBy1  = shiftLeftU64
  ; shiftRightBy1 = shiftRightU64
  }

--------------------------------------------------------------------------------
