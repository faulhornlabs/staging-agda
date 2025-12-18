
module Examples.FFT where

--------------------------------------------------------------------------------

open import Function using ( _$_ )
open import Relation.Binary.PropositionalEquality using ( refl )

open import Meta.Object hiding ( Gen ; _>>=_ ; _>>_ )

open import Algebra.API.Field
open import Algebra.Goldilocks using ( goldilocksAPI )

import Algebra.NTT

open module NTT = Algebra.NTT goldilocksAPI

--------------------------------------------------------------------------------

open IOLib
open U64Lib

private

  variable
    ty  : Ty
    s t : Ty
    
  _>>=_ : Tm (IO s) -> (Tm s -> Tm (IO t)) -> Tm (IO t)    
  _>>=_ u h = bind u (Lam \x -> h x)

  _>>_ : Tm (IO s) -> Tm (IO t) -> Tm (IO t)
  _>>_ u v = then u v

--------------------------------------------------------------------------------

private

  recAdd : Tm U64 -> Tm U64 -> Tm U64
  recAdd x y = App f y where
    +₁ -₁ : Tm U64 -> Tm U64
    +₁ x = addU64 x oneU64
    -₁ x = subU64 x oneU64
    add′ : Tm (U64 ⇒ U64) -> Tm (U64 ⇒ U64)
    add′ rec = Lam \y -> ifte (isZeroU64 y) x (+₁ (App rec (-₁ y)))
    f : Tm (U64 ⇒ U64)
    f = Fix add′

  ize′ : Tm (U64 ⇒ U64)
  ize′ = Fix \rec -> Lam \n -> ifte (isZeroU64 n) (kstU64′ 100) (incU64 (App rec (decU64 n)))
  
  ize : Tm U64 -> Tm U64
  ize = App ize′

  sanity : Tm U64
  sanity = App2 (Lam2 \x y -> mulTruncU64 (incU64 x) (incU64 y)) (kstU64′ 5) (kstU64′ 110)

exFFT0 : Tm U64
exFFT0 = ize (kstU64′ 3)

exFFT0a : Tm (IO Unit)
exFFT0a =
  Let (kstU64′ 5) \five ->
  Let (kstU64′ 3) \three ->
  Let (recAdd five three) \result -> 
  print "recursive 5 + 3" result

exFFT0b : Tm (IO Unit)
exFFT0b = do
  print "exp(5)" (exp₂ (kstU64′ 5))

exFFT1 : Tm (IO Unit)
exFFT1 = do
  res <- bitReverseDebugIO (kstU64′ 8) (kstU64′ 0x65)
  print "bitReverseIO(8,0x65)" res

exFFT2 : Tm (IO Unit)
exFFT2 = withTmpArray {vty = U64VTy} (kstU64′ 16) \arr -> do
  for arr \i -> write {eq = refl} arr i i
  perm <- bitReversalPerm arr
  print "bit-reversed" perm

