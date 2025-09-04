
{-

As the unrolled functions starts to get big, we don't want to inline them all the time.
Instead, we want to make them functions using Let and just call those at the use sites.

This module helps by giving you an API to conveniently do just that.

-}

module Algebra.Montgomery.Instance where

--------------------------------------------------------------------------------

open import Data.Nat

open import Relation.Binary.PropositionalEquality

open import Meta.Object

open import Algebra.BigInt using ( BigInt )
open import Algebra.Limbs
open import Algebra.Prime

--------------------------------------------------------------------------------

record MontgomeryAPI (p : Prime) : Set where
  field
    #limbs : ℕ
    Big    : Ty
    Big²   : Ty
    Mont   : Ty
    montFromℕ     : ℕ -> Tm Mont 
    unsafeFromBig : Tm Big  -> Tm Mont
    toBig         : Tm Mont -> Tm Big 
    importMont    : {l : ℕ} -> #limbs ≡ l -> Tm (BigInt l) -> Tm Mont
    exportMont    : {l : ℕ} -> #limbs ≡ l -> Tm Mont -> Tm (BigInt l)
    neg    : Tm Mont -> Tm Mont
    dbl    : Tm Mont -> Tm Mont
    add    : Tm Mont -> Tm Mont -> Tm Mont
    sub    : Tm Mont -> Tm Mont -> Tm Mont
    sqr    : Tm Mont -> Tm Mont
    mul    : Tm Mont -> Tm Mont -> Tm Mont

--------------------------------------------------------------------------------

import Algebra.Montgomery.Impl 

withMontgomery : {ty : Ty} -> (prime : Prime) -> (MontgomeryAPI prime -> Tm ty) -> Tm ty
withMontgomery {ty} prime kont = final where

  open module MontP = Algebra.Montgomery.Impl prime

  exportBig : {l : ℕ} -> MontP.#limbs ≡ l -> Tm Big -> Tm (BigInt l)
  exportBig refl tm = tm

  importBig : {l : ℕ} -> MontP.#limbs ≡ l -> Tm (BigInt l) -> Tm Big 
  importBig refl tm = tm

  final : Tm ty
  final = runGen do

    -- redcFun : Tm (Big² ⇒ Big)
    redcFun <- gen (Log "montREDC" (Lam MontP.montgomeryREDC))

    -- toBigFun : Tm (Mont ⇒ Big)
    -- unsafeFromBigFun : Tm (Big  ⇒ Mont)

    toBigFun <- gen (Log "montToBig" (Lam (MontP.toBigInt' redcFun)))
    unsafeFromBigFun <- gen (Log "unsafeMontFromBig" (Lam (MontP.unsafeFromBigInt' redcFun)))

    -- negFun  : Tm (Mont ⇒ Mont)
    -- dblFun  : Tm (Mont ⇒ Mont)
    -- addFun  : Tm (Mont ⇒ Mont ⇒ Mont)
    -- subFun  : Tm (Mont ⇒ Mont ⇒ Mont)

    negFun <- gen (Log "montNeg" (Lam  MontP.neg   ))
    dblFun <- gen (Log "montDbl" (Lam  MontP.double))
    addFun <- gen (Log "montAdd" (Lam2 MontP.add   ))
    subFun <- gen (Log "montSub" (Lam2 MontP.sub   ))

    -- sqrFun  : Tm (Big² ⇒ Big) -> Tm (Mont ⇒ Mont)
    -- mulFun  : Tm (Big² ⇒ Big) -> Tm (Mont ⇒ Mont ⇒ Mont)

    sqrFun <- gen (Log "sqr" (Lam  (MontP.square' redcFun)))
    mulFun <- gen (Log "mul" (Lam2 (MontP.mul'    redcFun)))
    -- sqrFun <- gen (Log "montSqr" (Lam  MontP.square))
    -- mulFun <- gen (Log "montMul" (Lam2 MontP.mul   ))

    let api = record
          { #limbs = MontP.#limbs
          ; Big    = MontP.Big
          ; Big²   = MontP.Big²
          ; Mont   = MontP.Mont
          ; montFromℕ     = MontP.montFromℕ
          ; toBig         = App toBigFun
          ; unsafeFromBig = App unsafeFromBigFun
          ; importMont    = \eq tm -> App unsafeFromBigFun (importBig eq tm)
          ; exportMont    = \eq tm -> exportBig eq (App toBigFun tm)
          ; neg    = App  negFun
          ; dbl    = App  dblFun
          ; add    = App2 addFun
          ; sub    = App2 subFun
          ; sqr    = App  sqrFun
          ; mul    = App2 mulFun
          }

    return (kont api)

--------------------------------------------------------------------------------
