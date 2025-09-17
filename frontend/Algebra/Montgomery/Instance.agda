
{-

As the unrolled functions starts to get big, we don't want to inline them all the time.
Instead, we want to make them functions using Let and just call those at the use sites.

This module helps by giving you an API to conveniently do just that.

-}

module Algebra.Montgomery.Instance where

--------------------------------------------------------------------------------

open import Data.Nat
open import Data.String using ( String )
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
    tyName : String
    montFromℕ     : ℕ -> Tm Mont 
    unsafeFromBig : Tm Big  -> Tm Mont
    toBig         : Tm Mont -> Tm Big 
    importMont    : {l : ℕ} -> #limbs ≡ l -> Tm (BigInt l) -> Tm Mont
    exportMont    : {l : ℕ} -> #limbs ≡ l -> Tm Mont -> Tm (BigInt l)
    isEqual : Tm Mont -> Tm Mont -> Tm Bit
    neg    : Tm Mont -> Tm Mont
    dbl    : Tm Mont -> Tm Mont
    add    : Tm Mont -> Tm Mont -> Tm Mont
    sub    : Tm Mont -> Tm Mont -> Tm Mont
    sqr    : Tm Mont -> Tm Mont
    mul    : Tm Mont -> Tm Mont -> Tm Mont
    inv    : Tm Mont -> Tm Mont
    div    : Tm Mont -> Tm Mont -> Tm Mont
--    staticPow : Tm Mont -> ℕ -> Tm Mont

--------------------------------------------------------------------------------

open import Algebra.API.Field

montgomeryApiToFieldAPI : {prime : Prime} -> MontgomeryAPI prime -> FieldAPI
montgomeryApiToFieldAPI {prime} mont = api where

  api = record
    { F      = MontgomeryAPI.Mont       mont
    ; fromℕ  = MontgomeryAPI.montFromℕ mont
    -- metadata
    ; name   = MontgomeryAPI.tyName mont
    ; size   = Prime.primeℕ prime
--    ; mulGen : Tm F
    -- queries
    ; isEqual  = MontgomeryAPI.isEqual mont
--    ; isEqualℕ : ℕ    -> Tm F -> Tm Bit
    -- arithmetic
    ; neg   = MontgomeryAPI.neg mont
    ; add   = MontgomeryAPI.add mont
    ; sub   = MontgomeryAPI.sub mont
    ; sqr   = MontgomeryAPI.sqr mont
    ; mul   = MontgomeryAPI.mul mont
    ; inv   = MontgomeryAPI.inv mont
    ; div   = MontgomeryAPI.div mont
--    ; divBySmallConst : Tm F -> ℕ -> Tm F
    -- exponentiation
--    ; staticPow = MontgomeryAPI.staticPow mont
    } 

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

    isEqualFun <- gen (Log "montIsEqual" (Lam2 MontP.isEqual))
    
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

    sqrFun <- gen (Log "montSqr" (Lam  (MontP.square' redcFun)))
    mulFun <- gen (Log "montMul" (Lam2 (MontP.mul'    redcFun)))

    invFun <- gen (Log "montInv" (Lam  MontP.inv))
    divFun <- gen (Log "montDiv" (Lam2 MontP.div))

    -- cannot really "gen" this???
    -- staticPowFun <- gen ...
    
    let api = record
          { #limbs = MontP.#limbs
          ; Big    = MontP.Big
          ; Big²   = MontP.Big²
          ; Mont   = MontP.Mont
          ; tyName = MontP.tyName
          ; montFromℕ     = MontP.montFromℕ
          ; toBig         = App toBigFun
          ; unsafeFromBig = App unsafeFromBigFun
          ; importMont    = \eq tm -> App unsafeFromBigFun (importBig eq tm)
          ; exportMont    = \eq tm -> exportBig eq (App toBigFun tm)
          ; isEqual = App2 isEqualFun
          ; neg    = App  negFun
          ; dbl    = App  dblFun
          ; add    = App2 addFun
          ; sub    = App2 subFun
          ; sqr    = App  sqrFun
          ; mul    = App2 mulFun
          ; inv    = App  invFun
          ; div    = App2 divFun
--          ; staticPow = \base expo -> App (staticPowFun expo) base 
          }

    return (kont api)

--------------------------------------------------------------------------------

withMontgomeryAsField : {ty : Ty} -> (prime : Prime) -> (FieldAPI -> Tm ty) -> Tm ty
withMontgomeryAsField prime kont = withMontgomery prime \montAPI -> kont (montgomeryApiToFieldAPI montAPI)

--------------------------------------------------------------------------------
  
