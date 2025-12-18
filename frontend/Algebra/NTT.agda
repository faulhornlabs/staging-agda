
-- Number Theoretical Transform

open import Algebra.API.Field

module Algebra.NTT ( theField : FieldAPI ) where

--------------------------------------------------------------------------------

open import Data.Empty
open import Data.Nat
open import Data.String

open import Function using ( _$_ )
open import Relation.Binary.PropositionalEquality using ( refl )

open import Meta.Object hiding ( Gen ; return ; _>>_ ; _>>=_ )

--------------------------------------------------------------------------------

open FieldAPI theField

--------------------------------------------------------------------------------

opaque
  Log2 : Set
  Log2 = ℕ

  fromLog2 : Log2 -> ℕ
  fromLog2 m = m

  toLog2 : ℕ -> Log2
  toLog2 m = m

  exp2 : Log2 -> ℕ
  exp2 zero    = 1
  exp2 (suc k) = 2 * exp2 k
  
--------------------------------------------------------------------------------

record FFTField : Set where
  constructor MkFFTField
  field
    maxSgGen     : Val F
    maxSgLogSize : Log2

-- A cyclic multiplicative) subgroup 
record Subgroup : Set where
  constructor MkSubgroup
  field 
    generator : Val F         -- the cyclic generator 
    logSize   : Log2          -- size of the subgroup

subgroupOrder : Subgroup -> ℕ
subgroupOrder sg = exp2 (Subgroup.logSize sg)

--------------------------------------------------------------------------------

open U64Lib
open IOLib

private

  variable
    ty  : Ty
    s t : Ty
    
  _>>=_ : Tm (IO s) -> (Tm s -> Tm (IO t)) -> Tm (IO t)    
  _>>=_ u h = bind u (Lam \x -> h x)

  _>>_ : Tm (IO s) -> Tm (IO t) -> Tm (IO t)
  _>>_ u v = then u v

--------------------------------------------------------------------------------

exp₂′ : Tm (U64 ⇒ U64)
exp₂′ = Fix (\rec -> Lam \n -> ifte (isZeroU64 n) oneU64 (twiceU64 (App rec (decU64 n))))

exp₂ : Tm U64 -> Tm U64
exp₂ = App exp₂′

log₂′ : Tm (U64 ⇒ U64)
log₂′ = Fix (\rec -> Lam \n -> ifte (isOneU64 n) zeroU64 (incU64 (App rec (snd (shiftRightU64₁ n)))))

log₂ : Tm U64 -> Tm U64
log₂ = App log₂′

bitReverse : Tm U64 -> Tm U64 -> Tm U64
bitReverse nbits input = App2 rev nbits zeroU64 where
  rev : Tm (U64 ⇒ U64 ⇒ U64)
  rev = Fix \rec -> Lam2 \k acc -> 
               Let (decU64 k) \k′ ->
                 ifte (isZeroU64 k)
                   acc
                   (Let
                     (bitOrU64
                       acc
                       (shiftLeftByU64 (bitAndU64 oneU64 (shiftRightByU64 input k′)) (subU64 nbits k))
                     )
                     \acc′ -> App2 rec k′ acc′
                   )

bitReverseDebugIO : Tm U64 -> Tm U64 -> Tm (IO U64)
bitReverseDebugIO nbits input = App2 rev nbits zeroU64 where
  rev : Tm (U64 ⇒ U64 ⇒ IO U64)
  rev = Fix \rec -> Lam2 \k acc -> 
               Let (decU64 k) \k′ ->
                 ifte (isZeroU64 k)
                   (pure acc)
                   (Let
                     (shiftLeftByU64 (bitAndU64 oneU64 (shiftRightByU64 input k′)) (subU64 nbits k))
                     \this -> Let (bitOrU64 acc this) \acc′ -> do
                       print "k"    k
                       print "this" this
                       print "acc"  acc
                       print "acc'" acc′
                       App2 rec k′ acc′
                   )

staticBitReverse : Log2 -> Tm U64 -> Tm U64
staticBitReverse nbits = bitReverse (kstU64′ (fromLog2 nbits))

private variable
  vty : VTy
  
bitReversalPerm : Tm (Ptr vty) -> Tm (IO (Ptr vty))
bitReversalPerm {vty = vty} inputArr = do
  N <- getArraySize inputArr
  Let (log₂ N) \n -> do
    -- print "n = log(N)" n
    outputArr <- allocArray vty N
    loop N \i -> do
      Let (bitReverse n i) \j -> do
        -- print "(i,j)" (mkPair i j)
        x <- read {eq = refl} inputArr i
        write {eq = refl} outputArr j x
    pure outputArr
  
--------------------------------------------------------------------------------

  

