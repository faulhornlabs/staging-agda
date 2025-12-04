
-- modulo P arithmetic
--

open import Data.Nat
open import Algebra.Prime

module Algebra.Modular (prime′ : Prime) where

--------------------------------------------------------------------------------

open import Data.Bool     using ( Bool )
open import Data.Nat      using ( ℕ ; _+_ ; _*_ ; _/_ ; _%_ ) renaming ( zero to nzero ; suc to nsuc )
open import Data.Nat.Show using ( show ) 
open import Data.String   using ( String ; _++_ )
open import Data.Fin      using ( Fin ; opposite ) renaming ( zero to fzero ; suc to fsuc )
open import Data.Vec      using ( Vec ; [] ; _∷_ ; _∷ʳ_ ; allFin )
open import Data.List     using ( List ; [] ; _∷_ ; _++_ )
open import Data.Word64   using ( Word64 ; _<_ )
open import Data.Product
open import Data.Empty

open import Relation.Binary.PropositionalEquality

open import Meta.Object

open import Algebra.BigInt as BigInt using ( BigInt ; BigInt' ; BigIntVTy ; BigIntVTy' )
open import Algebra.Limbs
open import Algebra.Misc

--------------------------------------------------------------------------------

prime : ℕ
prime = Prime.primeℕ prime′

private 

  -- note: without the `private` restriction, this crashes Agda!
  instance
    PrimeNonZero : NonZero prime
    PrimeNonZero = Prime.isNonZero prime′

--------------------------------------------------------------------------------

open BitLib
open U64Lib

private

  Σlimbs :  Σ[ nlimbs ∈ ℕ ] (Literal (BigInt nlimbs))
  Σlimbs = natToBigIntLit prime

#limbs : ℕ
#limbs = proj₁ Σlimbs

private

  primeBigIntLit : Literal (BigInt #limbs)
  primeBigIntLit = proj₂ Σlimbs

  primeBigInt : Tm (BigInt #limbs)
  primeBigInt = Lit primeBigIntLit

tyName : String
tyName = Data.String._++_ "Mod" (Data.Nat.Show.show prime)

Big : Ty
Big = BigInt #limbs

Mod : Ty
Mod = Named tyName Big   -- (BigInt #limbs) 

toBig : Tm Mod -> Tm Big
toBig = unwrap

fromBig : Tm Big -> Tm Mod
fromBig = wrap

fromℕ : ℕ -> Tm Mod
fromℕ k = fromBig (bigIntFromℕ (k % prime))

--------------------------------------------------------------------------------

private 

  muAsℕ : ℕ
  muAsℕ = numer / prime where

{-
    -- we have to "prove" that it's nonzero...
    prime₊ : ℕ
    prime₊ = nsuc (pred prime)
-}

    square : ℕ -> ℕ
    square x = x * x
  
    numer : ℕ
    numer = square (twoTo64 ^ #limbs)

  Σmu : Σ[ nlimbs ∈ ℕ ] (Vec Word64 nlimbs)
  Σmu = natToLimbs muAsℕ

  mu-nlimbs : ℕ
  mu-nlimbs = proj₁ Σmu

  muVal : Vec Word64 mu-nlimbs
  muVal = proj₂ Σmu

--------------------------------------------------------------------------------

private 

  unwrap1 : {ty : Ty} -> Tm Mod -> (Tm Big -> Tm ty) -> Tm ty
  unwrap1 tm f = Let (unwrap tm) f

  unwrap2 : {ty : Ty} -> Tm Mod -> Tm Mod -> (Tm Big -> Tm Big -> Tm ty) -> Tm ty
  unwrap2 tm1 tm2 g = Let (unwrap tm1) \x -> Let (unwrap tm2) \y -> g x y

  with1 : Tm Mod -> (Tm Big -> Tm Big) -> Tm Mod
  with1 tm f = wrap (unwrap1 tm f)

  with2 : Tm Mod -> Tm Mod -> (Tm Big -> Tm Big -> Tm Big) -> Tm Mod 
  with2 tm1 tm2 f = wrap (unwrap2 tm1 tm2 f)

--------------------------------------------------------------------------------

add' : Tm Big -> Tm Big -> Tm Big
add' big1 big2 = runGen do
  carry , big3 <- pair⇑ (BigInt.add big1 big2)
  let overflow = or carry (BigInt.isGE big3 primeBigInt)
  let result = ifte overflow
        (BigInt.subNC big3 primeBigInt)
        big3
  return result

sub' : Tm Big -> Tm  Big -> Tm Big
sub' big1 big2 = runGen do
  carry , big3 <- pair⇑ (BigInt.sub big1 big2)
  let result = ifte carry
        (BigInt.addNC big3 primeBigInt)
        big3  
  return result

add : Tm Mod -> Tm Mod -> Tm Mod
add mod1 mod2 = unwrap2 mod1 mod2 \big1 big2 -> wrap (add' big1 big2)

sub : Tm Mod -> Tm Mod -> Tm Mod
sub mod1 mod2 = unwrap2 mod1 mod2 \big1 big2 -> wrap (sub' big1 big2)

--------------------------------------------------------------------------------

private

  reduceBySubtraction : Tm Big -> Tm Mod
  reduceBySubtraction input = wrap (App (Fix (Lam worker)) input) where
    worker : Tm (Big ⇒ Big) -> Tm (Big ⇒ Big)
    worker rec = Lam \y -> ifte (BigInt.isLT y primeBigInt)
      y
      (App rec (snd (BigInt.sub y primeBigInt)))

  record PlusMinus1 (n : ℕ) : Set where
    field
      n-1    : ℕ
      n+1    : ℕ
      eq₋    : suc n-1 ≡ n
      eq₊    : n+1 ≡ suc n
      plus₋₊ : n + n ≡ n-1 + n+1 
      plus₊₋ : n + n ≡ n+1 + n-1 

  import Data.Nat.Properties
  import Relation.Binary.PropositionalEquality.TrustMe

  thm-±1' : (n₁ : ℕ) -> PlusMinus1 (suc n₁)
  thm-±1' n₁ = record
    { n-1  = n₁
    ; n+1  = suc (suc n₁)
    ; eq₋  = refl
    ; eq₊  = refl
    ; plus₋₊ = Relation.Binary.PropositionalEquality.TrustMe.trustMe   -- TODO
    ; plus₊₋ = Relation.Binary.PropositionalEquality.TrustMe.trustMe
    }

  thm-±1 : (n : ℕ) -> (Data.Nat._>_ n 0) -> PlusMinus1 n
  thm-±1 n (s≤s .{0} {n₁} prf) = thm-±1' n₁

{-
-- it could be more generally from `BigInt (k + #limbs)` where `k <= #nlimbs`
barretReduction' : (#limbs > 0) -> Tm (BigInt (#limbs + #limbs)) -> Tm (BigInt #limbs)
barretReduction' pos-prf input = ? where

  #limbs-1 : ℕ
  #limbs-1 = pred #limbs
  
  q1 : Tm (BigInt (1 + #limbs))
  q1 = BigInt.dropBigInt #limbs-1 input
-}


  
{-
-- | See: Handbook of Applied Cryptography, section 14.3.3
barrettReduction :: Modulus -> Limbs -> Limbs
barrettReduction modulus input0 
  | length input0 > 2*k  = error "barrettReduction: input is too big"
  | otherwise            = safeReduceLimbsTo k $ reduceBySubtraction (modulus++[0]) r
  where

    k     = length modulus
    input = take (2*k) $ input0 ++ repeat 0

    q1 = drop (k-1) input
    q2 = mulBigInt q1 mu                       -- note: we could specialize to multiplication by mu as it's a constant!
    q3 = drop (k+1) q2

    r1 = take (k+1) input 
    r2 = take (k+1) (mulBigInt q3 modulus)     -- here too

    -- Note: if r1<r2, that is, r<0, then we should have `r + 64^(k+1)` instead
    -- but subBigInt automatically does this, we can simply ignore the carry
    (carry,r) = subBigInt zeroBit r1 r2

    -- | This is normally precalculated
    -- NOTE: does not always fit into (k+1) limbs ?!
    mu = integerToLimbsAsRequired        
       $ (2^(twiceLimbSize*k)) `div` (integerFromLimbs modulus)
-}

--------------------------------------------------------------------------------

open import Algebra.API.Word.BigInt

open import Algebra.Euclid (bigIntAsWordAPI #limbs) using ( modularInv′ ; modularDiv′ )

inv : Tm Mod -> Tm Mod
inv x = with1 x (modularInv′ prime′)

div : Tm Mod -> Tm Mod -> Tm Mod
div x y = with2 x y (modularDiv′ prime′)

--------------------------------------------------------------------------------
