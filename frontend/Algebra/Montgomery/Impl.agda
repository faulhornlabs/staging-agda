
-- prime fields in Montgomery representation

open import Data.Nat
open import Algebra.Prime

module Algebra.Montgomery.Impl (prime′ : Prime) where

--------------------------------------------------------------------------------

open import Data.Bool     using ( Bool )
open import Data.Nat      using ( ℕ ; _+_ ; _*_ ; _/_ ; _%_ ) renaming ( zero to nzero ; suc to nsuc )
open import Data.Nat.Show using ( show )
open import Data.String   using ( String ; _++_ )
open import Data.Fin      using ( Fin ; opposite ; _↑ˡ_ ; _↑ʳ_ ; inject₁ ) renaming ( zero to fzero ; suc to fsuc )
open import Data.Vec      using ( Vec ; [] ; _∷_ ; _∷ʳ_ ; allFin )
open import Data.List     using ( List ; [] ; _∷_ )
open import Data.Word64   using ( Word64 ; _<_ ; fromℕ ; toℕ ; _==_ )

open import Data.Empty
open import Data.Sum
open import Data.Product

open import Function.Base using ( case_of_ )
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.TrustMe

import Data.Nat.Properties

open import Meta.Object
open import Meta.Show
open import Algebra.BigInt as BigInt using ( BigInt ; BigInt' ; mkBigInt ; mkBigInt' ; bigproj )
open import Algebra.Limbs
open import Algebra.U128 using ( addU64toU64 ; addU64toU128 )
open import Algebra.Misc 

open BitLib
open U64Lib

--------------------------------------------------------------------------------

prime : ℕ
prime = Prime.primeℕ prime′

-- prime-nonZero : NonZero prime
-- prime-nonZero = Prime.isNonZero prime′

private 

  -- note: without the `private` restriction, this crashes Agda!
  instance
    PrimeNonZero : NonZero prime
    PrimeNonZero = Prime.isNonZero prime′

--------------------------------------------------------------------------------

private 

  Σlimbs :  Σ[ nlimbs ∈ ℕ ] (Val (BigInt nlimbs))
  Σlimbs = natToBigInt prime

#limbs : ℕ
#limbs = proj₁ Σlimbs

2×#limbs : ℕ
2×#limbs = #limbs + #limbs

private 

  primeBigIntVal : Val (BigInt #limbs)
  primeBigIntVal = proj₂ Σlimbs

  primeBigInt : Tm (BigInt #limbs)
  primeBigInt = Lit primeBigIntVal
  

tyName : String
tyName = Data.String._++_ "Mont" (Data.Nat.Show.show prime)

private 

  Big' : Ty
  Big' = BigInt' #limbs

Big : Ty
Big = BigInt #limbs

Big² : Ty
Big² = BigInt 2×#limbs

Mont : Ty
Mont = Named tyName Big  

private 

  unwrap1 : {ty : Ty} -> Tm Mont -> (Tm Big -> Tm ty) -> Tm ty
  unwrap1 tm f = Let (unwrap tm) f

  unwrap2 : {ty : Ty} -> Tm Mont -> Tm Mont -> (Tm Big -> Tm Big -> Tm ty) -> Tm ty
  unwrap2 tm1 tm2 g = Let (unwrap tm1) \x -> Let (unwrap tm2) \y -> g x y

isEqual : Tm Mont -> Tm Mont -> Tm Bit
isEqual x y = unwrap2 x y BigInt.isEqual

--------------------------------------------------------------------------------

private

{-
  -- we have to "prove" that it's nonzero...
  prime₊ : ℕ
  prime₊ = nsuc (pred prime)
-}

  private 

    R-full-ℕ : ℕ
    R-full-ℕ = twoTo64 ^ #limbs

    R1-ℕ : ℕ
    R1-ℕ = R-full-ℕ % prime

    R2-ℕ : ℕ
    R2-ℕ = (R1-ℕ * R1-ℕ) % prime

    R3-ℕ : ℕ
    R3-ℕ = (R2-ℕ * R1-ℕ) % prime

  R1' : Tm Big'
  R1' = Lit (bigInt'ValFromℕ R1-ℕ)

  R2' : Tm Big'
  R2' = Lit (bigInt'ValFromℕ R2-ℕ)

  R3' : Tm Big'
  R3' = Lit (bigInt'ValFromℕ R3-ℕ)

  R1 : Tm Big
  R1 = Lit (bigIntValFromℕ R1-ℕ)

  R2 : Tm Big
  R2 = Lit (bigIntValFromℕ R2-ℕ)

  R3 : Tm Big
  R3 = Lit (bigIntValFromℕ R3-ℕ)

--------------------------------------------------------------------------------

private 

  -- a number 0 < Q < B := 2^64 such that `Q * P = -1 mod 2^64`
  -- assuming P is odd, this can be computed as
  --
  -- Q = powMod (mod (-P) B) (div B 2 - 1) B
  --
  -- This is because EulerPhi[2^n] == 2^(n-1)

  montQ : Word64
  montQ = powWord64 expo -p where

    p : Word64
    p = fromℕ prime

    -p : Word64
    -p = negWord64 p

    expo : ℕ
    expo = pred (2 ^ (pred limbSize))     -- EulerPhi[2^n] == 2^(n-1)

  montQ-sanityTest : Word64
  montQ-sanityTest = fromℕ (toℕ montQ * prime)

  montQ-OK : Bool
  montQ-OK = eqWord64 montQ-sanityTest (negWord64 (fromℕ 1))

  montQTm : Tm U64
  montQTm = Lit (U64V montQ)


sanityCheckMontgomeryText : String
sanityCheckMontgomeryText
  =  "\nMontogemry prime = " ++ show       prime
  ++ "\nmontQ            = " ++ showWord64 montQ           
  ++ "\nmontQ-sanityTest = " ++ showWord64 montQ-sanityTest
  ++ "\nmontQ-OK         = " ++ showBool   montQ-OK        
  ++ "\nR1               = " ++ show       R1-ℕ    
  ++ "\nR2               = " ++ show       R2-ℕ    
  ++ "\nR3               = " ++ show       R3-ℕ    
  ++ "\n"

--------------------------------------------------------------------------------

private

  neg' : Tm Big -> Tm Big
  neg' input = runGen do
    big <- gen input
    let result = ifte (BigInt.isZero big)
          big
          (BigInt.subNC primeBigInt big)
    return result

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

neg : Tm Mont -> Tm Mont
neg mod = unwrap1 mod \big -> wrap (neg' big)

double : Tm Mont -> Tm Mont
double mod = unwrap1 mod \big -> wrap (add' big big)

add : Tm Mont -> Tm Mont -> Tm Mont
add mod1 mod2 = unwrap2 mod1 mod2 \big1 big2 -> wrap (add' big1 big2)

sub : Tm Mont -> Tm Mont -> Tm Mont
sub mod1 mod2 = unwrap2 mod1 mod2 \big1 big2 -> wrap (sub' big1 big2)

--------------------------------------------------------------------------------

private

  Fin₁ : ℕ -> Set
  Fin₁ n = Fin (suc n)

  finPlus₁ : {n m : ℕ} -> Fin₁ n -> Fin₁ m -> Fin₁ (n + m)
  finPlus₁ {n}      {m} fzero     j = subst Fin (Data.Nat.Properties.+-suc n m) (n ↑ʳ j)
  finPlus₁ {suc n₁} {m} (fsuc i₁) j = inject₁ (finPlus₁ i₁ j)

  finPlus : {n m : ℕ} -> Fin n -> Fin m -> Fin (n + m)
  finPlus {suc n₁} {suc m₁} i j = inject₁ (subst Fin eq i+j) where
    eq : suc (n₁ + m₁) ≡ n₁ + suc m₁ 
    eq = sym (Data.Nat.Properties.+-suc n₁ m₁)
    i+j : Fin (suc (n₁ + m₁))
    i+j = finPlus₁ i j

  splitFin : (n : ℕ) -> {k : ℕ} -> Fin (n + k) -> Fin n ⊎ Fin k
  splitFin n {k} = Data.Fin.splitAt n {k}
  
--------------------------------------------------------------------------------

private 

{-
  subPrimeIfNecessary : Tm Big -> Tm Big
  subPrimeIfNecessary input = Let input \y -> 
    ifte (Algebra.BigInt.isGE y primeBigInt)
      (Algebra.BigInt.subNC y primeBigInt)
      y
-}

  Vec₁ : (A : Set) -> ℕ -> Set
  Vec₁ A n₁ = Vec A (suc n₁)

  BigInt₁ : ℕ -> Ty
  BigInt₁ n = BigInt' (n + 1) -- (suc n)

  Big₁ : ℕ -> Ty
  Big₁ k = BigInt₁ (#limbs + k)

  TmBigInt₁ : ℕ -> Set
  TmBigInt₁ n = Tm (BigInt₁ n)

  TmBig₁ : ℕ -> Set
  TmBig₁ n = Tm (Big₁ n)

  VecTm : ℕ -> Set
  VecTm k = Vec (Tm U64) k

  VecLimbs₁ : ℕ -> Set
  VecLimbs₁ k = Vec (Tm U64) (#limbs + k + 1)

  Big₁-0 : Tm (Big₁ zero) -> Tm (BigInt₁ #limbs)
  Big₁-0 = subst TmBigInt₁ (Data.Nat.Properties.+-identityʳ #limbs)

  primeBigInt₁ : Tm (BigInt (#limbs + 1))
  primeBigInt₁ = BigInt.extendBigInt 1 primeBigInt

  subPrimeIfNecessary₁ : Tm (BigInt (#limbs + 1)) -> Tm (BigInt (#limbs + 1))
  subPrimeIfNecessary₁ input = Let input \x -> 
    ifte (BigInt.isGE x primeBigInt₁)
      (BigInt.subNC x primeBigInt₁)
      x

  +-lemma₁ : (k : ℕ) -> #limbs + suc k ≡ suc (#limbs + k)
  +-lemma₁ k = Relation.Binary.PropositionalEquality.TrustMe.trustMe

  +-lemma₂ : (k : ℕ) -> #limbs + k + 1 ≡ suc (#limbs + k)
  +-lemma₂ k = Relation.Binary.PropositionalEquality.TrustMe.trustMe

  +-lemma₃ : (k : ℕ) -> #limbs + suc k + 1 ≡ suc (#limbs + k + 1)
  +-lemma₃ k = Relation.Binary.PropositionalEquality.TrustMe.trustMe

  +-lemma₄ : (k : ℕ) -> #limbs + suc (k + 1) ≡ #limbs + suc k + 1
  +-lemma₄ k = Relation.Binary.PropositionalEquality.TrustMe.trustMe

  myHead : {A : Set} -> {k : ℕ} -> Vec A (#limbs + k + 1) -> A
  myHead {A} {k} vec = Data.Vec.head (subst (Vec A) (+-lemma₂ k) vec)
  
  myTail : {A : Set} -> {k : ℕ} -> Vec A (#limbs + suc k + 1) -> Vec A (#limbs + k + 1)
  myTail {A} {k} vec = Data.Vec.tail (subst (Vec A) (+-lemma₃ k) vec)

  -- Montgomery REDC is a dependent sequence of functions
  --   n+k+1 -> n+k -> n+k-1 -> ... -> n+1
  -- each of which is a mapAccum
  myDepSeqM
    :  {k : ℕ} 
    -> ( (i : ℕ) -> Tm (Big₁ (suc i)) -> Gen (Tm (Big₁ i)) )
    -> Tm (Big₁ k) -> Gen (Tm (Big₁ zero))
  myDepSeqM {k} fun = go k where
    go : (k : ℕ) -> Tm (Big₁ k) -> Gen (Tm (Big₁ zero))
    go zero     v = return v
    go (suc k₁) v = do
      v′ <- gen v
      v″ <- fun k₁ v′
      go k₁ v″

--------------------------------------------------------------------------------

private

  -- body of the inner loop of Montgomery REDC algo
  redcInnerWorker : Tm U64 -> (k : ℕ) -> Tm U64 -> Fin (#limbs + (k + 1)) × Tm U64 -> Gen (Tm U64 × Tm U64) 
  redcInnerWorker mlo k carry (i , tm) = do
    let ei = splitFin #limbs i
    case ei of λ where
      (inj₁ j) -> do
        -- note: `a + b + x*y` never overflows, because:
        -- let m = (2^n - 1) in m*m + 2*m = 2^(2n) - 1
        -- BUT, we have to compute in U128!
        tmp128 <- gen (mulAddU64 carry mlo (bigproj j primeBigInt))      --          m ⋅ N[j] + c
        (xhi , xlo) <- pair⇑ (addU64toU128 tm tmp128)                    -- T[i+j] + m ⋅ N[j] + c
        return (xhi , xlo)                                               -- hi = carry, low = result
      (inj₂ j) -> do
        (xhi , xlo) <- pair⇑ (addU64toU64 tm carry)
        return (xhi , xlo)

  -- body of the outer loop of Montgomery REDC algo
  redcOuterWorker : (k : ℕ) -> Tm (Big₁ (suc k)) -> Gen (Tm (Big₁ k))
  redcOuterWorker k oldT0 = do
    oldT <- gen oldT0
    vec <- BigInt.deconstruct' oldT
    mlo <- gen (mulTruncU64 (myHead vec) montQTm)
    let idxs = allFin (#limbs + (suc k + 1))
    let idxs′ : Vec (Fin (#limbs + (suc k + 1))) (#limbs + suc k + 1)
        idxs′ = subst (Vec _) (+-lemma₄ k) idxs
    let vecidx = Data.Vec.zip idxs′ vec
    (_ , vec') <- vecForAccumM zeroU64 vecidx (redcInnerWorker mlo (suc k))
    let newT = mkBigInt' (myTail vec') -- (Data.Vec.tail vec')
    return newT

  montgomeryREDC' : Tm (BigInt' (#limbs + #limbs)) -> Tm (BigInt' #limbs)
  montgomeryREDC' input = runGen do
    input′  <- gen (BigInt.extendBigInt' 1 input)
    output  <- myDepSeqM redcOuterWorker input′
    output′ <- gen (Big₁-0 output)
    output″ <- gen (subPrimeIfNecessary₁ (wrap output′))
    return ((BigInt.takeBigInt' #limbs (unwrap output″)))

montgomeryREDC : Tm (BigInt (#limbs + #limbs)) -> Tm (BigInt #limbs)
montgomeryREDC input = wrap (montgomeryREDC' (unwrap input))
-- montgomeryREDC input = Let input \inp -> wrap (montgomeryREDC' (unwrap inp))

{-

from <https://en.wikipedia.org/wiki/Montgomery_modular_multiplication>:

function MultiPrecisionREDC is
    Input: Integer N with gcd(B, N) = 1, stored as an array of p words,
           Integer R = Br,     --thus, r = logB R
           Integer N′ in [0, B − 1] such that NN′ ≡ −1 (mod B),
           Integer T in the range 0 ≤ T < RN, stored as an array of r + p words.

    Output: Integer S in [0, N − 1] such that TR−1 ≡ S (mod N), stored as an array of p words.

    Set T[r + p] = 0  (extra carry word)
    for 0 ≤ i < r do
        --loop1- Make T divisible by Bi+1

        c ← 0
        m ← T[i] ⋅ N′ mod B
        for 0 ≤ j < p do
            --loop2- Add the m ⋅ N[j] and the carry from earlier, and find the new carry

            x ← T[i + j] + m ⋅ N[j] + c
            T[i + j] ← x mod B
            c ← ⌊x / B⌋
        end for
        for p ≤ j ≤ r + p − i do
            --loop3- Continue carrying

            x ← T[i + j] + c
            T[i + j] ← x mod B
            c ← ⌊x / B⌋
        end for
    end for

    for 0 ≤ i ≤ p do
        S[i] ← T[i + r]
    end for

    if S ≥ N then
        return S − N
    else
        return S
    end if
end function

-}

--------------------------------------------------------------------------------

-- \A B -> R^-1*(A*B) mod P 
montMulBig' : Tm (Big² ⇒ Big) -> Tm Big -> Tm Big -> Tm Big
montMulBig' redc big1 big2 = runGen do
  prod <- gen (BigInt.mulExt big1 big2)
  return (App redc prod)

mul' : Tm (Big² ⇒ Big) -> Tm Mont -> Tm Mont -> Tm Mont
mul' redc mont1 mont2 = unwrap2 mont1 mont2 \big1 big2 -> wrap (montMulBig' redc big1 big2)
-- mul' redc mont1 mont2 = unwrap2 mont1 mont2 \big1 big2 -> runGen do
--   prod <- gen (BigInt.mulExt big1 big2)
--   return (wrap (App redc prod))

square' : Tm (Big² ⇒ Big) -> Tm Mont -> Tm Mont
square' redc mont = unwrap1 mont \big -> runGen do
  prod <- gen (BigInt.squareExt big)
  return (wrap (App redc prod))

-- \A B -> R^-1*(A*B) mod P 
montMulBig : Tm Big -> Tm Big -> Tm Big
montMulBig  big1 big2 = runGen do
  prod <- gen (BigInt.mulExt big1 big2)
  return (montgomeryREDC prod)

mul : Tm Mont -> Tm Mont -> Tm Mont
mul mont1 mont2 = unwrap2 mont1 mont2 \big1 big2 -> wrap (montMulBig big1 big2)
-- mul mont1 mont2 = unwrap2 mont1 mont2 \big1 big2 -> runGen do
--   prod <- gen (BigInt.mulExt big1 big2)
--   return (wrap (montgomeryREDC prod))

square : Tm Mont -> Tm Mont
square mont = unwrap1 mont \big -> runGen do
  prod <- gen (BigInt.squareExt big)
  return (wrap (montgomeryREDC prod))

-------------------------------------------------------------------------------- 

montValFromℕ : ℕ -> Val Mont
montValFromℕ k = WrapV (bigIntValFromℕ montk) where
  montk : ℕ
  montk = ((k * R-full-ℕ) % prime)

montFromℕ : ℕ -> Tm Mont
montFromℕ k = Lit (montValFromℕ k)

unsafeFromBigInt' : Tm (Big² ⇒ Big) -> Tm Big -> Tm Mont
unsafeFromBigInt' redc input = mul' redc (wrap input) (wrap R2)

toBigInt' : Tm (Big² ⇒ Big) -> Tm Mont -> Tm Big
toBigInt' redc input = App redc (BigInt.extendBigInt #limbs (unwrap input))

-- we assume that the input is in the range [0 , prime-1]
unsafeFromBigInt : Tm Big -> Tm Mont
unsafeFromBigInt input = mul (wrap input) (wrap R2)

toBigInt : Tm Mont -> Tm Big
toBigInt input = montgomeryREDC (BigInt.extendBigInt #limbs (unwrap input))

--------------------------------------------------------------------------------

montZero montOne montTwo : Tm Mont
montZero = montFromℕ 0
montOne  = montFromℕ 1
montTwo  = montFromℕ 2

open import Algebra.Misc using ( Half ; Even ; Odd ; halve )

{-# TERMINATING #-}
staticPow' : (Tm Mont -> Tm Mont) -> (Tm Mont -> Tm Mont -> Tm Mont) -> Tm Mont -> ℕ -> Tm Mont
staticPow' sqr mul base expo = go expo base where
  go : ℕ -> Tm Mont -> Tm Mont
  go 0 _ = montOne
  go 1 x = x
  go n x with halve n 
  go _ x | Even k = Let (go k x) \s ->      sqr s
  go _ x | Odd  k = Let (go k x) \s -> mul (sqr s) x

staticPow : Tm Mont -> ℕ -> Tm Mont
staticPow base expo = staticPow' square mul base expo

--------------------------------------------------------------------------------

open import Algebra.API.Word.BigInt

open import Algebra.Euclid (bigIntAsWordAPI #limbs) using ( modularInv′ ; modularDiv′ )

--
-- Remark: as we use Montgomery multiplicatation *** here (not normal modulo P multiplication *),
-- that adds an extra R^-1 factor:
--
--     x *** y  :=  R^-1 * (x * y)
--    Rx *** Ry  =     R * (x * y)
--
-- which we need to compensate for:
--
--     R*(1/x) = R^2 * (1/Rx) = R^3 *** (1/Rx)
--
-- hence the R^3 correction factor.
--
-- Similarly in division we need R^2:
--
--     R*(x/y) = R*(Rx/Ry) = R^2 *** (Rx/Ry)
--

inv : Tm Mont -> Tm Mont
inv x = unwrap1 x \big -> wrap (montMulBig R3 (modularInv′ prime′ big))

div : Tm Mont -> Tm Mont -> Tm Mont
div x y = unwrap2 x y \big1 big2 -> wrap (montMulBig R2 (modularDiv′ prime′ big1 big2))

--------------------------------------------------------------------------------
