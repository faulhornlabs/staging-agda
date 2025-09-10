
-- extended binary Euclidean algorithm

open import Algebra.API.Word

module Algebra.Euclid (api : WordAPI) where

--------------------------------------------------------------------------------

open import Data.Nat
open import Data.Product

open import Meta.Object

open import Algebra.Prime

--------------------------------------------------------------------------------

open BitLib
open WordAPI api

modularBinaryEuclid : Prime -> Tm Word -> Tm Word -> Tm Word -> Tm Word -> Tm Word 
modularBinaryEuclid prime′ x0 y0 u0 v0 = App worker (mkQuad u0 x0 v0 y0) where 

  prime : Tm Word
  prime = fromℕ (Prime.primeℕ prime′)

  halfPrime : Tm Word
  halfPrime = snd (shiftRightBy1 prime)

  halfPrime₊₁ : Tm Word
  halfPrime₊₁ = add halfPrime (fromℕ 1)

  step : Tm (Pair Word Word ⇒ Pair Word Word)
  step = Fix (Lam recU) where
    recU : Tm (Pair Word Word ⇒ Pair Word Word) -> Tm (Pair Word Word ⇒ Pair Word Word)
    recU rec = Lam \u,x -> runGen do
      (u , x  ) <- pair⇑ u,x
      (c , u′ ) <- pair⇑ (shiftRightBy1 u)
      let kont = runGen do
            (d , x′ ) <- pair⇑ (shiftRightBy1 x)
            x″ <- gen (ifte d (add x′ halfPrime₊₁) x′)
            return (mkPair u′ x″)
      return (ifte c u,x (App rec kont))

  Quad : Ty
  Quad = Pair (Pair Word Word) (Pair Word Word)

  mkQuad : Tm Word -> Tm Word -> Tm Word -> Tm Word -> Tm Quad
  mkQuad u x v y = mkPair (mkPair u x) (mkPair v y)

  subModP : Tm Word -> Tm Word -> Tm Word
  subModP x y = runGen do
    (c , z) <- pair⇑ (subCarry x y)
    let z′ = ifte c (add z prime) z
    return z′
  
  worker : Tm (Quad ⇒ Word)
  worker = Fix (Lam recQ) where
    recQ : Tm (Quad ⇒ Word) -> Tm (Quad ⇒ Word)
    recQ rec = Lam \u,x,v,y -> runGen do
      (u,x , v,y) <- pair⇑ u,x,v,y
      u , x <- pair⇑ u,x
      v , y <- pair⇑ v,y
      -- debug "u" u
      -- debug "x" x
      -- debug "v" v
      -- debug "y" y
      let kont = runGen do
            u′,x′ <- gen (App step u,x)
            v′,y′ <- gen (App step v,y)
            u′ , x′ <- pair⇑ u′,x′
            v′ , y′ <- pair⇑ v′,y′
            return (ifte (isLT u′ v′)
              (mkQuad      u′              x′     (sub v′ u′) (subModP y′ x′))
              (mkQuad (sub u′ v′) (subModP x′ y′)      v′              y′    ))
            
      let out = ifte (isEqualℕ 1 u) x
                  (ifte (isEqualℕ 1 v) y
                    (App rec kont))
      return out
      
--------------------------------------------------------------------------------

modularDiv′ : Prime -> Tm Word -> Tm Word -> Tm Word
modularDiv′ prime a b = modularBinaryEuclid prime x y u v where
  x = a
  y = fromℕ 0
  u = b
  v = fromℕ (Prime.primeℕ prime)

modularInv′ : Prime -> Tm Word -> Tm Word
modularInv′ prime what = modularDiv′ prime (fromℕ 1) what

--------------------------------------------------------------------------------

{-

void bn128_Fp_std_euclid( uint64_t *x1, uint64_t *x2, uint64_t *u, uint64_t *v, uint64_t *tgt ) {

  while( ( (!bigint256_is_one(u)) && (!bigint256_is_one(v)) ) ) {

    // note: x1 < p
    // if x1 is odd, it can't be p-1, hence, it's at most p-2
    // then we divide by two: (p-2)/2 = (p-3)/2
    // (p-3)/2 + (p+1)/2 = (2p-2)/2 = (p-1)
    // so the addition x1 + (p+1)/2 = (x1+p)/2 will never overflow

    while (!(u[0] & 1)) {
      bigint256_shift_right_by_1(u,u);
      uint8_t odd = bigint256_shift_right_by_1(x1,x1);
      if (odd) { bigint256_add_inplace(x1, bn128_Fp_std_half_p_plus_1); }
    }

    while (!(v[0] & 1)) {
      bigint256_shift_right_by_1(v,v);
      uint8_t odd = bigint256_shift_right_by_1(x2,x2);
      if (odd) { bigint256_add_inplace(x2, bn128_Fp_std_half_p_plus_1); }
    }

    uint64_t w[4];
    uint8_t b = bigint256_sub(u,v,w);      // w = u - v 
    if (b) {
      // u-v < 0, that is, u < v
      bigint256_neg(w,v);                  // v  := v  - u
      bn128_Fp_std_sub_inplace(x2,x1);     // x2 := x2 - x1
    }
    else {
      // u-v >= 0, that is, u >= v
      bigint256_copy(w,u);                 // u  := u  - v
      bn128_Fp_std_sub_inplace(x1,x2);     // x1 := x1 - x2
    }
  
  }

  if (bigint256_is_one(u)) { 
    bigint256_copy( x1, tgt ); 
  } 
  else { 
    bigint256_copy( x2, tgt ); 
  }
}

-}

{-

-- | Extended binary Euclidean algorithm
euclid :: Integer -> Integer -> Integer -> Integer -> Integer -> Integer 
euclid !p !x1 !x2 !u !v = go x1 x2 u v where

  halfp1 = shiftR (p+1) 1

  modp :: Integer -> Integer
  modp n = mod n p

  -- Inverse using the binary Euclidean algorithm 
  euclid :: Integer -> Integer
  euclid a 
    | a == 0     = 0
    | otherwise  = go 1 0 a p
  
  go :: Integer -> Integer -> Integer -> Integer -> Integer
  go !x1 !x2 !u !v 
    | u==1       = x1
    | v==1       = x2
    | otherwise  = stepU x1 x2 u v

  stepU :: Integer -> Integer -> Integer -> Integer -> Integer
  stepU !x1 !x2 !u !v = if even u 
    then let u'  = shiftR u 1
             x1' = if even x1 then shiftR x1 1 else shiftR x1 1 + halfp1
         in  stepU x1' x2 u' v
    else     stepV x1  x2 u  v

  stepV :: Integer -> Integer -> Integer -> Integer -> Integer
  stepV !x1 !x2 !u !v = if even v
    then let v'  = shiftR v 1
             x2' = if even x2 then shiftR x2 1 else shiftR x2 1 + halfp1
         in  stepV x1 x2' u v' 
    else     final x1 x2  u v

  final :: Integer -> Integer -> Integer -> Integer -> Integer
  final !x1 !x2 !u !v = if u>=v

    then let u'  = u-v
             x1' = if x1 >= x2 then modp (x1-x2) else modp (x1+p-x2)               
         in  go x1' x2  u' v 

    else let v'  = v-u
             x2' = if x2 >= x1 then modp (x2-x1) else modp (x2+p-x1)
         in  go x1  x2' u  v'

-}
