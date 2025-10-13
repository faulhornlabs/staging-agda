
module Algebra.BigInt where

--------------------------------------------------------------------------------

open import Data.Bool     using ( Bool )
open import Data.Nat      using ( ℕ ; _+_ ) renaming ( zero to nzero ; suc to nsuc )
open import Data.Nat.Show using ( show )
open import Data.String   using ( String ; _++_ )
open import Data.Fin      using ( Fin ; opposite ) renaming ( zero to fzero ; suc to fsuc )
open import Data.Vec      using ( Vec ; [] ; _∷_ ; _∷ʳ_ ; allFin )
open import Data.List     using ( List ; [] ; _∷_ ; _++_ )
open import Data.Word64   using ( fromℕ )
open import Data.Product
open import Data.Maybe    using ( Maybe ; just ; nothing )

open import Relation.Binary.PropositionalEquality
-- open import Data.Vec.Properties using ( lookup-replicate )

open import Data.Nat.Properties using ( m≤m+n ; m≤n+m )
open import Data.Fin.Properties using ( _≟_ )

open import Meta.Object
open import Algebra.U128

open BitLib
open U64Lib

--------------------------------------------------------------------------------

private variable
  nlimbs : ℕ
  n m : ℕ
  
--------------------------------------------------------------------------------

BigInt' : ℕ -> Ty
BigInt' nlimbs = Struct (Data.Vec.replicate nlimbs U64)

BigInt : ℕ -> Ty
BigInt nlimbs = Named name (BigInt' nlimbs) where
  name = Data.String._++_ "BigInt" (Data.Nat.Show.show nlimbs)

mkBigInt' : {nlimbs : ℕ} -> Vec (Tm U64) nlimbs -> Tm (BigInt' nlimbs)
mkBigInt' tms = mkStruct (vecToHList Tm tms) 

mkBigInt : {nlimbs : ℕ} -> Vec (Tm U64) nlimbs -> Tm (BigInt nlimbs)
mkBigInt tms = wrap (mkBigInt' tms)

deconstruct' : {n : ℕ} -> Tm (BigInt' n) -> Gen (Vec (Tm U64) n)
deconstruct' big = 
 do
    struct ← gen big
    return (worker struct)
  where
    worker : {n : ℕ} -> Tm (Vect n U64) -> Vec (Tm U64) n
    worker {n} struct = go (allFin n) where
      go : {k : ℕ} -> Vec (Fin n) k -> Vec (Tm U64) k 
      go []       = []
      go (j ∷ js) = vecproj j struct ∷ go js
 
deconstruct : {n : ℕ} -> Tm (BigInt n) -> Gen (Vec (Tm U64) n)
deconstruct big = deconstruct' (unwrap big)

--------------------------------------------------------------------------------

private

  TmBigInt' : ℕ -> Set
  TmBigInt' n = Tm (BigInt' n)

  TmBigInt : ℕ -> Set
  TmBigInt n = Tm (BigInt n)

--------------------------------------------------------------------------------

mkSmall : (nlimbs : ℕ) -> Tm U64 -> Tm (BigInt nlimbs)
mkSmall nzero     x = mkBigInt []
mkSmall (nsuc n₁) x = mkBigInt (x ∷ Data.Vec.replicate n₁ zeroU64)

zero : (nlimbs : ℕ) -> Tm (BigInt nlimbs)
zero nlimbs = mkSmall nlimbs zeroU64

one : (nlimbs : ℕ) -> Tm (BigInt nlimbs)
one nlimbs = mkSmall nlimbs (kstU64 (fromℕ 1))

two : (nlimbs : ℕ) -> Tm (BigInt nlimbs)
two nlimbs = mkSmall nlimbs (kstU64 (fromℕ 2))

bigproj : Fin n -> Tm (BigInt n) -> Tm U64
bigproj j big = vecproj j (unwrap big)

--------------------------------------------------------------------------------

private

  unwrap1 : {ty : Ty} -> Tm (BigInt n) -> (Tm (BigInt' n) -> Tm ty) -> Tm ty
  unwrap1 tm f = Let (unwrap tm) f

  unwrap2 : {ty : Ty} -> Tm (BigInt n) -> Tm (BigInt m) -> (Tm (BigInt' n) -> Tm (BigInt' m) -> Tm ty) -> Tm ty
  unwrap2 tm1 tm2 g = Let (unwrap tm1) \x -> Let (unwrap tm2) \y -> g x y

--------------------------------------------------------------------------------

bitComplement : Tm (BigInt n) -> Tm (BigInt n)
bitComplement big = runGen do
  xs <- deconstruct big
  let zs = Data.Vec.map bitComplU64 xs
  return (mkBigInt zs)
  
bitOr : Tm (BigInt n) -> Tm (BigInt n) -> Tm (BigInt n)
bitOr big1 big2 = runGen do
  xs <- deconstruct big1
  ys <- deconstruct big2
  let zs = Data.Vec.zipWith bitOrU64 xs ys
  return (mkBigInt zs)

bitAnd : Tm (BigInt n) -> Tm (BigInt n) -> Tm (BigInt n)
bitAnd big1 big2 = runGen do
  xs <- deconstruct big1
  ys <- deconstruct big2
  let zs = Data.Vec.zipWith bitAndU64 xs ys
  return (mkBigInt zs)

bitXor : Tm (BigInt n) -> Tm (BigInt n) -> Tm (BigInt n)
bitXor big1 big2 = runGen do
  xs <- deconstruct big1
  ys <- deconstruct big2
  let zs = Data.Vec.zipWith bitXorU64 xs ys
  return (mkBigInt zs)

--------------------------------------------------------------------------------

isEqual : Tm (BigInt n) -> Tm (BigInt n) -> Tm Bit
isEqual {n} big1 big2 = unwrap2 big1 big2 \x y -> worker x y (allFin n) where
  worker : Tm (BigInt' n) -> Tm (BigInt' n) -> Vec (Fin n) n -> Tm Bit
  worker x y list = go list where
    go : {k : ℕ} -> Vec (Fin n) k -> Tm Bit
    go []       = true
    go (j ∷ js) = ifte (vecproj j x == vecproj j y) (go js) false

isZero : Tm (BigInt n) -> Tm Bit
isZero {n} x = isEqual x (zero n)

--------------------------------------------------------------------------------

isGE : Tm (BigInt n) -> Tm (BigInt n) -> Tm Bit
isGE {n} big1 big2 = unwrap2 big1 big2 \x y -> worker x y (allFin n) where
  worker : Tm (BigInt' n) -> Tm (BigInt' n) -> Vec (Fin n) n -> Tm Bit
  worker x y list = go list where
    go : {k : ℕ} -> Vec (Fin n) k -> Tm Bit
    go []       = true
    go (j ∷ js) = Let (vecproj (opposite j) x) \(a : Tm U64) ->
                  Let (vecproj (opposite j) y) \(b : Tm U64) ->
                  ifte (a < b)
                    false
                    (ifte (a > b)
                      true
                      (go js)
                    )
    
isLE : Tm (BigInt n) -> Tm (BigInt n) -> Tm Bit
isLE x y = isGE y x

isGT : Tm (BigInt n) -> Tm (BigInt n) -> Tm Bit
isGT x y = not (isLE x y)

isLT : Tm (BigInt n) -> Tm (BigInt n) -> Tm Bit
isLT x y = not (isGE x y)

--------------------------------------------------------------------------------

addCarry : Tm Bit -> Tm (BigInt n) -> Tm (BigInt n) -> Tm (Pair Bit (BigInt n))
addCarry {n} carry₀ big1 big2 =
  unwrap2 big1 big2 \xs ys -> runGen do
      (carry₁ , tms) ← worker xs ys (Data.Vec.allFin n)
      return (mkPair carry₁ (mkBigInt tms))

  where
    worker : Tm (BigInt' n) -> Tm (BigInt' n) -> Vec (Fin n) n -> Gen (Tm Bit × Vec (Tm U64) n)
    worker xs ys vec = go vec carry₀ where

      go : {k : ℕ} -> Vec (Fin n) k -> Tm Bit -> Gen (Tm Bit × Vec (Tm U64) k)
      go []       c₀ = return (c₀ , [])
      go (j ∷ js) c₀ = do
                          c₁ , z  ← pair⇑ (addCarryU64 c₀ (vecproj j xs) (vecproj j ys))
                          c₂ , zs ← go js c₁
                          return (c₂ , z ∷ zs)

subCarry : Tm Bit -> Tm (BigInt n) -> Tm (BigInt n) -> Tm (Pair Bit (BigInt n))
subCarry {n} carry₀ big1 big2 =
  unwrap2 big1 big2 \xs ys -> runGen do
      (carry₁ , tms) ← worker xs ys (Data.Vec.allFin n)
      return (mkPair carry₁ (mkBigInt tms))

  where
    worker : Tm (BigInt' n) -> Tm (BigInt' n) -> Vec (Fin n) n -> Gen (Tm Bit × Vec (Tm U64) n)
    worker xs ys vec = go vec carry₀ where

      go : {k : ℕ} -> Vec (Fin n) k -> Tm Bit -> Gen (Tm Bit × Vec (Tm U64) k)
      go []       c₀ = return (c₀ , [])
      go (j ∷ js) c₀ = do
                          c₁ , z  ← pair⇑ (subCarryU64 c₀ (vecproj j xs) (vecproj j ys))
                          c₂ , zs ← go js c₁
                          return (c₂ , z ∷ zs)

add : Tm (BigInt n) -> Tm (BigInt n) -> Tm (Pair Bit (BigInt n))
add = addCarry zeroBit

sub : Tm (BigInt n) -> Tm (BigInt n) -> Tm (Pair Bit (BigInt n))
sub = subCarry zeroBit

addNC : Tm (BigInt n) -> Tm (BigInt n) -> Tm (BigInt n)
addNC x y = snd (add x y)

subNC : Tm (BigInt n) -> Tm (BigInt n) -> Tm (BigInt n)
subNC x y = snd (sub x y)

neg : Tm (BigInt n) -> Tm (BigInt n)
neg {n} x = subNC (zero n) x

--------------------------------------------------------------------------------

takeBigInt' : {n : ℕ} -> (k : ℕ) -> Tm (BigInt' (k + n)) -> Tm (BigInt' k)
takeBigInt' {n} k input = Let input \what -> mkBigInt' (worker what indices) where

  indices : Vec (Fin (k + n)) k 
  indices = Data.Vec.take k (Data.Vec.allFin (k + n))

  worker : {l : ℕ} -> Tm (BigInt' (k + n)) -> Vec (Fin (k + n)) l -> Vec (Tm U64) l
  worker what []       = []
  worker what (j ∷ js) = vecproj j what ∷ worker what js

dropBigInt' : {n : ℕ} -> (k : ℕ) -> Tm (BigInt' (k + n)) -> Tm (BigInt' n)
dropBigInt' {n} k input = Let input \what -> mkBigInt' (worker what indices) where

  indices : Vec (Fin (k + n)) n
  indices = Data.Vec.drop k (Data.Vec.allFin (k + n))

  worker : {l : ℕ} -> Tm (BigInt' (k + n)) -> Vec (Fin (k + n)) l -> Vec (Tm U64) l
  worker what []       = []
  worker what (j ∷ js) = vecproj j what ∷ worker what js

takeBigInt : {n : ℕ} -> (k : ℕ) -> Tm (BigInt (k + n)) -> Tm (BigInt k)
takeBigInt k input = wrap (takeBigInt' k  (unwrap input))

dropBigInt : {n : ℕ} -> (k : ℕ) -> Tm (BigInt (k + n)) -> Tm (BigInt n)
dropBigInt k input = wrap (dropBigInt' k  (unwrap input))

extendBigInt' : {n : ℕ} -> (k : ℕ) -> Tm (BigInt' n) -> Tm (BigInt' (n + k))
extendBigInt' {n} k input = runGen do
  what <- gen input
  xs   <- deconstruct' what
  return (mkBigInt' (Data.Vec._++_ xs (Data.Vec.replicate k zeroU64)))

extendBigInt : {n : ℕ} -> (k : ℕ) -> Tm (BigInt n) -> Tm (BigInt (n + k))
extendBigInt k input = wrap (extendBigInt' k (unwrap input))

extendBigInt₁' : {n : ℕ} -> Tm (BigInt' n) -> Tm (BigInt' (nsuc n))
extendBigInt₁' {n} tm = subst TmBigInt' (lemma n) (extendBigInt' 1 tm) where

  lemma : (n : ℕ) -> n + 1 ≡ nsuc n
  lemma n = trans eq1 (cong nsuc eq2) where
    eq1 : n + 1 ≡ nsuc (n + 0)
    eq1 = Data.Nat.Properties.+-suc n 0
    eq2 : n + 0 ≡ n
    eq2 = Data.Nat.Properties.+-identityʳ n  

extendBigInt₁ : {n : ℕ} -> Tm (BigInt n) -> Tm (BigInt (nsuc n))
extendBigInt₁ input = wrap (extendBigInt₁' (unwrap input))

--------------------------------------------------------------------------------

-- rotate left through carry
rotateLeftBy1 : Tm Bit -> Tm (BigInt n) -> Tm (Pair Bit (BigInt n))
rotateLeftBy1 {n} carry₀ big = 
  unwrap1 big \xs -> runGen do
    (carry₁ , tms) ← worker xs carry₀ (Data.Vec.allFin n)
    return (mkPair carry₁ (mkBigInt tms))

  where
    worker : Tm (BigInt' n) -> Tm Bit -> Vec (Fin n) n -> Gen (Tm Bit × Vec (Tm U64) n)
    worker xs carry₀ vec = go vec carry₀ where

      go : {k : ℕ} -> Vec (Fin n) k -> Tm Bit -> Gen (Tm Bit × Vec (Tm U64) k)
      go []       c₀ = return (c₀ , [])
      go (j ∷ js) c₀ = do
                         c₁ , y  ← pair⇑ (rotLeftU64 c₀ (vecproj j xs))
                         c₂ , ys ← go js c₁
                         return (c₂ , y ∷ ys)

-- rotate right through carry
rotateRightBy1 : Tm Bit -> Tm (BigInt n) -> Tm (Pair Bit (BigInt n))
rotateRightBy1 {n} carry₀ big = 
  unwrap1 big \xs -> runGen do
    (carry₁ , tms) ← worker xs carry₀ (Data.Vec.allFin n)
    return (mkPair carry₁ (mkBigInt (Data.Vec.reverse tms)))

  where
    worker : Tm (BigInt' n) -> Tm Bit -> Vec (Fin n) n -> Gen (Tm Bit × Vec (Tm U64) n)
    worker xs carry₀ vec = go vec carry₀ where

      go : {k : ℕ} -> Vec (Fin n) k -> Tm Bit -> Gen (Tm Bit × Vec (Tm U64) k)
      go []       c₀ = return (c₀ , [])
      go (j ∷ js) c₀ = do
                         c₁ , y  ← pair⇑ (rotRightU64 c₀ (vecproj (opposite j) xs))
                         c₂ , ys ← go js c₁
                         return (c₂ , y ∷ ys)

shiftLeftBy1 : Tm (BigInt n) -> Tm (Pair Bit (BigInt n))
shiftLeftBy1 = rotateLeftBy1 zeroBit

shiftRightBy1 : Tm (BigInt n) -> Tm (Pair Bit (BigInt n))
shiftRightBy1 = rotateRightBy1 zeroBit

--------------------------------------------------------------------------------

scaleExtCarry : Tm U64 -> Tm (BigInt n) -> Tm (Pair U64 (BigInt n))
scaleExtCarry {n} scalar big =
  unwrap1 big \xs -> runGen do
    (carry₁ , tms) ← worker xs (Data.Vec.allFin n)
    return (mkPair carry₁ (mkBigInt tms))

  where
    worker : Tm (BigInt' n) -> Vec (Fin n) n -> Gen (Tm U64 × Vec (Tm U64) n)
    worker xs vec = go vec zeroU64 where

      go : {k : ℕ} -> Vec (Fin n) k -> Tm U64 -> Gen (Tm U64 × Vec (Tm U64) k)
      go []       c₀ = return (c₀ , [])
      go (j ∷ js) c₀ = do
                          c₁ , z  ← pair⇑ (mulAddU64 c₀ scalar (vecproj j xs))
                          c₂ , zs ← go js c₁
                          return (c₂ , z ∷ zs)
 
scaleExt : Tm U64 -> Tm (BigInt n) -> Tm (BigInt (nsuc n))
scaleExt scalar big = runGen do
  (carry , res) ← pair⇑ (scaleExtCarry scalar big)
  limbs ← deconstruct big
  return (mkBigInt (limbs ∷ʳ carry))

--------------------------------------------------------------------------------

import Algebra.Misc
open Algebra.Misc.Diagonal

{-
private

  listProd : {A B : Set} -> List A -> List B -> List (A × B)
  listProd {A} {B} []       ys = []
  listProd {A} {B} (x ∷ xs) ys = Data.List._++_ (glueLeft x ys) (listProd xs ys) where
    glueLeft : A ->  List B -> List (A × B)
    glueLeft x ys = Data.List.map (\y -> (x , y)) ys

  finPlus : Fin n -> Fin m -> Fin (n + m)
  finPlus {n} {m} fzero    k = Data.Fin.inject≤ k (m≤n+m m n)
  finPlus {n} {m} (fsuc j) k = fsuc (finPlus j k)

  finEq : Fin n -> Fin n -> Bool
  finEq fzero    fzero    = Data.Bool.true
  finEq (fsuc x) (fsuc y) = finEq x y
  finEq _        _        = Data.Bool.false

  diagonal : (n m : ℕ) -> Fin (n + m) -> List (Fin n × Fin m)
  diagonal n m k = Data.List.filterᵇ cond ijs where
    ijs : List (Fin n × Fin m)
    ijs = listProd (Data.List.allFin n) (Data.List.allFin m)
    cond : Fin n × Fin m -> Bool
    cond (i , j) = finEq (finPlus i j) k
-}

mulExt : {n m : ℕ} -> Tm (BigInt n) -> Tm (BigInt m) -> Tm (BigInt (n + m))
mulExt {n} {m} big1 big2 =
  unwrap2 big1 big2 \xs ys -> runGen do
    (carry , parts) <- vecMapAccumM (wrapper xs ys) [] (allFin (n + m))
    return (mkBigInt parts)
  where
    wrapper : Tm (BigInt' n) -> Tm (BigInt' m) -> List (Tm U64) -> Fin (n + m) -> Gen (List (Tm U64) × Tm U64)
    wrapper xs ys = worker where
      worker : List (Tm U64) -> Fin (n + m) -> Gen (List (Tm U64) × Tm U64)
      worker prev k = do
        pairs <- listMapM (\(i , j) -> pair⇑ (mulExtU64 (vecproj i xs) (vecproj j ys))) (diagonal n m k)
        let (hiList , loList) = Data.List.unzip pairs
        (sumHi , sumLo) <- pair⇑ (sumU64 (Data.List._++_ prev loList))
        return (sumHi ∷ hiList , sumLo)

{-
private

  open import Data.Fin using ( _↑ˡ_ )
  
  smallDiagonal : (n : ℕ) -> Fin n -> List (Fin n × Fin n)
  smallDiagonal n k = diagonal n n (k ↑ˡ n) 
-}

mulTrunc : {n : ℕ} -> Tm (BigInt n) -> Tm (BigInt n) -> Tm (BigInt n)
mulTrunc {n} big1 big2 =
  unwrap2 big1 big2 \xs ys -> runGen do
    (carry , parts) <- vecMapAccumM (wrapper xs ys) [] (allFin n)
    return (mkBigInt parts)
  where
    wrapper : Tm (BigInt' n) -> Tm (BigInt' n) -> List (Tm U64) -> Fin n -> Gen (List (Tm U64) × Tm U64)
    wrapper xs ys = worker where
      worker : List (Tm U64) -> Fin n -> Gen (List (Tm U64) × Tm U64)
      worker prev k = do
        pairs <- listMapM (\(i , j) -> pair⇑ (mulExtU64 (vecproj i xs) (vecproj j ys))) (smallDiagonal n k)
        let (hiList , loList) = Data.List.unzip pairs
        (sumHi , sumLo) <- pair⇑ (sumU64 (Data.List._++_ prev loList))
        return (sumHi ∷ hiList , sumLo)

--------------------------------------------------------------------------------

private 

  FoldedDiag : (n : ℕ) -> Set 
  FoldedDiag n = List (Fin n × Fin n) × Maybe (Fin n)

  foldedDiagonal : (n : ℕ) -> Fin (n + n) -> FoldedDiag n
  foldedDiagonal n k = go (diagonal n n k) where

    insert : Fin n × Fin n -> FoldedDiag n -> FoldedDiag n
    insert ij (list , mb) = (ij ∷ list) , mb

    go : List (Fin n × Fin n) -> FoldedDiag n
    go [] = [] , nothing
    go ((i , j) ∷ rest) with Data.Fin.compare i j 
    go ((i , j) ∷ rest) | Data.Fin.greater _ _  = [] , nothing 
    go ((i , j) ∷ rest) | Data.Fin.equal   _    = [] , (just i)
    go ((i , j) ∷ rest) | Data.Fin.less    _ _  = insert (i , j) (go rest) 

{-
  testDiag : List (Fin 4 × Fin 4)
  testDiag = diagonal 4 4 (fsuc (fsuc (fsuc fzero)))

  testFoldDiag3 : FoldedDiag 4
  testFoldDiag3 = foldedDiagonal 4 (fsuc (fsuc (fsuc fzero)))

  testFoldDiag4 : FoldedDiag 5
  testFoldDiag4 = foldedDiagonal 5 (fsuc (fsuc (fsuc (fsuc fzero))))
-}

  duplicateList : List (Tm U64) -> Gen (List (Tm U64))
  duplicateList []       = return []
  duplicateList (x ∷ xs) = do
    x'  <- gen x
    xs' <- duplicateList xs
    return (x' ∷ x' ∷ xs')

  helper : List (Tm U64 × Tm U64) -> Gen (List (Tm U64) × List (Tm U64))
  helper pairs = do
    let (hiList , loList) = Data.List.unzip pairs
    hiList' <- duplicateList hiList
    loList' <- duplicateList loList
    return (hiList' , loList')

  combineSingle : Maybe (Tm U64 × Tm U64) -> List (Tm U64 × Tm U64) -> Gen (List (Tm U64) × List (Tm U64))
  combineSingle  nothing           list = helper list 
  combineSingle (just (hi₁ , lo₁)) list = do
    (hiList₂ , loList₂) <- helper list
    return (hi₁ ∷ hiList₂ , lo₁ ∷ loList₂)

squareExt : {n : ℕ} -> Tm (BigInt n) -> Tm (BigInt (n + n))
squareExt {n} big =
  unwrap1 big \xs -> runGen do
    (carry , parts) <- vecMapAccumM (wrapper xs) [] (allFin (n + n))
    return (mkBigInt parts)
  where

    wrapper : Tm (BigInt' n) -> List (Tm U64) -> Fin (n + n) -> Gen (List (Tm U64) × Tm U64)
    wrapper xs = worker where
      worker : List (Tm U64) -> Fin (n + n) -> Gen (List (Tm U64) × Tm U64)
      worker prev k = do
        let (list , mb) = foldedDiagonal n k
        pairs  <- listMapM  (\(i , j) -> pair⇑ (mulExtU64 (vecproj i xs) (vecproj j xs))) list
        single <- maybeMapM (\ i      -> pair⇑ (sqrExtU64 (vecproj i xs)               )) mb 
        (hiList , loList) <- combineSingle single pairs
        (sumHi , sumLo) <- pair⇑ (sumU64 (Data.List._++_ prev loList))
        return (sumHi ∷ hiList , sumLo)

private

  open import Data.Fin using ( _↑ˡ_ )
  
  smallFoldedDiagonal : (n : ℕ) -> Fin n -> FoldedDiag n
  smallFoldedDiagonal n k = foldedDiagonal n (k ↑ˡ n) 

squareTrunc : {n : ℕ} -> Tm (BigInt n) -> Tm (BigInt n)
squareTrunc {n} big =
  unwrap1 big \xs -> runGen do
    (carry , parts) <- vecMapAccumM (wrapper xs) [] (allFin n)
    return (mkBigInt parts)
  where

    wrapper : Tm (BigInt' n) -> List (Tm U64) -> Fin n -> Gen (List (Tm U64) × Tm U64)
    wrapper xs = worker where
      worker : List (Tm U64) -> Fin n -> Gen (List (Tm U64) × Tm U64)
      worker prev k = do
        let (list , mb) = smallFoldedDiagonal n k
        pairs  <- listMapM  (\(i , j) -> pair⇑ (mulExtU64 (vecproj i xs) (vecproj j xs))) list
        single <- maybeMapM (\ i      -> pair⇑ (sqrExtU64 (vecproj i xs)               )) mb 
        (hiList , loList) <- combineSingle single pairs
        (sumHi , sumLo) <- pair⇑ (sumU64 (Data.List._++_ prev loList))
        return (sumHi ∷ hiList , sumLo)

--------------------------------------------------------------------------------


open import Algebra.Misc using ( Half ; Even ; Odd ; halve )

--open BitLib
--open U64Lib

{-# TERMINATING #-}
powℕ : {nlimbs : ℕ} -> Tm (BigInt nlimbs) -> ℕ -> Tm (BigInt nlimbs)
powℕ {nlimbs} base expo = go expo base where
  go : ℕ -> Tm (BigInt nlimbs) -> Tm (BigInt nlimbs)
  go 0 _ = one nlimbs 
  go 1 x = x
  go n x with halve n 
  go _ x | Even k = Let (go k x) \s ->           squareTrunc s
  go _ x | Odd  k = Let (go k x) \s -> mulTrunc (squareTrunc s) x

--------------------------------------------------------------------------------

{-

open import Algebra.Limbs          -- this causes cyclic dependency
open import Algebra.API.Word

bigIntAsWordAPI : ℕ -> WordAPI
bigIntAsWordAPI nlimbs =  record
  { #bits = 64 * nlimbs
  ; Word  = BigInt nlimbs
  ; fromℕ = bigIntFromℕ
    -- queries
  ; isEqualℕ = \n y -> isEqual (bigIntFromℕ n) y
  ; isEqual  = isEqual
  ; isLT     = isLT
  ; isLE     = isLE
    -- arithmetic
  ; neg   = neg
  ; add   = add
  ; sub   = sub
  ; sqr   = sqr
  ; mul   = mul
  ; powℕ  = powℕ
    -- bit operations
  ; complement = bitComplement
  ; bitOr      = bitOr
  ; bitAnd     = bitAnd
  ; bitXor     = bitXor
    -- shifts
  ; shiftLeftBy1  = shiftLeftBy1
  ; shiftRightBy1 = shiftRightBy1
  }

-}

--------------------------------------------------------------------------------
