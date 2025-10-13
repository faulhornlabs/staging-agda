
module Algebra.Misc where

--------------------------------------------------------------------------------

open import Data.Bool   hiding ( _≤_ )
open import Data.Word64 hiding ( _≤_ )
open import Data.Nat

--------------------------------------------------------------------------------

twoTo64 : ℕ
twoTo64 = 0x10000000000000000

--------------------------------------------------------------------------------

eqWord64 : Word64 -> Word64 -> Bool
eqWord64 = _==_

negWord64 : Word64 -> Word64
negWord64 x = fromℕ (twoTo64 ∸ toℕ x)

addWord64 : Word64 -> Word64 -> Word64
addWord64 x y = fromℕ (toℕ x + toℕ y)

mulWord64 : Word64 -> Word64 -> Word64
mulWord64 x y = fromℕ (toℕ x * toℕ y)

--------------------------------------------------------------------------------

data Half : Set where
  Even : ℕ -> Half
  Odd  : ℕ -> Half

{-
-- TOO SLOW
halve : ℕ -> Half
halve zero     = Even zero
halve (suc n₁) with halve n₁
halve _ | Even h = Odd h
halve _ | Odd  h = Even (suc h)
-}

halve : ℕ -> Half
halve n with n / 2
halve n | k with n % 2
halve n | k | zero = Even k
halve n | k | _    = Odd  k

{-# TERMINATING #-}
powWord64 : ℕ -> Word64 -> Word64
powWord64 = go where
  go : ℕ -> Word64 -> Word64
  go 0 _ = fromℕ 1
  go 1 x = x
  go n x with halve n 
  go _ x | Even k = let y = go k x in            mulWord64 y y
  go _ x | Odd  k = let y = go k x in mulWord64 (mulWord64 y y) x

--------------------------------------------------------------------------------

open import Data.Fin using ( Fin ; opposite ) renaming ( zero to fzero ; suc to fsuc )
open import Data.Fin.Properties using ( _≟_ )
open import Data.Nat.Properties using ( m≤m+n ; m≤n+m )
open import Data.Vec hiding ( diagonal )
open import Data.List

variable
  n m : ℕ

module MyFin where
    
  finPlus : Fin n -> Fin m -> Fin (n Data.Nat.+ m)
  finPlus {n} {m} fzero    k = Data.Fin.inject≤ k (m≤n+m m n)
  finPlus {n} {m} (fsuc j) k = fsuc (finPlus j k)

  finEq : Fin n -> Fin n -> Bool
  finEq fzero    fzero    = Data.Bool.true
  finEq (fsuc x) (fsuc y) = finEq x y
  finEq fzero    (fsuc _) = Data.Bool.false
  finEq (fsuc _) fzero    = Data.Bool.false

module MyFin₁ where

  Fin₁ : ℕ -> Set
  Fin₁ n = Fin (suc n)

  finMax : Fin₁ n
  finMax = opposite fzero

  private

    open import Relation.Binary.PropositionalEquality

    {-
    lemma₁ : (n m : ℕ) -> n + suc m ≡ suc (n + m)
    lemma₁ zero _    = refl
    lemma₁ (suc n) m = cong suc (lemma₁ n m)
    -}
    
    lemma₂ : (n m : ℕ) -> n ≤ m -> suc n ≤ suc m
    lemma₂ _ _ = s≤s
    
    m₁≤[n+m]₁ : (m n : ℕ) -> suc m ≤ suc (n + m)
    m₁≤[n+m]₁ m n = lemma₂ m (n + m) (m≤n+m m n)

  open MyFin
  
  finPlus₁ : Fin₁ n -> Fin₁ m -> Fin₁ (n Data.Nat.+ m)
  finPlus₁ {n}     {m} fzero    k = Data.Fin.inject≤ k (m₁≤[n+m]₁ m n)
  finPlus₁ {suc n} {m} (fsuc j) k = fsuc (finPlus₁ j k) 

  vecAllFin₁ : (n : ℕ) -> Vec (Fin₁ n) (suc n)
  vecAllFin₁ n = Data.Vec.allFin (suc n)

  listAllFin₁ : (n : ℕ) -> List (Fin₁ n) 
  listAllFin₁ n = Data.List.allFin (suc n)

open import Data.Product
open import Data.List

module Diagonal where

  listProd : {A B : Set} -> List A -> List B -> List (A × B)
  listProd {A} {B} []       ys = []
  listProd {A} {B} (x ∷ xs) ys = Data.List._++_ (glueLeft x ys) (listProd xs ys) where
    glueLeft : A ->  List B -> List (A × B)
    glueLeft x ys = Data.List.map (\y -> (x , y)) ys

  open MyFin
    
  -- here the last one is empty (?!)
  diagonal : (n m : ℕ) -> Fin (n Data.Nat.+ m) -> List (Fin n × Fin m)
  diagonal n m k = Data.List.filterᵇ cond ijs where
    ijs : List (Fin n × Fin m)
    ijs = listProd (Data.List.allFin n) (Data.List.allFin m)
    cond : Fin n × Fin m -> Bool
    cond (i , j) = finEq (finPlus i j) k

  open MyFin₁

  -- actually this is the correct one (polynomial multiplication)
  diagonal₁ : (n m : ℕ) -> Fin₁ (n Data.Nat.+ m) -> List (Fin₁ n × Fin₁ m)
  diagonal₁ n m k = Data.List.filterᵇ cond ijs where
    ijs : List (Fin₁ n × Fin₁ m)
    ijs = listProd (listAllFin₁ n) (listAllFin₁ m)
    cond : Fin₁ n × Fin₁ m -> Bool
    cond (i , j) = finEq (finPlus₁ i j) k
    
  -- open import Data.Fin ( _↑ˡ_ )
  smallDiagonal : (n : ℕ) -> Fin n -> List (Fin n × Fin n)
  smallDiagonal n k = diagonal n n (Data.Fin._↑ˡ_ k n) 

--------------------------------------------------------------------------------

{-
ex1 : Word64
ex1 = powWord64 50 (fromℕ 3)

ex2 : Word64
ex2 = powWord64 500 (fromℕ 3)

ex3 : Word64
ex3 = powWord64 5000 (fromℕ 3)

ex4 : Word64
ex4 = powWord64 50000 (fromℕ 3)
-}

