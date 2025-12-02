
module Meta.FinVec where

--------------------------------------------------------------------------------

open import Data.Empty
open import Data.Sum
open import Data.Nat
open import Data.Nat.Properties using ( +-identityʳ )
open import Data.Fin renaming ( zero to fzero ; suc to fsuc ) hiding ( _+_ )
open import Data.Vec
open import Data.Vec.Properties using ( ) 
open import Data.Maybe

open import Relation.Binary.PropositionalEquality

--------------------------------------------------------------------------------

natToFin : (n : ℕ) -> (k : ℕ) -> Maybe (Fin n)
natToFin zero     _        = nothing
natToFin (suc n₁) zero     = just fzero
natToFin (suc n₁) (suc k₁) with natToFin n₁ k₁
natToFin _        _        | nothing  = nothing
natToFin _        _        | just f₁  = just (fsuc f₁)

--------------------------------------------------------------------------------

finSemiDecEq : {n : ℕ} -> (a b : Fin n) -> Maybe (a ≡ b)
finSemiDecEq fzero     fzero     = just refl
finSemiDecEq fzero     (fsuc _ ) = nothing
finSemiDecEq (fsuc _ ) fzero     = nothing
finSemiDecEq (fsuc a₁) (fsuc a₂) with finSemiDecEq a₁ a₂
... | just refl = just refl
... | nothing   = nothing

--------------------------------------------------------------------------------

splitFin′ : (n m : ℕ) -> Fin (n + m) -> Fin n ⊎ Fin m
splitFin′ = go where
  go : (n m : ℕ) -> Fin (n + m) -> Fin n ⊎ Fin m
  go zero     m j        = inj₂ j
  go (suc n₁) m fzero    = inj₁ fzero
  go (suc n₁) m (fsuc j₁) with go n₁ m j₁
  ... | inj₂ k = inj₂ k 
  ... | inj₁ i = inj₁ (fsuc i)

splitFin : {n₁ n₂ : ℕ} -> Fin (n₁ + n₂) -> Fin n₁ ⊎ Fin n₂
splitFin {n₁ = n₁} {n₂ = n₂} = splitFin′ n₁ n₂

--------------------------------------------------------------------------------

lemma-opposite-n : (n : ℕ) -> opposite (Data.Fin.fromℕ n) ≡ fzero
lemma-opposite-n zero     = refl
lemma-opposite-n (suc n₁) = cong inject₁ (lemma-opposite-n n₁)  

--------------------------------------------------------------------------------

private variable
  A B : Set
  n m : ℕ
  vec : Vec A n
  
lemma-prepend-[] : (vec : Vec A n) -> ([] ++ vec) ≡ vec
lemma-prepend-[] _ = refl

{-
private

  lemma-cong-suc : (n₁ : ℕ) -> cong suc (+-identityʳ n₁) ≡ (+-identityʳ (suc n₁))
  lemma-cong-suc n₁ = refl

lemma-append-[] : {n : ℕ} -> (vec : Vec A n) -> subst (Vec A) (+-identityʳ n) (vec ++ []) ≡ vec
lemma-append-[] {A = _} {n = zero  } []       = refl
lemma-append-[] {A = A} {n = suc n₁} (x ∷ xs) =
  let f : Vec A n₁ -> Vec A (suc n₁)
      f xs = x ∷ xs
      eq = cong f (lemma-append-[] xs)
  in {!!}
-}


--------------------------------------------------------------------------------

lkpOppo : Vec A n -> Fin n -> A
lkpOppo ctx j = Data.Vec.lookup ctx (Data.Fin.opposite j)

lkpOppo₁ : (s : A) -> Vec A n -> Fin n -> A
lkpOppo₁ s ctx j = lkpOppo (s ∷ ctx) (inject₁ j)

lkpOppoNat : {n : ℕ} -> Vec A n -> (k : ℕ) -> Maybe A
lkpOppoNat {n = n} ctx k with natToFin n k
... | nothing = nothing
... | just f  = just (lkpOppo ctx f)

--------------------------------------------------------------------------------

lookup-sub₂ : (vec : Vec A n) -> {j₁ j₂ : Fin n} -> (j₁ ≡ j₂) -> lookup vec j₁ ≡ lookup vec j₂
lookup-sub₂ vec refl = refl

--------------------------------------------------------------------------------

fact-lookup-suc : {A : Set} -> {n : ℕ} -> {x : A} -> {xs : Vec A n} -> (j : Fin n) -> Data.Vec.lookup (x ∷ xs) (fsuc j) ≡ Data.Vec.lookup xs j
fact-lookup-suc j = refl

thm-opposite-inject₁ : {n : ℕ} -> (j : Fin n) -> opposite (inject₁ j) ≡ Data.Fin.suc (opposite j)
thm-opposite-inject₁ {n} fzero    = refl
thm-opposite-inject₁ {n} (fsuc j) = let eq = thm-opposite-inject₁ j in cong inject₁ eq

lemma-lkp-first : {A : Set} -> (vec : Vec A n) -> (s : A) -> lookup (s ∷ vec) fzero ≡ s
lemma-lkp-first vec s = refl
  
lemma-lkp-last : {n : ℕ} -> (ctx : Vec A n) -> (s : A) -> lkpOppo (s ∷ ctx) (Data.Fin.fromℕ n) ≡ s
lemma-lkp-last {n = n} ctx s with lemma-lkp-first ctx s
... | eq rewrite (lemma-opposite-n n) = refl

private

  lemma-opposite-inject₁ : (k : Fin n) -> opposite (inject₁ k) ≡ fsuc (opposite k)
  lemma-opposite-inject₁ fzero     = refl
  lemma-opposite-inject₁ (fsuc k₁) = let eq = lemma-opposite-inject₁ k₁ in cong inject₁ eq 

  lemma-lkp-fsuc : {A : Set} -> (vec : Vec A n) -> (s : A) -> (k : Fin n) -> lookup vec k ≡ lookup (s ∷ vec) (fsuc k)
  lemma-lkp-fsuc vec s k = refl

  lemma-lkp-penultimate′ : {n : ℕ} -> (ctx : Vec A n) -> (s t : A) -> lookup (s ∷ t ∷ ctx) (fsuc fzero) ≡ t
  lemma-lkp-penultimate′ ctx s t = lemma-lkp-fsuc (t ∷ ctx) s fzero

  lemma-lkp-map-idx : {ctx : Vec A n} -> {j k : Fin n} -> (j ≡ k) -> lookup ctx j ≡ lookup ctx k 
  lemma-lkp-map-idx refl = refl
  
lemma-lkp-penultimate : {n : ℕ} -> (ctx : Vec A n) -> (s t : A) -> lkpOppo (s ∷ t ∷ ctx) (inject₁ (Data.Fin.fromℕ n)) ≡ t
lemma-lkp-penultimate {n = n} ctx s t =
  let eq = lemma-lkp-map-idx {ctx = s ∷ t ∷ ctx} (lemma-opposite-inject₁ (Data.Fin.fromℕ n))
  in  trans eq (lemma-lkp-last ctx t)

--------------------------------------------------------------------------------
