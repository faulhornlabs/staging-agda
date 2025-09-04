
{-# OPTIONS --type-in-type #-}
module Meta.Gen where

--------------------------------------------------------------------------------

open import Agda.Builtin.Unit

open import Data.Nat
open import Data.List
open import Data.Vec
open import Data.Maybe using ( Maybe ; nothing ; just )
open import Data.String using ( String )

open import Meta.Ty using ( Ty ; Pair )
open import Meta.HOAS
open import Meta.Lib using ( fst ; snd ; mkPair )

open import Data.Product using ( _×_ ; _,_ )

--------------------------------------------------------------------------------

private variable
  A B : Set
  s t ty : Ty

data Gen (A : Set) : Set where
  MkGen : (∀ {ty} -> (A -> Tm ty) -> Tm ty) -> Gen A

unGen : Gen A -> (∀ {ty} -> (A -> Tm ty) -> Tm ty)
unGen (MkGen f) = f

_>>=_ : Gen A -> (A -> Gen B) -> Gen B
_>>=_ (MkGen h) u = MkGen \k -> h (\x -> unGen (u x) k)

_>>_ : Gen A -> Gen B -> Gen B
_>>_ (MkGen h) (MkGen g) = MkGen \k -> h (\_ -> g k)

return : A -> Gen A 
return x = MkGen \k -> k x

infixl 10 _>>=_
infixl 10 _>>_

runGen : Gen (Tm ty) -> Tm ty
runGen (MkGen f) = f id where
  id : Tm ty -> Tm ty
  id x = x 

gen : Tm ty -> Gen (Tm ty)
gen tm = MkGen \k -> Let tm \x -> k x 

--------------------------------------------------------------------------------

pair⇑ : Tm (Pair s t) -> Gen (Tm s × Tm t)
pair⇑ pair = do
  p ← gen pair
  return (fst p , snd p)

pair⇓ : Gen (Tm s × Tm t) ->  Tm (Pair s t)
pair⇓ action = runGen do
  (x , y) ← action
  return (mkPair x y)

--------------------------------------------------------------------------------

--  data Gen (A : Set) : Set where
--  MkGen : (∀ {ty} -> (A -> Tm ty) -> Tm ty) -> Gen A

--  halt : Tm IO
--  halt = IOp Halt

--  get′ : String -> (ty : Ty) -> (Tm ty -> Tm IO) -> Tm IO  
--  get′ name ty kont = IOp (Get name kont)

--  get : {ty : Ty} -> String -> (Tm ty -> Tm IO) -> Tm IO
--  get {ty} name kont = get′ name ty kont

--  put : {ty : Ty} -> String -> Tm ty -> Tm IO -> Tm IO
--  put {ty} name what kont = IOp (Put name what kont)

--------------------------------------------------------------------------------
-- standard monadic functions specialized to Gen

maybeMapM : {A B : Set} -> (A -> Gen B) -> Maybe A -> Gen (Maybe B)
maybeMapM f nothing  = return nothing
maybeMapM f (just x) = do
  y <- f x
  return (just y)

listMapM : {A B : Set} -> (A -> Gen B) -> List A -> Gen (List B)
listMapM {A} {B} f = go where
  go : List A -> Gen (List B)
  go []       = return []
  go (x ∷ xs) = do
    y  <- f x
    ys <- go xs
    return (y ∷ ys)
    
vecMapM : {A B : Set} -> {n : ℕ} -> (A -> Gen B) -> Vec A n -> Gen (Vec B n)
vecMapM {A} {B} f = go where
  go : {k : ℕ} -> Vec A k -> Gen (Vec B k)
  go []       = return []
  go (x ∷ xs) = do
    y  <- f x
    ys <- go xs
    return (y ∷ ys)

listMapM′ : {A : Set} -> (A -> Gen ⊤) -> List A -> Gen ⊤
listMapM′ {A} f = go where
  go : List A -> Gen ⊤
  go []       = return tt
  go (x ∷ xs) = do
    f x
    go xs
    
vecMapM′ : {A : Set} -> {n : ℕ} -> (A -> Gen ⊤) -> Vec A n -> Gen ⊤
vecMapM′ {A} f = go where
  go : {k : ℕ} -> Vec A k -> Gen ⊤
  go []       = return tt
  go (x ∷ xs) = do
    f x
    go xs

listForM : {A B : Set} -> List A -> (A -> Gen B) -> Gen (List B)
listForM xs f = listMapM f xs

vecForM : {A B : Set} -> {n : ℕ} -> Vec A n -> (A -> Gen B) -> Gen (Vec B n)
vecForM xs f = vecMapM f xs

listForM′ : {A : Set} -> List A -> (A -> Gen ⊤) -> Gen ⊤
listForM′ xs f = listMapM′ f xs
    
vecForM′ : {A : Set} -> {n : ℕ} -> Vec A n -> (A -> Gen ⊤) -> Gen ⊤
vecForM′ xs f = vecMapM′ f xs

----------------------------------------

listFoldM : {A B : Set} -> (B -> A -> Gen B) -> B -> List A -> Gen B
listFoldM {A} {B} f = go where
  go : B -> List A -> Gen B
  go y []       = return y
  go y (x ∷ xs) = f y x >>= \z -> go z xs  

vecFoldM : {A B : Set} -> {n : ℕ} -> (B -> A -> Gen B) -> B -> Vec A n -> Gen B
vecFoldM {A} {B} f = go where
  go : {k : ℕ} -> B -> Vec A k -> Gen B
  go y []       = return y
  go y (x ∷ xs) = f y x >>= \z -> go z xs  

----------------------------------------

listMapAccumM : {S A B : Set} -> (S -> A -> Gen (S × B)) -> S -> List A -> Gen (S × List B)
listMapAccumM {S} {A} {B} f = go where
  go : S -> List A -> Gen (S × List B)
  go s []        = return (s , [])
  go s₀ (x ∷ xs) = do
    (s₁ , y ) <- f  s₀ x
    (s₂ , ys) <- go s₁ xs
    return (s₂ , y ∷ ys)

vecMapAccumM : {S A B : Set} -> {n : ℕ} -> (S -> A -> Gen (S × B)) -> S -> Vec A n -> Gen (S × Vec B n)
vecMapAccumM {S} {A} {B} {n} f = go where
  go : {k : ℕ} -> S -> Vec A k -> Gen (S × Vec B k)
  go s []        = return (s , [])
  go s₀ (x ∷ xs) = do
    (s₁ , y ) <- f  s₀ x
    (s₂ , ys) <- go s₁ xs
    return (s₂ , y ∷ ys)

listForAccumM : {S A B : Set} -> S -> List A -> (S -> A -> Gen (S × B)) -> Gen (S × List B)
listForAccumM s0 xs f = listMapAccumM f s0 xs

vecForAccumM : {S A B : Set} -> {n : ℕ} -> S -> Vec A n -> (S -> A -> Gen (S × B)) -> Gen (S × Vec B n)
vecForAccumM s0 xs f = vecMapAccumM f s0 xs

--------------------------------------------------------------------------------

