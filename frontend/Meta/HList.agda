
module Meta.HList where

--------------------------------------------------------------------------------

open import Data.Nat
open import Data.Fin
open import Data.Vec
open import Data.List

open import Function
open import Effect.Applicative

-- open import Meta.Ty

--------------------------------------------------------------------------------

private variable
  m  : ℕ
  Ty : Set
  t  : Ty
  ts : Vec Ty m
  
data HList {Ty : Set} (F : Ty -> Set) : {n : ℕ} -> Vec Ty n -> Set where
  Nil  : HList F {0} []
  Cons : F t -> HList F {m} ts -> HList F {suc m} (t ∷ ts)

--------------------------------------------------------------------------------

project : {F : Ty -> Set} -> HList F {m} ts -> (j : Fin m) -> F (Data.Vec.lookup ts j)
project (Cons x rest)  Fin.zero   = x
project (Cons x rest) (Fin.suc k) = project rest k

--------------------------------------------------------------------------------

vecToHList : {n : ℕ} -> {ty : Ty} -> (F : Ty -> Set) -> Vec (F ty) n -> HList F (Data.Vec.replicate n ty)
vecToHList F []       = Nil
vecToHList F (x ∷ xs) = Cons x (vecToHList F xs)

hPair : {s t : Ty} -> (F : Ty -> Set) -> F s -> F t -> HList F (s ∷ t ∷ [])
hPair F x y = Cons x (Cons y Nil)

--------------------------------------------------------------------------------

mapHList′ : {Ty₁ Ty₂ : Set} -> {F : Ty₁ -> Set} -> {G : Ty₂ -> Set} -> (h : Ty₁ -> Ty₂) -> (f : {t : Ty₁} -> F t -> G (h t)) -> {ts : Vec Ty₁ m} -> HList F ts -> HList G (Data.Vec.map h ts)
mapHList′ {Ty₁ = Ty₁} {Ty₂ = Ty₂} {F = F} {G = G} h f = go where
  go : {ts : Vec Ty₁ m} -> HList F ts -> HList G (Data.Vec.map h ts)
  go Nil = Nil
  go (Cons x xs) = Cons (f x) (go xs)

mapHList : {F : Ty -> Set} -> (h : Ty -> Ty) -> (f : {t : Ty} -> F t -> F (h t)) -> HList F ts -> HList F (Data.Vec.map h ts)
mapHList {F = F} h f = go where
  go : HList F ts -> HList F (Data.Vec.map h ts)
  go Nil = Nil
  go (Cons x xs) = Cons (f x) (go xs)

zipHList : {F : Ty -> Set} -> {B : Set} -> ((ty : Ty) -> F ty -> B) -> {n : ℕ} -> (tys : Vec Ty n) -> HList F tys -> Vec B n
zipHList {Ty = Ty} {F = F} {B = B} f = go where
  go : {n : ℕ} -> (tys : Vec Ty n) -> HList {Ty = Ty} F tys -> Vec B n
  go []       Nil         = []
  go (t ∷ ts) (Cons x xs) = f t x ∷ go ts xs

--------------------------------------------------------------------------------

transform : {F G : Ty -> Set} -> ({t : Ty} -> F t -> G t) -> {n : ℕ} -> {ts : Vec Ty n} -> HList F {n} ts -> HList G {n} ts
transform f Nil = Nil
transform f (Cons this rest) = Cons (f this) (transform f rest)

zipHList′ : {F G : Ty -> Set} -> ({t : Ty} -> F t -> G t) -> {n : ℕ} -> {ts : Vec Ty n} -> HList F {n} ts -> HList G {n} ts
zipHList′ = transform

traverse
  :  {G : Set -> Set} -> {F : Ty -> Set}
  -> {n : ℕ}
  -> RawApplicative G
  -> ({ty : Ty} -> F ty -> G (F ty))
  -> {ts : Vec Ty n}  -> HList F {n} ts -> G (HList F {n} ts)
traverse {Ty = Ty} {G} {F} {n} applicative h = go where
  pure  = RawApplicative.pure  applicative
  _<*>_ = RawApplicative._<*>_ applicative

  go : {n : ℕ} -> {ts : Vec Ty n} -> HList F {n} ts -> G (HList F {n} ts)
  go Nil         = pure Nil
  go (Cons x xs) = (| Cons (h x) (go xs) |)

--------------------

traverse₂
  :  {G : Set -> Set} -> {F₁ F₂ : Ty -> Set}
  -> {n : ℕ}
  -> RawApplicative G
  -> ({ty : Ty} -> F₁ ty -> G (F₂ ty))
  -> {ts : Vec Ty n} -> HList F₁ {n} ts -> G (HList F₂ {n} ts)
traverse₂ {Ty = Ty} {G} {F₁} {F₂} {n} applicative h = go where
  pure  = RawApplicative.pure  applicative
  _<*>_ = RawApplicative._<*>_ applicative

  go : {n : ℕ} -> {ts : Vec Ty n} -> HList F₁ {n} ts -> G (HList F₂ {n} ts)
  go Nil         = pure Nil
  go (Cons x xs) = (| Cons (h x) (go xs) |)

--------------------

traverseTyVec
  :  {G : Set -> Set} -> {F : Ty -> Set}
  -> {n : ℕ}
  -> RawApplicative G
  -> ((ty : Ty) -> G (F ty))
  -> (ts : Vec Ty n) -> G (HList F {n} ts)
traverseTyVec {Ty = Ty} {G} {F} {n} applicative h = go where
  pure  = RawApplicative.pure  applicative
  _<*>_ = RawApplicative._<*>_ applicative

  go : {n : ℕ} -> (ts : Vec Ty n) -> G (HList F {n} ts)
  go []       = pure Nil
  go (t ∷ ts) = (| Cons (h t) (go ts) |)

--------------------------------------------------------------------------------

-- make a normalis list out of a heterogenous list
hlistForget : {F : Ty -> Set} -> {A : Set} -> ({t : Ty} -> F t -> A) -> {n : ℕ} -> {ts : Vec Ty n} -> HList F ts -> List A
hlistForget {Ty = Ty} {F} {A} f = go where
  go : {n : ℕ} -> {ts : Vec Ty n} -> HList F ts -> List A
  go Nil         = []
  go (Cons x xs) = f x ∷ go xs

--------------------------------------------------------------------------------
