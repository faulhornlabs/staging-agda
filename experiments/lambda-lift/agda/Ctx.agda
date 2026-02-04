
{-# OPTIONS --hidden-argument-puns --rewriting #-}
module Ctx where

--------------------------------------------------------------------------------

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import Data.Nat
open import Data.Fin hiding ( _+_ ) renaming ( zero to fzero ; suc to fsuc )
open import Data.Vec
open import Data.Maybe

open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties using ( +-suc     )
open import Data.Vec.Properties using ( reverse-∷ )

{-# REWRITE +-suc #-}

--------------------------------------------------------------------------------

Fin₁ : ℕ -> Set
Fin₁ n = Fin (suc n)

private variable
  A B : Set
  n m : ℕ

infixl 25 _⊳_
_⊳_ : Vec A n -> A -> Vec A (suc n)
_⊳_ xs x = x ∷ xs

cons : A -> Vec A n -> Vec A (suc n)
cons = _∷_

append : Vec A n -> Vec A m -> Vec A (m + n)
append Γ as = as ++ Γ

--
-- extend a context with the arguments of a multi-lambda: 
--
--     ctx ◆ args  ≡  reverse args ++ ctx
--
infixl 20 _◆_
_◆_ : Vec A n -> Vec A m -> Vec A (m + n)
_◆_         {m = zero  } ctx []       = ctx
_◆_ {A} {n} {m = suc m₁} ctx (a ∷ as) = (a ∷ ctx) ◆ as      -- without REWRITE: subst (Vec A) (+-suc m₁ n) ((a ∷ ctx) ◆ as)

lemma-reverse : (Γ : Vec A n) -> (a : A) -> (as : Vec A m) -> reverse (a ∷ as) ++ Γ ≡ reverse as ++ a ∷ Γ
lemma-reverse Γ a as = trans eq₁ eq₂ where 

  helper : {Γ : Vec A n} -> (a : A) -> (as : Vec A m) -> (as ∷ʳ a) ++ Γ ≡ as ++ a ∷ Γ
  helper a [] = refl
  helper a (x ∷ xs) = cong (cons x) (helper a xs)

  eq₁ = cong (append Γ) (reverse-∷ a as)
  eq₂ = helper a (reverse as)
  
lemma-◆ : (Γ : Vec A n) -> (as : Vec A m) -> Γ ◆ as ≡ reverse as ++ Γ
lemma-◆ Γ [] = refl
lemma-◆ Γ (a ∷ as) = trans eq₁ (sym eq₂) where
  eq₁ = lemma-◆ (a ∷ Γ) as
  eq₂ = lemma-reverse Γ a as

{-
◆-extend : (Γ : Vec A n) -> (ts : Vec A m) -> (a : A) -> (Γ ◆ ts) ⊳ a ≡ Γ ◆ (a ⊲ ts)
◆-extend {n} {m} Γ [] a = refl
◆-extend {n} {m} Γ ts a =
  let eq₁ = cong (\xs -> xs ⊳ a) (lemma-◆ Γ ts)
      eq₂ = sym (lemma-reverse Γ a ts)
      eq₃ = sym (lemma-◆ Γ (ts ⊳ a))
  in  trans eq₁ (trans {!!} eq₃)
-}


--------------------------------------------------------------------------------

data Ty : Set where
  _⇒_  : Ty -> Ty -> Ty   -- function type
  base : Ty               -- some base type

tyEq : (s t : Ty) -> Maybe (s ≡ t)
tyEq = go where

  go : (s t : Ty) -> Maybe (s ≡ t)
  go base base = just refl
  go (s₁ ⇒ s₂) (t₁ ⇒ t₂) with go s₁ t₁
  ... | nothing = nothing
  ... | just refl with go s₂ t₂
  ...             | nothing   = nothing
  ...             | just refl = just refl
  go _ _ = nothing
  
private variable
  s t u : Ty
  ty    : Ty

funTy : Vec Ty n -> Ty -> Ty
funTy []       ret = ret
funTy (t ∷ ts) ret = t ⇒ (funTy ts ret)

lemma-funTy-concat : {ret : Ty} -> (xs : Vec Ty m) -> (ys : Vec Ty n) -> funTy xs (funTy ys ret) ≡ funTy (xs ++ ys) ret
lemma-funTy-concat []       ys = refl
lemma-funTy-concat (x ∷ xs) ys = cong (\ret -> x ⇒ ret) (lemma-funTy-concat xs ys)

lemma-funTy-arrow : (tys : Vec Ty n) -> funTy tys (s ⇒ t) ≡ funTy (tys ∷ʳ s) t
lemma-funTy-arrow []       = refl
lemma-funTy-arrow (u ∷ us) = cong (\ret -> u ⇒ ret) (lemma-funTy-arrow us)

--------------------------------------------------------------------------------

Ctx : ℕ -> Set
Ctx n = Vec Ty n

∅ : Ctx 0
∅ = []

private variable
  Γ : Ctx n

-- extend a context by injecting a fresh variable at the given location
insertCtx : Ty -> Fin₁ n -> Ctx n -> Ctx (suc n)
insertCtx ty fzero          Γ  = ty ∷ Γ
insertCtx ty (fsuc k₁) (s ∷ Γ) = s ∷ insertCtx ty k₁ Γ

-- shift a (de Bruijn) index so that it works in an enlarged context 
_#_ : {n : ℕ} -> (m : ℕ) -> Fin n -> Fin (m + n)
_#_ zero     j = j
_#_ (suc m₁) j = fsuc (m₁ # j)

lemma-insertCtx-pre : {m : ℕ} -> {k : Fin₁ n} -> (ts : Vec Ty m) -> insertCtx s (m # k) (ts ++ Γ) ≡ ts ++ insertCtx s k Γ
lemma-insertCtx-pre [] = refl
lemma-insertCtx-pre (t ∷ ts) = cong (cons t) (lemma-insertCtx-pre ts)

lemma-insertCtx : {m : ℕ} -> (s : Ty) -> (k : Fin₁ n) -> (ts : Vec Ty m) -> insertCtx s (m # k) (Γ ◆ ts) ≡ insertCtx s k Γ ◆ ts
lemma-insertCtx {n} {Γ} {m} s k ts = trans (trans eq₁ eq₂) (sym eq₃) where

  helper : {n : ℕ} ->{xs ys : Vec Ty n} -> (k : Fin₁ n) -> xs ≡ ys -> insertCtx s k xs ≡ insertCtx s k ys  
  helper _ refl = refl

  eq₁ = helper (m # k) (lemma-◆ Γ ts)
  eq₂ = lemma-insertCtx-pre {s = s} {Γ = Γ} {k = k} (reverse ts)
  eq₃ = lemma-◆ (insertCtx s k Γ) ts
  
--------------------------------------------------------------------------------

-- we use de Bruijn indices
data Lookup : (Γ : Ctx n) -> (ty : Ty) -> Set where
  Here  :               Lookup (t ∷ Γ) t
  There : Lookup Γ t -> Lookup (s ∷ Γ) t 

-- "shift" de Bruijn indices into an extended context
shiftLkp : (s : Ty) -> (k : Fin (suc n)) -> Lookup Γ ty -> Lookup (insertCtx s k Γ) ty
shiftLkp s fzero     lkp  = There lkp
shiftLkp s (fsuc k₁) Here = Here
shiftLkp s (fsuc k₁) (There prf₁) = There (shiftLkp s k₁ prf₁)

--------------------------------------------------------------------------------

private variable
  ts : Vec Ty n
  us : Vec Ty n

data HVec (F : Ty -> Set) : {n : ℕ} -> Vec Ty n -> Set where
  HNil  : HVec F {n = 0} []
  HCons : F t -> HVec F {n = m} ts -> HVec F {n = suc m} (t ∷ ts)

hsnoc : {F : Ty -> Set} -> HVec F ts -> F u -> HVec F (ts ∷ʳ u)
hsnoc  HNil        y = HCons y HNil
hsnoc (HCons x xs) y = HCons x (hsnoc xs y)

hconcat : {F : Ty -> Set} -> HVec F ts -> HVec F us -> HVec F (ts ++ us)
hconcat  HNil        ys = ys
hconcat (HCons x xs) ys = HCons x (hconcat xs ys)

hmap : {F G : Ty -> Set} -> ({t : Ty} -> F t -> G t) -> HVec F ts -> HVec G ts
hmap {F} {G} f = go where
  go : {n : ℕ} -> {ts : Vec Ty n} -> HVec F ts -> HVec G ts
  go HNil         = HNil
  go (HCons x xs) = HCons (f x) (go xs)

hfoldr : {F : Ty -> Set} -> ({ty : Ty} -> F ty -> B -> B) -> HVec F ts -> B -> B
hfoldr {B} {F} f = go where
  go : {n : ℕ} -> {ts : Vec Ty n} -> HVec F ts -> B -> B
  go  HNil        old = old
  go (HCons x xs) old = f x (go xs old)

--------------------------------------------------------------------------------

