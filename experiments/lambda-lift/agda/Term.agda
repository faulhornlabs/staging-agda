
{-# OPTIONS --hidden-argument-puns --rewriting #-}
module Term where

--------------------------------------------------------------------------------

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties
open import Data.Vec.Properties

open import Data.Nat
open import Data.Fin hiding ( _+_ ) renaming (zero to fzero ; suc to fsuc)
open import Data.Vec
open import Data.Maybe

--------------------------------------------------------------------------------

{-# REWRITE +-suc #-}

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
-- ctx ◆ args ≡ reverse args ++ ctx
--
infixl 20 _◆_
_◆_ : Vec A n -> Vec A m -> Vec A (m + n)
_◆_         {m = zero  } ctx []       = ctx
_◆_ {A} {n} {m = suc m₁} ctx (a ∷ as) = {- subst (Vec A) (+-suc m₁ n) -} ((a ∷ ctx) ◆ as)

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
  
--------------------------------------------------------------------------------

data Ty : Set where
  _⇒_ : Ty -> Ty -> Ty 
  T   : Ty

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
  Γ     : Ctx n

-- extend a context by injecting a fresh variable at the given location
insertCtx : Ty -> Fin (suc n) -> Ctx n -> Ctx (suc n)
insertCtx ty fzero          Γ  = ty ∷ Γ
insertCtx ty (fsuc k₁) (s ∷ Γ) = s ∷ insertCtx ty k₁ Γ

-- shift a (de Bruijn) index so that it works in an enlarged context 
_#_ : {n : ℕ} -> (m : ℕ) -> Fin n -> Fin (m + n)
_#_ zero     j = j
_#_ (suc m₁) j = fsuc (m₁ # j)

lemma-insertCtx-pre : {m : ℕ} -> {k : Fin (suc n)} -> (ts : Vec Ty m) -> insertCtx s (m # k) (ts ++ Γ) ≡ ts ++ insertCtx s k Γ
lemma-insertCtx-pre [] = refl
lemma-insertCtx-pre (t ∷ ts) = cong (cons t) (lemma-insertCtx-pre ts)

lemma-insertCtx : {m : ℕ} -> (s : Ty) -> (k : Fin (suc n)) -> (ts : Vec Ty m) -> insertCtx s (m # k) (Γ ◆ ts) ≡ insertCtx s k Γ ◆ ts
lemma-insertCtx {n} {Γ} {m} s k ts = trans (trans eq₁ eq₂) (sym eq₃) where

  helper : {n : ℕ} ->{xs ys : Vec Ty n} -> (k : Fin (suc n)) -> xs ≡ ys -> insertCtx s k xs ≡ insertCtx s k ys  
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

variable
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
hmap {F = F} {G = G} f = go where
  go : {n : ℕ} -> {ts : Vec Ty n} -> HVec F ts -> HVec G ts
  go HNil         = HNil
  go (HCons x xs) = HCons (f x) (go xs)
  
--------------------------------------------------------------------------------

-- STLC terms
data Tm : Ctx n -> Ty -> Set where
  Var : Lookup Γ t                    -> Tm Γ t
  App : Tm Γ (s ⇒ t) -> Tm Γ s        -> Tm Γ t 
  Lam : Tm (Γ ⊳ s) t                  -> Tm Γ (s ⇒ t)
  Let : Tm Γ s       -> Tm (Γ ⊳ s) t  -> Tm Γ t
  Rec : Tm (Γ ⊳ s) s -> Tm (Γ ⊳ s) t  -> Tm Γ t

--------------------------------------------------------------------------------

-- multi-application
data Application (tm₁ tm₂ : Ty -> Set) : Ty -> Set where
  MkApp : {tys : Vec Ty n} -> tm₁ (funTy tys t) -> HVec tm₂ tys -> Application tm₁ tm₂ t
    
-- multi-lambda
data Function (tm : {m : ℕ} -> Ctx m -> Ty -> Set) :  Ctx n -> Ty -> Set where
  MkFun : {tys : Vec Ty n} -> tm (Γ ◆ tys) t -> Function tm Γ (funTy tys t)

termIsApp : Tm Γ ty -> Application (Tm Γ) (Tm Γ) ty
termIsApp = go where
  go : {ty : Ty} -> {n : ℕ} -> {Γ : Ctx n} -> Tm Γ ty -> Application (Tm Γ) (Tm Γ) ty
  go {Γ} (App {s} {t} f x) with go f
  ... | MkApp {tys} h xs = MkApp (subst (Tm Γ) (lemma-funTy-arrow tys) h) (hsnoc xs x)
  go term = MkApp term HNil

termIsLam : Tm Γ ty -> Function Tm Γ ty
termIsLam = go where
  go : {ty : Ty} -> {n : ℕ} -> {Γ : Ctx n} -> Tm Γ ty -> Function Tm Γ ty
  go {Γ} (Lam {s} {t} body) with go body
  ... | MkFun {tys} body′ = MkFun {tys = s ∷ tys} body′
  go term = MkFun {tys = []} term

--------------------------------------------------------------------------------

-- "simplified" terms after preprocessing (all application heads are variables)
data Tm′ : Ctx n -> Ty -> Set where
  App′ : Application (Lookup Γ) (Tm′ Γ) t         -> Tm′ Γ t    -- applications (and variables)
  Let′ : Tm′ Γ s                -> Tm′ (Γ ⊳ s) t  -> Tm′ Γ t    -- let binding of an expression
  Fun′ : Function Tm′  Γ      s -> Tm′ (Γ ⊳ s) t  -> Tm′ Γ t    -- let binding of a function
  Rec′ : Function Tm′ (Γ ⊳ s) s -> Tm′ (Γ ⊳ s) t  -> Tm′ Γ t    -- let binding of a recursive function

pattern Variable lkp = MkApp lkp HNil
pattern Var′     lkp = App′ (Variable lkp)

--------------------------------------------------------------------------------

substTm′ : {n : ℕ} -> {Γ₁ Γ₂ : Ctx n} -> Γ₁ ≡ Γ₂ -> Tm′ Γ₁ ty -> Tm′ Γ₂ ty
substTm′ refl tm = tm

substTm″ : {n m : ℕ} -> {Γ₁ : Ctx n} -> {Γ₂ : Ctx m} -> (eq : n ≡ m) -> subst (Vec Ty) eq Γ₁ ≡ Γ₂ -> Tm′ Γ₁ ty -> Tm′ Γ₂ ty
substTm″ refl refl tm = tm

-- reinterpret a term in an extended context
{-# NON_TERMINATING #-}
shift′ : (s : Ty) -> (k : Fin (suc n)) -> Tm′ Γ ty -> Tm′ (insertCtx s k Γ) ty 
shift′ s = go where
  mutual
    goApp : {n : ℕ} -> {Γ : Ctx n} -> {ty : Ty} -> (k : Fin (suc n)) -> Application (Lookup Γ) (Tm′ Γ) ty -> Application (Lookup (insertCtx s k Γ)) (Tm′ (insertCtx s k Γ)) ty
    goApp k (MkApp i args) = MkApp (shiftLkp s k i) (hmap (go k) args)

    goFun : {n : ℕ} -> {Γ : Ctx n} -> {ty : Ty} -> (k : Fin (suc n)) -> Function Tm′ Γ ty -> Function Tm′ (insertCtx s k Γ) ty
    goFun k (MkFun {tys = args} body) = MkFun {tys = args} (goExt k args body)

    goExt : {n m : ℕ} -> {Γ : Ctx n} -> {ty : Ty} -> (k : Fin (suc n)) -> (args : Vec Ty m) -> Tm′ (Γ ◆ args) ty -> Tm′ (insertCtx s k Γ ◆ args) ty
    goExt {m} k args funbody = substTm′ (lemma-insertCtx s k args) (go (m # k) funbody)

    go : {n : ℕ} -> {Γ : Ctx n} -> {ty : Ty} -> (k : Fin (suc n)) -> Tm′ Γ ty -> Tm′ (insertCtx s k Γ) ty
    go k (App′ application) = App′ (goApp k application)
    go k (Let′ rhs body)    = Let′ (go k rhs) (go (fsuc k) body)
    go k (Fun′ fun body)    = Fun′ (goFun       k  fun) (go (fsuc k) body)
    go k (Rec′ rec body)    = Rec′ (goFun (fsuc k) rec) (go (fsuc k) body)

shift₀ : {s : Ty} -> Tm′ Γ ty -> Tm′ (Γ ⊳ s) ty
shift₀ {s} = shift′ s fzero 

shift₁ : {s : Ty} -> Tm′ (Γ ⊳ u) ty -> Tm′ (Γ ⊳ s ⊳ u) ty
shift₁ {s} = shift′ s (fsuc fzero)

--------------------------------------------------------------------------------

-- apply with let-floating
letFloatApp : {args : Vec Ty m} -> Tm′ Γ (funTy args ty) -> HVec (Tm′ Γ) args -> Tm′ Γ ty
letFloatApp {m} {args} = float where

  float : {argTys : Vec Ty m} -> Tm′ Γ (funTy argTys ty) -> HVec (Tm′ Γ) argTys -> Tm′ Γ ty
  float (Let′ rhs body) args = Let′ rhs (float body (hmap shift₀ args))
  float (Fun′ fun body) args = Fun′ fun (float body (hmap shift₀ args))
  float (Rec′ fun body) args = Rec′ fun (float body (hmap shift₀ args))
  float {Γ} {ty} {argTys}
        (App′ (MkApp {tys} i xs)) args =
          let eq = lemma-funTy-concat {ret = ty} tys argTys
              i′ = subst (Lookup Γ) eq i
          in  App′ (MkApp i′ (hconcat xs args))

{-# NON_TERMINATING #-}
preprocess : Tm ∅ ty -> Tm′ ∅ ty
preprocess = go where

  go : {n : ℕ} -> {Γ : Ctx n} -> Tm Γ ty -> Tm′ Γ ty

  go (Var idx)  = Var′ idx

  go (Lam body) = go (Let (Lam body) (Var Here))

  go term@(App f x) with termIsApp term
  ... | MkApp h xs = letFloatApp (go h) (hmap go xs)

  go (Let rhs letbody) with termIsLam rhs
  ... | MkFun {tys = []    } exp     = Let′ (go exp) (go letbody)
  ... | MkFun {tys = t ∷ ts} funbody = Fun′ (MkFun (go funbody)) (go letbody)

  go (Rec rhs letbody) with termIsLam rhs
  ... | MkFun funbody = Rec′ (MkFun (go funbody)) (go letbody)

--------------------------------------------------------------------------------
