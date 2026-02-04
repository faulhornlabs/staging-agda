
{-# OPTIONS --hidden-argument-puns --rewriting #-}
module Term where

--------------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality

open import Data.Nat
open import Data.Fin hiding ( _+_ ) renaming ( zero to fzero ; suc to fsuc )
open import Data.Vec

open import Ctx

--------------------------------------------------------------------------------

private variable
  A B   : Set
  n m   : ℕ
  s t u : Ty
  ty    : Ty
  Γ : Ctx n

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
  MkFun : {tys : Vec Ty n} -> {lamty : Ty} -> {eq : funTy tys t ≡ lamty} -> tm (Γ ◆ tys) t -> Function tm Γ lamty
  -- yet another example of "don't touch the green slime"...
  -- pattern matching on MkFun is problematic if `Function` is indexed by (funTy tys t)
  
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
  ... | MkFun {tys} {eq = refl} body′ = MkFun {tys = s ∷ tys} {eq = refl} body′
  go term = MkFun {tys = []} {eq = refl} term

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
shift′ : (s : Ty) -> (k : Fin₁ n) -> Tm′ Γ ty -> Tm′ (insertCtx s k Γ) ty 
shift′ s = go where
  mutual
    goApp : {n : ℕ} -> {Γ : Ctx n} -> {ty : Ty} -> (k : Fin₁ n) -> Application (Lookup Γ) (Tm′ Γ) ty -> Application (Lookup (insertCtx s k Γ)) (Tm′ (insertCtx s k Γ)) ty
    goApp k (MkApp i args) = MkApp (shiftLkp s k i) (hmap (go k) args)

    goFun : {n : ℕ} -> {Γ : Ctx n} -> {ty : Ty} -> (k : Fin₁ n) -> Function Tm′ Γ ty -> Function Tm′ (insertCtx s k Γ) ty
    goFun k (MkFun {tys = args} {eq = refl} body) = MkFun {tys = args} {eq = refl} (goExt k args body)

    goExt : {n m : ℕ} -> {Γ : Ctx n} -> {ty : Ty} -> (k : Fin₁ n) -> (args : Vec Ty m) -> Tm′ (Γ ◆ args) ty -> Tm′ (insertCtx s k Γ ◆ args) ty
    goExt {m} k args funbody = substTm′ (lemma-insertCtx s k args) (go (m # k) funbody)

    go : {n : ℕ} -> {Γ : Ctx n} -> {ty : Ty} -> (k : Fin₁ n) -> Tm′ Γ ty -> Tm′ (insertCtx s k Γ) ty
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

  -- this must be type-directed, as functions are not yet saturated!
  go (Let {s} rhs letbody) with s
  go (Let {s} rhs letbody) | U ⇒ V with termIsLam rhs
  go (Let {s} rhs letbody) | U ⇒ V | MkFun {eq = eq} funbody = Fun′ (MkFun {eq = eq} (go funbody)) (go letbody)
  go (Let {s} rhs letbody) | _                               = Let′ (go rhs) (go letbody)

  go (Rec rhs letbody) with termIsLam rhs
  ... | MkFun {eq} funbody = Rec′ (MkFun {eq = eq} (go funbody)) (go letbody)

--------------------------------------------------------------------------------
