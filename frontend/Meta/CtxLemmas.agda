
-- Context manipulation

module Meta.CtxLemmas where

--------------------------------------------------------------------------------

open import Function
open import Relation.Binary.PropositionalEquality

open import Data.Nat
open import Data.Nat.Properties using ( +-suc )
open import Data.Vec
open import Data.Vec.Properties using ( take++drop≡id )
open import Data.Fin using ( Fin ; opposite ; inject₁ ) renaming ( zero to fzero ; suc to fsuc )
--open import Data.String using ( String )

open import Meta.FinVec
open import Meta.Ty
open import Meta.Ctx
open import Meta.PrimOp
open import Meta.IO
open import Meta.STLC

--------------------------------------------------------------------------------

private

  open import Data.Sum
  open import Data.Fin.Properties using ( opposite-involutive )

  variable
    n m : ℕ
    ctx : Ctx n
    ty  : Ty

  data LkpPrf (A : Set) (n : ℕ) (vec : Vec A n) (y : A) : Set where
    MkLkpPrf : (i : Fin n) -> Data.Vec.lookup vec i ≡ y -> LkpPrf A n vec y

  data VarPrf (n : ℕ) (ctx : Ctx n) (ty : Ty) : Set where
    MkVarPrf : (j : Fin n) -> lkpCtx ctx j ≡ ty -> VarPrf n ctx ty

  lkpToVar : LkpPrf Ty n ctx ty -> VarPrf n ctx ty
  lkpToVar {ctx = ctx} (MkLkpPrf i refl) =
    let eq = cong (lookup ctx) (opposite-involutive i)
    in  MkVarPrf (opposite i) (trans eq refl) 

  varToLkp : VarPrf n ctx ty -> LkpPrf Ty n ctx ty 
  varToLkp (MkVarPrf j refl) = MkLkpPrf (opposite j) refl

  insertLkp :  {A : Set} -> {n₁ n₂ : ℕ} -> (vec₁ : Vec A n₁) -> (vec₂ : Vec A n₂)
            -> (y u : A) -> LkpPrf A (n₁ + n₂) (vec₁ ++ vec₂) y -> LkpPrf A (n₁ + suc n₂) (vec₁ ++ u ∷ vec₂) y
  insertLkp {A = A} {n₁ = n₁} {n₂ = n₂} vec₁ vec₂ y u prf = go n₁ n₂ vec₁ vec₂ prf where
    go : (n m : ℕ) -> (vec₁ : Vec A n) -> (vec₂ : Vec A m) -> LkpPrf A (n + m) (vec₁ ++ vec₂) y -> LkpPrf A (n + suc m) (vec₁ ++ u ∷ vec₂) y
    go zero     m []         vec₂ (MkLkpPrf j         refl) = MkLkpPrf (fsuc j) refl
    go (suc n₁) m (s ∷ vec₁) vec₂ (MkLkpPrf fzero     refl) = MkLkpPrf fzero    refl
    go (suc n₁) m (s ∷ vec₁) vec₂ (MkLkpPrf (fsuc j₁) refl) with go n₁ m vec₁ vec₂ (MkLkpPrf j₁ refl)
    ...| MkLkpPrf k₁ eq = MkLkpPrf (fsuc k₁) eq

  insertVar :  {n₁ n₂ : ℕ} -> (ctx₁ : Ctx n₁) -> (ctx₂ : Ctx n₂)
            -> (u : Ty) -> VarPrf (n₁ + n₂) (ctx₁ ++ ctx₂) ty -> VarPrf (n₁ + suc n₂) (ctx₁ ++ u ∷ ctx₂) ty
  insertVar {ty = ty} {n₁ = n₁} {n₂ = n₂} ctx₁ ctx₂ u varprf = lkpToVar (insertLkp ctx₁ ctx₂ ty u (varToLkp varprf))

----------------------------------------

{-# TERMINATING #-}
insertIntoCtx :  {n₁ n₂ : ℕ} -> (ctx₁ : Ctx n₁) -> (ctx₂ : Ctx n₂)
              -> (u : Ty) -> LC (ctx₁ ++ ctx₂) ty -> LC (ctx₁ ++ u ∷ ctx₂) ty
insertIntoCtx {n₁ = n₁} {n₂ = n₂} ctx₁ ctx₂ u = go {ctx₁ = ctx₁} {ctx₂ = ctx₂} where

  go     : {n₁ n₂ : ℕ} -> {ctx₁ : Ctx n₁} -> {ctx₂ : Ctx n₂} ->          LC (ctx₁ ++ ctx₂)  ty -> LC          (ctx₁ ++ u ∷ ctx₂)  ty
  goIO   : {n₁ n₂ : ℕ} -> {ctx₁ : Ctx n₁} -> {ctx₂ : Ctx n₂} -> InOut   (LC (ctx₁ ++ ctx₂)) ty -> InOut   (LC (ctx₁ ++ u ∷ ctx₂)) ty 
  goPrim : {n₁ n₂ : ℕ} -> {ctx₁ : Ctx n₁} -> {ctx₂ : Ctx n₂} -> PrimOp  (LC (ctx₁ ++ ctx₂)) ty -> PrimOp  (LC (ctx₁ ++ u ∷ ctx₂)) ty

  go (App f x  )   = App (go f) (go x)
  go (Pri prim )   = Pri (goPrim prim)
  go (IOp xio  )   = IOp (goIO xio)
  go (Lit {eq = refl} y)   = Lit {eq = refl} y
  go (Log s x  )   = Log s (go x)
  go (Dbg s x y)   = Dbg s (go x) (go y)
  -- go (Fix f    )   = Fix (go f)

  go {ctx₁ = ctx₁} {ctx₂ = ctx₂} (Lam {s = s}     body) = Lam          (go {ctx₁ = s ∷ ctx₁} {ctx₂ = ctx₂} body)
  go {ctx₁ = ctx₁} {ctx₂ = ctx₂} (Let {s = s} rhs body) = Let (go rhs) (go {ctx₁ = s ∷ ctx₁} {ctx₂ = ctx₂} body)
  go {ctx₁ = ctx₁} {ctx₂ = ctx₂} (Rec {u = u} rhs body) = Rec (go {ctx₁ = u ∷ ctx₁} {ctx₂ = ctx₂} rhs) (go {ctx₁ = u ∷ ctx₁} {ctx₂ = ctx₂} body)
  go {ctx₁ = ctx₁} {ctx₂ = ctx₂} (Var j eq) with insertVar ctx₁ ctx₂ u (MkVarPrf j eq)
  ... | MkVarPrf j′ eq′ = Var j′ eq′ 

  goIO {ctx₁ = ctx₁} {ctx₂ = ctx₂} inout = mapInOut go inout

  goPrim {n₁ = n₁} {n₂ = n₂} {ctx₁ = ctx₁} {ctx₂ = ctx₂} prim =
    mapPrim {tm₁ = LC (ctx₁ ++ ctx₂)} {tm₂ = (LC (ctx₁ ++ u ∷ ctx₂))} go prim


inExtendedCtx  : (u : Ty) -> LC ctx ty -> LC (u ∷ ctx) ty 
inExtendedCtx {ctx = ctx} u = insertIntoCtx [] ctx u

inExtendedCtx2  : (u v : Ty) -> LC ctx ty -> LC (u ∷ v ∷ ctx) ty 
inExtendedCtx2 u v term = inExtendedCtx u (inExtendedCtx v term)

----------------------------------------

lastVar : {n : ℕ} -> {ctx : Ctx n} -> {s : Ty} -> LC (s ∷ ctx) s
lastVar {n = n} {ctx = ctx} {s = s} = Var (Data.Fin.fromℕ n) (lemma-lkp-last ctx s)

penultimateVar : {n : ℕ} -> {ctx : Ctx n} -> {s t : Ty} -> LC (s ∷ t ∷ ctx) t
penultimateVar {n = n} {ctx = ctx} {s = s} {t = t} = Var (inject₁ (Data.Fin.fromℕ n)) (lemma-lkp-penultimate ctx s t)

--------------------------------------------------------------------------------

-- fix unfix   ~>   letrec f = App unfix f in f
fixToLetRec : {n : ℕ} -> {ctx : Ctx n} -> {u : Ty} -> LC ctx (u ⇒ u) -> LC ctx u
fixToLetRec {n = n} {ctx = ctx} {u = u} unfix = Rec def body where

  def  : LC (u ∷ ctx) u
  def  = App (inExtendedCtx u unfix) lastVar

  body : LC (u ∷ ctx) u
  body = lastVar 

--------------------------------------------------------------------------------

private

  variable
    A : Set
    vec : Vec A n

  data LkpWhere (A : Set) (n₁ n₂ : ℕ) (vec₁ : Vec A n₁) (vec₂ : Vec A n₂) (u : A) (y : A) : Set where
    This  : u ≡ y              -> LkpWhere A n₁ n₂ vec₁ vec₂ u y
    Left  : LkpPrf A n₁ vec₁ y -> LkpWhere A n₁ n₂ vec₁ vec₂ u y
    Right : LkpPrf A n₂ vec₂ y -> LkpWhere A n₁ n₂ vec₁ vec₂ u y

  prependLkp : (u : A) -> {y : A} -> LkpPrf A n vec y -> LkpPrf A (suc n) (u ∷ vec) y
  prependLkp u (MkLkpPrf i refl) = MkLkpPrf (fsuc i) refl
  
  findWhere :  {n₁ n₂ : ℕ} -> (vec₁ : Vec A n₁) (vec₂ : Vec A n₂) -> (u y : A)
            -> LkpPrf A (n₁ + suc n₂) (vec₁ ++ u ∷ vec₂) y -> LkpWhere A n₁ n₂ vec₁ vec₂ u y
  findWhere {n₁ = zero  } {n₂ = _     } []               vec₂  u y (MkLkpPrf  fzero    refl) = This refl
  findWhere {n₁ = zero  } {n₂ = suc n′} []          (_ ∷ vec′) u y (MkLkpPrf (fsuc i′) refl) = Right (MkLkpPrf i′ refl)
  findWhere {n₁ = suc n′} {n₂ = n₂    } (_  ∷ vec′)      vec₂  u y (MkLkpPrf  fzero    refl) = Left  (MkLkpPrf fzero refl)
  findWhere {n₁ = suc n′} {n₂ = n₂    } (x₀ ∷ vec′)      vec₂  u y (MkLkpPrf (fsuc i′) eq  ) with findWhere {n₁ = n′} {n₂ = n₂} vec′ vec₂  u y (MkLkpPrf i′ eq)
  ... | This  eq  = This  eq
  ... | Left  prf = Left  (prependLkp x₀ prf)
  ... | Right prf = Right prf

  data VarWhere (n₁ n₂ : ℕ) (ctx₁ : Ctx n₁) (ctx₂ : Ctx n₂) (u ty : Ty) : Set where
    This′  : u ≡ ty            -> VarWhere n₁ n₂ ctx₁ ctx₂ u ty
    Left′  : VarPrf n₁ ctx₁ ty -> VarWhere n₁ n₂ ctx₁ ctx₂ u ty
    Right′ : VarPrf n₂ ctx₂ ty -> VarWhere n₁ n₂ ctx₁ ctx₂ u ty

{-
  findWhere′ : {n₁ n₂ : ℕ} -> (ctx₁ : Ctx n₁) (ctx₂ : Ctx n₂) -> (u ty : Ty)
            -> VarPrf (n₁ + suc n₂) (ctx₁ ++ u ∷ ctx₂) ty -> VarWhere n₁ n₂ ctx₁ ctx₂ u ty
  findWhere′ ctx₁ ctx₂ u ty varprf with (let prf = (varToLkp varprf) in findWhere ctx₂ ctx₁ u ty {!!})
  ... | This eq = This′ eq
-}


{-
{-# TERMINATING #-}
removeFromCtx :  {n₁ n₂ : ℕ} -> (ctx₁ : Ctx n₁) -> (ctx₂ : Ctx n₂)
              -> {u : Ty} -> LC ctx₂ u
              -> LC (ctx₁ ++ u ∷ ctx₂) ty -> LC (ctx₁ ++ ctx₂) ty
removeFromCtx {n₁ = n₁} {n₂ = n₂} ctx₁ ctx₂ {u = u} replaceBy = go {ctx₁ = ctx₁} {ctx₂ = ctx₂} where

  go     :  {ty : Ty} -> {n₁ n₂ : ℕ} -> {ctx₁ : Ctx n₁} -> {ctx₂ : Ctx n₂} ->          LC (ctx₁ ++ u ∷ ctx₂)  ty -> LC          (ctx₁ ++ ctx₂)  ty
  go {ty = ty} {n₁ = n₁} {n₂ = n₂} {ctx₁ = ctx₁} {ctx₂ = ctx₂} (Var j eq) with findWhere′ ctx₁ ctx₂ u ty (MkVarPrf j eq)
  ... | Left′ (MkVarPrf j′ eq′) = {!!}

substitute : {n₀ : ℕ} -> {ctx₀ : Ctx n₀} -> {s₀ t₀ : Ty} -> LC (s₀ ∷ ctx₀) t₀ -> LC ctx₀ s₀ -> LC ctx₀ t₀
substitute {n₀ = n₀} {ctx₀ = ctx₀} {s₀ = s₀} body what = removeFromCtx [] ctx₀ {s₀} what body
-}

----------------------------------------

{-
removeAppLam : LC ctx ty -> LC ctx ty
removeAppLam = go where
  go : {s : Ty} -> LC ctx s -> LC ctx s
  -- body : LC (s ∷ ctx) t
  -- arg  : s
  go (App {s = s} {t = t} (Lam body) arg) = substitute 
-}

--------------------------------------------------------------------------------
