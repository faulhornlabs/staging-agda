
-- Context manipulation

module Meta.CtxLemmas where

--------------------------------------------------------------------------------

open import Function
open import Relation.Binary.PropositionalEquality

-- open import Data.Empty
open import Data.Nat
open import Data.Nat.Properties using ( +-suc )
open import Data.Vec
open import Data.Vec.Properties using ( take++drop≡id )
open import Data.Fin using ( Fin ; opposite ; inject₁ ) renaming ( zero to fzero ; suc to fsuc )
--open import Data.String using ( String )

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
{-
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
-}

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
  
{-
  goIO (Pure′ what)     = Pure′ (go what)
  goIO (Bind′ u h)      = Bind′ (go u) (go h)
  goIO (Get′ name ty  ) = Get′ name ty
  goIO (Put′ name what) = Put′ name (go what)
-}

  goPrim {n₁ = n₁} {n₂ = n₂} {ctx₁ = ctx₁} {ctx₂ = ctx₂} prim =
    mapPrim {tm₁ = LC (ctx₁ ++ ctx₂)} {tm₂ = (LC (ctx₁ ++ u ∷ ctx₂))} go prim

{-
  goPrim (PrimGet tok name ty  ) = PrimGet (go tok) name ty
  goPrim (PrimPut tok name what) = PrimPut (go tok) name (go what)
-}

inExtendedCtx  : (u : Ty) -> LC ctx ty -> LC (u ∷ ctx) ty 
inExtendedCtx {ctx = ctx} u = insertIntoCtx [] ctx u

inExtendedCtx2  : (u v : Ty) -> LC ctx ty -> LC (u ∷ v ∷ ctx) ty 
inExtendedCtx2 u v term = inExtendedCtx u (inExtendedCtx v term)

----------------------------------------

private

  import Data.Vec.Properties
  lemma-opposite-n : (n : ℕ) -> opposite (Data.Fin.fromℕ n) ≡ fzero
  lemma-opposite-n zero     = refl
  lemma-opposite-n (suc n₁) = cong inject₁ (lemma-opposite-n n₁)  

lemma-lkp-first : {A : Set} -> (vec : Vec A n) -> (s : A) -> lookup (s ∷ vec) fzero ≡ s
lemma-lkp-first vec s = refl
  
lemma-lkp-last : {n : ℕ} -> (ctx : Ctx n) -> (s : Ty) -> lkpCtx (s ∷ ctx) (Data.Fin.fromℕ n) ≡ s
lemma-lkp-last {n = n} ctx s with lemma-lkp-first ctx s
... | eq rewrite (lemma-opposite-n n) = refl

private

  lemma-opposite-inject₁ : (k : Fin n) -> opposite (inject₁ k) ≡ fsuc (opposite k)
  lemma-opposite-inject₁ fzero     = refl
  lemma-opposite-inject₁ (fsuc k₁) = let eq = lemma-opposite-inject₁ k₁ in cong inject₁ eq 

  lemma-lkp-fsuc : {A : Set} -> (vec : Vec A n) -> (s : A) -> (k : Fin n) -> lookup vec k ≡ lookup (s ∷ vec) (fsuc k)
  lemma-lkp-fsuc vec s k = refl

  lemma-lkp-penultimate′ : {n : ℕ} -> (ctx : Ctx n) -> (s t : Ty) -> lookup (s ∷ t ∷ ctx) (fsuc fzero) ≡ t
  lemma-lkp-penultimate′ ctx s t = lemma-lkp-fsuc (t ∷ ctx) s fzero

  lemma-lkp-map-idx : {ctx : Ctx n} -> {j k : Fin n} -> (j ≡ k) -> lookup ctx j ≡ lookup ctx k 
  lemma-lkp-map-idx refl = refl
  
  lemma-lkp-penultimate : {n : ℕ} -> (ctx : Ctx n) -> (s t : Ty) -> lkpCtx (s ∷ t ∷ ctx) (inject₁ (Data.Fin.fromℕ n)) ≡ t
  lemma-lkp-penultimate {n = n} ctx s t =
    let eq = lemma-lkp-map-idx {ctx = s ∷ t ∷ ctx} (lemma-opposite-inject₁ (Data.Fin.fromℕ n))
    in  trans eq (lemma-lkp-last ctx t)

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
