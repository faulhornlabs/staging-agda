
-- convert HOAS to (well-typed) STLC and in the latter replace `IO a` with `RW ⇒ (a,RW)`

{-# OPTIONS --large-indices #-}
module IOTokenPassing where

----------------------------------------

open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable

open import Data.Empty
open import Data.Nat
open import Data.Nat.Properties using ( +-suc )
open import Data.Vec
open import Data.Vec.Properties using ( take++drop≡id )
open import Data.Fin using ( Fin ; opposite ; inject₁ ) renaming ( zero to fzero ; suc to fsuc )
open import Data.String using ( String )
open import Data.Maybe

----------------------------------------

data Ty : Set where
  Unit  : Ty
  Bool  : Ty
  Int   : Ty
  _⇒_   : Ty -> Ty -> Ty
  Pair  : Ty -> Ty -> Ty
  --
  IO    : Ty -> Ty        -- monadic IO
  Token : Ty              -- RealWorld token

infixr 30 _⇒_

----------------------------------------

private variable
  n : ℕ

data SemiDec (p : Set) : Set where
  STrue  : p -> SemiDec p
  SFalse : SemiDec p

tyEq     : (s t : Ty      ) -> SemiDec (s ≡ t)
tyVecEq  : (u v : Vec Ty n) -> SemiDec (u ≡ v)

tyEq = go where

  go : (s t : Ty) -> SemiDec (s ≡ t)
  go Unit  Unit  = STrue refl
  go Token Token = STrue refl
  go Int   Int   = STrue refl
  go Bool  Bool  = STrue refl

  go (IO s) (IO t) with go s t
  go (IO s) (IO t) | SFalse     = SFalse
  go (IO s) (IO t) | STrue refl = STrue refl
  
  go (s₁ ⇒ s₂) (t₁ ⇒ t₂) with go s₁ t₁
  go (s₁ ⇒ s₂) (t₁ ⇒ t₂) | SFalse = SFalse
  go (s₁ ⇒ s₂) (t₁ ⇒ t₂) | STrue refl with go s₂ t₂
  go (s₁ ⇒ s₂) (t₁ ⇒ t₂) | STrue refl | SFalse     = SFalse
  go (s₁ ⇒ s₂) (t₁ ⇒ t₂) | STrue refl | STrue refl = STrue refl

  go _ _ = SFalse

tyVecEq []       []       = STrue refl
tyVecEq (x ∷ xs) (y ∷ ys) with tyEq x y
tyVecEq (x ∷ xs) (y ∷ ys) | SFalse = SFalse
tyVecEq (x ∷ xs) (y ∷ ys) | STrue refl with tyVecEq xs ys
tyVecEq (x ∷ xs) (y ∷ ys) | STrue refl | SFalse     = SFalse
tyVecEq (x ∷ xs) (y ∷ ys) | STrue refl | STrue refl = STrue refl

----------------------------------------

Ctx : ℕ -> Set
Ctx n = Vec Ty n

lkpCtx : Ctx n -> Fin n -> Ty
lkpCtx ctx j = Data.Vec.lookup ctx (Data.Fin.opposite j)

data InCtx {n : ℕ} (ctx : Ctx n) : Set where
  MkInCtx : (j : Fin n) -> (ty : Ty) -> lkpCtx ctx j ≡ ty -> InCtx ctx

lkpInCtx : (ctx : Ctx n) -> Fin n -> InCtx ctx
lkpInCtx ctx j = MkInCtx j (lkpCtx ctx j) refl

natToFin : (n : ℕ) -> (k : ℕ) -> Maybe (Fin n)
natToFin zero     _        = nothing
natToFin (suc n₁) zero     = just fzero
natToFin (suc n₁) (suc k₁) with natToFin n₁ k₁
natToFin _        _        | nothing  = nothing
natToFin _        _        | just f₁  = just (fsuc f₁)

lkpCtxNatWithProof  : {n : ℕ} -> (ctx : Ctx n) -> (k : ℕ) -> Maybe (InCtx ctx)
lkpCtxNatWithProof {n} ctx k with natToFin n k
lkpCtxNatWithProof {n} ctx k | nothing = nothing
lkpCtxNatWithProof {n} ctx k | just f  = just (lkpInCtx ctx f)

----------------------------------------

variable
  s t : Ty
  ty  : Ty

-- high-level, monadic IO primitives
data XIO (tm : Ty -> Set) : Ty -> Set where
  Pure : tm t                       -> XIO tm t
  Bind : tm (IO s) -> tm (s ⇒ IO t) -> XIO tm t 
  Get  : String -> (t : Ty)         -> XIO tm t          
  Put  : String -> tm t             -> XIO tm Unit

-- primop-level, token-passing IO primitives
data Prim (tm : Ty -> Set) : Ty -> Set where
  Get′  : tm Token -> String -> (ty : Ty) -> Prim tm ty
  Put′  : tm Token -> String -> tm ty     -> Prim tm Unit

----------------------------------------

{-# NO_POSITIVITY_CHECK #-}
data Tm : (ty : Ty) -> Set where
  Lam : (Tm s -> Tm t) -> Tm (s ⇒ t)
  App : Tm (s ⇒ t) -> Tm s -> Tm t
  Let : Tm s -> (Tm s -> Tm t) -> Tm t
  IOp : XIO Tm ty -> Tm (IO ty)
  Tt  : Tm Unit
  Var : (s : Ty) -> (l : ℕ) -> Tm s        -- this is only for conversion to first order syntax

App2 : {s t u : Ty} -> Tm (s ⇒ t ⇒ u) -> Tm s -> Tm t -> Tm u
App2 f x y = App (App f x) y

----------------------------------------

private variable
  ctx : Ctx n

-- well-typed lambda calculus
data LC : Ctx n -> (ty : Ty) -> Set where
  Lam′ : {s t : Ty} -> LC (s ∷ ctx) t -> LC ctx (s ⇒ t)
  Let′ : LC ctx s -> LC (s ∷ ctx) t -> LC ctx t
  App′ : LC ctx (s ⇒ t) -> LC ctx s -> LC ctx t
  Pri′ : Prim (LC ctx) t -> LC ctx t
  IOp′ : XIO (LC ctx) t -> LC ctx (IO t)                     -- this will be eliminated
  Var′ : (j : Fin n) -> lkpCtx ctx j ≡ t -> LC {n} ctx t
  Tt′  : LC ctx Unit
  
App2′ : {s t u : Ty} -> LC ctx (s ⇒ t ⇒ u) -> LC ctx s -> LC ctx t -> LC ctx u
App2′ f x y = App′ (App′ f x) y

----------------------------------------

{-# TERMINATING #-}
convertToLC' : Tm ty -> Maybe (LC ctx ty)
convertToLC' = go where

  go   : {n : ℕ} -> {ctx : Ctx n} -> {ty : Ty} -> Tm ty     -> Maybe (LC ctx ty)
  goIO : {n : ℕ} -> {ctx : Ctx n} -> {ty : Ty} -> XIO Tm ty -> Maybe (XIO (LC ctx) ty)

  --------------------
  
  goIO (Pure what) = do
    what' <- go what
    just (Pure what')

  goIO (Bind action next) = do
    action' <- go action
    next'   <- go next
    just (Bind action' next')
    
  goIO (Put name what) = do
    what' <- go what
    just (Put name what')

  goIO (Get name ty) = do
    just (Get name ty)

  --------------------
  
  go {n} {ctx} (Var s k) = do
    MkInCtx j t refl <- lkpCtxNatWithProof ctx k
    case tyEq s t of λ where
      SFalse       -> nothing
      (STrue refl) -> just (Var′ j refl)

  go {n} {ctx} {s ⇒ t} (Lam f) = do
    body <- go (f (Var s n))
    just (Lam′ body)

  go {n} {ctx} (Let {s} rhs kont) = do
    rhs'  <- go rhs
    body' <- go (kont (Var s n))
    just (Let′ rhs' body')
    
  go (App f x) = do
    f' <- go f
    x' <- go x
    just (App′ f' x')

  go (IOp io) = do
   io' <- goIO io
   just (IOp′ io')
     
  go Tt  = just Tt′

convertToLC : Tm ty -> Maybe (LC [] ty)
convertToLC = convertToLC'

----------------------------------------

convTy : Ty -> Ty
convTy = go where
  go : Ty -> Ty
  go Unit       = Unit
  go Bool       = Bool
  go Int        = Int
  go (s ⇒ t)    = go s ⇒ go t
  go (Pair s t) = Pair (go s) (go t)
  go (IO t)     = Token ⇒ go t
  go Token      = Token

convCtx : Ctx n -> Ctx n
convCtx = Data.Vec.map convTy

----------------------------------------

private

  open import Data.Sum
  open import Data.Fin.Properties using ( opposite-involutive )

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

insertIntoCtx :  {n₁ n₂ : ℕ} -> (ctx₁ : Ctx n₁) -> (ctx₂ : Ctx n₂)
              -> (u : Ty) -> LC (ctx₁ ++ ctx₂) ty -> LC (ctx₁ ++ u ∷ ctx₂) ty
insertIntoCtx {n₁ = n₁} {n₂ = n₂} ctx₁ ctx₂ u = go {ctx₁ = ctx₁} {ctx₂ = ctx₂} where

  go     : {n₁ n₂ : ℕ} -> {ctx₁ : Ctx n₁} -> {ctx₂ : Ctx n₂} ->       LC (ctx₁ ++ ctx₂)  ty -> LC       (ctx₁ ++ u ∷ ctx₂)  ty
  goIO   : {n₁ n₂ : ℕ} -> {ctx₁ : Ctx n₁} -> {ctx₂ : Ctx n₂} -> XIO  (LC (ctx₁ ++ ctx₂)) ty -> XIO  (LC (ctx₁ ++ u ∷ ctx₂)) ty 
  goPrim : {n₁ n₂ : ℕ} -> {ctx₁ : Ctx n₁} -> {ctx₂ : Ctx n₂} -> Prim (LC (ctx₁ ++ ctx₂)) ty -> Prim (LC (ctx₁ ++ u ∷ ctx₂)) ty

  go Tt′            = Tt′
  go (App′ f x  )   = App′ (go f) (go x)
  go (Pri′ prim )   = Pri′ (goPrim prim)
  go (IOp′ xio  )   = IOp′ (goIO xio)
  go {ctx₁ = ctx₁} {ctx₂ = ctx₂} (Lam′ {s = s}     body) = Lam′          (go {ctx₁ = s ∷ ctx₁} {ctx₂ = ctx₂} body)
  go {ctx₁ = ctx₁} {ctx₂ = ctx₂} (Let′ {s = s} rhs body) = Let′ (go rhs) (go {ctx₁ = s ∷ ctx₁} {ctx₂ = ctx₂} body)
  go {ctx₁ = ctx₁} {ctx₂ = ctx₂} (Var′ j eq) with insertVar ctx₁ ctx₂ u (MkVarPrf j eq)
  ... | MkVarPrf j′ eq′ = Var′ j′ eq′ 

  goIO (Pure what)     = Pure (go what)
  goIO (Bind u h)      = Bind (go u) (go h)
  goIO (Get name ty  ) = Get name ty
  goIO (Put name what) = Put name (go what)

  goPrim (Get′ tok name ty  ) = Get′ (go tok) name ty
  goPrim (Put′ tok name what) = Put′ (go tok) name (go what)

inExtendedCtx  : (u : Ty) -> LC ctx ty -> LC (u ∷ ctx) ty 
inExtendedCtx {ctx = ctx} u = insertIntoCtx [] ctx u

inExtendedCtx2  : (u v : Ty) -> LC ctx ty -> LC (u ∷ v ∷ ctx) ty 
inExtendedCtx2 u v term = inExtendedCtx u (inExtendedCtx v term)

----------------------------------------

private

  import Data.Vec.Properties

  lemma-lkp-map : {ctx : Ctx n} -> (j : Fin n) -> lkpCtx (convCtx ctx) j ≡ convTy (lkpCtx ctx j)
  lemma-lkp-map {ctx = ctx} j = Data.Vec.Properties.lookup-map (opposite j) convTy ctx

  lemma-opposite-n : (n : ℕ) -> opposite (Data.Fin.fromℕ n) ≡ fzero
  lemma-opposite-n zero     = refl
  lemma-opposite-n (suc n₁) = cong inject₁ (lemma-opposite-n n₁)  

  lemma-lkp-first : {A : Set} -> (vec : Vec A n) -> (s : A) -> lookup (s ∷ vec) fzero ≡ s
  lemma-lkp-first vec s = refl
  
  lemma-lkp-last : {n : ℕ} -> (ctx : Ctx n) -> (s : Ty) -> lkpCtx (s ∷ ctx) (Data.Fin.fromℕ n) ≡ s
  lemma-lkp-last {n = n} ctx s with lemma-lkp-first ctx s
  ... | eq rewrite (lemma-opposite-n n) = refl

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

  lastVar : {n : ℕ} -> {ctx : Ctx n} -> {s : Ty} -> LC (s ∷ ctx) s
  lastVar {n = n} {ctx = ctx} {s = s} = Var′ (Data.Fin.fromℕ n) (lemma-lkp-last ctx s)

  penultimateVar : {n : ℕ} -> {ctx : Ctx n} -> {s t : Ty} -> LC (s ∷ t ∷ ctx) t
  penultimateVar {n = n} {ctx = ctx} {s = s} {t = t} = Var′ (inject₁ (Data.Fin.fromℕ n)) (lemma-lkp-penultimate ctx s t)

convLC : {ctx : Ctx n} -> {ty : Ty} -> LC ctx ty -> LC (convCtx ctx) (convTy ty)
convLC = go where

  go     : {n : ℕ} -> {ctx : Ctx n} -> {ty : Ty} ->       LC ctx ty  ->       LC (convCtx ctx)  (convTy ty)
  goIO   : {n : ℕ} -> {ctx : Ctx n} -> {ty : Ty} -> XIO  (LC ctx) ty ->       LC (convCtx ctx)  (Token ⇒ convTy ty)
  goPrim : {n : ℕ} -> {ctx : Ctx n} -> {ty : Ty} -> Prim (LC ctx) ty -> Prim (LC (convCtx ctx)) (convTy ty)

  go              Tt′            = Tt′
  go             (Lam′ body    ) = Lam′ (go body)
  go             (Let′ rhs body) = Let′ (go rhs) (go body)
  go             (App′ f x     ) = App′ (go f) (go x)
  go             (Pri′ prim    ) = Pri′ (goPrim prim)
  go {ctx = ctx} (Var′ j refl  ) = Var′ j (lemma-lkp-map {ctx = ctx} j)
  go             (IOp′ xio     ) = goIO xio

  -- this is only here so that Agda does not complain
  goPrim (Get′ rw name ty  ) = Get′ (go rw) name (convTy ty)
  goPrim (Put′ rw name what) = Put′ (go rw) name (go what)

  goIO         (Pure x    ) = Lam′ {s = Token} (inExtendedCtx Token (go x))

  -- u : IO A          ~>     u' : Token -> A'
  -- h : A -> IO B     ~>     h' : A' -> (Token -> B')
  -- bind u h          ~>     bind' u' h' = \rw -> let x = u' rw in h' x rw
  
  goIO {n = n} {ctx = ctx} (Bind {s = A} {t = B} u h) =
    let rw  = lastVar            -- the variable bound by the lambda constructor of the type (Token -> A')
        rw₂ = penultimateVar     -- same as `rw` but in a different context
        x'  = Var′ (Data.Fin.fromℕ (suc n)) (lemma-lkp-last (Token ∷ convCtx ctx) (convTy A))
    in  Lam′ {s = Token} $
          Let′ {s = convTy A}
            (App′  (inExtendedCtx             Token (go u))    rw )
            (App2′ (inExtendedCtx2 (convTy A) Token (go h)) x' rw₂)

  goIO {n = n} {ctx = ctx} (Put name x) =
    let rw = lastVar 
        x' = inExtendedCtx Token (go x)
    in  Lam′ {s = Token} (Pri′ (Put′ rw name x'))

  goIO {n = n} {ctx = ctx} (Get name t) =
     let rw = lastVar
     in  Lam′ {s = Token} (Pri′ (Get′ rw name (convTy t)))

--------------------------------------------------------------------------------
