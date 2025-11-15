
-- Conversion from second order HOAS terms to standard first order STLC terms

{-# OPTIONS --type-in-type #-}
{-# OPTIONS --show-implicit #-}

module Meta.Convert where

--------------------------------------------------------------------------------

open import Data.Bool using ( Bool ; true ; false )
open import Data.Nat using ( ℕ ; zero ; suc )
open import Data.Fin using ( Fin ; cast ; inject₁ ; opposite ) renaming ( zero to fzero ; suc to fsuc )
open import Data.Vec
open import Data.Maybe

open import Function
open import Relation.Binary.PropositionalEquality

{-
open import Data.Word64 using ( Word64 ; fromℕ ) 
open import Data.Product using ( _×_ ; _,′_ )
-}

open import Meta.Ty
open import Meta.Ctx
open import Meta.CtxLemmas using ( fixToLetRec )
open import Meta.Val
open import Meta.PrimOp
open import Meta.IO

open import Meta.HOAS using ( Tm )
open import Meta.STLC using ( LC )

import Meta.HOAS as HOAS
import Meta.STLC as STLC

--------------------------------------------------------------------------------

private variable
  s t : Ty
  n   : ℕ
  ctx : Ctx n
  ty  : Ty

--------------------------------------------------------------------------------

{-# TERMINATING #-}
convert' : Tm ty -> Maybe (LC ctx ty)
convert' = go where

  go   : {n : ℕ} -> {ctx : Ctx n} -> {ty : Ty} -> Tm ty       -> Maybe (LC ctx ty)
  goIO : {n : ℕ} -> {ctx : Ctx n} -> {ty : Ty} -> InOut Tm ty -> Maybe (InOut (LC ctx) ty)    -- InOut′ LC ctx ty)

  --------------------

  goIO {ctx = ctx} what = mapMaybeInOut go what 
  
{-  
  goIO {n} {ctx} (Pure what) = do
    what' <- go what
    just (Pure′ what')

  goIO {n} {ctx} (Bind {s = s} action next) = do
    action' <- go action
    next'   <- go (HOAS.App next (HOAS.Var s n))
    just (Bind′ action' next')

  goIO {n} {ctx} (Get name ty) = do
    just (Get′ name ty)

  goIO {n} {ctx} (Put {ty} name what) = do
    what' <- go what
    just (Put′ name what')
-}

  --------------------

  -- eliminate `App Lam`
  go (HOAS.App (HOAS.Lam f) x) = go (f x)     
  
  go (HOAS.IOp io) = do
   io' <- goIO io
   just (STLC.IOp io')
  
  go {n} {ctx} (HOAS.Var s k) = do
    MkInCtx j t refl <- lkpCtxNatWithProof ctx k
    case tyEq s t of λ where
      SFalse       -> nothing
      (STrue refl) -> just (STLC.Var j refl)

  go {n} {ctx} {s ⇒ t} (HOAS.Lam f) = do
    body <- go (f (HOAS.Var s n))
    just (STLC.Lam body)

  go {n} {ctx} (HOAS.Let {s} rhs kont) = do
    rhs'  <- go rhs
    body' <- go (kont (HOAS.Var s n))
    just (STLC.Let rhs' body')
    
  go (HOAS.App f x) = do
    f' <- go f
    x' <- go x
    just (STLC.App f' x')

  go (HOAS.Lit {eq = refl} v) = just (STLC.Lit {eq = refl} v)

  go (HOAS.Pri prim) = do
    prim' <- mapMaybePrim go prim
    just (STLC.Pri prim')
     
  go (HOAS.Fix f) = do
    f' <- go f
    just (fixToLetRec f')
    -- just (STLC.Fix f')

  go (HOAS.Log n x) = do
    x' <- go x
    just (STLC.Log n x')

  go (HOAS.Dbg n x y) = do
    x' <- go x
    y' <- go y
    just (STLC.Dbg n x' y')
  
      
convert : Tm ty -> Maybe (LC [] ty)
convert = convert'

--------------------------------------------------------------------------------

{-

private

  tm-sub₂ : {s t : Ty} -> (s ≡ t) -> LC ctx s -> LC ctx t
  tm-sub₂ refl tm = tm

  lemma₁ : (n : ℕ) -> opposite (Data.Fin.fromℕ n) ≡ fzero
  lemma₁ zero     = refl
  lemma₁ (suc n₁) = cong inject₁ (lemma₁ n₁) 

  lemma₂ : {n : ℕ} -> (u : Ty) -> (ctx : Ctx n) -> lkpCtx (u ∷ ctx) (Data.Fin.fromℕ n) ≡ u
  lemma₂ {n} u ctx = lookup-sub₂ (u ∷ ctx) (lemma₁ n)

  mkVar₊₁ : (u : Ty) -> (ctx : Ctx n) -> LC (u ∷ ctx) u
  mkVar₊₁ u ctx = tm-sub₂ (lemma₂ u ctx) (Var (opposite fzero))

-}

--------------------------------------------------------------------------------
