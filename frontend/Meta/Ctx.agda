
{-# OPTIONS --type-in-type #-}
module Meta.Ctx where

--------------------------------------------------------------------------------

open import Data.Nat
open import Data.Vec
open import Data.String using ( String ; _++_ )
open import Data.Fin using ( Fin ; zero ; suc ;  opposite ; inject₁ )
open import Data.Maybe

open import Relation.Binary.PropositionalEquality

open import Meta.Ty
open import Meta.FinVec

--------------------------------------------------------------------------------

private variable
  n : ℕ

Ctx : ℕ -> Set
Ctx n = Vec Ty n

-- note: we use de Bruijn *levels* for indexing,
-- so we have to use `Fin.opposite` for lookup up!
--
lkpCtx : Ctx n -> Fin n -> Ty
lkpCtx = lkpOppo
-- lkpCtx ctx j = Data.Vec.lookup ctx (Data.Fin.opposite j)

lkpCtx₁ : (s : Ty) -> Ctx n -> Fin n -> Ty
lkpCtx₁ = lkpOppo₁
-- lkpCtx₁ s ctx j = lkpCtx (s ∷ ctx) (inject₁ j)

--------------------------------------------------------------------------------

data InCtx {n : ℕ} (ctx : Ctx n) : Set where
  MkInCtx : (j : Fin n) -> (ty : Ty) -> lkpCtx ctx j ≡ ty -> InCtx ctx

lkpInCtx : (ctx : Ctx n) -> Fin n -> InCtx ctx
lkpInCtx ctx j = MkInCtx j (lkpCtx ctx j) refl

lkpCtxNatWithProof  : {n : ℕ} -> (ctx : Ctx n) -> (k : ℕ) -> Maybe (InCtx ctx)
lkpCtxNatWithProof {n} ctx k with natToFin n k
lkpCtxNatWithProof {n} ctx k | nothing = nothing
lkpCtxNatWithProof {n} ctx k | just f  = just (lkpInCtx ctx f)

--------------------------------------------------------------------------------

{-
thm-lkp-extended-ctx : {n : ℕ} -> {ctx : Ctx n} -> (s : Ty) -> (j : Fin n) -> lkpCtx ctx j ≡ lkpCtx (s ∷ ctx) (inject₁ j)
thm-lkp-extended-ctx {n} {ctx} s j = sym (trans eq₂ fact) where

  fact : Data.Vec.lookup (s ∷ ctx) (suc (opposite j)) ≡ Data.Vec.lookup ctx (opposite j) 
  fact = fact-lookup-suc {Ty} {n} {s} {ctx} (opposite j)

  eq₁ : opposite (inject₁ j) ≡ suc (opposite j)
  eq₁ = thm-opposite-inject₁ j

  eq₂ : Data.Vec.lookup (s ∷ ctx) (opposite (inject₁ j)) ≡ Data.Vec.lookup (s ∷ ctx) (suc (opposite j))
  eq₂ = cong (Data.Vec.lookup (s ∷ ctx)) eq₁
-}

--------------------------------------------------------------------------------

 
