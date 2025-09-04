{-# OPTIONS --type-in-type #-}
{-# OPTIONS --show-implicit #-}

module Meta.STLC where

--------------------------------------------------------------------------------

open import Data.Bool using ( Bool ; true ; false )
open import Data.Nat using ( ℕ ; zero ; suc  )
open import Data.Fin using ( Fin ; fromℕ ; opposite ; cast )
open import Data.Vec using ( Vec ; _∷_ ; [] ; lookup )
open import Data.String

open import Relation.Binary.PropositionalEquality

open import Meta.Ty
open import Meta.Ctx
open import Meta.Val
open import Meta.PrimOp
open import Meta.IO

--------------------------------------------------------------------------------

private variable
  s t : Ty
  n   : ℕ
  ts  : Vec Ty n
  ctx : Ctx n

-- well-typed lambda calculus
data LC : Ctx n -> (ty : Ty) -> Set where
  Lam : LC (s ∷ ctx) t -> LC ctx (s ⇒ t)
  Let : LC ctx s -> LC (s ∷ ctx) t -> LC ctx t
  App : LC ctx (s ⇒ t) -> LC ctx s -> LC ctx t
  Fix : LC ctx ((s ⇒ t) ⇒ (s ⇒ t)) -> LC ctx (s ⇒ t)
  Pri : PrimOp (LC ctx) t -> LC ctx t
  IOp : InOut′ LC ctx -> LC ctx IO
  Lit : Val t -> LC ctx t
  Var : (j : Fin n) -> lkpCtx ctx j ≡ t -> LC {n} ctx t
  Log : String -> LC ctx t -> LC ctx t
  
--------------------------------------------------------------------------------
