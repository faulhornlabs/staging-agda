{-# OPTIONS --type-in-type #-}
{-# OPTIONS --show-implicit #-}

module Meta.STLC where

--------------------------------------------------------------------------------

open import Data.Bool using ( Bool ; true ; false )
open import Data.Nat using ( ℕ ; zero ; suc  )
open import Data.Fin using ( Fin ; fromℕ ; opposite ; cast ; inject₁ ) renaming ( zero to fzero ; suc to fsuc )
open import Data.Vec using ( Vec ; _∷_ ; [] ; lookup )
open import Data.String
open import Data.Maybe

open import Relation.Binary.PropositionalEquality

open import Meta.Ty
open import Meta.Ctx
open import Meta.Val
open import Meta.PrimOp
open import Meta.IO

--------------------------------------------------------------------------------

private variable
  ty  : Ty
  s t : Ty
  u v : Ty
  n   : ℕ
  ts  : Vec Ty n
  ctx : Ctx n

-- well-typed lambda calculus
data LC : Ctx n -> (ty : Ty) -> Set where
  App : LC ctx (s ⇒ t) -> LC ctx s -> LC ctx t
  Lam : LC (s ∷ ctx) t -> LC ctx (s ⇒ t)
  Let : LC      ctx  s -> LC (s ∷ ctx) t -> LC ctx t
  Rec : LC (u ∷ ctx) u -> LC (u ∷ ctx) t -> LC ctx t      -- letrec
  Pri : PrimOp (LC ctx) t -> LC ctx t
  Lit : {t′ : VTy} -> {eq : vtyToTy t′ ≡ t} -> Val′ t′ -> LC ctx t
  Var : (j : Fin n) -> lkpCtx ctx j ≡ t -> LC {n} ctx t
  Log : String -> LC ctx t -> LC ctx t
  Dbg : String -> LC ctx s -> LC ctx t -> LC ctx t

{-
  Fix : LC ctx ((s ⇒ t) ⇒ (s ⇒ t)) -> LC ctx (s ⇒ t)     -- eliminated into `letrec`
  Lit : Val t -> LC ctx t                                 -- needed a more complex Lit
  IOp : InOut′ LC ctx t -> LC ctx (IO t)                  -- needed a simpler IO (temporarily, it will turned into token passing)
-}

--------------------------------------------------------------------------------

App2 : LC ctx (s ⇒ t ⇒ u) -> LC ctx s -> LC ctx t -> LC ctx u
App2 f x y = App (App f x) y

App3 : LC ctx (s ⇒ t ⇒ u ⇒ v) -> LC ctx s -> LC ctx t -> LC ctx u -> LC ctx v
App3 f x y z = App (App (App f x) y) z

--------------------------------------------------------------------------------
