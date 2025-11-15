
{-# OPTIONS --type-in-type #-}
{-# OPTIONS --show-implicit #-}

module Meta.HOAS where

--------------------------------------------------------------------------------

open import Function

open import Data.Bool using ( Bool ; true ; false )
open import Data.Nat using ( ℕ ; zero ; suc )
open import Data.Fin using ( Fin ; cast ; inject₁ )
open import Data.Vec
open import Data.Word64 using ( Word64 ; fromℕ ) 
open import Data.String

open import Relation.Binary.PropositionalEquality

open import Meta.Ty
open import Meta.Ctx
open import Meta.Val
open import Meta.IO
open import Meta.PrimOp
  
--------------------------------------------------------------------------------

private variable
  ty  : Ty
  s t : Ty
  u v w : Ty
  n   : ℕ
  ts  : Vec Ty n
  ctx : Ctx n
  
{-# NO_POSITIVITY_CHECK #-}
data Tm : (ty : Ty) -> Set where
  Lam : (Tm s -> Tm t) -> Tm (s ⇒ t)
  Let : Tm s -> (Tm s -> Tm t) -> Tm t
  App : Tm (s ⇒ t) -> Tm s -> Tm t
  Fix : Tm ((s ⇒ t) ⇒ (s ⇒ t)) -> Tm (s ⇒ t)
  Pri : PrimOp Tm t -> Tm t
  --  IOs : Tm (Token ⇒ Pair t Token) -> Tm (IO t)
  IOp : InOut Tm t -> Tm (IO t)
  Lit : {t′ : VTy} -> {eq : vtyToTy t′ ≡ t} -> Val′ t′ -> Tm t
  Var : (s : Ty) -> (l : ℕ) -> Tm s        -- this is only for conversion to first order syntax
  Log : String -> Tm t -> Tm t             -- this is a hack to be able give names to subexpressions
  Dbg : String -> Tm s -> Tm t -> Tm t     -- printf debugging hack

--------------------------------------------------------------------------------

{-
data TmIO (ty : Ty) : Set where
  MkTmIO : (Tm Token -> Tm (Pair ty Token)) -> TmIO ty

runTmIO : TmIO ty -> Tm Token -> Tm (Pair ty Token)
runTmIO (MkTmIO f) = f

private
  mkPair : Tm s -> Tm t -> Tm (Pair s t)
  mkPair x y = Pri (MkPair x y)

  fst : Tm (Pair s t) -> Tm s
  fst x  = Pri (Fst x)

  snd : Tm (Pair s t) -> Tm t
  snd x  = Pri (Snd x)

pureTmIO : Tm t -> TmIO t
pureTmIO what = MkTmIO \rwt -> mkPair what rwt

bindTmIO : TmIO s -> (Tm s -> TmIO t) -> TmIO t
bindTmIO (MkTmIO u) h = MkTmIO $ \rwt -> Let (u rwt) \pair -> runTmIO (h (fst pair)) (snd pair)
-}

--------------------------------------------------------------------------------

Lam2 : (Tm s -> Tm t -> Tm u) -> Tm (s ⇒ t ⇒ u)
Lam2 f = Lam \x -> Lam \y -> f x y

Lam3 : (Tm s -> Tm t -> Tm u -> Tm v) -> Tm (s ⇒ t ⇒ u ⇒ v)
Lam3 f = Lam \x -> Lam \y -> Lam \z -> f x y z

Lam4 : (Tm s -> Tm t -> Tm u -> Tm v -> Tm w) -> Tm (s ⇒ t ⇒ u ⇒ v ⇒ w)
Lam4 f = Lam \x -> Lam \y -> Lam \z -> Lam \w -> f x y z w

App2 : Tm (s ⇒ t ⇒ u) -> Tm s -> Tm t -> Tm u
App2 f x y = App (App f x) y

App3 : Tm (s ⇒ t ⇒ u ⇒ v) -> Tm s -> Tm t -> Tm u -> Tm v
App3 f x y z = App (App (App f x) y) z

App4 : Tm (s ⇒ t ⇒ u ⇒ v ⇒ w) -> Tm s -> Tm t -> Tm u -> Tm v -> Tm w
App4 f x y z w = App (App (App (App f x) y) z) w

--------------------------------------------------------------------------------

{-
  Decl : (s : Ty) -> (Tm s -> Tm t) -> Tm t
  Def  : (name : Tm s) -> (def : Tm s) -> Tm t -> Tm t            

Fix1 : {s : Ty} -> Tm (s ⇒ s) -> Tm s
Fix1 {s} u = Decl s \f -> Def f (App u f) f

Fix2' : {a b : Ty} -> Tm (a ⇒ b ⇒ a) -> Tm (a ⇒ b ⇒ b) -> Tm a × Tm b

Fix2'' : {a b : Ty} -> Tm (a ⇒ b ⇒ a) -> Tm (a ⇒ b ⇒ b) -> (Tm a -> Tm b -> Tm c) -> Tm c
Fix2'' {a} {b} f g h = Decl a \a' -> Decl b \b' -> Def a' (App2 f a' b') $ Def b' (App2 g a' b') $ h a' b'
-}

--------------------------------------------------------------------------------

