{-# OPTIONS --type-in-type #-}

module Meta.Export where

--------------------------------------------------------------------------------

open import Data.Bool using ( Bool ; true ; false )
open import Data.Nat  using ( ℕ ; zero ; suc  )
open import Data.Fin  using ( Fin ; fromℕ ; opposite ; cast ; toℕ )
open import Data.Vec  using ( Vec ; _∷_ ; [] ; lookup )
open import Data.List using ( List ; _∷_ ; [] )
open import Data.Product using ( _×_ ; _,_ )
open import Data.String using ( String ; _++_ )
open import Data.Word64
open import Data.Maybe

open import Meta.Ty
open import Meta.Ctx
open import Meta.PrimOp
open import Meta.IO
open import Meta.HList
open import Meta.Show

import Meta.Val     as TVal
import Meta.STLC    as STLC
import Meta.HOAS    as HOAS
import Meta.Convert as Conv

--------------------------------------------------------------------------------

private variable
  s t : Ty
  n   : ℕ
  ctx : Ctx n

--------------------------------------------------------------------------------

data RVal : Set where
  TtV     :                   RVal
  BitV    : Bool           -> RVal
  U64V    : Word64         -> RVal
  NatV    : ℕ              -> RVal
  StructV : List RVal      -> RVal
  WrapV   : String -> RVal -> RVal

----------------------------------------

valForget : TVal.Val t -> RVal
valForget = go where

  {-# NON_COVERING #-}
  go : {ty : Ty} -> TVal.Val ty -> RVal
  goList : {ts : Vec Ty n} -> HList TVal.Val ts -> List RVal

  go TVal.TtV          = TtV
  go (TVal.BitV b)     = BitV b
  go (TVal.U64V u)     = U64V u
  go (TVal.NatV n)     = NatV n
  go (TVal.StructV xs) = StructV (goList xs)
  go (TVal.WrapV {t} {nam} v)  = WrapV nam (go v)
  -- go (TVal.Fun fun)   = {!!}
  -- go (TVal.ArrayV xs)  = {!!}

  goList Nil = []
  goList (Cons x xs) = go x ∷ goList xs

----------------------------------------

{-# TERMINATING #-}
showRValPrec : ℕ -> RVal -> String
showRValPrec = go where

  go : ℕ -> RVal -> String
  go d  TtV         = "TtV"
  go d (BitV b)     = showParen (d >ᵇ appPrec) ("BitV " ++ showBoolHs b)
  go d (U64V w    ) = showParen (d >ᵇ appPrec) ("U64V " ++ showWord64 w)
  go d (NatV n    ) = showParen (d >ᵇ appPrec) ("NatV " ++ showNat    n)
  go d (WrapV n v)  = showParen (d >ᵇ appPrec) ("WrapV " ++ showString n ++ " " ++ go appPrec₊₁ v)
  go d (StructV xs) = showParen (d >ᵇ appPrec) ("StructV " ++ showList (go 0) xs)

{-
  -- just testing the termination checker
  goList : List RVal -> String
  goList [] = "[]"
  goList ys = "[ " ++ worker ys where
    worker : List RVal -> String
    worker []       = " ]"
    worker (x ∷ []) = go 0 x ++ " ]"
    worker (x ∷ xs) = go 0 x ++ ", " ++ worker xs
-}

showRVal : RVal -> String
showRVal = showRValPrec 0

--------------------------------------------------------------------------------

data Raw : Set where
  Dum : Raw                  -- dummy
  App : Raw -> Raw -> Raw
  Lam : Ty -> Raw -> Raw
  Let : Ty -> Raw -> Raw -> Raw
  Rec : Ty -> Raw -> Raw -> Raw
  Pri : RawPrim -> List Raw -> Raw
  Lit : RVal -> Raw
  Var : (j : ℕ) -> Raw
  Log : String -> Raw -> Raw
  Dbg : String -> Ty -> Raw -> Raw -> Raw
  
{-# TERMINATING #-}
convertToRaw : STLC.LC ctx t -> Raw 
convertToRaw = go where

  go : {n : ℕ} -> {ctx : Ctx n} -> {ty : Ty} -> STLC.LC ctx ty -> Raw
  go (STLC.Lam {s = s} body    )   = Lam s (go body)
  go (STLC.Let {s = s} rhs body)   = Let s (go rhs) (go body)
  go (STLC.Rec {u = u} rhs body)   = Rec u (go rhs) (go body)
  go (STLC.App         fun arg )   = App (go fun) (go arg)
  go (STLC.Var         j   _   )   = Var (Data.Fin.toℕ j)
  go (STLC.Lit         lit     )   = Lit (valForget (TVal.literalToVal lit))
  go (STLC.Pri         pri     )   = let raw , list = primOpForget go pri in Pri raw list
  go (STLC.Log         nam body)   = Log nam (go body)
  go (STLC.Dbg {s = s} nam x y )   = Dbg nam s (go x) (go y)
  
--------------------------------------------------------------------------------

{-# TERMINATING #-}
showRawPrec : ℕ -> Raw -> String
showRawPrec = go where

  go : ℕ -> Raw -> String
  go d (Dum            ) = "Dummy"
  go d (Lam ty body    ) = showParen (d >ᵇ appPrec) ("Lam " ++ showTyPrec appPrec₊₁ ty ++ " " ++ go appPrec₊₁ body)
  go d (Let ty rhs body) = showParen (d >ᵇ appPrec) ("Let " ++ showTyPrec appPrec₊₁ ty ++ " " ++ go appPrec₊₁ rhs ++ " " ++ go appPrec₊₁ body)
  go d (Rec ty rhs body) = showParen (d >ᵇ appPrec) ("Rec " ++ showTyPrec appPrec₊₁ ty ++ " " ++ go appPrec₊₁ rhs ++ " " ++ go appPrec₊₁ body)
  go d (App fun arg)     = showParen (d >ᵇ appPrec) ("App " ++ go appPrec₊₁ fun ++ " " ++ go appPrec₊₁ arg)
  go d (Lit lit)         = showParen (d >ᵇ appPrec) ("Lit " ++ showRValPrec appPrec₊₁ lit)
  go d (Var j)           = showParen (d >ᵇ appPrec) ("Var " ++ showNat j)
  go d (Pri raw args)    = showParen (d >ᵇ appPrec) ("Pri " ++ showRawPrimPrec appPrec₊₁ raw ++ " " ++ showList (go 0) args)
  go d (Log name body)   = showParen (d >ᵇ appPrec) ("Log " ++ showString name ++ " " ++ go appPrec₊₁ body)
  go d (Dbg name ty x y) = showParen (d >ᵇ appPrec) ("Dbg " ++ showString name ++ " " ++ showTyPrec appPrec₊₁ ty ++ " " ++ go appPrec₊₁ x ++ " " ++ go appPrec₊₁ y)
 
showRaw : Raw -> String
showRaw = showRawPrec 0 

--------------------------------------------------------------------------------

exportToStringMaybe : {ty : Ty} -> HOAS.Tm ty -> Maybe String
exportToStringMaybe tm = do
  lc <- Conv.convert tm
  let raw = convertToRaw lc
  just (showRaw raw)

{-# NON_COVERING #-}
exportToString : {ty : Ty} -> HOAS.Tm ty -> String
exportToString tm with exportToStringMaybe tm
exportToString _ | (just str) = str
exportToString _ | nothing    = "<<nothing>>"

--------------------------------------------------------------------------------
