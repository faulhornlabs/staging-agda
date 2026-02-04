
{-# OPTIONS --hidden-argument-puns --rewriting #-}
module Lift where

--------------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality

open import Data.Bool
open import Data.Product
open import Data.Nat
open import Data.Fin hiding ( _+_ ) renaming ( zero to fzero ; suc to fsuc )
open import Data.Vec
open import Data.List hiding ( _++_ ; reverse )

open import Ctx
open import Term

--------------------------------------------------------------------------------

private variable
  n m : ℕ
  s t : Ty
  u v : Ty
  ty  : Ty
  Γ   : Ctx n
  ts  : Vec Ty m

--------------------------------------------------------------------------------

-- function signature
record Sig : Set where
  constructor MkSig
  field
    sigArity : ℕ
    sigArgs  : Vec Ty sigArity
    sigRet   : Ty

open Sig

sigTy : Sig -> Ty
sigTy (MkSig arity args ret) = funTy args ret

TopCtx : ℕ -> Set
TopCtx N = Vec Sig N

private variable
  N : ℕ
  Δ : TopCtx N
  sig : Sig

data TopLookup : (Δ : TopCtx N) -> (sig : Sig) -> Set where
  MkLkp : (i : Fin N) -> Data.Vec.lookup Δ (opposite i) ≡ sig -> TopLookup Δ sig

VarLookup : (Γ : Ctx n) -> (sig : Sig) -> Set 
VarLookup Γ sig = Lookup Γ (sigTy sig)

--------------------------------------------------------------------------------

private variable
  arity : ℕ
  args  : Vec Ty arity
  ret   : Ty

data ApplyE (exp : TopCtx N -> Ctx n -> Ty -> Set) : (Δ : TopCtx N) -> (Γ : Ctx n) -> Ty -> Set where
  MkTopApp : TopLookup Δ (MkSig arity args ret) -> HVec (exp Δ Γ) args -> ApplyE exp Δ Γ ret
  MkVarApp : VarLookup Γ (MkSig arity args ret) -> HVec (exp Δ Γ) args -> ApplyE exp Δ Γ ret

pattern VarE lkp = MkVarApp lkp HNil

{-
-- equivalent, but the above seems simpler now
data ApplyE (exp : TopCtx N -> Ctx n -> Ty -> Set) : (Δ : TopCtx N) -> (Γ : Ctx n) -> Ty -> Set where
  MkTopApp : TopLookup Δ sig -> HVec (exp Δ Γ) (sigArgs sig) -> sigRet sig ≡ ty -> ApplyE exp Δ Γ ty
  MkVarApp : VarLookup Γ sig -> HVec (exp Δ Γ) (sigArgs sig) -> sigRet sig ≡ ty -> ApplyE exp Δ Γ ty

-- VarE : Lookup Γ t -> Exp Δ Γ t
pattern VarE lkp = MkVarApp lkp HNil refl
-}

----------------------------------------

data Exp : TopCtx N -> Ctx n -> Ty -> Set where
  LetE : Exp Δ Γ s -> Exp Δ (Γ ⊳ s) t     -> Exp Δ Γ t
  AppE : ApplyE Exp Δ Γ t                 -> Exp Δ Γ t


data FunDef : (Δ : TopCtx N) -> (sig : Sig) -> Set where
  MkDef : (sig : Sig) -> Exp Δ ∅ (sigTy sig) -> FunDef Δ sig 

data TopEnv : (Δ : TopCtx N) -> Set where
  Empty  : TopEnv []
  Define : TopEnv Δ -> FunDef (Δ ⊳ sig) sig -> TopEnv (Δ ⊳ sig)
  
data Program : (ty : Ty) -> Set where
  MkPrg : {N : ℕ} -> {Δ : TopCtx N} -> TopEnv Δ -> Exp Δ ∅ ty -> Program ty
  
--------------------------------------------------------------------------------

-- a de Bruijn index into a context
data Index (Γ : Ctx n) : Set where
  MkIdx : (t : Ty) -> Lookup Γ t -> Index Γ

idxHere : Index (Γ ⊳ ty)
idxHere {ty} = MkIdx ty Here

idxThere : Index Γ -> Index (s ∷ Γ)
idxThere (MkIdx ty lkp) = MkIdx ty (There lkp)

allIndices : (Γ : Ctx n) -> Vec (Index Γ) n
allIndices = go where
  go : {k : ℕ} -> (Γ : Ctx k) -> Vec (Index Γ) k
  go []       = []
  go (t ∷ ts) = idxHere ∷ Data.Vec.map idxThere (go ts)

----------------------------------------

-- subset of a context
Mark : Ctx n -> Set
Mark {n} Γ = Vec Bool n

-- same as above, just different interpretation
Ignore : Ctx n -> Set
Ignore {n} Γ = Vec Bool n

-- mark a given de Bruijn index
mark : Lookup Γ t -> Mark Γ -> Mark Γ
mark Here        (_ ∷ bs) = true ∷ bs
mark (There lkp) (b ∷ bs) = b ∷ mark lkp bs

-- conditional to ignore flag
markUnless : Ignore Γ -> Lookup Γ t -> Mark Γ -> Mark Γ
markUnless (c ∷ cs) Here        (b ∷ bs) = (if c then b else true) ∷ bs
markUnless (c ∷ cs) (There lkp) (b ∷ bs) = b ∷ markUnless cs lkp bs

-- returns the list of marked indices
markedList : Mark {n} Γ -> List (Index Γ)
markedList {n} {Γ} flags = go Γ flags (allIndices Γ) where

  go : {k : ℕ} -> Vec Ty k -> Vec Bool k -> Vec (Index Γ) k -> List (Index Γ)
  go []       []           _        = []
  go (t ∷ ts) (false ∷ bs) (i ∷ is) =     go ts bs is
  go (t ∷ ts) (true  ∷ bs) (i ∷ is) = i ∷ go ts bs is 

----------------------------------------

{-# TERMINATING #-}
markFreeVars′ : {n m : ℕ} -> {Γ : Ctx n} -> {ts : Ctx m} -> Ignore Γ -> Exp Δ (ts ++ Γ) ty -> Mark Γ
markFreeVars′ {n} {Γ} ignore term = goExp term (Data.Vec.replicate n false) where

  markLookup : {m : ℕ} -> {ts : Ctx m} -> Lookup (ts ++ Γ) ty -> (Mark Γ -> Mark Γ)
  markLookup {ts} lookup = worker ts lookup where
    worker :  {m : ℕ} -> (ts : Ctx m) -> Lookup (ts ++ Γ) ty -> (Mark Γ -> Mark Γ)
    worker (u ∷ us)  Here        old = old
    worker (u ∷ us) (There lkp′) old = worker us lkp′ old
    worker []        lkp         old = markUnless ignore lkp old
    
  goExp  : {m   : ℕ} -> {ts : Ctx m} -> {ty : Ty}         ->       Exp Δ (ts ++ Γ)  ty    -> Mark Γ -> Mark Γ
  goArgs : {m k : ℕ} -> {ts : Ctx m} -> {args : Vec Ty k} -> HVec (Exp Δ (ts ++ Γ)) args  -> Mark Γ -> Mark Γ

  goArgs args old = hfoldr goExp args old
  
  goExp (LetE rhs letbody) old = goExp letbody (goExp rhs old) 
  goExp (AppE apply      ) old with apply
  ... | MkTopApp topLkp args =                    goArgs args old
  ... | MkVarApp varLkp args = markLookup varLkp (goArgs args old)

    
markFreeVars : {Δ : TopCtx N} -> {Γ : Ctx n} -> {ts : Ctx m} -> {ty : Ty} ->
               Ignore Γ -> Exp Δ (Γ ◆ ts) ty -> Mark Γ
markFreeVars {Δ} {Γ} {ts} {ty} ignore term = markFreeVars′ {Γ = Γ} {ts = reverse ts} ignore term′ where  
  term′ : Exp Δ (reverse ts ++ Γ) ty 
  term′ = subst (\ctx -> Exp Δ ctx ty) (lemma-◆ Γ ts) term

freeVars : Ignore Γ -> Exp Δ (Γ ◆ ts) ty -> List (Index Γ)
freeVars ignore term = markedList (markFreeVars ignore term)

--------------------------------------------------------------------------------
