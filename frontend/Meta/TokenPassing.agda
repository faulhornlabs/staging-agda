
-- replace `IO a` with `RW ⇒ (RW,a)`

{-# OPTIONS --large-indices #-}
module Meta.TokenPassing where

--------------------------------------------------------------------------------

open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.TrustMe using ( trustMe )

open import Data.Empty
open import Data.Nat
open import Data.Nat.Properties using ( +-suc )
open import Data.Vec
open import Data.Vec.Properties using ( take++drop≡id )
open import Data.Fin using ( Fin ; opposite ; inject₁ ) renaming ( zero to fzero ; suc to fsuc )
open import Data.String using ( String )

open import Meta.HList using ( mapHList ; zipHList′ )
open import Meta.Ty
open import Meta.Ctx
open import Meta.CtxLemmas
open import Meta.Val
open import Meta.IO
open import Meta.PrimOp
open import Meta.STLC

--------------------------------------------------------------------------------

private variable
  n m : ℕ
  ctx : Ctx n
  s t : Ty
  ty  : Ty

private

  mkPair : LC ctx s -> LC ctx t -> LC ctx (Pair s t)
  mkPair x y = Pri (MkPair x y)

  fst : LC ctx (Pair s t) -> LC ctx s
  fst p = Pri (Fst p)

  snd : LC ctx (Pair s t) -> LC ctx t
  snd p = Pri (Snd p)

--------------------------------------------------------------------------------

{-# TERMINATING #-}
convTy : Ty -> Ty
convTy = go where
  go : Ty -> Ty
  go Unit         = Unit
  go (s ⇒ t)      = go s ⇒ go t
  go (IO t)       = Token ⇒ Pair Token (go t)
  go Token        = Token
  go Bit          = Bit
  go U64          = U64
  go Nat          = Nat
  go (Struct tys) = Struct (Data.Vec.map go tys)
  go (Named n ty) = Named n (go ty)
  go (Ptr vty)    = Ptr vty

convCtx : Ctx n -> Ctx n
convCtx = Data.Vec.map convTy

--------------------------------------------------------------------------------

private

  convTy-lemma-Named : {nam : String} -> convTy s ≡ t -> convTy (Named nam s) ≡ Named nam t
  convTy-lemma-Named refl = refl

convVTy : (ty′ : VTy) -> {ty : Ty} -> {eq : vtyToTy ty′ ≡ ty} -> convTy ty ≡ ty
convVTy = go where
  go : (ty′ : VTy) -> {ty : Ty} -> {eq : vtyToTy ty′ ≡ ty} -> convTy ty ≡ ty
  go Unit′  {eq = refl}   = refl
  go Token′ {eq = refl}   = refl
  go Bit′   {eq = refl}   = refl
  go U64′   {eq = refl}   = refl
  go Nat′   {eq = refl}   = refl
  go (Named′ n t′) {ty = Named n t} {eq = refl} = let eq′ = go t′ {ty = t} {eq = refl} in convTy-lemma-Named eq′
  go (Struct′ ts′) {ty = Struct ts} {eq = refl} = trustMe --  let eqs′ = Data.Vec.map go ts′ in ?

private 

  convTy-VTy-lemma : {vty : VTy} -> {ty : Ty} -> vtyToTy vty ≡ ty -> vtyToTy vty ≡ convTy ty
  convTy-VTy-lemma {vty = vty} {ty = ty} eq = trans eq (sym (convVTy vty {eq = eq}))
  
--------------------------------------------------------------------------------

private

  lemma-lkp-map : {ctx : Ctx n} -> (j : Fin n) -> lkpCtx (convCtx ctx) j ≡ convTy (lkpCtx ctx j)
  lemma-lkp-map {ctx = ctx} j = Data.Vec.Properties.lookup-map (opposite j) convTy ctx

--------------------------------------------------------------------------------

translateIO : {ctx : Ctx n} -> {ty : Ty} -> LC ctx ty -> LC (convCtx ctx) (convTy ty)
translateIO = go where

  WrapIO : {n : ℕ} -> {ctx : Ctx n} -> {ty : Ty} -> PrimIO (LC ctx) ty -> LC ctx ty 
  WrapIO pio = Pri (WrapPrimIO pio)

  LamTok : {n : ℕ} -> {ctx : Ctx n} -> {ty : Ty} -> LC (Token ∷ ctx) ty -> LC ctx (Token ⇒ ty)
  LamTok body = Lam {s = Token} body
  
  go     : {n : ℕ} -> {ctx : Ctx n} -> {ty : Ty} ->         LC ctx ty  ->         LC (convCtx ctx)  (convTy ty)
  goIO   : {n : ℕ} -> {ctx : Ctx n} -> {ty : Ty} -> InOut  (LC ctx) ty ->         LC (convCtx ctx)  (Token ⇒ Pair Token (convTy ty))
  goPrim : {n : ℕ} -> {ctx : Ctx n} -> {ty : Ty} -> PrimOp (LC ctx) ty -> PrimOp (LC (convCtx ctx)) (convTy ty)

  go (Lam body    ) = Lam (go body)
  go (Let rhs body) = Let (go rhs) (go body)
  go (Rec rhs body) = Rec (go rhs) (go body)
  go (App f x     ) = App (go f) (go x)
  go (Pri prim    ) = Pri (goPrim prim)
  go (Log s x     ) = Log s (go x)
  go (Dbg s x y   ) = Dbg s (go x) (go y)
  go (IOp xio     ) = goIO xio

  go {ctx = ctx} (Var j eq   ) = let eq₁ = (lemma-lkp-map {ctx = ctx} j)
                                     eq₂ = cong convTy eq
                                 in  Var j (trans eq₁ eq₂)

  go (Lit {t = t} {t′ = t′} {eq = eq} x) =
    let eq₁ = convVTy t′ {ty = t} {eq = eq}
        eq₂ = trans eq (sym eq₁)
    in  Lit {t = convTy t} {t′ = t′} {eq = eq₂} x
    
  -- this is only here so that Agda does not complain, so we just return a dummy value (yeah it's a hack)
  goPrim {ty = ty} prim = DummyPrimOp (convTy ty)

  goIO (Pure x    ) = Lam {s = Token} (mkPair lastVar (inExtendedCtx Token (go x)))

  -- u : IO A          ~>     u' : Token -> (Token, A')
  -- h : A -> IO B     ~>     h' : A' -> (Token -> (Token, B'))
  -- bind u h          ~>     bind' u' h' = \rw -> let p = u' rw in h' (snd x) (fst p)

  goIO {n = n} {ctx = ctx} (Bind {s = A} {t = B} u h) =
    let rw  = lastVar            -- the variable bound by the lambda constructor of the type (Token -> A')
        P   = Pair Token (convTy A)
        p   = Var (Data.Fin.fromℕ (suc n)) (lemma-lkp-last (Token ∷ convCtx ctx) P)
        rw₂ = fst p
        x'  = snd p
    in  Lam {s = Token} $
          Let {s = P}
            (App  (inExtendedCtx    Token (go u))    rw )
            (App2 (inExtendedCtx2 P Token (go h)) x' rw₂)

  goIO  (Put name x) =
    let rw = lastVar 
        x' = inExtendedCtx Token (go x)
    in  LamTok (WrapIO (PrimPut rw name x'))

  goIO  (Get name t) =
     let rw = lastVar
     in  LamTok (WrapIO (PrimGet rw name (convTy t)))

  goIO (Alloc size) =
     let rw = lastVar
         size' = inExtendedCtx Token (go size)
     in  LamTok (WrapIO (PrimAlloc rw size'))

  goIO (Free ptr) =
     let rw = lastVar
         ptr' = inExtendedCtx Token (go ptr)
     in  LamTok (WrapIO (PrimFree rw ptr'))

  goIO (Read {eq = eq} ptr j) = 
     let rw = lastVar
         ptr' = inExtendedCtx Token (go ptr)
         j'   = inExtendedCtx Token (go j  )
     in  LamTok (WrapIO (PrimRead {eq = convTy-VTy-lemma eq} rw ptr' j'))

  goIO (Write {eq = eq} ptr j y) = 
     let rw = lastVar
         ptr' = inExtendedCtx Token (go ptr)
         j'   = inExtendedCtx Token (go j  )
         y'   = inExtendedCtx Token (go y  )
     in  LamTok (WrapIO (PrimWrite {eq = convTy-VTy-lemma eq} rw ptr' j' y'))

--------------------------------------------------------------------------------
