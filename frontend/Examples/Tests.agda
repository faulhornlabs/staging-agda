
module Examples.Tests where

--------------------------------------------------------------------------------

open import Data.Nat using ( ℕ ; _+_ ) renaming ( zero to nzero ; suc to nsuc )
open import Data.Word64
open import Data.Product
open import Function using ( _$_ )

open import Meta.Object

open import Algebra.Misc using ( Half ; Even ; Odd ; halve )

--------------------------------------------------------------------------------

open BitLib
open NatLib
open U64Lib

{-# TERMINATING #-}
natFixPow : ℕ -> Tm Nat -> Tm Nat
natFixPow = go where
  go : ℕ -> Tm Nat -> Tm Nat
  go 0 _ = kstNat 1
  go 1 x = x
  go n x with halve n 
  go _ x | Even k = Let (go k x) \s ->         mulNat s s
  go _ x | Odd  k = Let (go k x) \s -> mulNat (mulNat s s) x

--------------------------------------------------------------------------------

natDynPowNaive : Tm Nat -> Tm Nat -> Tm Nat
natDynPowNaive expo base = App (Fix powRec) expo where
  powRec : Tm (Nat ⇒ Nat) -> Tm (Nat ⇒ Nat)
  powRec rec = Lam \e -> ifte (isZeroNat e)
    (kstNat 1)
    (mulNat base (App rec (predNat e)))

{-
natDynPowFast : Tm Nat -> Tm Nat -> Tm Nat
natDynPowFast expo base = App (Fix powRec) expo base where
  powRec : Tm ((Nat ⇒ Nat ⇒ Nat) ⇒ (Nat ⇒ Nat ⇒ Nat))
  powRec = Lam \rec -> Lam \e b -> ifte (isZeroNat e)
-}

--------------------------------------------------------------------------------

squarePlus7 : Tm (Nat ⇒ Nat)
squarePlus7 = Lam \x -> addNat (mulNat x x) (kstNat 7)

fun1 : Tm (Nat ⇒ Nat ⇒ Nat)
fun1 = Lam2 \x y -> mulNat (App squarePlus7 x) (addNat y (kstNat 10))

fun2 : Tm (Nat ⇒ Nat ⇒ Nat ⇒ Nat)
fun2 = Lam3 \x y z -> addNat (App2 fun1 x z) (App squarePlus7 y)

lamTest1 : Tm (Pair Nat Nat)
lamTest1 = mkPair
  (App squarePlus7 (kstNat 10))
  (App squarePlus7 (kstNat 100))

lamTest2 : Tm (Pair Nat Nat)
lamTest2 = mkPair
  (App squarePlus7 (kstNat 10))
  (App2 fun1 (kstNat 20) (kstNat 100))

lamTest3' : Tm (Nat ⇒ Nat)
lamTest3' = Lam \a -> App3 fun2 (addNat a c) b (mulNat d d) where
  b = kstNat 20
  c = kstNat 100
  d = kstNat 500

lamTest3 : Tm Nat
lamTest3 = App lamTest3' (kstNat 5)

lambdaLiftTest : Tm (Pair Nat Nat)
lambdaLiftTest = mkPair x y where

  a = kstNat 5
  b = kstNat 20
  c = kstNat 100
  d = kstNat 500

  x = App3 fun2 (addNat a c) b (mulNat d d)
  y = addNat (App2 fun1 c d) (App squarePlus7 (addNat a b))

mixedFun1 : Tm (Bit ⇒ U64 ⇒ Nat ⇒ Pair U64 Nat)
mixedFun1 = Lam3 \bit w n -> mkPair (xxx bit w) (App lamTest3' n) where
  xxx : Tm Bit -> Tm U64 -> Tm U64
  xxx bit w = mulTruncU64 (addU64 (castBitU64 bit) (kstU64 (fromℕ 5))) w
  
mixedTest1 : Tm (Pair U64 Nat)
mixedTest1 = App3 mixedFun1 bit word nat where
  bit  = not zeroBit
  word = mulTruncU64 (kstU64 (fromℕ 3)) (kstU64 (fromℕ 4))
  nat  = addNat (kstNat 10) (kstNat 7)

--------------------------------------------------------------------------------

liftTest1 : Tm U64
liftTest1 = App3 f (kstU64′ 5) (kstU64′ 11) (kstU64′ 100) where

  f : Tm (U64 ⇒ U64 ⇒ U64 ⇒ U64)
  f = Lam3 \u v w ->
        App3 (Lam3 \x y z -> addU64 (mulTruncU64 (addU64 u x) (addU64 y v)) z)
          w (addU64 w (kstU64′ 1)) (addU64 w (kstU64′ 2))
          
--------------------------------------------------------------------------------

letFunTest : Tm U64
letFunTest = runGen do
  fvar <- gen $ Lam2 \x y -> addU64 (addU64 x y) (kstU64′ 100)
  gvar <- gen $ Lam  \z   -> addU64 (addU64 z z) (kstU64′ 1  )
  hvar <- gen $ Lam2 \a b -> mulTruncU64 (App2 fvar a b) (App gvar (mulTruncU64 a b))
  return $ App2 hvar (kstU64′ 5) (kstU64′ 7)
  
--------------------------------------------------------------------------------

recAdd : Tm U64 -> Tm U64 -> Tm U64
recAdd x y = App f y where
  +₁ -₁ : Tm U64 -> Tm U64
  +₁ x = addU64 x oneU64
  -₁ x = subU64 x oneU64
  add : Tm (U64 ⇒ U64) -> Tm (U64 ⇒ U64)
  add rec = Lam \y -> ifte (isZeroU64 y) x (+₁ (App rec (-₁ y)))
  f : Tm (U64 ⇒ U64)
  f = Fix add

recMul : Tm U64 -> Tm U64 -> Tm U64
recMul a b = App g b where
  +ₐ -₁ : Tm U64 -> Tm U64
  +ₐ x = recAdd x a  --  addU64 x a
  -₁ x = subU64 x oneU64
  mul : Tm (U64 ⇒ U64) -> Tm (U64 ⇒ U64)
  mul rec = Lam \y -> ifte (isZeroU64 y) zeroU64 (+ₐ (App rec (-₁ y)))
  g : Tm (U64 ⇒ U64)
  g = Fix mul

exRecAdd exRecMul : Tm U64
exRecAdd = App2 (Lam2 recAdd) (kstU64′ 7) (kstU64′ 5)
exRecMul = App2 (Lam2 recMul) (kstU64′ 7) (kstU64′ 5)

open IOLib

exRecAddMul : Tm (IO Unit)
exRecAddMul = then 
  (print "7 + 5" exRecAdd)
  (print "7 * 5" exRecMul)

--------------------------------------------------------------------------------

exClosure1 : Tm U64
exClosure1 =
  Let 
    (Lam \x ->
      Let (mulTruncU64 x x) \y -> Lam \z -> addU64 (mulTruncU64 x z) y)
    \g -> Let (kstU64′ 5) \x0 ->
      Let (App g x0) \h ->
        App h (kstU64′ 7)
            
--------------------------------------------------------------------------------

