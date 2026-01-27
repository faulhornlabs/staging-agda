
{-# LANGUAGE BlockArguments #-}
module Ex where

--------------------------------------------------------------------------------

import Common
import HOAS
import Eval

--------------------------------------------------------------------------------

instance Num Obj where
  fromInteger = Lit . NatL . fromInteger
  (+) x y = Pri (Add x y)
  (-) x y = Pri (Sub x y)
  (*) x y = Pri (Mul x y)
  abs    = undefined
  signum = undefined

ifte :: Obj -> Obj -> Obj -> Obj
ifte c x y = Pri (IFTE c x y)

(=?=) :: Obj -> Obj -> Obj
(=?=) x y = Pri (Equ x y)

isZero :: Obj -> Obj
isZero x = (x =?= 0)

--------------------------------------------------------------------------------

inc, dec :: Obj -> Obj
inc x = x + 1
dec x = x - 1

-- letrec g cnt = if (cnt == 0) then x else inc (g (dec cnt))
recAdd :: Obj -> Obj -> Obj
recAdd x y = Rec (NatT ~> NatT) g (\f -> App f y) where
  g :: Obj -> Obj
  g recg = lam \y -> ifte (isZero y) x (inc (App recg (dec y)))

recMul :: Obj -> Obj -> Obj
recMul a b = Rec (NatT ~> NatT) h (\f -> App f b) where
  plusA x = recAdd x a 
  h :: Obj -> Obj
  h rech = lam \y -> ifte (isZero y) 0 (plusA (App rech (dec y)))

recMulAdd :: Obj -> Obj -> Obj
recMulAdd x y = 1000 * (recMul x y) + recAdd x y

recMulAdd' :: Obj -> Obj -> Obj
recMulAdd' x y = (recMul 1000 (recMul x y)) `recAdd` (recAdd x y)

--------------------------------------------------------------------------------

