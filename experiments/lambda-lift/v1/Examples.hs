
{-# LANGUAGE BlockArguments #-}
module Examples where

--------------------------------------------------------------------------------

import Shared
import HOAS 
import Term ( Tm , evalTm )
import Lift 

--------------------------------------------------------------------------------

zero, one, two :: Obj
zero = Lit 0
one  = Lit 1
two  = Lit 2

add, sub, mul :: Obj -> Obj -> Obj
add x y = Pri (Add x y)
sub x y = Pri (Sub x y)
mul x y = Pri (Mul x y)

ifz :: Obj -> Obj -> Obj -> Obj
ifz c x y = Pri (IfZ c x y)

inc, dec :: Obj -> Obj
inc x = add x (Lit 1)
dec x = sub x (Lit 1)

fix :: (Obj -> Obj) -> Obj
fix f = Rec f id

instance Num Obj where
  fromInteger = Lit . fromInteger
  (+) = add
  (-) = sub
  (*) = mul
  abs    = error "Obj/abs"
  signum = error "Obj/signum"

--------------------------------------------------------------------------------

recAdd :: Obj -> Obj -> Obj
recAdd x y = App (fix add) y where
  -- Tm (U64 ⇒ U64) -> Tm (U64 ⇒ U64)
  add :: Obj -> Obj                 
  add rec = Lam \y -> ifz y x (inc (App rec (dec y)))

recMul :: Obj -> Obj -> Obj
recMul a b = App (fix mul) b where
  plusA x = recAdd a x
  -- Tm (U64 ⇒ U64) -> Tm (U64 ⇒ U64)
  mul :: Obj -> Obj
  mul rec = Lam \y -> ifz y zero (plusA (App rec (dec y)))

recExp :: Obj -> Obj 
recExp y = App (fix exp2) y where
  -- Tm (U64 ⇒ U64) -> Tm (U64 ⇒ U64)
  exp2 :: Obj -> Obj                 
  exp2 rec = Lam \y -> ifz y 1 (mul 2 (App rec (dec y)))

--------------------------------------------------------------------------------

-- non-recursive
ex0_H = Let (lam2 add) \add ->
        Let (lam2 mul) \mul -> 
        Let (lam2 \a b -> App2 add a (App2 mul 1000 b)) \combine ->
        Let (lam2 \x y -> App2 combine (App2 add x y) (App2 mul x y)) \final ->
        App2 final 3 6

-- simple recursive
ex1a_H = App2 (lam2 recAdd) 5 7  
ex1b_H = App2 (lam2 recMul) 5 7  

-- simple recursive
ex2_H = Let (lam2 recAdd) \add -> 
        Let (lam2 recMul) \mul ->
        App2 mul 3 (App2 add 5 (App2 mul 7 9)) 
-- simpler counterexample
ex2b_H = Let (Lam \x -> x + 666) \fun1 -> 
         Let (Lam \x -> x + 667) \fun2 -> 
         Let (Lam \x -> x + 668) \fun3 ->
         Let (lam2 recAdd) \add ->
         -- Let (lam2 \x y -> Let (Lam \z -> z * x) \w -> w $$ y) \add ->      -- this works so we ened recursion
         App2 add 5 7 
-- this works (so we need two arguments?)
ex2c_H = Let (Lam \x -> x + 666) \fun -> 
         Let (Lam recExp) \exp2 ->
         App exp2 6

-- recursive
ex3_H = Let (lam2 recAdd) \add ->
        Let (lam2 recMul) \mul ->
        Let (lam2 \a b -> App2 add a (App2 mul 1000 b)) \combine -> 
        Let (lam2 \x y -> App2 combine (App2 add x y) (App2 mul x y)) \final ->
        App2 final 5 7 
        -- App2 mul 5 7

ex0_F  = fromHOAS ex0_H
ex1a_F = fromHOAS ex1a_H
ex1b_F = fromHOAS ex1b_H
ex2_F  = fromHOAS ex2_H
ex2b_F = fromHOAS ex2b_H
ex2c_F = fromHOAS ex2c_H
ex3_F  = fromHOAS ex3_H

ex0_L  = lambdaLift ex0_F
ex1a_L = lambdaLift ex1a_F
ex1b_L = lambdaLift ex1b_F
ex2_L  = lambdaLift ex2_F
ex2b_L = lambdaLift ex2b_F
ex2c_L = lambdaLift ex2c_F
ex3_L  = lambdaLift ex3_F

--------------------------------------------------------------------------------
-- euclidean algo

{-
type Prime = Int

modularBinaryEuclid :: Prime -> Obj -> Obj -> Obj -> Obj -> Obj
modularBinaryEuclid prime x0 y0 u0 v0 = App4 worker u0 x0 v0 y0 where
  halfPrimPlus1 = div prime 2 + 1

  ... 
modularDiv :: Prime -> Obj -> Obj -> Obj
modularDiv prime a b = modularBinaryEuclid prime x y u v where
  x = a
  y = Lit 0
  u = b
  v = Lit prime

modularInv :: Prime -> Obj -> Obj
modularInv prime b = modularDiv prime 1 b
-}
