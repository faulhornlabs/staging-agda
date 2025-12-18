
{-# LANGUAGE BlockArguments, PatternSynonyms #-}
module Term where

--------------------------------------------------------------------------------

type Nat   = Int
type Level = Int

--------------------------------------------------------------------------------

data Tm 
  = Var Level
  | Lit Nat
  ---
  | App Tm Tm
  | Lam Tm           -- Lam : Tm (ctx |> s) t             -> Tm (s -> t) 
  | Let Tm Tm        -- Let : Tm ctx s -> Tm (ctx |> s) t -> Tm t
  | Fix Tm           -- Fix : Tm (ctx |> s) s             -> Tm s 
  ---
  | Add Tm Tm
  | Sub Tm Tm
  | IfZ Tm Tm Tm
  -- 
  | Print String Tm Tm
  deriving Show

pattern Inc tm = Add tm (Lit 1)
pattern Dec tm = Sub tm (Lit 1)

pattern App2 f x y = App (App f x) y
pattern Lam2 body  = Lam (Lam body)


--------------------------------------------------------------------------------

-- letrec plus100 n = if n == 0 then 100 else 1 + plus100 (n-1)

plus100 :: Tm
plus100 = Fix body where
  -- body : Tm (Nat -> Nat) -> (Nat -> Nat)
  r = Var 0  -- Nat -> Nat
  n = Var 1  -- Nat
  body = Lam $ IfZ n (Lit 100) (Inc (App r (Dec n)))

plus100' :: Tm
plus100' = Fix body where
  -- body : Tm (Nat -> Nat) -> (Nat -> Nat)
  r = Var 0  -- Nat -> Nat
  n = Var 1  -- Nat
  body = Lam $ IfZ n (Lit 100) (Inc (App r (Dec n)))

test :: Tm
test = App plus100 (Lit 7)

--------------------------------------------------------------------------------

