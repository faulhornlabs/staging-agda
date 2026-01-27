
{-# LANGUAGE BlockArguments #-}
module Eval where

--------------------------------------------------------------------------------

import Seq
import Common

import qualified HOAS as HOAS
import qualified Term as Term

--------------------------------------------------------------------------------
-- * values

data Val
  = VBool Bool
  | VNat  Integer
  | VLam  Ty (Val -> Val)

instance Show Val where
  show (VBool b  ) = show b
  show (VNat  n  ) = show n
  show (VLam  t _) = "< \\(_:" ++ showTy t ++ ") -> ... >"

{-
valTy :: Val -> Ty
valTy = go where
  go VBool = BoolT
  go VNat  = NatT
  go (VLam s f) = Arrow s $ go (f undefined)
-}

litToVal :: Literal -> Val
litToVal lit = case lit of
  BoolL b -> VBool b
  NatL  n -> VNat  n

valApp :: Val -> Val -> Val
valApp fun arg = case fun of
  VLam t f -> f arg
  _        -> error "valApp: application to a non-lambda value"

valApps :: Val -> [Val] -> Val
valApps fun []     = fun
valApps fun (a:as) = valApps (valApp fun a) as

--------------------------------------------------------------------------------

evalPrimOp :: PrimOp Val -> Val
evalPrimOp op = case op of
  -- arithmetic
  Add  (VNat x)  (VNat y)  -> VNat (x + y)
  Sub  (VNat x)  (VNat y)  -> VNat (x - y)
  Mul  (VNat x)  (VNat y)  -> VNat (x * y)
  Div  (VNat x)  (VNat y)  -> VNat (x `div` y)
  Mod  (VNat x)  (VNat y)  -> VNat (x `mod` y)
  -- comparison
  Equ  (VBool x) (VBool y) -> VBool (x == y)
  Equ  (VNat  x) (VNat  y) -> VBool (x == y)
  IFTE (VBool c) x y       -> if c then x else y

--------------------------------------------------------------------------------

evalHOAS :: HOAS.Obj -> Val
evalHOAS = eval where

  norm :: HOAS.Obj -> HOAS.Obj
  norm = quote . eval 

  eval :: HOAS.Obj -> Val
  eval obj = case obj of
    HOAS.App fun arg    -> valApp (eval fun) (eval arg)
    HOAS.Lam t fun      -> VLam t \x -> eval (fun (quote x))
    HOAS.Let   rhs body -> eval $ body (norm rhs)
    HOAS.Rec s rhs body -> case eval (HOAS.Lam s rhs) of { VLam t f -> eval $ body (quote (fix f)) }
    HOAS.Pri op         -> evalPrimOp $ fmap eval op
    HOAS.Lit y          -> litToVal y
    HOAS.Var _          -> error "evalHOAS: Var (shouldn't happen)"

  quote :: Val -> HOAS.Obj
  quote (VBool  b) = HOAS.Lit (BoolL b)
  quote (VNat   k) = HOAS.Lit (NatL  k)
  quote (VLam t f) = HOAS.Lam t \obj -> quote (f (eval obj))

  fix :: (a -> a) -> a
  fix f = let x = f x in x

--------------------------------------------------------------------------------

type Env = Seq Val

evalTm :: Term.Tm -> Val
evalTm = go emptySeq where

  go :: Env -> Term.Tm -> Val
  go env term = case term of
    Term.Var j          -> seqIndex env j
    Term.App f x        -> valApp (go env f) (go env x)
    Term.Lam t body     -> VLam t \x -> go (env |> x) body
    Term.Let s rhs body -> let x = go  env       rhs in go (env |> x) body
    Term.Rec s rhs body -> let f = go (env |> f) rhs in go (env |> f) body
    Term.Pri op         -> evalPrimOp $ fmap (go env) op
    Term.Lit y          -> litToVal y

----------------------------------------

evalTm' :: Term.Tm' -> Val
evalTm' = go emptySeq where

  go :: Env -> Term.Tm' -> Val
  go env term = case term of
    Term.Var' j            -> seqIndex env j
    Term.App' (MkApp j xs) -> valApps (go env (Term.Var' j)) (map (go env) (seqToList xs))
    Term.Let' _ rhs body   -> let x = go     env       rhs in go (env |> x) body
    Term.Fun' _ fun body   -> let f = goFun  env       fun in go (env |> f) body
    Term.Rec' _ fun body   -> let f = goFun (env |> f) fun in go (env |> f) body
    Term.Pri' op           -> evalPrimOp $ fmap (go env) op
    Term.Lit' y            -> litToVal y

  goFun :: Env -> Fun Term.Tm' -> Val
  goFun env (Fun_ args ret body) = worker env (seqToList args) where
    worker env []     = go env body
    worker env (t:ts) = VLam t \x -> worker (env |> x) ts

--------------------------------------------------------------------------------
