
-- higher-order abstract syntax (for easy code generation)

{-# LANGUAGE PatternSynonyms, BlockArguments #-}
module HOAS where

--------------------------------------------------------------------------------

import Seq
import Common
import Val

import qualified Term 

--------------------------------------------------------------------------------

data Obj where
  App :: Obj -> Obj                         -> Obj
  Lam :: Ty -> (Obj -> Obj)                 -> Obj
  Let ::        Obj ->         (Obj -> Obj) -> Obj
  Rec :: Ty -> (Obj -> Obj) -> (Obj -> Obj) -> Obj
  Pri :: PrimOp Obj                         -> Obj
  Lit :: Literal                            -> Obj
  Var :: Level                              -> Obj

pattern App2 f x y   = App (App  f x  ) y
pattern App3 f x y z = App (App2 f x y) z

lam :: (Obj -> Obj) -> Obj
lam = Lam NatT

lam2 :: (Obj -> Obj -> Obj) -> Obj
lam2 f = lam (\x -> lam  (f x))

lam3 :: (Obj -> Obj -> Obj -> Obj) -> Obj
lam3 f = lam (\x -> lam2 (f x))

($$) :: Obj -> Obj -> Obj
($$) = App
infixr 1 $$

--------------------------------------------------------------------------------
-- *** convert from HOAS to first-order syntax

fromHOAS :: Obj -> Term.Tm
fromHOAS = go emptyCtx where

  go :: Ctx -> Obj -> Term.Tm
  go ctx obj = 
    case obj of
      Var j      -> Term.Var j
      App f x    -> Term.App (go ctx f) (go ctx x)
      Lam t f    -> Term.Lam t (go (ctx |> t) (f v))
      Let r g    -> let r' = go ctx r
                        t  = Term.inferTy ctx r' 
                    in  Term.Let t r' (go (ctx |> t) (g v))
      Rec s r h  -> Term.Rec s (go (ctx |> s) (r v)) (go (ctx |> s) (h v))
      Pri op     -> Term.Pri (fmap (go ctx) op)
      Lit y      -> Term.Lit y
    where 
      level = ctxLevel ctx
      v     = Var level

--------------------------------------------------------------------------------
-- *** evaluate

evalHOAS :: Obj -> Val
evalHOAS = eval where

  norm :: Obj -> Obj
  norm = quote . eval 

  eval :: Obj -> Val
  eval obj = case obj of
    App fun arg    -> valApp (eval fun) (eval arg)
    Lam t fun      -> VLam t \x -> eval (fun (quote x))
    Let   rhs body -> eval $ body (norm rhs)
    Rec s rhs body -> case eval (Lam s rhs) of { VLam t f -> eval $ body (quote (fix f)) }
    Pri op         -> evalPrimOp $ fmap eval op
    Lit y          -> litToVal y
    Var _          -> error "evalHOAS: Var (shouldn't happen)"

  quote :: Val -> Obj
  quote (VBool  b) = Lit (BoolL b)
  quote (VNat   k) = Lit (NatL  k)
  quote (VLam t f) = Lam t \obj -> quote (f (eval obj))

  fix :: (a -> a) -> a
  fix f = let x = f x in x

--------------------------------------------------------------------------------
