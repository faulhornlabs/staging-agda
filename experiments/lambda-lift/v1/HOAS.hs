
-- higher-order abstract syntax (for easy code generation)

{-# LANGUAGE PatternSynonyms, BlockArguments #-}
module HOAS where

--------------------------------------------------------------------------------

import Shared

import qualified Term 

--------------------------------------------------------------------------------

data Obj where
  App :: Obj -> Obj                   -> Obj
  Lam :: (Obj -> Obj)                 -> Obj
  Let ::  Obj ->         (Obj -> Obj) -> Obj
  Rec :: (Obj -> Obj) -> (Obj -> Obj) -> Obj
  Pri :: PrimOp Obj                   -> Obj
  Var :: Level                        -> Obj
  Lit :: Int                          -> Obj

pattern App2 f x y   = App (App  f x  ) y
pattern App3 f x y z = App (App2 f x y) z

lam :: (Obj -> Obj) -> Obj
lam = Lam

lam2 :: (Obj -> Obj -> Obj) -> Obj
lam2 f = Lam (\x -> Lam  (f x))

lam3 :: (Obj -> Obj -> Obj -> Obj) -> Obj
lam3 f = Lam (\x -> lam2 (f x))

($$) :: Obj -> Obj -> Obj
($$) = App
infixr 1 $$

--------------------------------------------------------------------------------

-- ???
evalHOAS :: Obj -> Val
evalHOAS = eval where

  norm :: Obj -> Obj
  norm = quote . eval 

  eval :: Obj -> Val
  eval (App fun arg ) = valApp (eval fun) (eval arg)
  eval (Lam fun     ) = VLam \x -> eval (fun (quote x))
  eval (Let rhs body) = eval $ body (norm rhs)
  eval (Rec rhs body) = case eval (Lam rhs) of { VLam f -> eval $ body (quote (fix f)) }
  eval (Pri op      ) = evalPrimOp $ fmap eval op
  eval (Lit k       ) = VInt k
  eval (Var _       ) = error "evalHOAS: Var (shouldn't happen)"

  quote :: Val -> Obj
  quote (VInt k) = Lit k
  quote (VLam f) = Lam \obj -> quote (f (eval obj))

  fix :: (a -> a) -> a
  fix f = let x = f x in x

--------------------------------------------------------------------------------

-- convert from HOAS to first-order syntax
fromHOAS :: Obj -> Term.Tm
fromHOAS = go 0 where

  go :: Level -> Obj -> Term.Tm
  go level obj = 
    case obj of
      Var j    -> Term.Var j
      App f x  -> Term.App (go  level f) (go level x)
      Lam f    -> Term.Lam (go (level+1) (f v))
      Let r g  -> Term.Let (go  level     r   ) (go (level+1) (g v))
      Rec r h  -> Term.Rec (go (level+1) (r v)) (go (level+1) (h v))
      Pri op   -> Term.Pri (fmap (go level) op)
      Lit k    -> Term.Lit k
    where 
      v = Var level

--------------------------------------------------------------------------------
