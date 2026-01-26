
-- generate random terms for testing purposes

module AST.Random where

--------------------------------------------------------------------------------

import Control.Monad
import System.Random

import Text.Show.Pretty

import AST.Ty
import AST.Term
import AST.Val

--------------------------------------------------------------------------------

-- | The argument is the probability of @True@
coinFlip :: Double -> IO Bool
coinFlip prob = do
  x <- randomIO
  return (x < prob)

type Level = Int
type Arity = Int
type Size  = Int

data Sized a
  = MkSized Size a
  deriving Show

size :: Sized a -> Size
size (MkSized n _) = n

extract :: Sized a -> a
extract (MkSized _ y) = y

randDivideTargetSize :: Int -> Size -> IO [Size]
randDivideTargetSize = go where

  go :: Int -> Size -> IO [Size]
  go 1 target = return [target]
  go k target = do
    n  <- randomRIO (1, max 1 (target-k)) :: IO Size
    ns <- go (k-1) (max 1 (target-n))     :: IO [Size]
    return (n:ns)

--------------------------------------------------------------------------------

-- Note: in this simple version, all bound variables have type U64
-- (it never binds lambdas...)
--
-- TODO: generate more interesting terms
randomTermU64 :: Int -> IO Raw
randomTermU64 targetSize = final where

  maxArity :: Arity
  maxArity = 4

  -- if we don't start with a Let, then "Var" may just fail
  final = Let U64 (Lit (U64L 666)) <$> (extract <$> mkTerm targetSize 1)

  mkKst :: IO (Sized Raw)
  mkKst = do
    k <- randomRIO (1,65536)
    return $ MkSized 1 $ Lit (U64L k)

  mkAtom :: Level -> IO (Sized Raw)
  mkAtom level = do
    c <- randomRIO (1,3)
    case c of
      1 -> mkKst 
      _ -> mkVar level

  mkTerm :: Size -> Level -> IO (Sized Raw)
  mkTerm target level = do
    if target <= 1
      then mkAtom level
      else do
        c <- randomRIO (1,4)
        case c of
          1 -> mkPrim (target-1) level
          2 -> mkApp  (target-1) level
          _ -> mkLet  (target-2) level

  mkVar :: Level -> IO (Sized Raw)
  mkVar 0     = error "randomTermU64/mkVar: empty context"
  mkVar level = do
    last <- coinFlip 0.333       -- we want to use the last variable with some good probability...
    if last 
      then return $ MkSized 1 $ Var (level-1)
      else do
        j <- randomRIO (0,level-1)
        return $ MkSized 1 $ Var j

  mkPrim :: Size -> Level -> IO (Sized Raw)
  mkPrim target level = do
    c <- randomRIO (1,2)
    let op = case c of
          1 -> "AddU64"
          2 -> "MulTruncU64"
    [n1,n2] <- randDivideTargetSize 2 target 
    x <- mkTerm n1 level
    y <- mkTerm n2 level
    return $ MkSized (size x + size y + 1) 
           $ Pri (MkRawPrim op) [extract x, extract y]

  mkLet :: Size -> Level -> IO (Sized Raw)
  mkLet target level = do
    [n1,n2] <- randDivideTargetSize 2 target 
    rhs  <- mkTerm n1 level
    body <- mkTerm n2 (level+1)
    return $ MkSized (size rhs + size body + 1) 
           $ Let U64 (extract rhs) (extract body)

  mkApp :: Size -> Level -> IO (Sized Raw)
  mkApp target level = do
    arity  <- randomRIO (1,maxArity)
    (n:ns) <- randDivideTargetSize (arity+1) target 
    lam   <- mkLam n level arity
    args  <- sequence [ mkTerm siz level | siz <- ns ]
    return $ MkSized (arity + size lam + sum (map size args))
           $ appList (extract lam) (map extract args)

  mkLam :: Size -> Level -> Arity -> IO (Sized Raw)
  mkLam target level arity = do
    let sz = max 1 (target - arity)
    body <- mkTerm sz arity                          -- we don't allow closures 
    let body' = shiftVars (+level) (extract body)    -- but we are using de Bruijn levels!
    return $ MkSized (size body + arity) 
           $ lamList (replicate arity U64) body'

--------------------------------------------------------------------------------

