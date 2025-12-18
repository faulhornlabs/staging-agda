{-# LANGUAGE PatternSynonyms #-}
module Run.IO where

--------------------------------------------------------------------------------

import Data.Word
import Data.Bits
import Data.List

import Control.Monad

import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.Storable
import System.IO.Unsafe

import Text.Printf

import AST.Ty
import AST.Val
import AST.PrimOp
import AST.IO

import Run.Input
import Run.Semantics

import Aux.Misc

--------------------------------------------------------------------------------

evalPrimIO  :: RawPrimIO -> [Val] -> IO Val
evalPrimIO  prim args = case (prim , args) of

  ( RawPrimGet name ty , [TokenV k] ) -> do 
    int <- getInputIO_ name 
    case marshalInto ty int of
      Nothing  -> fail $ "evalPrimIO: cannot marshal input `" ++ name ++ "` into " ++ show ty
      Just val -> return $ PairV val (TokenV (k+1))

  ( RawPrimPut name , [value, TokenV k]  ) -> do
    case marshalFrom value of
      Nothing  -> fail $ "evalPrimIO: cannot marshal output `" ++ name ++ "` into integer"
      Just int -> do
        putOutputIO name int 
        return $ PairV TtV (TokenV (k+1))

  ( RawPrimPrint name , [value, TokenV k]  ) -> do
    putStrLn $ "# " ++ name ++ " = " ++ showVal value
    return $ PairV TtV (TokenV (k+1))

  ( RawPrimAlloc ty , [U64V n, TokenV k] ) -> case isFlatTy ty of
    Nothing -> fail "evalPrimIO: RawPrimAlloc: expecting a flat type"
    Just fty -> do
      let len = fromIntegral n :: Int
      fptr <- mallocForeignPtrArray (len * flatTySize fty)
      return $ PairV (PtrV fty fptr len) (TokenV (k+1))

  ( RawPrimFree , [PtrV {} , TokenV k] ) -> return $ PairV TtV (TokenV (k+1))

  ( RawPrimRead   ty , [PtrV fty fptr len , U64V ofs , TokenV k] ) -> do
     y <- peekFlatTy fty fptr (fromIntegral ofs)
     return $ PairV y (TokenV (k+1))

  ( RawPrimWrite  ty , [PtrV fty fptr len , U64V ofs , val , TokenV k] ) -> do
    pokeFlatTy fty fptr (fromIntegral ofs) val
    return $ PairV TtV (TokenV (k+1))

  ( RawPrimLen , [PtrV fty fptr len , TokenV k] ) -> return $ PairV (U64V (fromIntegral len)) (TokenV (k+1))

  ( RawPrimLoop , [U64V looplen, FunV rtfun , TokenV k] ) -> do
    k' <- evalLoop rtfun looplen (k+1)
    return $ PairV TtV (TokenV k')

  _ -> fail $ "evalPrimIO: invalid primitive IO / argument combination: " ++ show prim ++ " " ++ show args

  where

    evalLoop :: RunTimeFun -> Word64 -> Int -> IO Int
    evalLoop rtfun n k = go n 0 k where
      go 0 _   k = return k
      go n idx k = do
        FunV  rtfun'        <- runRunTimeFun rtfun  (U64V idx)
        PairV _ (TokenV k') <- runRunTimeFun rtfun' (TokenV k)
        go (n-1) (idx+1) k'

--------------------------------------------------------------------------------

printVal :: Val -> IO ()
printVal val = showValIO val >>= putStrLn

{-# NOINLINE showVal #-}
showVal :: Val -> String
showVal val = unsafePerformIO (showValIO val)

{-# NOINLINE showValIO #-}
showValIO :: Val -> IO String
showValIO val = case val of
  PtrV fty fptr len -> do
    vals <- peekFlatArray fty fptr len
    xs <- mapM showValIO vals
    return $ "[" ++ intercalate "," xs ++ "]"
  _ -> return (showVal' val)  

showVal' :: Val -> String
showVal' = go where
  go val = case val of
    TtV        -> "()"
    BitV b     -> show b
    U64V y     -> printf "0x%x" y -- printf "0x%016x" y
    NatV n     -> show n
    StructV xs -> "{" ++ intercalate "," (map go xs) ++ "}"
    WrapV n v  -> n ++ "(" ++ go v ++ ")"
    FunV   {}  -> "<<lambda>>"
    TokenV {}  -> "<<token>>"
    PtrV   {}  -> "<<array>>"

peekFlatArray :: FlatTy -> ForeignPtr a -> Int -> IO [Val]
peekFlatArray fty fptr n = forM [0..n-1] $ \i -> peekFlatTy fty fptr i

peekFlatTy :: FlatTy -> ForeignPtr a -> Int -> IO Val
peekFlatTy fty fptr ofs = withForeignPtr fptr $ \ptr -> go fty (plusPtr ptr (ofs * flatTySize fty)) where

  go :: FlatTy -> Ptr a -> IO Val
  go FlatBit ptr = do
    k <- peek (castPtr ptr :: Ptr Word8)
    return (BitV (k /= 0))
  go FlatU64 ptr = do
    x <- peek (castPtr ptr :: Ptr Word64)
    return (U64V x)
  go (FlatNamed _ fty) ptr = go fty ptr
  go (FlatStruct fts)  ptr = StructV <$> goTup fts ptr 

  goTup :: [FlatTy] -> Ptr a -> IO [Val]
  goTup []     _   = return []
  goTup (t:ts) ptr = do
    let k = flatTySize t 
    x  <- go    t           ptr
    xs <- goTup ts (plusPtr ptr k) 
    return (x:xs)

pokeFlatTy :: FlatTy -> ForeignPtr a -> Int -> Val -> IO ()
pokeFlatTy fty fptr ofs val = withForeignPtr fptr $ \ptr -> go fty (plusPtr ptr (ofs * flatTySize fty)) val where

  go :: FlatTy -> Ptr a -> Val -> IO ()
  go FlatBit           ptr (BitV b)       = poke (castPtr ptr :: Ptr Word8 ) (if b then 1 else 0)
  go FlatU64           ptr (U64V x)       = poke (castPtr ptr :: Ptr Word64) x
  go (FlatNamed _ fty) ptr (WrapV _ val)  = go    fty ptr val
  go (FlatStruct fts)  ptr (StructV xs)   = goTup fts ptr xs

  goTup :: [FlatTy] -> Ptr a -> [Val] -> IO ()
  goTup []     _   []     = return ()
  goTup (t:ts) ptr (x:xs) = do
    let k = flatTySize t 
    go    t           ptr    x
    goTup ts (plusPtr ptr k) xs

{-
pokeFlatTy_ :: ForeignPtr a -> Val -> IO ()
pokeFlatTy_ fptr val = withForeignPtr fptr $ \ptr -> void (go ptr val) where

  go :: Ptr a -> Val -> IO Int
  go ptr (BitV b)       = poke (castPtr ptr :: Ptr Word8 ) (if b then 1 else 0) >> return 1
  go ptr (U64V x)       = poke (castPtr ptr :: Ptr Word64) x                    >> return 1
  go ptr (WrapV _ val)  = go    ptr val
  go ptr (StructV xs)   = goTup ptr xs

  goTup :: Ptr a -> [Val] -> IO Int
  goTup _   []     = return 0
  goTup ptr (x:xs) = do
    k  <- go ptr x
    ks <- goTup (plusPtr ptr k) xs
    return (k + ks)
-}

--------------------------------------------------------------------------------
