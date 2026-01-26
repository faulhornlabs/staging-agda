
module Main where

--------------------------------------------------------------------------------

import Data.Bits

import Control.Monad

import Text.Read
import Text.Show.Pretty

import AST.Term
import AST.Val
import AST.Random
import Run.Eval

import CodeGen.Lifting
import CodeGen.ANF
import CodeGen.C.Source

import Big.Marshal
import Big.Limbs

--------------------------------------------------------------------------------

-- main = main_Poseidon
-- main = main_MontP
-- main = main_LetFun
-- main = main_Lift
-- main = main_Lam
-- main = main_ModP 
-- main = main_binary
-- main = main_Mod1
-- main = main_Small1
-- main = main_Nat

main = main_modInv
-- main = main_tiny_modInv
-- main = main_baby_modInv
-- main = main_montDiv
-- main = main_recAdd
-- main = runCommon "examples/ex_closure1.ast" $ \_ -> return ()

--main = runCommon "examples/ex_fft0.ast" $ \_ -> return ()
--main = runCommon "examples/ex_io2.ast" $ \_ -> return ()

main_binary = do
  runCommon "examples/ex_binary.ast" $ \_ -> return ()
  putStrLn $ "\nexpected = " ++ show expected ++ "\n"
  where
    xs = integerToLimbs 4 12535032671501493392438659292886563663979619812816639413586309554197071221275
    ys = integerToLimbs 4 20670156704232560809430694243501641649572216251781105022963497476851362916519
    zs = integerToLimbs 4 10734482926936635597888852654981536388697257091861152194513442686302125663795
    f x y z = (x .|. y) `xor` (complement x .&. z)
    expected = zipWith3 f xs ys zs

main_Lam = do
  runCommon "examples/ex_mixed.ast" $ \_ -> return ()

main_Lift = do
  runCommon "examples/ex_lift1.ast" $ \_ -> return ()

main_Nat = do
  runCommon "examples/ex_nat2.ast" $ \_ -> return ()

main_LetFun = do
  runCommon "examples/ex_letfun1.ast" $ \_ -> return ()

main_Small1 = do
  runCommon "examples/ex_small1.ast" $ \_ -> return ()

main_Mod1 = do
  runCommon "examples/ex_mod1.ast" $ \_ -> return ()

main_recAdd = do
  --runCommon "examples/ex_recadd.ast" $ \_ -> return ()
  runCommon "examples/ex_recmul.ast" $ \_ -> return ()

main_ModP = do
  runCommon "examples/ex.ast" $ \res -> case res of
    WrapV _ bigint -> do
      printBigIntVal bigint
      putStrLn $ "expected : " ++ show xplusy
  where
    r = mod (2^256) p
    p = 21888242871839275222246405745257275088548364400416034343698204186575808495617
    x = 12535032671501493392438659292886563663979619812816639413586309554197071221275
    y = 20670156704232560809430694243501641649572216251781105022963497476851362916519
    z = 10734482926936635597888852654981536388697257091861152194513442686302125663795
    xplusy = mod (x+y) p
    expected = xplusy

main_montDiv = do
  runCommon "examples/ex_montdiv.ast" $ \res -> case res of
    WrapV _ bigint -> do
      printBigIntVal bigint

main_modInv = do
  putStrLn $ "expected inv : " ++ show invx
  putStrLn $ "expected div : " ++ show divxy
  putStrLn $ "sanity #1 (should be 1) = " ++ show sanity1 
  putStrLn $ "sanity #2 (should be 1) = " ++ show sanity2
  putStrLn $ "expected inv limbs : " ++ show (integerToLimbs 4 invx)
  putStrLn $ "expected div limbs : " ++ show (integerToLimbs 4 divxy)
  runCommon "examples/ex_modinv.ast" $ \res -> case res of
    WrapV _ bigint -> do
      printBigIntVal bigint
  where
    p = 21888242871839275222246405745257275088548364400416034343698204186575808495617
    x = 12535032671501493392438659292886563663979619812816639413586309554197071221275
    y = 20670156704232560809430694243501641649572216251781105022963497476851362916519
    -- from mathematica, because i don't have an inverse implementation here at hand
    invx = 20497519080257943986776131743913968879269810845517545049759101570108377018150
    invy = 9722546401593205226690879571419363794059601560122949494573692666275298887729
    divxy   = mod (x*invy) p
    sanity1 = mod (x*invx) p 
    sanity2 = mod (y*invy) p 

main_tiny_modInv = do
  putStrLn $ "expected inv : " ++ show invx
  putStrLn $ "expected div : " ++ show divxy
  putStrLn $ "sanity #1 (should be 1) = " ++ show sanity1 
  putStrLn $ "sanity #2 (should be 1) = " ++ show sanity2
  runCommon "examples/ex_modinv.ast" $ \res -> case res of
    WrapV _ bigint -> do
      printBigIntVal bigint
  where
    p = 1299709
    x = 386048
    y = 713841
    -- from mathematica, because i don't have an inverse implementation here at hand
    invx = 1013280
    invy = 590558
    divxy   = mod (x*invy) p
    sanity1 = mod (x*invx) p 
    sanity2 = mod (y*invy) p 

main_baby_modInv = do
  putStrLn $ "expected inv1 : " ++ show invx
  putStrLn $ "expected inv2 : " ++ show invy
  putStrLn $ "expected div  : " ++ show divxy
  putStrLn $ "sanity #1 (should be 1) = " ++ show sanity1 
  putStrLn $ "sanity #2 (should be 1) = " ++ show sanity2
  runCommon "examples/ex_modinv.ast" $ \res -> case res of
    WrapV _ bigint -> do
      printBigIntVal bigint
  where
    p = 61
    x = 17
    y = 23
    -- from mathematica, because i don't have an inverse implementation here at hand
    invx = 18
    invy =  8
    divxy   = mod (x*invy) p
    sanity1 = mod (x*invx) p 
    sanity2 = mod (y*invy) p 


main_MontP = do
  runCommon' False "examples/ex_mont2d.ast" $ \res -> case res of
    bigint -> do
      printBigIntVal bigint

main_Poseidon = do
  runCommon' False "examples/ex_posei5.ast" $ \res -> case res of
    StructV [bigx, bigy, bigz] -> do
      printBigIntVal bigx
      printBigIntVal bigy
      printBigIntVal bigz

{-
  runCommon "examples/ex_mont.ast" $ \res -> case res of
    WrapV _ bigint -> do
      printBigIntVal bigint
-}


----------------------------------------

runCommon :: FilePath -> (Val -> IO a) -> IO a
runCommon = runCommon' True

runCommon' :: Bool -> FilePath -> (Val -> IO a) -> IO a
runCommon' printAstFlag fname kont = do
  text <- readFile fname
  let mbAST = readMaybe text :: Maybe AST
  case mbAST of
    Nothing  -> error $ "cannot parse AST from `" ++ fname ++ "`"
    Just ast -> do

      when printAstFlag $ do
        putStrLn "---------------------------"
        print ast

      putStrLn "---------------------------"
      putStrLn $ "program type = " ++ show (inferTy_ ast)

      res <- eval ast

      putStrLn $ "\neval result = " ++ show res

      let program = lambdaLift   ast
      let anf     = programToANF program
      let csource = anfToCSource anf 

      putStrLn $ "\nresult of the original term     = " ++ show res

      when printAstFlag $ do
        putStrLn "---------------------------"
        putStrLn $ "lambda-lifted program:"
        printProgram program

      res' <- runProgram program
      putStrLn $ "\nresult of lambda lifted program = " ++ show res' 

      when printAstFlag $ do
        putStrLn "---------------------------"
        putStrLn $ "ANF converted program:"
        printANFProgram anf

      when printAstFlag $ do 
        putStrLn "---------------------------"
        putStrLn $ "C source code:"
        putStrLn csource
  
      writeFile "examples/out.c" csource

      res'  <- runProgram program
      res'' <- runANFProgram anf

      putStrLn $ "\nresult of the original term     = " ++ show res
      putStrLn $ "\nresult of lambda lifted program = " ++ show res' 
      putStrLn $ "\nresult of ANF converted program = " ++ show res''
      putStrLn " "
      kont res

--------------------------------------------------------------------------------
-- DEBUGGING

exRaw0 :: Raw
exRaw0 = 
  -- Lit (U64L 101) 
  -- (Pri (MkRawPrim "AddU64") [ Lit (U64L 101) , Lit (U64L 102) ])
  Let U64 (Lit (U64L 101)) (Var 0)

exRaw1 :: Raw
exRaw1 = Let U64 
  (Pri (MkRawPrim "AddU64") [ Lit (U64L 101) , Lit (U64L 102) ])
  (Pri (MkRawPrim "MulTruncU64") [ Var 0 , Var 0 ])

exRaw2 :: Raw
exRaw2 = Let U64 (Lit (U64L 666)) (Pri (MkRawPrim "MulTruncU64") [Var 0,App (App (Lam U64 (Lam U64 (Var 2))) (Lit (U64L 11999))) (Lit (U64L 25715))])

exRaw3 :: Raw
exRaw3 = Let U64 (Lit (U64L 666)) (Pri (MkRawPrim "AddU64") [Let U64 (Var 0) (Lit (U64L 30236)),Let U64 (Lit (U64L 25007)) (Var 1)])

exRaw4 :: Raw
exRaw4 = Let U64 (Lit (U64L 666)) (Let U64 (Let U64 (Var 0) (Lit (U64L 49887))) (Let U64 (Lit (U64L 22063)) (Var 2)))

debugAnfConversion :: Size -> IO ()
debugAnfConversion target = do
  term <- randomTermU64 target
  debugAnfConversion' term

debugAnfConversion' :: Raw -> IO ()
debugAnfConversion' term = do
  if (inferTy_ term /= U64) 
    then error "debugAnfConversion: type inference doesn't match expectations"
    else do
      let prg  = lambdaLift   term
      let anf  = programToANF prg

      putStrLn "---------------------------"
      putStrLn $ "raw program:"
      print term
      putStrLn "---------------------------"
      putStrLn $ "lambda-lifted program:"
      printProgram prg
      putStrLn "---------------------------"
      putStrLn $ "ANF converted program:"
      printANFProgram anf

      res1 <- eval term
      res2 <- runProgram prg
      res3 <- runANFProgram anf
      putStrLn $ "result of original      = " ++ show res1
      putStrLn $ "result of lambda-lifted = " ++ show res2
      putStrLn $ "result of anf converted = " ++ show res3

findAnfCounterExample :: Size -> IO Raw
findAnfCounterExample target = do
  term <- randomTermU64 target
  let prg  = lambdaLift   term
  let anf  = programToANF prg
  res2 <- runProgram prg
  res3 <- runANFProgram anf
  if (res2 /= res3) 
    then return term
    else findAnfCounterExample target

--------------------------------------------------------------------------------

testLambdaLifting1 :: Size -> IO Bool
testLambdaLifting1 target = do
  term <- randomTermU64 target
  if (inferTy_ term /= U64) 
    then error "testLambdaLifting1: type inference doesn't match expectations"
    else do
      let prg  = lambdaLift term
      res1 <- eval term
      res2 <- runProgram prg
      return (res1 == res2)
  
testAnfConversion1 :: Size -> IO Bool
testAnfConversion1 target = do
  term <- randomTermU64 target
  if (inferTy_ term /= U64) 
    then error "testAnfConversion1: type inference doesn't match expectations"
    else do
      let prg  = lambdaLift   term
      let anf  = programToANF prg
      res1 <- eval term
      res2 <- runProgram prg
      res3 <- runANFProgram anf
      return (res2 == res3)

testLambdaLiftingN :: Int -> Size -> IO Bool
testLambdaLiftingN n target = and <$> replicateM n (testLambdaLifting1 target)
  
testAnfConversionN :: Int -> Size -> IO Bool
testAnfConversionN n target = and <$> replicateM n (testAnfConversion1 target)

--------------------------------------------------------------------------------


