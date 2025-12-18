
-- | CLI executable

{-# LANGUAGE RecordWildCards #-}
module Main where

--------------------------------------------------------------------------------

import Control.Monad

import Text.Read
import Text.Show.Pretty

import Data.Maybe

import Data.Semigroup ( (<>) )
import Options.Applicative
import System.Exit
import System.Environment

import AST.Term
import AST.Random

import Run.Eval
import Run.Input

import CodeGen.Lifting
import CodeGen.ANF
import CodeGen.C.Source

import Big.Marshal
import Big.Limbs

--------------------------------------------------------------------------------

main :: IO ()
main = cliMain

cliMain :: IO ()
cliMain = do
  opts <- execParser options
  let files = optFiles opts
  let flags = optFlags opts
  when (flagVerbosity flags >= Verbose) $ printOpts opts

  case (fileAST files) of
    Nothing -> do
      putStrLn "no AST file given; nothing to do."
      putStrLn "use the option `-h` or `--help` to see the available options"
    Just astFile -> do
      runCommon flags files

--------------------------------------------------------------------------------

printSeparator :: IO ()
printSeparator = do
  putStrLn "\n----------------------------------------"

printSeparatorHeader :: String -> IO ()
printSeparatorHeader header = do
  printSeparator
  putStrLn $ "*** " ++ header ++ ":"

whenJust :: Maybe a -> (a -> IO ()) -> IO ()
whenJust mb action = case mb of
  Just x  -> action x
  Nothing -> return ()

--------------------------------------------------------------------------------

runCommon :: Flags -> Files -> IO ()
runCommon MkFlags{..} MkFiles{..} = do
  let fname = fromJust fileAST
  text <- readFile fname
  let mbAST = readMaybe text :: Maybe AST
  case mbAST of
    Nothing  -> error $ "cannot parse AST from `" ++ fname ++ "`"
    Just ast -> do
      let printAstFlag = (flagVerbosity >= Debug)

      when printAstFlag $ do
        printSeparatorHeader "original AST"
        print ast

      let program = lambdaLifting ast
      let anf     = programToANF  program
      let csource = anfToCSource  anf 

      when printAstFlag $ do
        printSeparatorHeader "lambda-lifted program"
        printProgram program

      when printAstFlag $ do
        printSeparatorHeader "ANF converted program"
        printANFProgram anf

      when printAstFlag $ do 
        printSeparatorHeader "C source code"
        putStrLn csource
  
      whenJust fileC $ \cfile -> do 
        when (flagVerbosity >= Verbose) $ do
          putStrLn $ "writing C output into `" ++ cfile ++ "`"
        writeFile cfile csource

      when (flagVerbosity >= Normal) $ do
        printSeparator
        putStrLn $ "program type = " ++ show (inferTy_ ast)

      inputs <- case fileInput of
        Nothing      -> return emptyInputs
        Just inpfile -> do
          text <- readFile inpfile
          let inputs = parseInputs text
          when (flagVerbosity >= Verbose) $ do
            printSeparatorHeader "inputs"
            printOutputs inputs
          return inputs

      when flagEvalProgram $ do
        printSeparator
{-
        putStrLn $ "result of the original term     = " ++ show (eval ast)           ++ "\n"
        putStrLn $ "result of lambda lifted program = " ++ show (runProgram program) ++ "\n"
        putStrLn $ "result of ANF converted program = " ++ show (runANFProgram anf)  ++ "\n"
-}
        let (out1,res1) = evalWithInputs          inputs ast 
        let (out2,res2) = runProgramWithInputs    inputs program
        let (out3,res3) = runANFProgramWithInputs inputs anf 

        putStrLn $ "result of the original term     = " ++ showVal res1 ++ "\n"
        putStrLn $ "result of lambda lifted program = " ++ showVal res2 ++ "\n"
        putStrLn $ "result of ANF converted program = " ++ showVal res3 ++ "\n"

        when (flagVerbosity >= Verbose) $ do
          putStrLn "\noutputs of the original term:"         ; printOutputs out1
          putStrLn "\noutputs of the lambda lifted program:" ; printOutputs out2
          putStrLn "\noutputs of the ANF converted program:" ; printOutputs out3


--------------------------------------------------------------------------------

data Opts = MkOpts
  { optFiles  :: Files
  , optFlags  :: Flags
  }
  deriving Show

data Files = MkFiles
  { fileAST    :: Maybe FilePath 
  , fileC      :: Maybe FilePath 
  , fileInput  :: Maybe FilePath 
  , fileOutput :: Maybe FilePath 
  , fileRef    :: Maybe FilePath 
  }
  deriving Show

data Flags = MkFlags
  { flagEvalProgram :: Bool
  , flagVerbosity   :: Verbosity
  , flagMeasureTime :: Bool
  }
  deriving Show

data Verbosity 
  = Silent
  | Normal
  | Verbose
  | Debug
  deriving (Eq,Ord,Show)

printFiles :: Files -> IO ()
printFiles files@(MkFiles{..}) = do
  putStrLn $ "AST file          = " ++ show fileAST   
  putStrLn $ "C source file     = " ++ show fileC
  putStrLn $ "Input file        = " ++ show fileInput
  putStrLn $ "Output file       = " ++ show fileOutput 
  putStrLn $ "Reference output  = " ++ show fileRef

printFlags :: Flags -> IO ()
printFlags flags@(MkFlags{..}) = do
  putStrLn $ "Evaluate program  = " ++ show flagEvalProgram 
  putStrLn $ "Verbosity         = " ++ show flagVerbosity   
  putStrLn $ "Measure time      = " ++ show flagMeasureTime 

printOpts :: Opts -> IO ()
printOpts opts = do
  putStrLn ""
  putStrLn "cli options set to:"
  putStrLn "-------------------"
  printFiles (optFiles opts)
  printFlags (optFlags opts)
  putStrLn ""

--------------------------------------------------------------------------------

options :: ParserInfo Opts
options = info (optsParser <**> helper)
  (  fullDesc
  <> header "staging-agda backend"
  )  

--------------------------------------------------------------------------------

optsParser :: Parser Opts
optsParser = MkOpts 
  <$> filesParser
  <*> flagsParser

flagsParser :: Parser Flags
flagsParser = MkFlags
  <$> evalProgramP
  <*> verbosityP  
  <*> measureTimeP

filesParser :: Parser Files
filesParser = MkFiles
  <$> astFileP
  <*> cFileP
  <*> inpFileP
  <*> outFileP
  <*> refFileP

--------------------------------------------------------------------------------

astFileP :: Parser (Maybe FilePath)
astFileP 
  = (Just <$> strOption
      (  long  "ast"
      <> short 'a'
      <> metavar "AST_FILE"
      <> help "AST file (the output from Agda)" ))
  <|> pure Nothing

cFileP :: Parser (Maybe FilePath)
cFileP 
  = (Just <$> strOption
      (  long  "csource"
      <> short 'c'
      <> metavar "C_SOURCE_FILE"
      <> help "C source file (our output)" ))
  <|> pure Nothing

inpFileP :: Parser (Maybe FilePath)
inpFileP 
  = (Just <$> strOption
      (  long  "input"
      <> short 'i'
      <> metavar "INPUT_FILE"
      <> help "input file" ))
  <|> pure Nothing

outFileP :: Parser (Maybe FilePath)
outFileP 
  = (Just <$> strOption
      (  long  "output"
      <> short 'o'
      <> metavar "OUTPUT_FILE"
      <> help "output file" ))
  <|> pure Nothing

refFileP :: Parser (Maybe FilePath)
refFileP 
  = (Just <$> strOption
      (  long  "ref"
      <> short 'r'
      <> metavar "REF_FILE"
      <> help "reference output file (for test cases)" ))
  <|> pure Nothing

----------------------------------------

verbosityP :: Parser Verbosity
verbosityP = (verbose <|> silent <|> debug <|> pure Normal) where
  verbose = flag' Verbose
    (  long  "verbose"
    <> short 'v'
    <> help  "verbose output"
    )
  silent = flag' Silent
    (  long  "silent"
    <> short 's'
    <> help  "silent output"
    )
  debug = flag' Debug
    (  long  "debug"
    <> short 'd'
    <> help  "debug output"
    )

measureTimeP :: Parser Bool
measureTimeP = switch
  (  long  "time"
  <> short 't'
  <> help  "measure running time"
  )

evalProgramP :: Parser Bool
evalProgramP = switch
  (  long  "eval"
  <> short 'E'
  <> help  "evaluate the input program"
  )

--------------------------------------------------------------------------------
