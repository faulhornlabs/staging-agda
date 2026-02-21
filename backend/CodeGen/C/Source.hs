
{-# LANGUAGE PatternSynonyms #-}
module CodeGen.C.Source where

--------------------------------------------------------------------------------

import Data.List
import Data.Word
import Text.Printf

import Control.Monad
import Control.Monad.Reader
import Control.Monad.State.Strict

import qualified Data.Set      as Set ; import Data.Set      ( Set )
import qualified Data.Map      as Map ; import Data.Map      ( Map )
import qualified Data.Sequence as Seq ; import Data.Sequence ( Seq , (|>) , (<|) , (><) )
import qualified Data.Foldable as F

import AST.Ty
import AST.Literal
import AST.PrimOp

import CodeGen.Lifting ( Program'(..) , Program , FunDef'(..) , FunDef )
import CodeGen.ANF     ( Atom(..) , ExpA(..) , ANF(..) , ANFE , extractAllTysExp , typeOfANFE )

import CodeGen.C.Types
import CodeGen.C.Prelude

import Aux.Lens
import Aux.Misc

--------------------------------------------------------------------------------

anfToCSource :: Program ANFE -> String
anfToCSource program@(MkProgram toplevel main) = cprelude ++ sep ++ unlines tydecls ++ sep ++ code where
  topnames = fmap _funName toplevel
  (tydecls, tymap) = calculateTyMapping program
  code = runCodegenM topnames tymap action
  action = do
    generatePrints   (Map.keys tymap)
    generatePrintLns (Map.keys tymap)
    genProgramCode program

sep :: String
sep = "\n//------------------------------------------------------------------------------\n"

addMain :: Ty -> CG ()
addMain mainTy = do
  tyname <- fetchTyName mainTy
  addLine $ "int main() {"
  addLine $ "  printf(\"hello, generated C code!\\n\");"
  addLine $ "  println_" ++ replaceSpaceByUnderscore tyname ++ "( \"final result\" , program() );"
  addLine $ "}"

--------------------------------------------------------------------------------

type Indent = Int

indent1 :: Indent -> String -> String
indent1 k str = replicate (2*k) ' ' ++ str

indentMany :: Indent -> [String] -> [String]
indentMany k = map (indent1 k)

indentText :: Indent -> String -> String
indentText k = unlines . indentMany k . lines

--------------------------------------------------------------------------------

-- indentantion and list of top-level names
data R = MkR
  { _indent   :: !Indent
  , _topNames :: !(Seq String)
  , _tyNames  :: !(Map Ty String)
  }
  deriving Show

incIndent :: R -> R
incIndent old = old { _indent = _indent old + 1 }

data S = MkS
  { _source :: !(Seq String)
  , _unique :: !Int
  }

iniS :: S
iniS = MkS Seq.empty 0

type CG a = StateT S (Reader R) a

askR :: CG R
askR = lift ask

fetchTyName :: Ty -> CG CType
fetchTyName ty = do
  table <- _tyNames <$> askR
  case Map.lookup ty table of 
    Just ctype -> return ctype
    Nothing    -> error $ "type not found in C type mapping table: " ++ show ty

fetchFunName :: TopLev -> CG String
fetchFunName k = do
  sequ <- _topNames <$> askR
  return (Seq.index sequ k)

freshName :: String -> CG String
freshName prefix = do
 MkS blocks cnt <- get
 put $! MkS blocks (cnt+1)
 return (prefix ++ show cnt)

addRawText :: String -> CG ()
addRawText text = do
 MkS blocks cnt <- get
 put $! MkS (blocks |> text) cnt

addLines :: [String] -> CG ()
addLines ls = do 
  MkR k _ _ <- lift ask
  addRawText $ unlines $ indentMany k ls

addLine :: String -> CG ()
addLine = addLines . (:[])

withIndent :: CG a -> CG a
withIndent action = do
  local incIndent action

inBlock :: CG a -> CG a
inBlock action = do
  addLine "{"
  y <- withIndent action
  addLine "}"
  return y

runCodegenM :: Seq String -> Map Ty String -> CG a -> a
runCodegenM topNames tyNames action = runReader (evalStateT action iniS) (MkR 0 topNames tyNames)

--------------------------------------------------------------------------------

addProgram :: Program ANFE -> CG ()
addProgram (MkProgram fundefs mainANF) = do
  mapM addFunDecl fundefs
  addLine sep
  mapM addFunDef fundefs
  let mainTy    = typeOfANFE mainANF 
  let mainFunTy = MkFunTy [] mainTy
  let preMain   = MkFunDef 0 "program" (MkLams mainFunTy mainANF)
  addFunDef preMain
  addLine sep
  addMain $ typeOfANFE mainANF

genProgramCode :: Program ANFE -> CG String
genProgramCode program = do
  addProgram program
  MkS blocks _ <- get
  return (concat $ F.toList blocks)

--------------------------------------------------------------------------------

type CVar = String

data DeclSet 
  = DeclareAndSet
  | JustSet      

addLet :: Level -> Typed ExpA -> CG ()
addLet level tyExpr@(MkTyped ty expr) = 
  unless (isArrowTy ty) $ do
    let cvar = "x" ++ show level
    cgenExp level DeclareAndSet cvar tyExpr

{-
    -- debugging only, print every termporary result
    MkCTy _ cty <- fetchCTy ty
    addLine $ "println_" ++ replaceSpaceByUnderscore cty ++ "( " ++ show cvar ++ " , " ++ cvar ++ ");"
-}


cgenExp :: Level -> DeclSet -> CVar -> Typed ExpA -> CG ()
cgenExp level declset cvar (MkTyped ty expr) = do
  cty <- fetchTyName ty
  let declPrefix    = cty ++ " " ++ cvar ++ ";"
      declSetPrefix = cty ++ " " ++ cvar ++ " = "
      justSetPrefix =               cvar ++ " = (" ++ cty ++ ") "
      setPrefix = case declset of
        DeclareAndSet -> declSetPrefix
        JustSet       -> justSetPrefix
  case expr of
    AtmA atom     -> addLine $ setPrefix ++ cgenAtom atom                ++ " ;"
    PriA op args  -> addLine $ setPrefix ++ cgenPrimOp (MkPrim op args)  ++ " ;"
  
    AppA idx args -> do
      fname <- fetchFunName idx
      addLine $ setPrefix ++ fname ++ "( " ++ intercalate " , " (map cgenAtom args) ++ " );"
  
    IftA cond trueBr falseBr -> do
      let cond' = cgenAtom cond
      join <- freshName "join"
      addLine $ cty ++ " " ++ join ++ ";"
      addLine $ "if (" ++ cond' ++ ")"
      inBlock (addANF' level JustSet join trueBr)
      addLine "else"
      inBlock (addANF' level JustSet join falseBr)
      addLine $ setPrefix ++ join ++ ";"

addANF' :: Level -> DeclSet -> CVar -> ANFE -> CG String 
addANF' level declset cvar (MkANF lets body@(MkTyped ty expr)) = do
  forM_ (zip [level..] (F.toList lets)) $ \(i,exp) -> addLet i exp
  let level' = level + (Seq.length lets)
  cgenExp level' declset cvar body
  return cvar

-- addANFWithSet :: Level -> CVar -> ANFE -> CG ()
-- addANFWithSet level cvar anf = do
--   final <- addANF' level cvar anf
--   let set = cvar ++ " = " ++ final ++ ";"
--   addLine set

addANFWithReturn :: Level -> ANFE -> CG ()
addANFWithReturn level anf = do
  result <- freshName "result"
  final  <- addANF' level DeclareAndSet result anf
  let ret = "return (" ++ final ++ ");"
  addLine ret

addFunDecl :: FunDef ANFE -> CG ()
addFunDecl = addFunDecl' True

addFunDecl' :: Bool -> FunDef ANFE -> CG ()
addFunDecl' semicolon (MkFunDef idx name (MkLams funTy@(MkFunTy argTys retTy) body)) = do
  cretTy <- fetchTyName retTy
  let arity = length argTys
  args <- forM (zip [0..] argTys) $ \(i,ty) -> do
    cty <- fetchTyName ty
    return (cty ++ " x" ++ show i)
  let decl = cretTy ++ " " ++ name ++ "( " ++ intercalate " , " args ++ " )" ++ (if semicolon then ";" else "")
  addLine decl
  
addFunDef :: FunDef ANFE -> CG ()
addFunDef fundef@(MkFunDef idx name (MkLams funTy@(MkFunTy argTys retTy) body)) = do
  let arity = length argTys
  addFunDecl' False fundef
  inBlock $ addANFWithReturn arity body
  addLine ""
{-
  cretTy <- fetchTyName retTy
  let arity = length argTys
  args <- forM (zip [0..] argTys) $ \(i,ty) -> do
    cty <- fetchTyName ty
    return (cty ++ " x" ++ show i)
  let decl = cretTy ++ " " ++ name ++ "( " ++ intercalate " , " args ++ " )"
  addLine decl
  inBlock $ addANFWithReturn arity body
-}


--------------------------------------------------------------------------------

cgenAtom' :: Program a -> Atom -> String
cgenAtom' program@(MkProgram toplevel main) atom = case atom of
  TopA k -> _funName (Seq.index toplevel k)
  _      -> cgenAtom atom

cgenAtom :: Atom -> String
cgenAtom atom = case atom of
  KstA l -> cgenLit l
  VarA j -> "x" ++ show j 
  TopA k -> error "cgenAtom: top level function"

--------------------------------------------------------------------------------

cgenLit :: Literal -> String
cgenLit val = case val of
  TtL         -> "(Unit)0"
  BitL b      -> if b then "1" else "0"
  U64L x      -> printf "0x%x" x
  NatL n      -> show n
  StructL xs  -> cgenStruct_ (map cgenLit xs)
  WrapL _ x   -> cgenLit x

cgenStruct_ :: [String] -> String
cgenStruct_ xs = "{ " ++ intercalate " , " xs ++ " }"

--------------------------------------------------------------------------------

data Prim a 
  = MkPrim RawPrim [a]
  deriving (Eq,Show)

cgenPrimOp :: Prim Atom -> String
cgenPrimOp primArgs = case primArgs of

  MkPrim (MkRawPrim prim   ) args     -> cgenNormalPrim (prim, args)
  MkPrim (RawProj   j      ) [struct] -> cgenAtom struct ++ "._field" ++ show j
  MkPrim (RawWrap   name   ) [x]      -> cgenAtom x
{-
  MkPrim (RawInput  name ty) []       -> error "cgenPrimOp: input: not implemented"
  MkPrim (RawOutput name   ) [x]      -> error "cgenPrimOp: output: not implemented"
-}
  _ -> error "cgenPrimOp: invalid combination"

--------------------------------------------------------------------------------

-- just sugar for nicer patterns below
pattern name :@@ args = (name, args)

cgenNormalPrim :: (String , [Atom]) -> String
cgenNormalPrim primArgs = 

  case primArgs of

    "AddU64"        :@@ [ x , y ]        -> cgenAtom x ++ " + " ++ cgenAtom y
    "SubU64"        :@@ [ x , y ]        -> cgenAtom x ++ " - " ++ cgenAtom y
    "AddCarryU64"   :@@ [ cin , x , y ]  -> "addCarryU64( " ++ cgenAtom cin ++ " , " ++ cgenAtom x ++ " , " ++ cgenAtom y ++ ")" 
    "SubCarryU64"   :@@ [ cin , x , y ]  -> "subCarryU64( " ++ cgenAtom cin ++ " , " ++ cgenAtom x ++ " , " ++ cgenAtom y ++ ")" 
    "MulTruncU64"   :@@ [ x , y ]        -> cgenAtom x ++ " * " ++ cgenAtom y
    "MulExtU64"     :@@ [ x , y ]        -> "mulExtU64( " ++ cgenAtom x ++ " , " ++ cgenAtom y ++ ")"
    "MulAddU64"     :@@ [ a  , x , y ]   -> "mulAddU64( " ++ cgenAtom a ++ " , " ++ cgenAtom x ++ " , " ++ cgenAtom y ++ ")" 
    "BitComplement" :@@ [ x ]            -> "~ " ++ cgenAtom x 
    "BitOr"         :@@ [ x , y ]        -> cgenAtom x ++ " | " ++ cgenAtom y
    "BitAnd"        :@@ [ x , y ]        -> cgenAtom x ++ " & " ++ cgenAtom y
    "BitXor"        :@@ [ x , y ]        -> cgenAtom x ++ " ^ " ++ cgenAtom y
    "RotLeftU64"    :@@ [ cin , x ]      -> "rotLeftU64( "  ++ cgenAtom cin ++ " , " ++ cgenAtom x ++ " )"
    "RotRightU64"   :@@ [ cin , x ]      -> "rotRightU64( " ++ cgenAtom cin ++ " , " ++ cgenAtom x ++ " )"
    "ShiftLeftByU64 " :@@ [ x , k ]      -> "(x<<k)"
    "ShiftRightByU64" :@@ [ x , k ]      -> "(x>>k)"
    "EqU64"         :@@ [ x   , y ]      -> "(" ++ cgenAtom x ++ " == " ++ cgenAtom y ++ ")"
    "LtU64"         :@@ [ x   , y ]      -> "(" ++ cgenAtom x ++ " < "  ++ cgenAtom y ++ ")"
    "LeU64"         :@@ [ x   , y ]      -> "(" ++ cgenAtom x ++ " <= " ++ cgenAtom y ++ ")"
    "CastBitU64"    :@@ [ b ]            -> "(uint64_t)" ++ cgenAtom b
    "Not"           :@@ [ b ]            -> "!" ++ cgenAtom b
    "And"           :@@ [ a , b ]        -> cgenAtom a ++ " && " ++ cgenAtom b
    "Or"            :@@ [ a , b ]        -> cgenAtom a ++ " || " ++ cgenAtom b
    "IFTE"          :@@ [ b , x , y ]    -> error "IFTE primop shouldn't appear in ANF"
    "MkStruct"      :@@ xs               -> cgenStruct_ (map cgenAtom xs)
    "Unwrap"        :@@ [ x]             -> cgenAtom x
    "Zero"          :@@ []               -> "0"
    "Succ"          :@@ [ n ]            -> cgenAtom n ++ " + 1"
    "IsZero"        :@@ [ n ]            -> "(" ++ cgenAtom n ++ " == 0)"
    "NatAdd"        :@@ [ x , y ]        -> cgenAtom x ++ " + " ++ cgenAtom y
    "NatMul"        :@@ [ x , y ]        -> cgenAtom x ++ " * " ++ cgenAtom y
    "NatSubTrunc"   :@@ [ x , y ]        -> "MAX( 0 , " ++ cgenAtom x ++ " - " ++ cgenAtom y ++ ")"

    _ -> error $ "cgenNormalPrim: unknown / unhandled primop: `" ++ fst primArgs ++ "`"

--------------------------------------------------------------------------------

data TyState = MkTyState
  { _tyMap  :: !TyMap   
  , _tyDefs :: ![CDecl] 
  , _tySCnt :: !Int     
  } 
  deriving Show

iniTyState :: TyState
iniTyState = MkTyState
  { _tyMap  = builtInTypes -- Map.empty
  , _tyDefs = []
  , _tySCnt = 0 
  } 

myTyLenses :: TyLenses TyState
myTyLenses = MkTyLenses 
  { tyMapLens  = MkLens _tyMap  $ \x s -> s { _tyMap  = x }
  , tyDefsLens = MkLens _tyDefs $ \y s -> s { _tyDefs = y }
  , tySCntLens = MkLens _tySCnt $ \z s -> s { _tySCnt = z }
  } 

calculateTyMapping :: Program ANFE -> ( [CDecl] , Map Ty CType )
calculateTyMapping (MkProgram tops main) = 
  case execState prgAction iniTyState of 
    tyState -> (reverse (_tyDefs tyState) , _tyMap tyState)

  where
    
    prgAction :: State TyState ()
    prgAction = do
      mapM_ workerFunDef (F.toList tops)
      workerANF main

    workerFunDef :: FunDef ANFE -> State TyState ()
    workerFunDef (MkFunDef idx name (MkLams (MkFunTy argsTy retTy) body)) = do
      mapM_ workerTy argsTy
      workerTy retTy 
      workerANF body

    workerANF :: ANFE -> State TyState ()
    workerANF (MkANF lets expr) = do
      mapM_ workerTyExp lets
      workerTyExp expr
      
    workerTyExp :: Typed ExpA -> State TyState ()
    workerTyExp (MkTyped ty expr) = do
      workerTy  ty
      workerExp expr

    workerTy :: Ty -> State TyState ()
    workerTy ty = do
      unless (isArrowTy ty) $ do
        void $ getTyName myTyLenses ty
      return ()

    workerExp :: ExpA -> State TyState ()
    workerExp expr = do
      mapM_ workerTy $ Set.toList $ extractAllTysExp expr

--------------------------------------------------------------------------------

replaceSpaceByUnderscore :: String -> String
replaceSpaceByUnderscore = map f where
  f ' ' = '_'
  f c   = c 

data CTy 
  = MkCTy Ty String
  deriving Show

fetchCTy :: Ty -> CG CTy
fetchCTy ty = MkCTy ty <$> fetchTyName ty

generatePrints :: [Ty] -> CG ()
generatePrints tys = do

  addLine ""
  addLine "// print declarations"
  addLine ""

  let cond (MkCTy ty _) = not (isAtomicBuiltInTy ty) && not (isArrowTy ty)
  ctys <- filter cond <$> mapM fetchCTy tys
  let decls = [ "void print_" ++ replaceSpaceByUnderscore cty ++ "( " ++ cty ++ " );" | MkCTy _ cty <- ctys ]
  addLines decls 

  addLine ""
  addLine "// print definitions"

  forM_ ctys $ \(MkCTy ty cty) -> do
    let first = "\nvoid print_" ++ replaceSpaceByUnderscore cty ++ "( " ++ cty ++ " input ) {"
    let last_ = "}"
    body <- case ty of 
      
      Named name what -> do
        MkCTy _ inner <- fetchCTy what
        let body = 
              [ "printf(\"" ++ name ++ " (\");"
              , "print_" ++ replaceSpaceByUnderscore inner ++ " ( input );"
              , "printf(\")\");"
              ]
        return $ body

      Struct types -> do 
        middle <- forM (zip [0..] types) $ \(i,what) -> do
          MkCTy _ component <- fetchCTy what
          return $ "print_" ++ replaceSpaceByUnderscore component ++ "( input._field" ++ show i ++ " );"
        let open  = "printf(\"[ \");"
            close = "printf(\" ]\");"
            sep   = "printf(\" , \");"
        let body = [open] ++ intersperse sep middle ++ [close]
        return body
       
      _ -> error $ "generatePrints: type is not handled: " ++ show ty

    addLine first 
    withIndent $ addLines body
    addLine last_ 

  addLine sep

generatePrintLns :: [Ty] -> CG ()
generatePrintLns tys = do

  addLine ""
  addLine "// println declarations"
  addLine ""

  let cond (MkCTy ty _) = not (isArrowTy ty)
  ctys <- filter cond <$> mapM fetchCTy tys
  let decls = [ "void println_" ++ replaceSpaceByUnderscore cty ++ "( const char * , " ++ cty ++ " );" | MkCTy _ cty <- ctys ]
  addLines decls 

  forM_ ctys $ \(MkCTy ty cty) -> do
    let first = "\nvoid println_" ++ replaceSpaceByUnderscore cty ++ "( const char *name , " ++ cty ++ " input ) {"
    let body = 
          [ "if (name != 0) { printf(\"%s = \", name); }"
          , "print_" ++ replaceSpaceByUnderscore cty ++ "( input );"
          , "printf(\"\\n\");"
          ]
    addLine first 
    withIndent $ addLines body
    addLine "}"

  addLine sep

--------------------------------------------------------------------------------
      