module AST

import Idris.Syntax
import Idris.Parser

import Core.FC    -- for the `PhysicalIdrSrc` type
import Core.Name    -- for the `ModuleIdent` type

import System
import System.File    -- for `readFile`

import ErrOr

import Deriving.Show
%language ElabReflection

%default covering

-------------------------------------------------------------------------------

mapM : Monad m => (f : a -> m b) -> List a -> m (List b)
mapM f [] = pure []
mapM f (x :: xs) = do
  xs' <- mapM f xs
  x' <- f x
  pure (x' :: xs')

-------------------------------------------------------------------------------
-- Erlang IR

public export
data EPat : Type where
  EPVar : String -> EPat

data EStmt : Type where
  ESVar   : String -> EStmt
  ESApp   : String -> List EStmt -> EStmt
  ESString : String -> EStmt

data EDecl : Type where
  EDNil : EDecl
  EDFun : (dn : String) -> (cs : List (List EPat, List EStmt)) -> EDecl

data EMod : Type where
  EM : (mn : String) -> List EDecl -> EMod


%hint
showEPat : Show EPat 
showEPat = %runElab derive

%hint
showEStmt : Show EStmt 
showEStmt = %runElab derive

%hint
showEDecl : Show EDecl 
showEDecl = %runElab derive

%hint
showEMod : Show EMod 
showEMod = %runElab derive


-------------------------------------------------------------------------------
-- Erlang IR Pretty Print

Tab : Type
Tab = Nat

ppEPat  : EPat -> String
ppEStmt : Tab -> EStmt -> String

ppEDecl : EDecl -> String
ppEDecl EDNil = ""
ppEDecl (EDFun dn cs) = dn ++ "() -> ok.\n"

ppEMod  : EMod -> String
ppEMod (EM mn ds) =
  let ds' = map ppEDecl ds
  in "-module(" ++ mn ++ ").\n\n" ++ (concat ds')


-------------------------------------------------------------------------------
-- IR Generation

getNameFrmName : Name.Name -> ErrorOr String
getNameFrmName n =
  case displayName n of
      (Nothing, n') => Just n'
      _ => error "getNameFrmTerm -- PRef -- non-empty namespace"

getNameFrmTerm : PTerm -> ErrorOr String
getNameFrmTerm (PRef fc' n) =
  getNameFrmName n
getNameFrmTerm (PApp fc' f x) =
  getNameFrmTerm f
getNameFrmTerm tm = error $ "getNameFrmTerm -- unimplemented -- " ++ show tm

getNameFrmClause : PClause -> ErrorOr String
getNameFrmClause (MkPatClause fc lhs _ _) =
  getNameFrmTerm lhs
getNameFrmClause (MkWithClause fc lhs _ _ _) =
  error "getNameFrmClause -- MkWithClause"
getNameFrmClause (MkImpossible fc lhs) =
  error "getNameFrmClause -- MkImpossible"

toEVarName : String -> ErrorOr String
toEVarName str =
  case strM str of
    StrNil => error "toEVarName: empty string"
    StrCons x xs => pure (strCons (toUpper x) xs)

genEPats : PTerm -> ErrorOr (List EPat)
genEPats (PRef fc n) =
  map (\n' => [EPVar n']) (getNameFrmName n >>= toEVarName)
genEPats (PApp fc (PRef _ _) x) =
  genEPats x
genEPats (PApp fc f x) = do
  xs <- genEPats f
  ys <- genEPats x
  pure (xs ++ ys)

genEPats p = error $ "genEPats: unimplemeted -- " ++ show p

genEPatsTop : PTerm -> ErrorOr (List EPat)
genEPatsTop (PRef fc n) = Just []
genEPatsTop p = genEPats p

mutual
  genEStmtsDo : PDo -> ErrorOr (List EStmt)
  genEStmtsDo (DoExp fc tm) = genEStmts tm
  genEStmtsDo (DoBind _ _ _ _) =
    error $ "genEStmtsDo: unimplemented -- DoBind"
  genEStmtsDo (DoBindPat _ _ _ _) =
    error $ "genEStmtsDo: unimplemented -- DoBindPat"
  genEStmtsDo (DoLet _ _ _ _ _ _) =
    error $ "genEStmtsDo: unimplemented -- DoLet"
  genEStmtsDo (DoLetPat _ _ _ _ _) =
    error $ "genEStmtsDo: unimplemented -- DoLetPat"
  genEStmtsDo (DoLetLocal _ _) =
    error $ "genEStmtsDo: unimplemented -- DoLetLocal"
  genEStmtsDo (DoRewrite _ _) =
    error $ "genEStmtsDo: unimplemented -- DoRewrite"

  genEStmtsStr : PStr -> ErrorOr String
  genEStmtsStr (StrLiteral fc str) = Just str
  genEStmtsStr (StrInterp fc tm) =
    error $ "genEStmtsStr: unimplemented -- StrInterp"

  genEStmts : PTerm -> ErrorOr (List EStmt)
  genEStmts (PRef fc n) =
    map (\n' => pure (ESVar n')) (getNameFrmName n)
  genEStmts (PApp fc f x) = do
    ESApp fn xs  <- genEStmt f
      | ESVar fn => do
        x' <- genEStmt x
        pure [ESApp fn [x']]
      | f' => error $ "TODO: " ++ show f'
    x' <- genEStmt x
    pure [ESApp fn (xs ++ [x'])]
  genEStmts (PString fc ht strs) = do
    strs' <- mapM genEStmtsStr strs
    pure [ESString (concat strs')]
  genEStmts (PDoBlock fc mns dss) = do 
    stmts <- mapM genEStmtsDo dss
    pure (concat stmts)
  genEStmts tm = error $ "genEStmts: unimplemented -- "  ++ show tm

  genEStmt : PTerm -> ErrorOr EStmt
  genEStmt tm = do
    (stmt :: _) <- genEStmts tm
      | [] => error $ "genEStmt: no statements generated"
    pure stmt

genEClause : PClause -> ErrorOr (List EPat, List EStmt)
genEClause (MkPatClause fc lhs rhs ws) = do
  pats <- genEPatsTop lhs
  stmts <- genEStmts rhs
  Just (pats, stmts) -- IGNORE WHERE BLOCK
genEClause c = error $ "genEClause: unimplemented -- " ++ show c

genEDecl : PDecl -> ErrorOr EDecl
genEDecl (PDef fc cs@(c :: _)) = do
  dn <- getNameFrmClause c
  body <- mapM genEClause cs
  pure (EDFun dn body) -- FIXME -- Parameters
-- 
genEDecl (PClaim fc rc v fopts ty) =
  Just EDNil -- we don't care for type signatures
genEDecl d = error $ "genEDecl: unimplemented -- " ++ show d

genIR : Module -> ErrorOr EMod
genIR m = do
  ds <- mapM genEDecl m.decls
  Just (EM "example" ds)

-------------------------------------------------------------------------------


{-
ind : Tab -> String
ind Z = ""
ind (S t) = " " ++ ind t

iPutStr : Tab -> String -> IO ()
iPutStr Z s = putStr s
iPutStr (S t) s = putStr " " >> iPutStr t s

-------------------------------------------------------------------------------

mutual
  genPDo : Tab -> String -> PDo -> IO ()
  genPDo t sfx (DoExp fc tm) = genPTerm t tm >> putStrLn sfx
  genPDo t sfx stmt = die $ "genPDo: unimplemented -- " -- ++ showDo stmt

  genPTerm : Tab -> PTerm -> IO ()
  genPTerm t (PRef fc n) = case displayName n of
    (_, n') => iPutStr t n'
  genPTerm t (PDoBlock fc mns []) = die "genPTerm: empty do block"
  genPTerm t (PDoBlock fc mns (s :: ss)) = do
    traverse_ (genPDo t ",") (init (s :: ss))
    genPDo t "." (last (s :: ss))
  genPTerm _ tm = die $ "genPTerm: unimplemented -- " ++ show tm

genPClause : PClause -> IO ()
genPClause (MkPatClause fc lhs rhs wb) = do
  genPTerm Z lhs
  putStr "() -> \n"
  genPTerm 2 rhs

-- ignore where blocks for now...
genPClause (MkWithClause fc lhs wps wfs cs) =
  die "genPClause: with clauses unsupported"
genPClause (MkImpossible fc lhs) = pure ()

genPDecl : PDecl -> IO ()
genPDecl (PClaim fc rc v fopts ty) = pure ()
  -- we don't care for type signatures
genPDecl (PDef fc [c]) = genPClause c
genPDecl (PDef fc (c :: cs)) = genPClause c
genPDecl x = die $ "genPDecl: unimplemented -- " ++ show x

gen : List PDecl -> IO ()
gen [] = pure ()
gen (d :: ds) = genPDecl d
-}

-----------------------------------------------------------------------------

main : IO ()
main = do
  -- let fName = "Main5.idr"
  -- let srcLoc = PhysicalIdrSrc (mkModuleIdent Nothing "Main5")
  let fName = "ParseEx.idr"
  let srcLoc = PhysicalIdrSrc (mkModuleIdent Nothing "ParseEx")

  Right rawSrc <- readFile fName
    | Left err => printLn err
  let Right (ws, st, mod) = runParser srcLoc Nothing rawSrc (prog srcLoc)
    | Left err => printLn err

  -- traverse_ printLn $ mod.decls
  -- traverse_ genPDecl mod.decls
  let Just ir = genIR mod
    | Err (StdErr err) => die err
    
  -- putStrLn (ppEMod ir)
  putStrLn (show ir)
  

