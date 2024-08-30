module AST

import Idris.Syntax
import Idris.Parser

import Core.FC
import Core.Name

import System
import System.File

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
-- IR Generation -- Names

Env : Type
Env = List String

prelude : String -> String
prelude "printLn"  = "io:format" -- N.B. newlines not preserved
prelude "putStrLn" = "io:format"
prelude "putStr"   = "io:format"
prelude "print"    = "io:format"
prelude str        = str

toEVarName : String -> String
toEVarName str =
  case strM str of
    StrNil => assert_total (idris_crash "toEVarName: impossible empty string")
    StrCons x xs => strCons (toUpper x) xs

lookup : Env -> String -> String
lookup [] str = prelude str
lookup (x :: xs) str = if str == x then toEVarName x else lookup xs str

getNameFrmName : Env -> Name.Name -> ErrorOr String
getNameFrmName env n =
  case displayName n of
      (Nothing, n') => Just (lookup env n')
      _ => error "getNameFrmTerm -- PRef -- non-empty namespace"

getNameFrmTerm : Env -> PTerm -> ErrorOr String
getNameFrmTerm env (PRef fc' n) =
  getNameFrmName env n
getNameFrmTerm env (PApp fc' f x) =
  getNameFrmTerm env f
getNameFrmTerm env tm =
  error $ "getNameFrmTerm -- unimplemented -- " ++ show tm

getNameFrmClause : Env -> PClause -> ErrorOr String
getNameFrmClause env (MkPatClause fc lhs _ _) =
  getNameFrmTerm env lhs
getNameFrmClause env (MkWithClause fc lhs _ _ _) =
  error "getNameFrmClause -- MkWithClause"
getNameFrmClause env (MkImpossible fc lhs) =
  error "getNameFrmClause -- MkImpossible"

-------------------------------------------------------------------------------
-- IR Generation -- Patterns

genEPats : Env -> PTerm -> ErrorOr (List EPat, Env)
genEPats env (PRef fc n) = do
  n' <- getNameFrmName env n
  pure ([EPVar (toEVarName n')], n' :: env)
genEPats env (PApp fc (PRef _ _) x) =
  genEPats env x
genEPats env (PApp fc f x) = do
  (xs, env')  <- genEPats env f
  (ys, env'') <- genEPats env' x
  pure (xs ++ ys, env'')
genEPats env p = error $ "genEPats: unimplemeted -- " ++ show p

genEPatsTop : PTerm -> ErrorOr (List EPat, Env)
genEPatsTop (PRef fc n) = Just ([], []) -- no arguments
genEPatsTop p = genEPats [] p

-------------------------------------------------------------------------------
-- IR Generation -- Terms/Expressions/Statements

mutual
  genEStmtsDo : Env -> PDo -> ErrorOr (List EStmt)
  genEStmtsDo env (DoExp fc tm) = genEStmts env tm
  genEStmtsDo env (DoBind _ _ _ _) =
    error $ "genEStmtsDo: unimplemented -- DoBind"
  genEStmtsDo env (DoBindPat _ _ _ _) =
    error $ "genEStmtsDo: unimplemented -- DoBindPat"
  genEStmtsDo env (DoLet _ _ _ _ _ _) =
    error $ "genEStmtsDo: unimplemented -- DoLet"
  genEStmtsDo env (DoLetPat _ _ _ _ _) =
    error $ "genEStmtsDo: unimplemented -- DoLetPat"
  genEStmtsDo env (DoLetLocal _ _) =
    error $ "genEStmtsDo: unimplemented -- DoLetLocal"
  genEStmtsDo env (DoRewrite _ _) =
    error $ "genEStmtsDo: unimplemented -- DoRewrite"

  genEStmtsStr : PStr -> ErrorOr String
  genEStmtsStr (StrLiteral fc str) = Just str
  genEStmtsStr (StrInterp fc tm) =
    error $ "genEStmtsStr: unimplemented -- StrInterp"

  genEStmts : Env -> PTerm -> ErrorOr (List EStmt)
  genEStmts env (PRef fc n) =
    map (\n' => pure (ESVar n')) (getNameFrmName env n)
  genEStmts env (PApp fc f x) = do
    ESApp fn xs  <- genEStmt env f
      | ESVar fn => do
        x' <- genEStmt env x
        pure [ESApp fn [x']]
      | f' => error $ "TODO: " ++ show f'
    x' <- genEStmt env x
    pure [ESApp fn (xs ++ [x'])]
  genEStmts env (PString fc ht strs) = do
    strs' <- mapM genEStmtsStr strs
    pure [ESString (concat strs')]
  genEStmts env (PDoBlock fc mns dss) = do
    stmts <- mapM (genEStmtsDo env) dss
    pure (concat stmts)
  genEStmts env tm = error $ "genEStmts: unimplemented -- "  ++ show tm

  genEStmt : Env -> PTerm -> ErrorOr EStmt
  genEStmt env tm = do
    (stmt :: _) <- genEStmts env tm
      | [] => error $ "genEStmt: no statements generated"
    pure stmt

-------------------------------------------------------------------------------
-- IR Generation -- Clauses/Statements

genEClause : PClause -> ErrorOr (List EPat, List EStmt)
genEClause (MkPatClause fc lhs rhs []) = do
  (pats, env) <- genEPatsTop lhs
  stmts <- genEStmts env rhs
  Just (pats, stmts)
genEClause c = error $ "genEClause: unimplemented -- " ++ show c

-------------------------------------------------------------------------------
-- IR Generation -- Declarations

genEDecl : PDecl -> ErrorOr EDecl
genEDecl (PDef fc cs@(c :: _)) = do
  dn <- getNameFrmClause [] c
  body <- mapM genEClause cs
  pure (EDFun dn body) -- FIXME -- Parameters
-- 
genEDecl (PClaim fc rc v fopts ty) =
  Just EDNil -- we don't care for type signatures
genEDecl d = error $ "genEDecl: unimplemented -- " ++ show d

-------------------------------------------------------------------------------
-- IR Generation -- Modules

genIR : Module -> ErrorOr EMod
genIR m = do
  ds <- mapM genEDecl m.decls
  Just (EM "example" ds)

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
