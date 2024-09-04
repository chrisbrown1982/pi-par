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

traverseWithSt : Monad m
              => {st : Type}
              -> (f : st -> a -> m (b, st))
              -> st
              -> List a
              -> m (List b, st)
traverseWithSt f st [] = pure ([], st)
traverseWithSt f st (x :: xs) = do
  (x', st') <- f st x
  (xs', st'') <- traverseWithSt f st' xs
  pure (x' :: xs', st'')

-------------------------------------------------------------------------------
-- Erlang IR

public export
data EPat : Type where
  EPVar : String -> EPat

data EStmt : Type where
  ESVar   : String -> EStmt
  ESApp   : String -> List EStmt -> EStmt
  ESString : String -> EStmt
  ESMatchOp : List EPat -> EStmt -> EStmt
  ESMacMod : EStmt
  ESList : List EStmt -> EStmt
  ESSelf : EStmt
  ESRecv : List (EPat, List EStmt) -> EStmt

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

prelude : String -> EStmt
prelude "printLn"  = ESVar "io:format" -- N.B. newlines not preserved
prelude "putStrLn" = ESVar "io:format"
prelude "putStr"   = ESVar "io:format"
prelude "print"    = ESVar "io:format"
prelude "Halt"     = ESApp "exit" [ESVar "halt"]
prelude str        = ESVar str

toEVarName : String -> String
toEVarName str =
  case strM str of
    StrNil => assert_total (idris_crash "toEVarName: impossible empty string")
    StrCons x xs => strCons (toUpper x) xs

lookup : Env -> String -> EStmt
lookup [] str = prelude str
lookup (x :: xs) str =
  if str == x then ESVar (toEVarName x) else lookup xs str

getNameStrFrmName : Env -> Name.Name -> ErrorOr String
getNameStrFrmName env n =
  case displayName n of
      (Nothing, n') => case lookup env n' of
        ESVar n'' => Just n''
        n'' => error
             $ "getNameStrFrmName: var lookup unexpected expand -- " ++ show n''
      _ => error "getNameStrFrmName -- non-empty namespace"

getNameStmtFrmName : Env -> Name.Name -> ErrorOr EStmt
getNameStmtFrmName env n =
  case displayName n of
      (Nothing, n') => Just (lookup env n')
      _ => error "getNameStmtFrmName -- non-empty namespace"

getNameFrmTerm : Env -> PTerm -> ErrorOr EStmt
getNameFrmTerm env (PRef fc' n) =
  getNameStmtFrmName env n
getNameFrmTerm env (PApp fc' f x) =
  getNameFrmTerm env f
getNameFrmTerm env tm =
  error $ "getNameFrmTerm -- unimplemented -- " ++ show tm

getNameFrmClause : Env -> PClause -> ErrorOr String
getNameFrmClause env (MkPatClause fc lhs _ _) = do
  ESVar n <- getNameFrmTerm env lhs
    | n =>
      error $ "getNameFrmClause: name causes unexpected expansion -- " ++ show n
  pure n
getNameFrmClause env (MkWithClause fc lhs _ _ _) =
  error "getNameFrmClause -- MkWithClause"
getNameFrmClause env (MkImpossible fc lhs) =
  error "getNameFrmClause -- MkImpossible"

-------------------------------------------------------------------------------
-- IR Generation -- Patterns

genEPats : Env -> PTerm -> ErrorOr (List EPat, Env)
genEPats env (PRef fc n) = do
  n' <- getNameStrFrmName env n
  pure ([EPVar (toEVarName n')], n' :: env)
genEPats env (PApp fc (PRef _ _) x) =
  genEPats env x
genEPats env (PApp fc f x) = do
  (xs, env')  <- genEPats env f
  (ys, env'') <- genEPats env' x
  pure (xs ++ ys, env'')
genEPats env (PPair fc l r) = do
  (xs, env') <- genEPats env l
  (ys, env'') <- genEPats env' r
  pure (xs ++ ys, env'')
genEPats env p = error $ "genEPats: unimplemeted -- " ++ show p

genEPatsTop : PTerm -> ErrorOr (List EPat, Env)
genEPatsTop (PRef fc n) = Just ([], []) -- no arguments
genEPatsTop p = genEPats [] p

-------------------------------------------------------------------------------
-- IR Generation -- Terms/Expressions/Statements

mutual
  genEStmtsDo : Env
             -> List PDo
             -> ErrorOr (List EStmt, Env)
  genEStmtsDo env [] = pure ([], env)
  genEStmtsDo env ((DoExp fc tm) :: dss) = do
    (es, env') <- genEStmts env tm
    (rest, env'') <- genEStmtsDo env' dss
    pure (es ++ rest, env'')
  genEStmtsDo env ((DoBindPat fc lhs rhs []) :: dss) = do
    ([x,y], env') <- genEPats env lhs
      | (xs, env') => do
        (e, env'') <- genEStmt env' rhs
        (rest, env''') <- genEStmtsDo env'' dss
        pure (ESMatchOp xs e :: rest, env''')
    (e@(ESApp "spawn" _), env'') <- genSpawn env' rhs -- SPAWN
      | (e, env'') => do
        (rest, env''') <- genEStmtsDo env'' dss
        pure (ESMatchOp [x,y] e :: rest, env''')
    (rest, env''') <- genEStmtsDo env'' dss
    pure (ESMatchOp [x] e :: rest, env''')
  genEStmtsDo env (DoBind fc nfc x rhs@(PApp _ (PRef _ fn) (PRef _ ch)) :: dss) = do
    x' <- getNameStrFrmName env x
    case displayName fn of
      (Nothing, "Recv") => do
        (rest, env') <- genEStmtsDo (x' :: env) dss
        pure ([ESRecv [(EPVar (toEVarName x'), rest)]], env')
      _ => do
        (rhs', env') <- genEStmt (x' :: env) rhs
        (rest, env'') <- genEStmtsDo env' dss
        pure (rhs' :: rest, env'')
  genEStmtsDo env (DoBind fc nfc x rhs :: dss) = do
    error $ "genEStmtsDo: unimplemented -- DoBind"
  genEStmtsDo env (DoBindPat _ _ _ _ :: dss) =
    error $ "genEStmtsDo: unimplemented -- DoBindPat"
  genEStmtsDo env (DoLet _ _ _ _ _ _ :: dss) =
    error $ "genEStmtsDo: unimplemented -- DoLet"
  genEStmtsDo env (DoLetPat _ _ _ _ _ :: dss) =
    error $ "genEStmtsDo: unimplemented -- DoLetPat"
  genEStmtsDo env (DoLetLocal _ _ :: dss) =
    error $ "genEStmtsDo: unimplemented -- DoLetLocal"
  genEStmtsDo env (DoRewrite _ _ :: ds) =
    error $ "genEStmtsDo: unimplemented -- DoRewrite"

  genEStmtsStr : PStr -> ErrorOr String
  genEStmtsStr (StrLiteral fc str) = Just str
  genEStmtsStr (StrInterp fc tm) =
    error $ "genEStmtsStr: unimplemented -- StrInterp"

  genEStmts : Env -> PTerm -> ErrorOr (List EStmt, Env)
  genEStmts env (PRef fc n) = do
    stmt <- getNameStmtFrmName env n
    pure ([stmt], env)
  genEStmts env (PApp fc f x) = do
    (ESApp fn xs, env')  <- genEStmt env f
      | (ESVar fn, env') => do
        (x', env'') <- genEStmt env' x
        pure ([ESApp fn [x']], env'')
      | f' => error $ "TODO: " ++ show f'
    (x', env') <- genEStmt env x
    pure ([ESApp fn (xs ++ [x'])], env')
  genEStmts env (PString fc ht strs) = do
    strs' <- mapM genEStmtsStr strs
    pure ([ESString (concat strs')], env)
  genEStmts env (PDoBlock fc mns dss) =
    genEStmtsDo env dss
  genEStmts env tm = error $ "genEStmts: unimplemented -- "  ++ show tm

  genEStmt : Env -> PTerm -> ErrorOr (EStmt, Env)
  genEStmt env tm = do
    ((stmt :: _), env') <- genEStmts env tm
      | ([], _) => error $ "genEStmt: no statements generated"
    pure (stmt, env')

  genSpawn : Env -> PTerm -> ErrorOr (EStmt, Env)
  genSpawn env tm@(PApp _ (PApp _ (PApp _ (PRef _ fn) (PRef _ ty1)) (PRef _ ty2)) (PRef _ p)) =
    case displayName fn of
      (Nothing, "Spawn") => do
        pStr <- getNameStmtFrmName env p
        Just (ESApp "spawn" [ESMacMod, pStr, ESList [ESVar "chan", ESSelf]], env)
      _ => genEStmt env tm
  genSpawn env tm = genEStmt env tm

-------------------------------------------------------------------------------
-- IR Generation -- Clauses/Statements

genEClause : PClause -> ErrorOr (List EPat, List EStmt)
genEClause (MkPatClause fc lhs rhs []) = do
  (pats, env) <- genEPatsTop lhs
  (stmts, _) <- genEStmts env rhs
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
