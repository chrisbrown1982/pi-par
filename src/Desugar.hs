module Desugar where

import Syntax 

import qualified Unbound.Generics.LocallyNameless as Unbound

transStmts :: [ Stmt ] -> Term 
transStmts [] = error "Empty do block"
transStmts [ (Bind n t) ] = error "A bind cannot be the last statment in a do expression"
transStmts [ (Seq t) ]    = t
transStmts (Bind n t : stmts) = App (App (Var (Unbound.string2Name "bindEq")) (Arg Rel t)) (Arg Rel lam)
                                  where
                                    lam = Lam Rel (Unbound.bind n (transStmts stmts)) 
transStmts (Seq t : stmts)    = App (App (Var (Unbound.string2Name "bind")) (Arg Rel t)) (Arg Rel (transStmts stmts))

transDo :: Stmts -> Term 
transDo (MkStmts stmts) = transStmts stmts

deSugarTerm :: Term -> Term 
deSugarTerm TyType = TyType
deSugarTerm (Var name) = Var name 
deSugarTerm (Lam x body) = Lam x body
deSugarTerm (App t1 arg) = App t1 arg 
deSugarTerm (TyPi t1 t2 t3) = TyPi t1 t2 t3
deSugarTerm (Ann term ty) = Ann (deSugarTerm term) ty
deSugarTerm (Pos po term) = Pos po (deSugarTerm term) 
deSugarTerm TrustMe = TrustMe
deSugarTerm PrintMe = PrintMe
deSugarTerm (Let term term2) = Let (deSugarTerm term) term2
deSugarTerm TyUnit = TyUnit
deSugarTerm LitUnit = LitUnit
deSugarTerm TyBool = TyBool
deSugarTerm (LitBool b) = LitBool b
deSugarTerm (If t1 t2 t3) = If (deSugarTerm t1) (deSugarTerm t2) (deSugarTerm t3)
deSugarTerm (TySigma term term2) = TySigma (deSugarTerm term) term2
deSugarTerm (Prod t1 t2) = Prod (deSugarTerm t1) (deSugarTerm t2) 
deSugarTerm (LetPair t1 t2) = LetPair (deSugarTerm t1) t2
deSugarTerm (TyEq t1 t2) = TyEq (deSugarTerm t1) (deSugarTerm t2) 
deSugarTerm Refl = Refl 
deSugarTerm (Subst t1 t2) = Subst (deSugarTerm t1) (deSugarTerm t2) 
deSugarTerm (Contra t) = Contra (deSugarTerm t)
deSugarTerm (TyCon x y) = TyCon x y
deSugarTerm (DataCon x y) = DataCon x y
deSugarTerm (Case t m) = Case (deSugarTerm t) m
deSugarTerm (Do stmts) = transDo stmts