-- Tomasz Zakrzewski, tz336079, 2015-2016
-- This module is responsible for static analysis of the code.
module StaticAnalyser where

import Data.List

import AbsLatte
import ErrM
import LexLatte
import ParLatte
import PrintLatte

-- String extraction ---------------------------------------------------------------------------------------------------
-- Extractins a list of all strings occuring in the program.
extractStrings :: Program -> [String]
extractStrings (Program topDefs) = nub $ extractStringsTopDefs topDefs

extractStringsTopDefs :: [TopDef] -> [String]
extractStringsTopDefs = concat . map (extractStringsTopDef)

extractStringsTopDef :: TopDef -> [String]
extractStringsTopDef (FnDef (FunDef _ _ _ (Block stmts))) = extractStringsStmts stmts
extractStringsTopDef (ClassDef _ cdefs) = extractStringsCDefs cdefs
extractStringsTopDef (ClassExtDef _ _ cdefs) = extractStringsCDefs cdefs

extractStringsCDefs :: [CDef] -> [String]
extractStringsCDefs = concat . map (extractStringsCDef)

extractStringsCDef :: CDef -> [String]
extractStringsCDef (Method funDef) = extractStringsTopDef (FnDef funDef)
extractStringsCDef _ = []

extractStringsStmts :: [Stmt] -> [String]
extractStringsStmts = concat . map (extractStringsStmt)

extractStringsStmt :: Stmt -> [String]
extractStringsStmt (BStmt (Block stmts)) = extractStringsStmts stmts
extractStringsStmt (Decl Str items) = concat $ map (extractStringsItem) items
extractStringsStmt (Ass _ expr) = extractStringsExpr expr
extractStringsStmt (Ret expr) = extractStringsExpr expr
extractStringsStmt (Cond expr stmt) = (extractStringsExpr expr) ++ (extractStringsStmt stmt)
extractStringsStmt (CondElse expr stmt1 stmt2) = (extractStringsExpr expr) ++ (extractStringsStmt stmt1) ++
        (extractStringsStmt stmt2)
extractStringsStmt (While expr stmt) = extractStringsStmt (Cond expr stmt)
extractStringsStmt (For _ _ lval stmt) = (extractStringsLVal lval) ++ (extractStringsStmt stmt)
extractStringsStmt (SExp expr) = extractStringsExpr expr
extractStringsStmt _ = []

extractStringsItem :: Item -> [String]
extractStringsItem (Init _ expr) = extractStringsExpr expr
extractStringsItem (NoInit _) = [""]

extractStringsExpr :: Expr -> [String]
extractStringsExpr (EString str) = [str]
extractStringsExpr (EApp (FnApp _ exprs)) = concat $ map (extractStringsExpr) exprs
extractStringsExpr (EAdd expr1 Plus expr2) = (extractStringsExpr expr1) ++ (extractStringsExpr expr2)
extractStringsExpr _ = []

extractStringsLVal :: LVal -> [String]
extractStringsLVal (LValFunApp fnApp) = extractStringsExpr (EApp fnApp)
-- TODO - methods
extractStringsLVal _ = []