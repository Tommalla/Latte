-- Tomasz Zakrzewski, tz336079, 2015
-- This module is responsible for the static type checking.
module TypeChecker where

import Control.Monad.Trans.Except
import Control.Monad.State
import qualified Data.Map as Map

import AbsLatte
import ErrM
import LexLatte
import ParLatte
import PrintLatte

data TypecheckError = ExactError String | IdentNotFound Ident | UnexpectedRetType Type Type | UnexpectedType Type Type | 
        ArgMismatch Arg | WrongArgsNo Int Int | NotNumeric Type | NotBoolConvertible Type | NotAnArray Ident
    deriving (Eq, Show)
type FunType = (Env, Type, [Arg], Block)
type PEnv = Map.Map Ident FunType
type Env = Map.Map Ident Type
type Eval a = ExceptT TypecheckError (State (Env, PEnv)) a

typeCheck :: Program -> Maybe String
typeCheck program = case fst (runState (runExceptT (checkProgram program)) (Map.empty, Map.empty)) of
    (Right _) -> Nothing
    (Left exc) -> case exc of
        (ExactError msg) -> Just msg
        err -> Just $ "Unknown error at top level: " ++ (show err)

checkProgram :: Program -> Eval ()
checkProgram (Program topDefs) = do
    mapM_ (checkTopDef) topDefs
    checkFnApp (Ident "main") []  -- TODO toplevel args still unsupported
    return ()

checkTopDef :: TopDef -> Eval ()
checkTopDef (FnDef retType ident args block) = checkFnDef retType ident args block

checkFnDef :: Type -> Ident -> [Arg] -> Block -> Eval ()
checkFnDef retType ident args block = do
    (env, penv) <- get
    put $ (env, Map.insert ident (env, retType, args, block) penv)

getFunction :: Ident -> Eval FunType
getFunction ident = do
    (_, penv) <- get
    case Map.lookup ident penv of
        (Just fn) -> return fn
        Nothing -> throwE (IdentNotFound ident)

getType :: Ident -> Eval Type
getType ident = do
    (env, _) <- get
    case Map.lookup ident env of
        (Just t) -> return t
        Nothing -> throwE (IdentNotFound ident)

checkFnApp :: Ident -> [Type] -> Eval Type
checkFnApp ident passedTypes = do
    (env, retType, args, block) <- getFunction ident
    (oldEnv, penv) <- get
    put (env, penv)
    res <- checkFnInv retType args passedTypes block
    put (oldEnv, penv)
    return res
    where
        checkFnInv :: Type -> [Arg] -> [Type] -> Block -> Eval Type
        checkFnInv retType args passedTypes block = do
            mem <- get
            bindArgs args passedTypes
            actRetType <- checkBlock block
            put mem
            if retType == actRetType then
                return retType
            else throwE (UnexpectedRetType retType actRetType)

bindArgs :: [Arg] -> [Type] -> Eval ()
bindArgs args passedTypes = do
    let (argsCnt, passedCnt) = (length args, length passedTypes)
    if argsCnt == passedCnt then
        mapM_ (\(arg, t) -> bindArg arg t) $ zip args passedTypes
    else throwE (WrongArgsNo argsCnt passedCnt)

bindArg :: Arg -> Type -> Eval ()
bindArg (Arg t ident) passedType = do
    if passedType == t then
        declare t ident
    else throwE (ArgMismatch (Arg t ident))

checkBlock :: Block -> Eval Type
checkBlock (Block stmts) = do
    checkBlockHelper stmts stmts
    where
        checkBlockHelper :: [Stmt] -> [Stmt] -> Eval Type
        checkBlockHelper (stmt : t) stmts = do
            retType <- checkStmt stmt
            case retType of
                (Just result) -> return result
                Nothing -> checkBlockHelper t stmts
        checkBlockHelper [] _ = return Void

checkStmt :: Stmt -> Eval (Maybe Type)
checkStmt Empty = return Nothing
checkStmt (BStmt block) = do
    mem <- get
    res <- checkBlock block
    put mem
    return (Just res)
checkStmt (Decl t items) = do
    mapM_ (declareItem t) items
    return Nothing
checkStmt (Ass ident expr) = do
    l <- getType ident
    r <- checkExpr expr
    if l == r then
        return Nothing
    else throwE (UnexpectedType l r)
checkStmt (Incr ident) = do
    t <- getType ident
    if isNumeric t then
        return Nothing
    else throwE (NotNumeric t)
checkStmt (Decr ident) = checkStmt (Incr ident)
checkStmt (Ret expr) = do
    res <- checkExpr expr
    return (Just res)
checkStmt VRet = return (Just Void)
checkStmt (Cond expr stmt) = checkStmt (CondElse expr stmt Empty)
checkStmt (CondElse expr stmtTrue stmtFalse) = do
    condT <- checkExpr expr
    if isBoolConvertible condT then do
        mem <- get
        checkStmt stmtTrue
        put mem
        checkStmt stmtFalse
        put mem
        return Nothing
    else throwE (NotBoolConvertible condT)
checkStmt (While expr stmt) = checkStmt (Cond expr stmt)
checkStmt (SExp expr) = do
    checkExpr expr
    return Nothing

declareItem :: Type -> Item -> Eval ()
declareItem t (NoInit ident) = declare t ident
declareItem t (Init ident expr) = do
    resT <- checkExpr expr
    if resT == t then
        declare t ident
    else throwE (UnexpectedType t resT)

declare :: Type -> Ident -> Eval ()
declare t ident = do
    (env, penv) <- get
    put $ (Map.insert ident t env, penv)

isNumeric :: Type -> Bool
isNumeric Int = True
isNumeric _ = False

isBoolConvertible :: Type -> Bool
isBoolConvertible Bool = True
isBoolConvertible t = isNumeric t

checkExpr :: Expr -> Eval Type
checkExpr (ENewArr t _) = return (Array t)
checkExpr (EArrElem ident _) = do
    t <- getType ident
    case t of
        (Array resT) -> return resT
        _ -> throwE (NotAnArray ident)
checkExpr (EVar ident) = do
    t <- getType ident
    return t
checkExpr (ELitInt _) = return Int
checkExpr ELitTrue = return Bool
checkExpr ELitFalse = return Bool
checkExpr (EApp ident exprs) = do 
   passedTypes <- mapM (checkExpr) exprs
   checkFnApp ident passedTypes
checkExpr (EString _) = return Str
checkExpr (Neg expr) = do
    t <- checkExpr expr
    if isNumeric t then
        return Bool
    else throwE (NotNumeric t)
checkExpr (Not expr) = do
    t <- checkExpr expr
    if isBoolConvertible t then
        return Bool
    else throwE (NotBoolConvertible t)
checkExpr (EMul expr1 _ expr2) = checkArithmeticExpr expr1 expr2
checkExpr (EAdd expr1 _ expr2) = checkArithmeticExpr expr1 expr2
checkExpr (ERel expr1 _ expr2) = checkArithmeticExpr expr1 expr2
checkExpr (EAnd expr1 expr2) = checkBoolExpr expr1 expr2
checkExpr (EOr expr1 expr2) = checkBoolExpr expr1 expr2

checkArithmeticExpr :: Expr -> Expr -> Eval Type
checkArithmeticExpr expr1 expr2 = do
    t1 <- checkExpr expr1
    t2 <- checkExpr expr2
    if t1 == t2 then  -- TODO allow conversions
        if isNumeric t1 then
            return t1
        else throwE (NotNumeric t1)
    else throwE (UnexpectedType t1 t2)

checkBoolExpr :: Expr -> Expr -> Eval Type
checkBoolExpr expr1 expr2 = do
    t1 <- checkExpr expr1
    t2 <- checkExpr expr2
    if (isBoolConvertible t1) && (isBoolConvertible t2) then
        return Bool
    else throwE (UnexpectedType t1 t2)
