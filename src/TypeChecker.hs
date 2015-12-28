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

data ExtType = NormalType Type | FunType Env Type [Arg] Block
    deriving (Eq, Show)
data TypecheckError = ExactError String | IdentNotFound Ident | UnexpectedExtType Ident ExtType | 
        UnexpectedRetType Type Type | UnexpectedType Type Type | ArgMismatch Arg | WrongArgsNo Int Int |
        NotNumeric Type | NotBoolConvertible Type

    deriving (Eq, Show)
type Env = Map.Map Ident ExtType
type Eval a = ExceptT TypecheckError (State Env) a

typeCheck :: Program -> Maybe String
typeCheck program = case fst (runState (runExceptT (checkProgram program)) Map.empty) of
    (Right _) -> Nothing
    (Left exc) -> case exc of
        (ExactError msg) -> Just msg
        err -> Just $ "Unknown error at top level: " ++ (show err)

checkProgram :: Program -> Eval ()
checkProgram (Program topDefs) = do
    mapM_ (checkTopDef) topDefs
    mainType <- getExtType (Ident "main")
    case mainType of
        (FunType _ retType args block) -> do
            env <- get  -- We need current env b/c of declarations
            -- TODO no top-level args for now
            checkFnInv retType args [] block
        _ -> throwE (ExactError $ "'main' is not a function. The actual type is: " ++ (show mainType))

checkTopDef :: TopDef -> Eval ()
checkTopDef (FnDef retType ident args block) = checkFnDef retType ident args block

checkFnDef :: Type -> Ident -> [Arg] -> Block -> Eval ()
checkFnDef retType ident args block = do
    env <- get
    put $ Map.insert ident (FunType env retType args block) env

getExtType :: Ident -> Eval ExtType
getExtType ident = do
    env <- get
    case Map.lookup ident env of
        (Just t) -> return t
        Nothing -> throwE (IdentNotFound ident)

getType :: Ident -> Eval Type
getType ident = do
    extType <- getExtType ident
    case extType of
        (NormalType t) -> return t
        _ -> throwE (UnexpectedExtType ident extType)

checkFnInv :: Type -> [Arg] -> [Ident] -> Block -> Eval ()
checkFnInv retType args passedIdents block = do
    env <- get
    bindArgs args passedIdents
    actRetType <- checkBlock block
    put env
    if retType == actRetType then
        return ()
    else throwE (UnexpectedRetType retType actRetType)

bindArgs :: [Arg] -> [Ident] -> Eval ()
bindArgs args passedIdents = do
    let (argsCnt, passedCnt) = (length args, length passedIdents)
    if argsCnt == passedCnt then
        mapM_ (\(arg, ident) -> bindArg arg ident) $ zip args passedIdents
    else throwE (WrongArgsNo argsCnt passedCnt)

bindArg :: Arg -> Ident -> Eval ()
bindArg (Arg t ident) passedIdent = do
    passedT <- getType passedIdent
    if passedT == t then
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
    env <- get
    res <- checkBlock block
    put env
    return (Just res)
checkStmt (Decl t items) = do
    mapM_ (declareItem t) items
    return Nothing
checkStmt (Ass ident expr) = do
    l <- getType ident
    r <- checkExpr expr
    if l == r then
        return (Just l)
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
        env <- get
        checkStmt stmtTrue
        put env
        checkStmt stmtFalse
        put env
        return Nothing
    else throwE (NotBoolConvertible condT)
checkStmt (While expr stmt) = checkStmt (Cond expr stmt)
checkStmt (SExp expr) = do
    res <- checkExpr expr
    return (Just res)

declareItem :: Type -> Item -> Eval ()
declareItem t (NoInit ident) = declare t ident
declareItem t (Init ident expr) = do
    resT <- checkExpr expr
    if resT == t then
        declare t ident
    else throwE (UnexpectedType t resT)

declare :: Type -> Ident -> Eval ()
declare t ident = do
    env <- get
    put $ Map.insert ident (NormalType t) env

isNumeric :: Type -> Bool
isNumeric Int = True
isNumeric _ = False

isBoolConvertible :: Type -> Bool
isBoolConvertible Bool = True
isBoolConvertible t = isNumeric t

checkExpr :: Expr -> Eval Type
checkExpr _ = return Int
