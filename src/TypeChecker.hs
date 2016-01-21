-- Tomasz Zakrzewski, tz336079, 2015
-- This module is responsible for the static type checking.
module TypeChecker where

import Control.Monad.Trans.Except
import Control.Monad.State
import qualified Data.Map as Map
import Data.Maybe
import Debug.Trace (trace)

import AbsLatte
import Common
import ErrM
import LexLatte
import ParLatte
import PrintLatte

data TypecheckError = ExactError String | IdentNotFound Ident | UnexpectedRetType Type Type | UnexpectedType Type Type |
        ArgMismatch Type Arg | WrongArgsNo Int Int | NotNumeric Type | NotBoolConvertible Type | NotAnArray LVal |
        IllegalStringArithmetic Expr | RetTypeMismatch Type Type | Redeclaration Ident
    deriving (Eq)
type FunType = (Env, Type, [Arg], Block)
type PEnv = Map.Map Ident FunType
type Env = Map.Map Ident (Type, Int) -- Type, level of declaration
type Eval a = ExceptT TypecheckError (State (Env, PEnv, Int)) a -- Env, PEnv, current block level

instance Show TypecheckError where
    show (ExactError str) = str
    show (IdentNotFound ident) = "The identifier '" ++ show ident ++ "' was not found."
    show (UnexpectedRetType expected found) = "Unexpected return type: expected '" ++ show expected ++
            "', found '" ++ show found ++ "'."
    show (UnexpectedType expected found) = "Unexpected type: expected '" ++ show expected ++ "', found '" ++
            show found ++ "'."
    show (ArgMismatch found (Arg expT expIdent)) = "Wrong argument: for '" ++ show expIdent ++ "' expected type '" ++
            show expT ++ "', found '" ++ show found ++ "'."
    show (WrongArgsNo expected found) = "Wrong number of arguments passed: expected " ++ show expected ++ " found " ++
            show found ++ "."
    show (NotNumeric t) = "Expected a numeric type, found: '" ++ show t ++ "'."
    show (NotBoolConvertible t) = "Expected a bool-convertible type, found: '" ++ show t ++ "'."
    show (NotAnArray expr) = "'" ++ show expr ++ "' expected to be an array."
    show (IllegalStringArithmetic expr) = "Tried to perform arithmetic on strings other than '+' in expression: '" ++
            show expr ++ "'."
    show (RetTypeMismatch expected found) = "Wrong return type. Expected '" ++ show expected ++ "', found '" ++
            show found ++ "'."
    show (Redeclaration ident) = "Tried to declare '" ++ show ident ++ "' for the second time in the same block."

incLevel :: Eval ()
incLevel = do
    (env, penv, level) <- get
    put (env, penv, level + 1)

getLevel :: Eval Int
getLevel = do
    (_, _, level) <- get
    return level

typeCheck :: Program -> Maybe String
typeCheck program = case fst (runState (runExceptT (checkProgram program)) (Map.empty, Map.empty, 0)) of
    (Right _) -> Nothing
    (Left exc) -> case exc of
        (ExactError msg) -> Just msg
        err -> Just $ "Unknown error at top level: " ++ (show err)

checkProgram :: Program -> Eval ()
checkProgram (Program topDefs) = do
    mapM_ (\(t, name, args) -> registerFnDef t (Ident name) args (Block [Empty])) builtins
    mapM_ (\(FnDef (FunDef retType ident args block)) -> registerFnDef retType ident args block) topDefs
    mapM_ (checkTopDef) topDefs
    checkFnApp (Ident "main") []  -- TODO toplevel args still unsupported
    return ()

checkTopDef :: TopDef -> Eval ()
checkTopDef (FnDef (FunDef retType ident args block)) = catchE (checkFnDef retType args block) (\exc ->
    throwE $ ExactError $ "In function '" ++ show ident ++ "': " ++ show exc)

-- Registers the function in env.
registerFnDef :: Type -> Ident -> [Arg] -> Block -> Eval ()
registerFnDef retType ident args block = do
    (env, penv, level) <- get
    put $ (env, Map.insert ident (env, retType, args, block) penv, level)

-- Registers args of necessary type and checks block.
checkFnDef :: Type -> [Arg] -> Block -> Eval ()
checkFnDef retType args block = do
    mem <- get
    mapM_ (registerArg) args
    actRetType <- checkTopLevelBlock block
    put mem
    if retType == actRetType then
        return ()
    else throwE $ UnexpectedRetType retType actRetType
    where
        registerArg :: Arg -> Eval ()
        registerArg (Arg t ident) = declare t ident

checkFnApp :: Ident -> [Type] -> Eval Type
checkFnApp ident passedTypes = do
    (env, retType, args, block) <- getFunction ident
    (oldEnv, penv, level) <- get
    put (env, penv, level)
    bindArgs args passedTypes
    put (oldEnv, penv, level)
    return retType

getFunction :: Ident -> Eval FunType
getFunction ident = do
    (_, penv, _) <- get
    case Map.lookup ident penv of
        (Just fn) -> return fn
        Nothing -> throwE (IdentNotFound ident)

getType :: Ident -> Eval Type
getType ident = do
    (env, _, _) <- get
    case Map.lookup ident env of
        (Just (t, _)) -> return t
        Nothing -> throwE (IdentNotFound ident)

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
    else throwE (ArgMismatch passedType (Arg t ident))

checkTopLevelBlock :: Block -> Eval Type
checkTopLevelBlock block = do
    res <- checkBlock block
    case res of
        (Just t) -> return t
        Nothing -> return Void

checkBlock :: Block -> Eval (Maybe Type)
checkBlock (Block stmts) = do
    checkBlockHelper stmts stmts
    where
        checkBlockHelper :: [Stmt] -> [Stmt] -> Eval (Maybe Type)
        checkBlockHelper (stmt : t) stmts = do
            retType <- checkStmtTopLevel stmt
            case retType of
                (Just result) -> return (Just result)
                Nothing -> checkBlockHelper t stmts
        checkBlockHelper [] _ = return Nothing

-- This method typechecks the statement and catches errors to raise them again with more information.
checkStmtTopLevel :: Stmt -> Eval (Maybe Type)
checkStmtTopLevel stmt = catchE (checkStmt stmt) (
        \exc -> throwE (ExactError $ "In statement '" ++ show stmt ++ "': " ++ show exc))

checkStmt :: Stmt -> Eval (Maybe Type)
checkStmt Empty = return Nothing
checkStmt (BStmt block) = do
    mem <- get
    incLevel
    res <- checkBlock block
    put mem
    return res
checkStmt (Decl t items) = do
    mapM_ (declareItem t) items
    return Nothing
checkStmt (Ass lval expr) = do
    l <- getLValType lval
    r <- checkExpr expr
    if l == r then
        return Nothing
    else throwE (UnexpectedType l r)
checkStmt (Incr lval) = do
    t <- getLValType lval
    if isNumeric t then
        return Nothing
    else throwE (NotNumeric t)
checkStmt (Decr lval) = checkStmt (Incr lval)
checkStmt (Ret expr) = do
    res <- checkExpr expr
    return (Just res)
checkStmt VRet = return (Just Void)
checkStmt (Cond expr stmt) = checkStmt (CondElse expr stmt Empty)
checkStmt (CondElse expr stmtTrue stmtFalse) = do
    case expr of
        ELitTrue -> oneClauseCondStmt stmtTrue
        ELitFalse -> oneClauseCondStmt stmtFalse
        _ -> do
            condT <- checkExpr expr
            if isBoolConvertible condT then do
                resTrue <- oneClauseCondStmt stmtTrue
                resFalse <- oneClauseCondStmt stmtFalse
                if not (isNothing resTrue) && not (isNothing resFalse) then do
                    if resTrue /= resFalse then
                        throwE $ RetTypeMismatch (fromJust resTrue) (fromJust resFalse)
                    else return resTrue
                else return Nothing
            else throwE (NotBoolConvertible condT)
    where
    oneClauseCondStmt :: Stmt -> Eval (Maybe Type)
    oneClauseCondStmt stmt = do
        mem <- get
        res <- checkStmtTopLevel stmt
        put mem
        return res
checkStmt (While expr stmt) = checkStmt (Cond expr stmt)
checkStmt (For t elemId array stmt) = do
    arrayT <- getLValType array
    arrayElemT <- case arrayT of
            (Array res) -> return res
            _ -> throwE $ NotAnArray array
    if arrayElemT /= t then
        throwE $ UnexpectedType t arrayElemT
    else do
        mem <- get
        declare t elemId
        res <- checkStmt stmt
        put mem
        return res
checkStmt (SExp expr) = do
    checkExpr expr
    return Nothing

checkFunApp :: FunApp -> Eval Type
checkFunApp (FnApp ident exprs) = do
    passedTypes <- mapM (checkExpr) exprs
    checkFnApp ident passedTypes

getLValType :: LVal -> Eval Type
getLValType (LValVal ident) = getType ident
getLValType (LValFunApp funApp) = checkFunApp funApp
getLValType (LValMethApp methodApp) = return Void -- TODO
getLValType (LValArrAcc (ArrElem lval expr)) = do
    t <- getLValType lval
    tExp <- checkExpr expr
    if tExp /= Int then
        throwE $ UnexpectedType Int tExp
    else
        case t of
            (Array resT) -> return resT
            _ -> throwE (NotAnArray lval)
getLValType (LValAttr clsAttrAcc) = return Void -- TODO

declareItem :: Type -> Item -> Eval ()
declareItem t (NoInit ident) = declare t ident
declareItem t (Init ident expr) = do
    resT <- checkExpr expr
    if resT == t then
        declare t ident
    else throwE (UnexpectedType t resT)

declare :: Type -> Ident -> Eval ()
declare t ident = do
    (env, penv, level) <- get
    let old = Map.lookup ident env
    let oldLevel = case old of
            (Just (_, oldLevel)) -> oldLevel
            Nothing -> level - 1
    if level == oldLevel then
        throwE $ Redeclaration ident
    else
        put $ (Map.insert ident (t, level) env, penv, level)

checkExpr :: Expr -> Eval Type
checkExpr (EAttr (AttrAcc lval ident)) = do
    lvalT <- getLValType lval
    case lvalT of
        (Array t) -> case ident of
            (Ident "length") -> return Int
            _ -> throwE $ ExactError $ "Unsupported operation for array: " ++ (show (AttrAcc lval ident))
        _ -> throwE $ ExactError "Classes not supported yet"
checkExpr (ENewArr t _) = return (Array t)
checkExpr (EArrElem arrElemAcc) = getLValType (LValArrAcc arrElemAcc)
checkExpr (EVar ident) = do
    t <- getType ident
    return t
checkExpr (ELitInt _) = return Int
checkExpr ELitTrue = return Bool
checkExpr ELitFalse = return Bool
checkExpr (EApp funApp) = checkFunApp funApp
checkExpr (EString _) = return Str
checkExpr (Neg expr) = do
    t <- checkExpr expr
    if isNumeric t then
        return Int
    else throwE (NotNumeric t)
checkExpr (Not expr) = do
    t <- checkExpr expr
    if isBoolConvertible t then
        return Bool
    else throwE (NotBoolConvertible t)
checkExpr (EMul expr1 _ expr2) = checkArithmeticExpr expr1 expr2
checkExpr (EAdd expr1 Plus expr2) = do
    t1 <- checkExpr expr1
    t2 <- checkExpr expr2
    if (isString t1) && (t1 == t2) then
        return Str
    else checkArithmeticExpr expr1 expr2
checkExpr (EAdd expr1 Minus expr2) = do
    -- Minus forbidden for strings.
    t1 <- checkExpr expr1
    t2 <- checkExpr expr2
    if (isString t1) || (isString t2) then
        throwE $ IllegalStringArithmetic $ EAdd expr1 Minus expr2
    else checkArithmeticExpr expr1 expr2
checkExpr (ERel expr1 rop expr2) = do
    if rop == EQU || rop == NE then do
        t1 <- checkExpr expr1
        t2 <- checkExpr expr2
        if t1 == t2 then
            return Bool
        else throwE $ UnexpectedType t1 t2
    else do
        checkArithmeticExpr expr1 expr2
        return Bool
checkExpr (EAnd expr1 expr2) = checkBoolExpr expr1 expr2
checkExpr (EOr expr1 expr2) = checkBoolExpr expr1 expr2
checkExpr unknown = throwE $ ExactError $ "Unknown expr: " ++ (show unknown)

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
